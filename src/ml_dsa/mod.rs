use core::{array, mem::MaybeUninit, ops::AddAssign};

use rand_core::CryptoRngCore;
use zeroize::Zeroize;

mod coeff;
mod hash;
mod reduce;

const Q: i32 = 8380417;
const N: usize = 256;
const ZETA: i32 = 1753;
const D: usize = 13;

/// pre-computed zetas in montgomery form
/// ordered by ZETAS\[i\] = z^BitRev8(i)
/// zeta -> zeta * 2^32 (mod Q)
const ZETAS: [i32; N] = {
    let mut zetas = [0; N];
    zetas[0] = reduce::R_MOD_Q;

    let mut i = 1;
    while i < N {
        zetas[i] = reduce::mont_mul(zetas[i - 1], reduce::to_mont(ZETA));

        i += 1
    }

    let mut zetas_bitrev = [0; N];

    i = 0;
    while i < N {
        let idx = (i as u8).reverse_bits();

        zetas_bitrev[i] = match zetas[idx as usize] {
            z if z > Q / 2 => z - Q,
            z if z < -Q / 2 => z + Q,
            z => z,
        };

        i += 1;
    }

    zetas_bitrev
};

const fn vk_size(k: usize) -> usize {
    k * Poly::PACKED_10BIT + 32
}

const fn sk_size(k: usize, l: usize, eta: usize) -> usize {
    match eta {
        2 => 32 + 32 + 64 + l * Poly::PACKED_3BIT + k * (Poly::PACKED_3BIT + Poly::PACKED_13BIT),
        4 => 32 + 32 + 64 + l * Poly::PACKED_4BIT + k * (Poly::PACKED_4BIT + Poly::PACKED_13BIT),
        _ => unreachable!(),
    }
}

pub mod mldsa44 {
    use super::{sk_size, vk_size};

    const K: usize = 4;
    const L: usize = 4;
    const ETA: usize = 2;

    pub const VK_SIZE: usize = vk_size(K);
    pub const SK_SIZE: usize = sk_size(K, L, ETA);

    pub type SigningKey = super::SigningKey<K, L, ETA>;
    pub type VerifyingKey = super::VerifyingKey<K>;
}

pub mod mldsa65 {
    use super::{sk_size, vk_size};

    const K: usize = 6;
    const L: usize = 5;
    const ETA: usize = 4;

    pub const VK_SIZE: usize = vk_size(K);
    pub const SK_SIZE: usize = sk_size(K, L, ETA);

    pub type SigningKey = super::SigningKey<K, L, ETA>;
    pub type VerifyingKey = super::VerifyingKey<K>;
}

pub mod mldsa87 {
    use super::{sk_size, vk_size};

    const K: usize = 8;
    const L: usize = 7;
    const ETA: usize = 2;

    pub const VK_SIZE: usize = vk_size(K);
    pub const SK_SIZE: usize = sk_size(K, L, ETA);

    pub type SigningKey = super::SigningKey<K, L, ETA>;
    pub type VerifyingKey = super::VerifyingKey<K>;
}

fn vk_encode<const K: usize>(dst: &mut [u8], rho: &[u8; 32], t1: &PolyVec<K>) {
    dst[..32].copy_from_slice(rho);
    for (xi, z) in
        t1.v.iter()
            .zip(dst[32..].chunks_exact_mut(Poly::PACKED_10BIT))
    {
        xi.pack_simple_10bit(z.try_into().unwrap())
    }
}

struct KeyGenTmp<const K: usize, const L: usize> {
    rho_prime: [u8; 64],
    t: PolyVec<K>,
    t1: PolyVec<K>,
}

impl<const K: usize, const L: usize> Drop for KeyGenTmp<K, L> {
    fn drop(&mut self) {
        self.rho_prime.zeroize();
    }
}

pub struct VerifyingKey<const K: usize> {
    rho: [u8; 32],
    t1: PolyVec<K>,
}

impl<const K: usize> VerifyingKey<K> {
    const fn uninit() -> MaybeUninit<Self> {
        MaybeUninit::uninit()
    }

    pub fn encode(&self, dst: &mut [u8]) {
        vk_encode(dst, &self.rho, &self.t1)
    }

    #[inline]
    pub fn decode(src: &[u8]) -> Self {
        let mut uninit_vk = Self::uninit();
        let vk = unsafe { uninit_vk.assume_init_mut() };

        vk.rho.copy_from_slice(&src[..32]);

        for (xi, z) in vk
            .t1
            .v
            .iter_mut()
            .zip(src[32..].chunks_exact(Poly::PACKED_10BIT))
        {
            xi.unpack_simple_10bit(z.try_into().unwrap())
        }

        unsafe { uninit_vk.assume_init() }
    }
}

pub struct SigningKey<const K: usize, const L: usize, const ETA: usize> {
    rho: [u8; 32],
    k: [u8; 32],
    tr: [u8; 64],
    s1_hat: PolyVec<L>,
    s2_hat: PolyVec<K>,
    t0_hat: PolyVec<K>,
    a_hat: PolyMat<K, L>,
}

impl<const K: usize, const L: usize, const ETA: usize> Drop for SigningKey<K, L, ETA> {
    fn drop(&mut self) {
        self.k.zeroize();
        self.tr.zeroize();
    }
}

impl<const K: usize, const L: usize, const ETA: usize> SigningKey<K, L, ETA> {
    const fn uninit() -> MaybeUninit<Self> {
        MaybeUninit::uninit()
    }

    #[inline]
    pub fn keygen<const VK_SIZE: usize>(
        vk: &mut [u8; VK_SIZE],
        rng: &mut impl CryptoRngCore,
    ) -> Self {
        debug_assert!(vk.len() >= vk_size(K));

        let mut ksi = [0u8; 32];
        rng.fill_bytes(&mut ksi);

        let mut sk = Self::uninit();
        unsafe {
            sk.assume_init_mut().keygen_internal(vk, &ksi);
            ksi.zeroize();
            sk.assume_init()
        }
    }

    fn keygen_internal<const PUBKEY_SIZE: usize>(
        &mut self,
        vk: &mut [u8; PUBKEY_SIZE],
        ksi: &[u8; 32],
    ) {
        let mut uninit_tmp: MaybeUninit<KeyGenTmp<K, L>> = MaybeUninit::uninit();
        let tmp = unsafe { uninit_tmp.assume_init_mut() };

        let mut h = hash::Shake256::init();
        h.absorb_multi(&[ksi, &[K as u8], &[L as u8]]);
        h.squeeze(&mut self.rho);
        h.squeeze(&mut tmp.rho_prime);
        h.squeeze(&mut self.k);

        self.a_hat.expand_a(&self.rho);
        expand_s::<K, L, ETA>(&mut self.s1_hat, &mut self.s2_hat, &tmp.rho_prime);

        self.s1_hat.ntt_inplace();

        tmp.t.multiply_matvec_ntt(&self.a_hat, &self.s1_hat);
        tmp.t.reduce_invntt_tomont_inplace();

        tmp.t += &self.s2_hat;

        tmp.t.power2round(&mut tmp.t1, &mut self.t0_hat);

        vk_encode(vk, &self.rho, &tmp.t1);

        h.reset();
        h.absorb(vk);
        h.finalize();
        h.squeeze(&mut self.tr);

        self.s2_hat.ntt_inplace();
        self.t0_hat.ntt_inplace();
    }

    pub fn encode(&self, dst: &mut [u8]) {
        struct Tmp<const K: usize, const L: usize> {
            s1: PolyVec<L>,
            s2: PolyVec<K>,
            t0: PolyVec<K>,
        }

        impl<const L: usize, const K: usize> Drop for Tmp<L, K> {
            fn drop(&mut self) {}
        }

        let mut uninit_tmp: MaybeUninit<Tmp<K, L>> = MaybeUninit::uninit();
        let tmp = unsafe { uninit_tmp.assume_init_mut() };

        tmp.s1.invntt(&self.s1_hat);
        tmp.s2.invntt(&self.s2_hat);
        tmp.t0.invntt(&self.t0_hat);

        dst[..32].copy_from_slice(&self.rho);
        dst[32..64].copy_from_slice(&self.k);
        dst[64..128].copy_from_slice(&self.tr);

        let buf = &mut dst[128..];

        match ETA {
            2 => {
                tmp.s1.pack_eta2(&mut buf[..L * Poly::PACKED_3BIT]);

                let buf = &mut buf[L * Poly::PACKED_3BIT..];
                tmp.s2.pack_eta2(&mut buf[..K * Poly::PACKED_3BIT]);

                let buf = &mut buf[K * Poly::PACKED_3BIT..];
                tmp.t0.pack_eta_2powdm1(buf)
            }
            4 => {
                tmp.s1.pack_eta4(&mut buf[..L * Poly::PACKED_4BIT]);

                let buf = &mut buf[L * Poly::PACKED_4BIT..];
                tmp.s2.pack_eta4(buf);

                let buf = &mut buf[K * Poly::PACKED_4BIT..];
                tmp.t0.pack_eta_2powdm1(buf)
            }
            _ => unreachable!(),
        }
    }

    #[inline]
    pub fn decode(src: &[u8]) -> Self {
        let mut uninit_sk = Self::uninit();
        let sk = unsafe { uninit_sk.assume_init_mut() };

        sk.rho.copy_from_slice(&src[..32]);
        sk.k.copy_from_slice(&src[32..64]);
        sk.tr.copy_from_slice(&src[64..128]);

        match ETA {
            2 => {
                let z = &src[128..];
                sk.s1_hat.unpack_eta2(&z[..L * Poly::PACKED_3BIT]);

                let z = &z[L * Poly::PACKED_3BIT..];
                sk.s2_hat.unpack_eta2(&z[..K * Poly::PACKED_3BIT]);

                let z = &z[K * Poly::PACKED_3BIT..];
                sk.t0_hat.unpack_eta_2powdm1(z)
            }
            4 => {
                let z = &src[128..];
                sk.s1_hat.unpack_eta4(&z[..L * Poly::PACKED_4BIT]);

                let z = &z[L * Poly::PACKED_4BIT..];
                sk.s2_hat.unpack_eta4(&z[..K * Poly::PACKED_4BIT]);

                let z = &z[K * Poly::PACKED_4BIT..];
                sk.t0_hat.unpack_eta_2powdm1(z)
            }
            _ => unreachable!(),
        }

        sk.a_hat.expand_a(&sk.rho);

        sk.s1_hat.ntt_inplace();
        sk.s2_hat.ntt_inplace();
        sk.t0_hat.ntt_inplace();

        unsafe { uninit_sk.assume_init() }
    }
}

struct Poly {
    f: [i32; N],
}

impl Drop for Poly {
    fn drop(&mut self) {
        self.f.zeroize();
    }
}

impl Poly {
    const fn zero() -> Self {
        Self { f: [0; N] }
    }

    const fn packed_bytesize(bitlen: usize) -> usize {
        (N * bitlen) / 8
    }

    /// NTT(w)
    fn ntt_inplace(&mut self) {
        let w = &mut self.f;

        let mut m = 1;

        for len in (0..8).map(|n| 128 >> n) {
            for start in (0..256).step_by(len << 1) {
                let zeta = ZETAS[m];
                m += 1;

                for j in start..start + len {
                    let t = reduce::mont_mul(zeta, w[j + len]);
                    w[j + len] = w[j] - t;
                    w[j] += t;
                }
            }
        }
    }

    /// NTT(w)
    fn ntt(&mut self, f: &Self) {
        let w_hat = &mut self.f;
        let w = &f.f;

        w_hat.copy_from_slice(w);

        let mut m = 1;

        for len in (0..8).map(|n| 128 >> n) {
            for start in (0..256).step_by(len << 1) {
                let zeta = ZETAS[m];
                m += 1;

                for j in start..start + len {
                    let t = reduce::mont_mul(zeta, w_hat[j + len]);
                    w_hat[j + len] = w_hat[j] - t;
                    w_hat[j] += t;
                }
            }
        }
    }

    /// NTT^-1 (w_hat)
    fn invntt(&mut self, w: &Self) {
        let w_hat = &mut self.f;

        w_hat.copy_from_slice(&w.f);

        let mut m = 255;

        for len in (0..8).map(|n| 1 << n) {
            for start in (0..256).step_by(len << 1) {
                let zeta = -ZETAS[m];
                m -= 1;
                for j in start..start + len {
                    let t = w_hat[j];
                    w_hat[j] = t + w_hat[j + len];
                    w_hat[j + len] = t - w_hat[j + len];
                    w_hat[j + len] = reduce::mont_mul(zeta, w_hat[j + len]);
                }
            }
        }

        // 2^32 / 256 = 2^{24}
        const DIV_256: i32 = ((1 << 24) % Q as i64) as i32;

        for a in w_hat.iter_mut() {
            *a = reduce::mont_mul(*a, DIV_256);
        }
    }

    /// NTT^-1 (w_hat)
    fn invntt_inplace(&mut self) {
        let w = &mut self.f;

        let mut m = 255;

        for len in (0..8).map(|n| 1 << n) {
            for start in (0..256).step_by(len << 1) {
                let zeta = -ZETAS[m];
                m -= 1;
                for j in start..start + len {
                    let t = w[j];
                    w[j] = t + w[j + len];
                    w[j + len] = t - w[j + len];
                    w[j + len] = reduce::mont_mul(zeta, w[j + len]);
                }
            }
        }

        // 2^32 / 256 = 2^{24}
        const DIV_256: i32 = ((1 << 24) % Q as i64) as i32;

        for a in w.iter_mut() {
            *a = reduce::mont_mul(*a, DIV_256);
        }
    }

    /// NTT^-1 (w_hat)
    fn invntt_tomont_inplace(&mut self) {
        let w = &mut self.f;

        let mut m = 255;

        for len in (0..8).map(|n| 1 << n) {
            for start in (0..256).step_by(len << 1) {
                let zeta = -ZETAS[m];
                m -= 1;
                for j in start..start + len {
                    let t = w[j];
                    w[j] = t + w[j + len];
                    w[j + len] = t - w[j + len];
                    w[j + len] = reduce::mont_mul(zeta, w[j + len]);
                }
            }
        }

        // (2^32)^2 / 256 = 2^{56}
        const DIV_256_MONT: i32 = ((1 << 56) % Q as i64) as i32;

        for a in w.iter_mut() {
            *a = reduce::mont_mul(*a, DIV_256_MONT);
        }
    }

    /// RejNTTPoly(rho)
    fn rej_ntt(&mut self, g: &mut hash::Shake128) {
        let mut idx = 0;

        while idx < N {
            let bytes = g.squeezeblock();

            for b in bytes.chunks_exact(3) {
                if let Some(a) = coeff::from_three_bytes(b[0], b[1], b[2]) {
                    self.f[idx] = a;
                    idx += 1;
                }

                if idx == N {
                    break;
                }
            }
        }
    }

    /// RejBoundedPoly(rho)
    fn rej_bounded<const ETA: usize>(&mut self, h: &mut hash::Shake256) {
        let mut idx = 0;

        while idx < N {
            let bytes = h.squeezeblock();

            for z in bytes
                .iter()
                .flat_map(|b| {
                    let (z0, z1) = coeff::from_halfbytes::<ETA>(*b);
                    [z0, z1]
                })
                .flatten()
            {
                self.f[idx] = z;
                idx += 1;

                if idx == N {
                    break;
                }
            }
        }
    }

    fn multiply_ntt_acc(&mut self, a: &Self, b: &Self) {
        for i in 0..N {
            self.f[i] += reduce::mont_mul(a.f[i], b.f[i])
        }
    }

    fn multiply_ntt(&mut self, a: &Self, b: &Self) {
        for i in 0..N {
            self.f[i] = reduce::mont_mul(a.f[i], b.f[i])
        }
    }

    fn dot_prod_ntt<const K: usize>(&mut self, u: &PolyVec<K>, v: &PolyVec<K>) {
        self.multiply_ntt(&u.v[0], &v.v[0]);

        for i in 1..K {
            self.multiply_ntt_acc(&u.v[i], &v.v[i]);
        }
    }

    fn reduce(&mut self) {
        for a in self.f.iter_mut() {
            *a = reduce::barrett_reduce(*a);
        }
    }

    fn power2round(&self, f: &mut Self, g: &mut Self) {
        for i in 0..N {
            let (r1, r0) = coeff::power2round(self.f[i]);
            f.f[i] = r1;
            g.f[i] = r0;
        }
    }

    fn decompose_32(&self, f: &mut Self, g: &mut Self) {
        for i in 0..N {
            let (r1, r0) = coeff::decompose_32(self.f[i]);
            f.f[i] = r1;
            g.f[i] = r0;
        }
    }

    fn decompose_88(&self, f: &mut Self, g: &mut Self) {
        for i in 0..N {
            let (r1, r0) = coeff::decompose_88(self.f[i]);
            f.f[i] = r1;
            g.f[i] = r0;
        }
    }

    const PACKED_10BIT: usize = (N * 10) / 8;

    fn pack_simple_10bit(&self, z: &mut [u8; Self::PACKED_10BIT]) {
        for (b, a) in z.chunks_exact_mut(5).zip(self.f.chunks_exact(4)) {
            b[0] = a[0] as u8;
            b[1] = (a[0] >> 8) as u8 | (a[1] << 2) as u8;
            b[2] = (a[1] >> 6) as u8 | (a[2] << 4) as u8;
            b[3] = (a[2] >> 4) as u8 | (a[3] << 6) as u8;
            b[4] = (a[3] >> 2) as u8;
        }
    }

    fn unpack_simple_10bit(&mut self, z: &[u8; Self::PACKED_10BIT]) {
        for (a, b) in self.f.chunks_exact_mut(4).zip(z.chunks_exact(5)) {
            let b: [i32; 5] = array::from_fn(|i| b[i] as i32);
            a[0] = (b[0] | (b[1] << 8)) & 0x3FF;
            a[1] = ((b[1] >> 2) | (b[2] << 6)) & 0x3FF;
            a[2] = ((b[2] >> 4) | (b[3] << 4)) & 0x3FF;
            a[3] = ((b[3] >> 6) | (b[4] << 2)) & 0x3FF;
        }
    }

    fn pack_simple_4bit(&self, z: &mut [u8; Self::packed_bytesize(4)]) {
        for (b, a) in z.iter_mut().zip(self.f.chunks_exact(2)) {
            *b = (a[0] | a[1] << 4) as u8;
        }
    }

    fn pack_simple_6bit(&self, z: &mut [u8; Self::packed_bytesize(6)]) {
        for (b, a) in z.chunks_exact_mut(3).zip(self.f.chunks_exact(4)) {
            b[0] = ((a[0] >> 0) | (a[1] << 6)) as u8;
            b[1] = ((a[1] >> 2) | (a[2] << 4)) as u8;
            b[2] = ((a[2] >> 4) | (a[3] << 2)) as u8;
        }
    }

    const PACKED_4BIT: usize = (N * 4) / 8;

    fn pack_eta4(&self, z: &mut [u8; Self::PACKED_4BIT]) {
        for (b, a) in z.iter_mut().zip(self.f.chunks_exact(2)) {
            let t0 = (4 - a[0]) as u8;
            let t1 = (4 - a[1]) as u8;
            *b = t0 | (t1 << 4);
        }
    }

    fn unpack_eta4(&mut self, z: &[u8; Self::PACKED_4BIT]) {
        for (a, b) in self.f.chunks_exact_mut(2).zip(z) {
            a[0] = 4 - (b & 0xF) as i32;
            a[1] = 4 - (b >> 4) as i32;
        }
    }

    const PACKED_3BIT: usize = (N * 3) / 8;

    fn pack_eta2(&self, z: &mut [u8; Self::PACKED_3BIT]) {
        for (b, a) in z.chunks_exact_mut(3).zip(self.f.chunks_exact(8)) {
            let t: [u8; 8] = array::from_fn(|i| (2 - a[i]) as u8);

            b[0] = t[0] | (t[1] << 3) | (t[2] << 6);
            b[1] = (t[2] >> 2) | (t[3] << 1) | (t[4] << 4) | (t[5] << 7);
            b[2] = (t[5] >> 1) | (t[6] << 2) | (t[7] << 5);
        }
    }

    fn unpack_eta2(&mut self, z: &[u8; Self::PACKED_3BIT]) {
        for (a, b) in self.f.chunks_exact_mut(8).zip(z.chunks_exact(3)) {
            a[0] = 2 - (b[0] & 7) as i32;
            a[1] = 2 - ((b[0] >> 3) & 7) as i32;
            a[2] = 2 - ((b[0] >> 6) | (b[1] << 2) & 7) as i32;
            a[3] = 2 - ((b[1] >> 1) & 7) as i32;
            a[4] = 2 - ((b[1] >> 4) & 7) as i32;
            a[5] = 2 - (((b[1] >> 7) | (b[2] << 1)) & 7) as i32;
            a[6] = 2 - ((b[2] >> 2) & 7) as i32;
            a[7] = 2 - (b[2] >> 5) as i32
        }
    }

    const PACKED_13BIT: usize = (N * 13) / 8;

    fn pack_eta_2powdm1(&self, z: &mut [u8; Self::PACKED_13BIT]) {
        const ETA: i32 = 1 << (D - 1);

        for (b, a) in z.chunks_exact_mut(13).zip(self.f.chunks_exact(8)) {
            let a: [u16; 8] = array::from_fn(|i| (ETA - a[i]) as u16);

            b[0] = a[0] as u8;
            b[1] = ((a[0] >> 8) | a[1] << 5) as u8;
            b[2] = (a[1] >> 3) as u8;
            b[3] = ((a[1] >> 11) | a[2] << 2) as u8;
            b[4] = ((a[2] >> 6) | (a[3] << 7)) as u8;
            b[5] = (a[3] >> 1) as u8;
            b[6] = ((a[3] >> 9) | a[4] << 4) as u8;
            b[7] = (a[4] >> 4) as u8;
            b[8] = ((a[4] >> 12) | a[5] << 1) as u8;
            b[9] = ((a[5] >> 7) | a[6] << 6) as u8;
            b[10] = (a[6] >> 2) as u8;
            b[11] = ((a[6] >> 10) | a[7] << 3) as u8;
            b[12] = (a[7] >> 5) as u8;
        }
    }

    fn unpack_eta_2powdm1(&mut self, z: &[u8; Self::PACKED_13BIT]) {
        const ETA: i32 = 1 << (D - 1);

        for (a, b) in self.f.chunks_exact_mut(8).zip(z.chunks_exact(13)) {
            let b: [i32; 13] = array::from_fn(|i| b[i] as i32);

            a[0] = ETA - ((b[0] | (b[1] << 8)) & 0x1FFF);
            a[1] = ETA - (((b[1] >> 5) | (b[2] << 3) | (b[3] << 11)) & 0x1FFF);
            a[2] = ETA - (((b[3] >> 2) | (b[4] << 6)) & 0x1FFF);
            a[3] = ETA - (((b[4] >> 7) | (b[5] << 1) | (b[6] << 9)) & 0x1FFF);
            a[4] = ETA - (((b[6] >> 4) | (b[7] << 4) | (b[8] << 12)) & 0x1FFF);
            a[5] = ETA - (((b[8] >> 1) | (b[9] << 7)) & 0x1FFF);
            a[6] = ETA - (((b[9] >> 6) | (b[10] << 2) | (b[11] << 10)) & 0x1FFF);
            a[7] = ETA - (((b[11] >> 3) | (b[12] << 5)) & 0x1FFF);
        }
    }
}

impl AddAssign<&Poly> for Poly {
    fn add_assign(&mut self, rhs: &Poly) {
        for (a, b) in self.f.iter_mut().zip(rhs.f.iter()) {
            *a += b;
        }
    }
}

struct PolyMat<const K: usize, const L: usize> {
    m: [PolyVec<L>; K],
}

impl<const K: usize, const L: usize> PolyMat<K, L> {
    /// ExpandA(rho)
    fn expand_a(&mut self, rho: &[u8; 32]) {
        let mut g = hash::Shake128::init();

        for (r, polyvec) in self.m.iter_mut().enumerate() {
            for (s, poly) in polyvec.v.iter_mut().enumerate() {
                g.absorb_multi(&[rho, &u16::to_le_bytes(((r << 8) + s) as u16)]);

                poly.rej_ntt(&mut g);

                g.reset();
            }
        }
    }
}

struct PolyVec<const K: usize> {
    v: [Poly; K],
}

impl<const K: usize> PolyVec<K> {
    const fn zero() -> Self {
        Self {
            v: [const { Poly::zero() }; K],
        }
    }

    const fn packed_bytesize(coeff_bitlen: usize) -> usize {
        K * Poly::packed_bytesize(coeff_bitlen)
    }

    fn ntt_inplace(&mut self) {
        for p in self.v.iter_mut() {
            p.ntt_inplace();
        }
    }

    fn ntt(&mut self, v_hat: &Self) {
        for (p_hat, p) in self.v.iter_mut().zip(&v_hat.v) {
            p_hat.ntt(p);
        }
    }

    fn invntt(&mut self, v: &Self) {
        for (p, v) in self.v.iter_mut().zip(&v.v) {
            p.invntt(v);
        }
    }

    fn invntt_inplace(&mut self) {
        for p in self.v.iter_mut() {
            p.invntt_inplace();
        }
    }

    fn reduce_invntt_tomont_inplace(&mut self) {
        for p in self.v.iter_mut() {
            p.reduce();
            p.invntt_tomont_inplace();
        }
    }

    fn power2round(&self, t1: &mut PolyVec<K>, t0: &mut PolyVec<K>) {
        for i in 0..K {
            self.v[i].power2round(&mut t1.v[i], &mut t0.v[i]);
        }
    }

    fn decompose_32(&self, x1: &mut PolyVec<K>, x0: &mut PolyVec<K>) {
        for i in 0..K {
            self.v[i].decompose_32(&mut x1.v[i], &mut x0.v[i]);
        }
    }

    fn decompose_88(&self, x1: &mut PolyVec<K>, x0: &mut PolyVec<K>) {
        for i in 0..K {
            self.v[i].decompose_88(&mut x1.v[i], &mut x0.v[i]);
        }
    }

    fn pack_eta4(&self, z: &mut [u8]) {
        for (buf, p) in z.chunks_exact_mut(Poly::PACKED_4BIT).zip(self.v.iter()) {
            p.pack_eta4(buf.try_into().unwrap());
        }
    }

    fn unpack_eta4(&mut self, z: &[u8]) {
        for (p, buf) in self.v.iter_mut().zip(z.chunks_exact(Poly::PACKED_4BIT)) {
            p.unpack_eta4(buf.try_into().unwrap());
        }
    }

    fn pack_eta2(&self, z: &mut [u8]) {
        for (buf, p) in z.chunks_exact_mut(Poly::PACKED_3BIT).zip(self.v.iter()) {
            p.pack_eta2(buf.try_into().unwrap());
        }
    }

    fn unpack_eta2(&mut self, z: &[u8]) {
        for (p, buf) in self.v.iter_mut().zip(z.chunks_exact(Poly::PACKED_3BIT)) {
            p.unpack_eta2(buf.try_into().unwrap());
        }
    }

    fn pack_eta_2powdm1(&self, z: &mut [u8]) {
        for (buf, p) in z.chunks_exact_mut(Poly::PACKED_13BIT).zip(self.v.iter()) {
            p.pack_eta_2powdm1(buf.try_into().unwrap());
        }
    }

    fn unpack_eta_2powdm1(&mut self, z: &[u8]) {
        for (p, buf) in self.v.iter_mut().zip(z.chunks_exact(Poly::PACKED_13BIT)) {
            p.unpack_eta_2powdm1(buf.try_into().unwrap());
        }
    }

    fn pack_simple_4bit<const BZ: usize>(&self, z: &mut [u8; BZ]) {
        for (chunk, p) in z
            .chunks_exact_mut(Poly::packed_bytesize(4))
            .zip(self.v.iter())
        {
            p.pack_simple_4bit(chunk.try_into().unwrap());
        }
    }

    fn pack_simple_6bit<const BZ: usize>(&self, z: &mut [u8; BZ]) {
        for (chunk, p) in z
            .chunks_exact_mut(Poly::packed_bytesize(6))
            .zip(self.v.iter())
        {
            p.pack_simple_6bit(chunk.try_into().unwrap());
        }
    }

    fn multiply_matvec_ntt<const L: usize>(&mut self, m: &PolyMat<K, L>, v: &PolyVec<L>) {
        for i in 0..K {
            self.v[i].dot_prod_ntt(&m.m[i], v)
        }
    }
}

impl<const K: usize> AddAssign<&PolyVec<K>> for PolyVec<K> {
    fn add_assign(&mut self, rhs: &PolyVec<K>) {
        for (f, g) in self.v.iter_mut().zip(rhs.v.iter()) {
            f.add_assign(g);
        }
    }
}

/// ExpandS(rho)
fn expand_s<const K: usize, const L: usize, const ETA: usize>(
    s1: &mut PolyVec<L>,
    s2: &mut PolyVec<K>,
    rho: &[u8; 64],
) {
    let mut h = hash::Shake256::init();

    for (nonce, poly) in s1.v.iter_mut().chain(s2.v.iter_mut()).enumerate() {
        h.absorb_multi(&[rho, &u16::to_le_bytes(nonce as u16)]);
        poly.rej_bounded::<ETA>(&mut h);
        h.reset();
    }
}

#[cfg(test)]
mod tests {
    use std::{fs::read_to_string, path::PathBuf};

    use serde::Deserialize;

    use super::*;

    #[test]
    fn test_keygen() {
        let mut test_data_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        test_data_path.push("tests/mldsa-keygen.json");

        let test_data = read_to_string(&test_data_path).unwrap();
        let test_data: Tests = serde_json::from_str(&test_data).unwrap();

        for tg in test_data.test_groups.iter() {
            match tg.parameter_set.as_str() {
                "ML-DSA-44" => {
                    let mut vk_bytes = [0u8; mldsa44::VK_SIZE];
                    let mut sk_bytes = [0u8; mldsa44::SK_SIZE];

                    for test in &tg.tests {
                        let mut sk = unsafe { mldsa44::SigningKey::uninit().assume_init() };
                        sk.keygen_internal(&mut vk_bytes, &test.seed);
                        sk.encode(&mut sk_bytes);

                        assert_eq!(vk_bytes, test.pk[..]);
                        assert_eq!(sk_bytes, test.sk[..]);

                        let sk_prime = mldsa44::SigningKey::decode(&test.sk);
                        sk_prime.encode(&mut sk_bytes);
                        assert_eq!(sk_bytes, test.sk[..]);

                        let vk_prime = mldsa44::VerifyingKey::decode(&test.pk);
                        vk_prime.encode(&mut vk_bytes);
                        assert_eq!(vk_bytes, test.pk[..]);
                    }
                }
                "ML-DSA-65" => {
                    let mut vk_bytes = [0u8; mldsa65::VK_SIZE];
                    let mut sk_bytes = [0u8; mldsa65::SK_SIZE];

                    for test in &tg.tests {
                        let mut sk = unsafe { mldsa65::SigningKey::uninit().assume_init() };
                        sk.keygen_internal(&mut vk_bytes, &test.seed);
                        sk.encode(&mut sk_bytes);

                        assert_eq!(vk_bytes, test.pk[..]);
                        assert_eq!(sk_bytes, test.sk[..]);

                        let sk_prime = mldsa65::SigningKey::decode(&test.sk);
                        sk_prime.encode(&mut sk_bytes);
                        assert_eq!(sk_bytes, test.sk[..]);

                        let vk_prime = mldsa65::VerifyingKey::decode(&test.pk);
                        vk_prime.encode(&mut vk_bytes);
                        assert_eq!(vk_bytes, test.pk[..]);
                    }
                }
                "ML-DSA-87" => {
                    let mut vk_bytes = [0u8; mldsa87::VK_SIZE];
                    let mut sk_bytes = [0u8; mldsa87::SK_SIZE];

                    for test in &tg.tests {
                        let mut sk = unsafe { mldsa87::SigningKey::uninit().assume_init() };
                        sk.keygen_internal(&mut vk_bytes, &test.seed);
                        sk.encode(&mut sk_bytes);

                        assert_eq!(vk_bytes, test.pk[..]);
                        assert_eq!(sk_bytes, test.sk[..]);

                        let sk_prime = mldsa87::SigningKey::decode(&test.sk);
                        sk_prime.encode(&mut sk_bytes);
                        assert_eq!(sk_bytes, test.sk[..]);

                        let vk_prime = mldsa87::VerifyingKey::decode(&test.pk);
                        vk_prime.encode(&mut vk_bytes);
                        assert_eq!(vk_bytes, test.pk[..]);
                    }
                }
                _ => panic!("invalid paramter set"),
            };
        }
    }

    #[derive(Deserialize)]
    struct KeyGenTV {
        #[serde(with = "hex")]
        pk: Vec<u8>,

        #[serde(with = "hex")]
        seed: [u8; 32],

        #[serde(with = "hex")]
        sk: Vec<u8>,
    }
    #[derive(Deserialize)]
    struct KeyGenTg {
        #[serde(rename = "parameterSet")]
        parameter_set: String,

        tests: Vec<KeyGenTV>,
    }
    #[derive(Deserialize)]
    struct Tests {
        #[serde(rename = "testGroups")]
        test_groups: Vec<KeyGenTg>,
    }
}
