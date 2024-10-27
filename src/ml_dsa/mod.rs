use core::{array, mem::MaybeUninit, ops::AddAssign};

use rand_core::CryptoRngCore;
use sha3::digest::XofReader;
use zeroize::Zeroize;

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

pub struct VerifyingKey<const K: usize> {
    rho: [u8; 32],
    t1: PolyVec<K>,
}

impl<const K: usize> Drop for VerifyingKey<K> {
    fn drop(&mut self) {
        self.rho.zeroize();
    }
}

fn vk_encode<const K: usize, const PK_SIZE: usize>(
    dst: &mut [u8; PK_SIZE],
    rho: &[u8; 32],
    t1: &PolyVec<K>,
) {
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
    s1_hat: PolyVec<L>,
}

impl<const K: usize, const L: usize> Drop for KeyGenTmp<K, L> {
    fn drop(&mut self) {
        self.rho_prime.zeroize();
    }
}

pub struct SigningKey<const K: usize, const L: usize, const ETA: usize> {
    rho: [u8; 32],
    k: [u8; 32],
    tr: [u8; 64],
    s1: PolyVec<L>,
    s2: PolyVec<K>,
    t0: PolyVec<K>,
    a_hat: PolyMat<K, L>,
}

impl<const K: usize, const L: usize, const ETA: usize> Drop for SigningKey<K, L, ETA> {
    fn drop(&mut self) {
        self.rho.zeroize();
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

        let mut h = hash::H::init();
        let mut xof = h.absorb(&[ksi, &[K as u8], &[L as u8]]);
        xof.read(&mut self.rho);
        xof.read(&mut tmp.rho_prime);
        xof.read(&mut self.k);

        self.a_hat.expand_a(&self.rho);
        expand_s::<K, L, ETA>(&mut self.s1, &mut self.s2, &tmp.rho_prime);

        tmp.s1_hat.ntt(&self.s1);
        tmp.t.multiply_matvec_ntt(&self.a_hat, &tmp.s1_hat);
        tmp.t.reduce_invntt_tomont();

        tmp.t += &self.s2;

        tmp.t.power2round(&mut tmp.t1, &mut self.t0);

        vk_encode(vk, &self.rho, &tmp.t1);

        let mut xof = h.absorb(&[vk]);
        xof.read(&mut self.tr);
    }

    pub fn encode(&self, dst: &mut [u8]) {
        dst[..32].copy_from_slice(&self.rho);
        dst[32..64].copy_from_slice(&self.k);
        dst[64..128].copy_from_slice(&self.tr);

        let buf = &mut dst[128..];

        match ETA {
            2 => {
                self.s1.pack_eta2(&mut buf[..L * Poly::PACKED_3BIT]);

                let buf = &mut buf[L * Poly::PACKED_3BIT..];
                self.s2.pack_eta2(&mut buf[..K * Poly::PACKED_3BIT]);

                let buf = &mut buf[K * Poly::PACKED_3BIT..];
                self.t0.pack_2pow12(buf)
            }
            4 => {
                self.s1.pack_eta4(&mut buf[..L * Poly::PACKED_4BIT]);

                let buf = &mut buf[L * Poly::PACKED_4BIT..];
                self.s2.pack_eta4(buf);

                let buf = &mut buf[K * Poly::PACKED_4BIT..];
                self.t0.pack_2pow12(buf)
            }
            _ => unreachable!(),
        }
    }
}

#[derive(Debug)]
struct Poly {
    f: [i32; N],
}

impl Drop for Poly {
    fn drop(&mut self) {
        self.f.zeroize();
    }
}

impl Poly {
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
    fn invntt_tomont(&mut self) {
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
    fn rej_ntt(&mut self, g: &mut impl XofReader) {
        let mut coeffs = self.f.iter_mut();
        let mut b = [0u8; 3];

        loop {
            g.read(&mut b);

            let a = coeff_from_bytes(b[0], b[1], b[2]);

            if a == 0 {
                continue;
            }

            match coeffs.next() {
                Some(a_hat) => *a_hat = a,
                None => break,
            }
        }
    }

    /// RejBoundedPoly(rho)
    fn rej_bounded<const ETA: usize>(&mut self, h: &mut impl XofReader) {
        let mut coeffs = self.f.iter_mut();
        let mut b = [0u8; 1];

        loop {
            h.read(&mut b);

            let (z0, z1) = coeffs_from_halfbytes::<ETA>(b[0]);

            if let Some(z) = z0 {
                match coeffs.next() {
                    Some(a) => *a = z,
                    None => break,
                }
            }

            if let Some(z) = z1 {
                match coeffs.next() {
                    Some(a) => *a = z,
                    None => break,
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
            let (r1, r0) = power2round(self.f[i]);
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

    const PACKED_4BIT: usize = (N * 4) / 8;

    fn pack_eta4(&self, z: &mut [u8; Self::PACKED_4BIT]) {
        for (b, a) in z.iter_mut().zip(self.f.chunks_exact(2)) {
            let t0 = (4 - a[0]) as u8;
            let t1 = (4 - a[1]) as u8;
            *b = t0 | (t1 << 4);
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

    const PACKED_13BIT: usize = (N * 13) / 8;

    fn pack_2pow12(&self, z: &mut [u8; Self::PACKED_13BIT]) {
        for (b, a) in z.chunks_exact_mut(13).zip(self.f.chunks_exact(8)) {
            let t: [u16; 8] = array::from_fn(|i| ((1 << (D - 1)) - a[i]) as u16);

            b[0] = t[0] as u8;
            b[1] = ((t[0] >> 8) | t[1] << 5) as u8;
            b[2] = (t[1] >> 3) as u8;
            b[3] = ((t[1] >> 11) | t[2] << 2) as u8;
            b[4] = ((t[2] >> 6) | (t[3] << 7)) as u8;
            b[5] = (t[3] >> 1) as u8;
            b[6] = ((t[3] >> 9) | t[4] << 4) as u8;
            b[7] = (t[4] >> 4) as u8;
            b[8] = ((t[4] >> 12) | t[5] << 1) as u8;
            b[9] = ((t[5] >> 7) | t[6] << 6) as u8;
            b[10] = (t[6] >> 2) as u8;
            b[11] = ((t[6] >> 10) | t[7] << 3) as u8;
            b[12] = (t[7] >> 5) as u8;
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

/// Decomposes r into (r1, r0) such that r = r1*2^d + r0 (mod Q)
const fn power2round(mut r: i32) -> (i32, i32) {
    r += (r >> 31) & Q;

    let q = (1 << (D - 1)) - 1;

    let r1 = (r + q) >> D;
    let r0 = r - (r1 << D);

    (r1, r0)
}

/// Convert 3 bytes into an element of Z_Q.
const fn coeff_from_bytes(b0: u8, b1: u8, b2: u8) -> i32 {
    let mut z = b0 as u32;
    z |= (b1 as u32) << 8;
    z |= (b2 as u32) << 16;
    z &= 0x7FFFFF;

    if z < Q as u32 {
        return z as i32;
    }

    0
}

const fn mod5(a: u32) -> i32 {
    const DIV_SHIFT: usize = 10;
    const M: u32 = ((1 << DIV_SHIFT) + 3) / 5;
    (a - ((a * M) >> DIV_SHIFT) * 5) as i32
}

/// Convert two half-bytes into two elements of Z_Q.
const fn coeffs_from_halfbytes<const ETA: usize>(b: u8) -> (Option<i32>, Option<i32>) {
    let b0 = (b & 0xF) as u32;
    let b1 = (b >> 4) as u32;

    match ETA {
        2 => (
            if b0 < 15 { Some(2 - mod5(b0)) } else { None },
            if b1 < 15 { Some(2 - mod5(b1)) } else { None },
        ),
        4 => (
            if b0 < 9 { Some(4 - b0 as i32) } else { None },
            if b1 < 9 { Some(4 - b1 as i32) } else { None },
        ),
        _ => unreachable!(),
    }
}

#[derive(Debug)]
struct PolyMat<const K: usize, const L: usize> {
    m: [PolyVec<L>; K],
}

impl<const K: usize, const L: usize> PolyMat<K, L> {
    /// ExpandA(rho)
    fn expand_a(&mut self, rho: &[u8; 32]) {
        let mut g = hash::G::init();

        for (r, polyvec) in self.m.iter_mut().enumerate() {
            for (s, poly) in polyvec.v.iter_mut().enumerate() {
                let mut xof = g.absorb(&[rho, &u16::to_le_bytes(((r << 8) + s) as u16)]);

                poly.rej_ntt(&mut xof);
            }
        }
    }
}

#[derive(Debug)]
struct PolyVec<const K: usize> {
    v: [Poly; K],
}

impl<const K: usize> PolyVec<K> {
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

    fn reduce_invntt_tomont(&mut self) {
        for p in self.v.iter_mut() {
            p.reduce();
            p.invntt_tomont();
        }
    }

    fn power2round(&self, t1: &mut PolyVec<K>, t0: &mut PolyVec<K>) {
        for i in 0..K {
            self.v[i].power2round(&mut t1.v[i], &mut t0.v[i])
        }
    }

    fn pack_eta4(&self, z: &mut [u8]) {
        for (buf, p) in z.chunks_exact_mut(Poly::PACKED_4BIT).zip(self.v.iter()) {
            p.pack_eta4(buf.try_into().unwrap());
        }
    }

    fn pack_eta2(&self, z: &mut [u8]) {
        for (buf, p) in z.chunks_exact_mut(Poly::PACKED_3BIT).zip(self.v.iter()) {
            p.pack_eta2(buf.try_into().unwrap());
        }
    }

    fn pack_2pow12(&self, z: &mut [u8]) {
        for (buf, p) in z.chunks_exact_mut(Poly::PACKED_13BIT).zip(self.v.iter()) {
            p.pack_2pow12(buf.try_into().unwrap());
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
    let mut h = hash::H::init();

    for (nonce, poly) in s1.v.iter_mut().chain(s2.v.iter_mut()).enumerate() {
        let mut xof = h.absorb(&[rho, &u16::to_le_bytes(nonce as u16)]);
        poly.rej_bounded::<ETA>(&mut xof);
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
