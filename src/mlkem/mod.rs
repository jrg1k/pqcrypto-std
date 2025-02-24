//! Implementation of ML-KEM (FIPS-203)
mod compress;
mod reduce;

use compress::{
    compr_1bit, compr_4bit, compr_10bit, decompr_1bit, decompr_4bit, decompr_10bit,
};
use core::{
    array,
    fmt::Display,
    hint::black_box,
    mem::{self, MaybeUninit, transmute},
    ops::{AddAssign, Mul, SubAssign},
};

use crate::hash;

const N: usize = 256;
const K: usize = 3;
const Q: i16 = 3329;
const DU: usize = 10;
const DV: usize = 4;

const COEFFICIENT_BITSIZE: usize = 12;

/// pre-computed zetas in montgomery form
/// ordered by ZETAS\[i\] = z^BitRev7(i)
/// zeta -> zeta * R (mod Q)
const ZETAS: [i16; 128] = {
    const ZETA1: i16 = reduce::to_mont(17);

    let mut zetas = [0; 128];
    zetas[0] = reduce::R_MOD_Q as i16;

    let mut i = 1;
    while i < 128 {
        zetas[i] = reduce::mont_mul(zetas[i - 1], ZETA1);

        i += 1
    }

    let mut zetas_bitrev = [0; 128];

    i = 0;
    while i < 128 {
        let idx = (i as u8).reverse_bits() >> 1;

        zetas_bitrev[i] = match zetas[idx as usize] {
            z if z > Q / 2 => z - Q,
            z if z < -Q / 2 => z + Q,
            z => z,
        };

        i += 1;
    }

    zetas_bitrev
};

#[derive(Debug, PartialEq)]
struct Poly {
    f: [i16; N],
}

impl Poly {
    const ENCODED_BYTES: usize = (COEFFICIENT_BITSIZE * N) / 8;
    const COMPRESSED_BYTES: usize = (N * DV) / 8;

    const fn zero() -> Self {
        Self { f: [0; N] }
    }

    /// Algorithm 9 NTT(f)
    fn ntt(&mut self) {
        let f = &mut self.f;

        let mut k = 1;

        for len in (0..7).map(|n| 128 >> n) {
            for start in (0..256).step_by(len << 1) {
                let zeta = ZETAS[k];
                k += 1;
                for j in start..start + len {
                    let t = reduce::mont_mul(zeta, f[j + len]);
                    f[j + len] = f[j] - t;
                    f[j] += t;
                }
            }
        }

        self.reduce();
    }

    /// Algorithm 10 NTT^-1 (f_hat)
    fn invntt(&mut self) {
        let f = &mut self.f;

        let mut k = 127;

        for len in (0..7).map(|n| 2 << n) {
            for start in (0..256).step_by(len << 1) {
                let zeta = ZETAS[k];
                k -= 1;
                for j in start..start + len {
                    let t = f[j];
                    f[j] = reduce::barrett_reduce(t + f[j + len]);
                    f[j + len] -= t;
                    f[j + len] = reduce::mont_mul(zeta, f[j + len]);
                }
            }
        }

        // (2^16)^2 / 128 = 2^{25}
        const DIV_128_MONT: i16 = ((1 << 25) % Q as i32) as i16;

        for a in f.iter_mut() {
            // a = (a * R) / 128 (mod Q)
            *a = reduce::mont_mul(*a, DIV_128_MONT);
        }
    }

    /// Algorithm 7 SampleNTT(B)
    fn sample_ntt(xof: &mut hash::Shake128) -> Self {
        let mut f: [MaybeUninit<i16>; N] = [MaybeUninit::uninit(); N];
        let mut idx = 0;

        while idx < N {
            let bytes = xof.squeezeblock();

            for d in bytes
                .chunks_exact(3)
                .flat_map(|b| {
                    let (b0, b1, b2) = (b[0] as u16, b[1] as u16, b[2] as u16);
                    let d1 = b0 | ((b1 & 0xF) << 8);
                    let d2 = (b1 >> 4) | (b2 << 4);

                    [d1, d2]
                })
                .filter(|d| *d < Q as u16)
            {
                f[idx].write(d as i16);
                idx += 1;

                if idx == N {
                    break;
                }
            }
        }

        Self {
            f: unsafe { transmute::<[MaybeUninit<i16>; N], [i16; N]>(f) },
        }
    }

    /// Algorithm 8 SamplePolyCBD_2 (B)
    fn sample_poly_cbd2(&mut self, bytes: &[u8; 128]) {
        let f = &mut self.f;

        for (i, bytes) in (0..N).step_by(8).zip(bytes.chunks_exact(4)) {
            let t = u32::from_le_bytes(bytes.try_into().unwrap());

            // add bits to each other in groups of two
            let d = (t & 0x55555555) + ((t >> 1) & 0x55555555);

            for j in 0..8 {
                // extract two 2-bit numbers
                let x = (d >> (j << 2)) & 3;
                let y = (d >> ((j << 2) + 2)) & 3;
                f[i + j] = x as i16 - y as i16;
            }
        }
    }

    /// Algorithm 11 MultiplyNTTs(f_hat, g_hat)
    fn multiply_ntts_acc(&mut self, f: &Poly, g: &Poly) {
        let h = &mut self.f;
        let f = &f.f;
        let g = &g.f;

        for i in (0..N).step_by(4) {
            let zeta_idx = 64 + (i >> 2);

            let a = basemul(f[i], f[i + 1], g[i], g[i + 1], ZETAS[zeta_idx]);
            let b = basemul(f[i + 2], f[i + 3], g[i + 2], g[i + 3], -ZETAS[zeta_idx]);

            h[i] += a.0;
            h[i + 1] += a.1;
            h[i + 2] += b.0;
            h[i + 3] += b.1;
        }
    }

    fn multiply_acc(&mut self, a: &PolyVec, b: &PolyVec) {
        for (f, g) in a.vec.iter().zip(b.vec.iter()) {
            self.multiply_ntts_acc(f, g);
        }

        self.reduce();
    }

    fn montgomery_form(&mut self) {
        for a in self.f.iter_mut() {
            *a = reduce::to_mont(*a);
        }
    }

    fn reduce(&mut self) {
        for a in self.f.iter_mut() {
            *a = reduce::barrett_reduce(*a);
        }
    }

    /// Encode coefficients as bits in little endian order.
    fn byte_encode(&self, bytes: &mut [u8; Poly::ENCODED_BYTES]) {
        for (a, b) in self.f.chunks(2).zip(bytes.chunks_mut(3)) {
            let (b0, b1, b2) = coeffs2bytes(a[0], a[1]);

            b[0] = b0;
            b[1] = b1;
            b[2] = b2;
        }
    }

    fn byte_decode(bytes: &[u8; Self::ENCODED_BYTES]) -> Self {
        let mut coeffs: [MaybeUninit<i16>; N] = [MaybeUninit::uninit(); N];

        for (a, b) in coeffs.chunks_exact_mut(2).zip(bytes.chunks_exact(3)) {
            let (t0, t1) = bytes2coeffs(b[0], b[1], b[2]);

            a[0].write(t0);
            a[1].write(t1);
        }

        Self {
            f: unsafe { mem::transmute::<[MaybeUninit<i16>; N], [i16; N]>(coeffs) },
        }
    }

    fn compress(&self, bytes: &mut [u8; Self::COMPRESSED_BYTES]) {
        for (b, a) in bytes.iter_mut().zip(self.f.chunks_exact(2)) {
            let c: [u8; 2] = array::from_fn(|i| compr_4bit(a[i]));

            *b = c[0] | (c[1] << 4);
        }
    }

    fn decompress(bytes: &[u8; Self::COMPRESSED_BYTES]) -> Self {
        const MOD_MASK: u8 = (1 << DV) - 1;

        let mut poly = Poly::zero();

        for (a, b) in poly.f.chunks_exact_mut(2).zip(bytes.iter()) {
            a[0] = decompr_4bit(b & MOD_MASK);
            a[1] = decompr_4bit(b >> DV);
        }

        poly
    }

    fn generate_eta2<I>(r: &[u8; 32], nonce: &mut I) -> Self
    where
        I: Iterator<Item = usize>,
    {
        let mut poly = Poly::zero();

        let mut prf = hash::Shake256::init();
        prf.absorb_multi(&[r, &[nonce.next().unwrap() as u8]]);
        let block = prf.squeezeblock();
        poly.sample_poly_cbd2(&block[..128].try_into().unwrap());
        prf.reset();
        poly
    }

    fn from_msg(m: &[u8; 32]) -> Self {
        let mut poly = Poly::zero();

        for (coeffs, byte) in poly.f.chunks_exact_mut(8).zip(m.iter()) {
            for (a, bit) in coeffs.iter_mut().zip((0..8).map(|n| *byte >> n)) {
                *a = decompr_1bit(bit);
            }
        }

        poly
    }

    fn to_msg(&self, m: &mut [u8; 32]) {
        for (byte, coeffs) in m.iter_mut().zip(self.f.chunks_exact(8)) {
            for (i, a) in coeffs.iter().enumerate() {
                *byte |= compr_1bit(*a) << i;
            }
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

impl SubAssign<&Poly> for Poly {
    fn sub_assign(&mut self, rhs: &Poly) {
        for (a, b) in self.f.iter_mut().zip(rhs.f.iter()) {
            *a -= b;
        }
    }
}

impl Display for Poly {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut coeffs = self.f.iter().enumerate().filter(|&(_, &a)| a != 0);

        match coeffs.next() {
            Some((_, a)) => write!(f, "f(X) = {}", a)?,
            None => return write!(f, "f(X) = 0"),
        };

        for (i, a) in coeffs {
            write!(f, " + {}X^{}", a, i)?;
        }

        Ok(())
    }
}

/// Convert 2 integers mod Q into 3 bytes.
const fn coeffs2bytes(a: i16, b: i16) -> (u8, u8, u8) {
    let t0 = a + ((a >> 15) & Q);
    let t1 = b + ((b >> 15) & Q);

    // encode 2 coeficcients (12 bit) into 24 bits
    (t0 as u8, ((t0 >> 8) | (t1 << 4)) as u8, (t1 >> 4) as u8)
}

/// Convert 3 bytes into 2 integers mod Q.
const fn bytes2coeffs(b0: u8, b1: u8, b2: u8) -> (i16, i16) {
    let t0 = ((b0 as u16) | ((b1 as u16) << 8)) & 0xFFF;
    let t1 = (((b1 as u16) >> 4) | ((b2 as u16) << 4)) & 0xFFF;

    (t0 as i16, t1 as i16)
}

/// Algorithm 12 BaseCaseMultiply(a_0, a_1, b_0, b_1, zeta)
/// Compute:
/// - c0 = (a0*b0 + a1*b1*zeta)R^-1 (mod Q)
/// - c1 = (a0*b1 + a1*b0)R^-1 (mod Q)
const fn basemul(a0: i16, a1: i16, b0: i16, b1: i16, zeta: i16) -> (i16, i16) {
    let c0 =
        reduce::mont_mul(a0, b0) + reduce::mont_mul(reduce::mont_mul(a1, b1), zeta);
    let c1 = reduce::mont_mul(a0, b1) + reduce::mont_mul(a1, b0);

    (c0, c1)
}

#[derive(Debug, PartialEq)]
struct PolyVec {
    vec: [Poly; K],
}

impl PolyVec {
    const BYTE_SIZE: usize = K * Poly::ENCODED_BYTES;
    const COMPRESSED_POLY_BYTES: usize = (N * DU) / 8;
    const COMPRESSED_BYTES: usize = K * Self::COMPRESSED_POLY_BYTES;

    const fn zero() -> Self {
        Self {
            vec: [const { Poly::zero() }; K],
        }
    }

    fn reduce(&mut self) {
        for p in self.vec.iter_mut() {
            p.reduce();
        }
    }

    fn ntt(&mut self) {
        for p in self.vec.iter_mut() {
            p.ntt();
        }
    }

    fn invntt(&mut self) {
        for p in self.vec.iter_mut() {
            p.invntt();
        }
    }

    fn byte_encode<const BYTE_SIZE: usize>(&self, bytes: &mut [u8; BYTE_SIZE]) {
        for (p, buf) in self
            .vec
            .iter()
            .zip(bytes.chunks_exact_mut(Poly::ENCODED_BYTES))
        {
            p.byte_encode(buf.try_into().unwrap());
        }
    }

    fn from_bytes(bytes: &[u8; K * Poly::ENCODED_BYTES]) -> Self {
        let mut vec = [const { Poly::zero() }; K];

        for (v, b) in vec.iter_mut().zip(bytes.chunks_exact(Poly::ENCODED_BYTES)) {
            *v = Poly::byte_decode(unsafe { b.try_into().unwrap_unchecked() });
        }

        Self { vec }
    }

    fn compress(&self, bytes: &mut [u8; Self::COMPRESSED_BYTES]) {
        for (p, b) in self
            .vec
            .iter()
            .zip(bytes.chunks_exact_mut(Self::COMPRESSED_POLY_BYTES))
        {
            for (b, a) in b.chunks_exact_mut(5).zip(p.f.chunks_exact(4)) {
                let t: [u16; 4] = array::from_fn(|i| compr_10bit(a[i]));

                b[0] = t[0] as u8;
                b[1] = ((t[0] >> 8) | (t[1] << 2)) as u8;
                b[2] = ((t[1] >> 6) | (t[2] << 4)) as u8;
                b[3] = ((t[2] >> 4) | (t[3] << 6)) as u8;
                b[4] = (t[3] >> 2) as u8;
            }
        }
    }

    fn decompress(bytes: &[u8; Self::COMPRESSED_BYTES]) -> Self {
        let mut pvec = PolyVec::zero();
        for (p, b) in pvec
            .vec
            .iter_mut()
            .zip(bytes.chunks_exact(Self::COMPRESSED_POLY_BYTES))
        {
            for (a, b) in p.f.chunks_exact_mut(4).zip(b.chunks_exact(5)) {
                let mut t: [u16; 5] = array::from_fn(|i| b[i] as u16);
                t[0] |= t[1] << 8;
                t[1] = (t[1] >> 2) | (t[2] << 6);
                t[2] = (t[2] >> 4) | (t[3] << 4);
                t[3] = (t[3] >> 6) | (t[4] << 2);

                for (a, n) in a.iter_mut().zip(&t[..4]) {
                    *a = decompr_10bit(n & 0x3FF);
                }
            }
        }

        pvec
    }

    fn generate_eta2<I>(r: &[u8; 32], nonce: &mut I) -> Self
    where
        I: Iterator<Item = usize>,
    {
        let mut pvec = PolyVec::zero();

        let mut prf = hash::Shake256::init();

        for (poly, nonce) in pvec.vec.iter_mut().zip(nonce) {
            prf.absorb_multi(&[r, &[nonce as u8]]);
            let block = prf.squeezeblock();
            poly.sample_poly_cbd2(&block[..128].try_into().unwrap());
            prf.reset();
        }

        pvec
    }
}

impl AddAssign<&PolyVec> for PolyVec {
    fn add_assign(&mut self, rhs: &PolyVec) {
        for (f, g) in self.vec.iter_mut().zip(rhs.vec.iter()) {
            f.add_assign(g);
        }
    }
}

impl Mul<&PolyVec> for &PolyVec {
    type Output = Poly;

    fn mul(self, rhs: &PolyVec) -> Self::Output {
        let mut out = Poly::zero();

        for (f, g) in self.vec.iter().zip(rhs.vec.iter()) {
            out.multiply_ntts_acc(f, g);
        }

        out.reduce();

        out
    }
}

#[derive(Debug)]
struct PolyMatrix {
    m: [PolyVec; K],
}

impl PolyMatrix {
    fn generate(xof: &mut hash::Shake128, rho: &[u8; 32]) -> Self {
        let mut m: [MaybeUninit<PolyVec>; K] = [const { MaybeUninit::uninit() }; K];

        for (i, pvec) in m.iter_mut().enumerate() {
            let mut v: [MaybeUninit<Poly>; K] = [const { MaybeUninit::uninit() }; K];

            for (j, poly) in v.iter_mut().enumerate() {
                xof.absorb_multi(&[rho, &u16::to_le_bytes((j | (i << 8)) as u16)]);
                poly.write(Poly::sample_ntt(xof));
                xof.reset();
            }

            pvec.write(PolyVec {
                vec: unsafe { transmute::<[MaybeUninit<Poly>; 3], [Poly; 3]>(v) },
            });
        }

        Self {
            m: unsafe { transmute::<[MaybeUninit<PolyVec>; 3], [PolyVec; 3]>(m) },
        }
    }

    fn generate_transposed(xof: &mut hash::Shake128, rho: &[u8; 32]) -> Self {
        let mut m: [MaybeUninit<PolyVec>; K] = [const { MaybeUninit::uninit() }; K];

        for (i, pvec) in m.iter_mut().enumerate() {
            let mut v: [MaybeUninit<Poly>; K] = [const { MaybeUninit::uninit() }; K];

            for (j, poly) in v.iter_mut().enumerate() {
                xof.absorb_multi(&[rho, &u16::to_le_bytes((i | (j << 8)) as u16)]);
                poly.write(Poly::sample_ntt(xof));
                xof.reset();
            }

            pvec.write(PolyVec {
                vec: unsafe { transmute::<[MaybeUninit<Poly>; 3], [Poly; 3]>(v) },
            });
        }

        Self {
            m: unsafe { transmute::<[MaybeUninit<PolyVec>; 3], [PolyVec; 3]>(m) },
        }
    }
}

impl Mul<&PolyVec> for &PolyMatrix {
    type Output = PolyVec;

    fn mul(self, rhs: &PolyVec) -> Self::Output {
        let mut out = PolyVec::zero();

        for (poly, rowvec) in out.vec.iter_mut().zip(&self.m) {
            poly.multiply_acc(rowvec, rhs);
        }

        out
    }
}

fn generate_se(prf: &mut hash::Shake256, sigma: &[u8; 32]) -> (PolyVec, PolyVec) {
    let mut s = PolyVec::zero();
    let mut e = PolyVec::zero();

    for (nonce, poly) in s.vec.iter_mut().chain(e.vec.iter_mut()).enumerate() {
        prf.absorb_multi(&[sigma, &[nonce as u8]]);

        let block = prf.squeezeblock();
        poly.sample_poly_cbd2(&block[..128].try_into().unwrap());

        prf.reset();
        poly.ntt();
    }

    (s, e)
}

struct PkeEncKey {
    t: PolyVec,
    rho: [u8; 32],
}

impl PkeEncKey {
    const BYTE_SIZE: usize = PolyVec::BYTE_SIZE + 32;
    const CIPHERTEXT_SIZE: usize = PolyVec::COMPRESSED_BYTES + Poly::COMPRESSED_BYTES;

    fn to_bytes(&self, bytes: &mut [u8; Self::BYTE_SIZE]) {
        self.t.byte_encode(bytes);
        bytes[PolyVec::BYTE_SIZE..].copy_from_slice(&self.rho);
    }

    fn from_bytes(bytes: &[u8; Self::BYTE_SIZE]) -> Self {
        let (t_bytes, bytes) = bytes.split_first_chunk().unwrap();
        let (rho, _) = bytes.split_first_chunk().unwrap();

        let mut t = PolyVec::from_bytes(t_bytes);
        t.reduce();

        Self { t, rho: *rho }
    }

    /// Algorithm 14 K-PKE.Encrypt(ek_PKE, m, r)
    fn encrypt(&self, c: &mut [u8; Self::CIPHERTEXT_SIZE], m: &[u8; 32], r: &[u8; 32]) {
        let mut xof = hash::Shake128::init();
        let at = PolyMatrix::generate_transposed(&mut xof, &self.rho);

        let mut nonces = 0..(2 * K + 1);

        let mut y = PolyVec::generate_eta2(r, &mut nonces);
        let e1 = PolyVec::generate_eta2(r, &mut nonces);

        let e2 = Poly::generate_eta2(r, &mut nonces);
        y.ntt();

        // u <- NTT^-1(A^T * y) + e_1
        let mut u = &at * &y;
        u.invntt();
        u += &e1;
        u.reduce();

        let mu = Poly::from_msg(m);

        // v <- NTT^-1(t^T * y) + e_2 + mu
        let mut v = &self.t * &y;
        v.invntt();
        v += &e2;
        v += &mu;
        v.reduce();

        let (c1, c2) = c.split_first_chunk_mut().unwrap();
        let (c2, _) = c2.split_first_chunk_mut().unwrap();

        u.compress(c1);
        v.compress(c2);
    }
}

struct PkeDecKey {
    s: PolyVec,
}

impl PkeDecKey {
    const BYTE_SIZE: usize = K * Poly::ENCODED_BYTES;

    fn to_bytes(&self, bytes: &mut [u8; Self::BYTE_SIZE]) {
        self.s.byte_encode(bytes);
    }

    fn from_bytes(bytes: &[u8; Self::BYTE_SIZE]) -> Self {
        let mut s = PolyVec::from_bytes(bytes);
        s.reduce();

        Self { s }
    }

    /// Algorithm 15 K-PKE.Encrypt(dk_PKE, c)
    fn decrypt(&self, m: &mut [u8; 32], c: &[u8; PkeEncKey::CIPHERTEXT_SIZE]) {
        let (c1, c2) = c.split_first_chunk().unwrap();
        let (c2, _) = c2.split_first_chunk().unwrap();

        let mut u_prime = PolyVec::decompress(c1);
        let mut v_prime = Poly::decompress(c2);

        u_prime.ntt();
        let mut w = &self.s * &u_prime;
        w.invntt();

        v_prime -= &w;
        v_prime.reduce();

        v_prime.to_msg(m);
    }
}

/// Algorithm 13 K-PKE.KeyGen(d)
fn pke_keygen(d: &[u8; 32]) -> (PkeEncKey, PkeDecKey) {
    let (rho, sigma) = hash::sha3_512_split(&[d, &[K as u8]]);

    let mut xof = hash::Shake128::init();
    let a = PolyMatrix::generate(&mut xof, &rho);

    let mut prf = hash::Shake256::init();

    let (s, e) = generate_se(&mut prf, &sigma);

    let mut t: PolyVec = PolyVec::zero();

    for i in 0..K {
        t.vec[i].multiply_acc(&a.m[i], &s);
        t.vec[i].montgomery_form();
    }

    t += &e;
    t.reduce();

    (PkeEncKey { t, rho }, PkeDecKey { s })
}

/// ML-KEM encapsulation key (public key).
pub struct EncapsKey {
    ek_pke: PkeEncKey,
}

impl EncapsKey {
    /// Byte size of the bit-packed key.
    pub const BYTE_SIZE: usize = PkeEncKey::BYTE_SIZE;

    /// Byte size of the produced ciphertext.
    pub const CIPHERTEXT_SIZE: usize = PkeEncKey::CIPHERTEXT_SIZE;

    /// Encode key to bytes.
    pub fn to_bytes(&self, bytes: &mut [u8; Self::BYTE_SIZE]) {
        self.ek_pke.to_bytes(bytes);
    }

    /// Decode key from bytes.
    pub fn from_bytes(bytes: &[u8; Self::BYTE_SIZE]) -> Self {
        let ek_pke = PkeEncKey::from_bytes(bytes);

        Self { ek_pke }
    }

    /// Algorithm 17 ML-KEM.Encaps_internal(ek, m)
    fn encaps_internal(
        &self,
        c: &mut [u8; PkeEncKey::CIPHERTEXT_SIZE],
        k: &mut [u8; 32],
        m: &[u8; 32],
    ) {
        let mut bytes = [0u8; Self::BYTE_SIZE];
        self.to_bytes(&mut bytes);
        let h = hash::sha3_256(&[&bytes]);

        let (key, r) = hash::sha3_512_split(&[m, &h]);

        self.ek_pke.encrypt(c, m, &r);

        k.copy_from_slice(&key);
    }

    /// Algorithm 20 ML-KEM.Encaps(ek)
    pub fn encaps(
        &self,
        c: &mut [u8; Self::CIPHERTEXT_SIZE],
        k: &mut [u8; 32],
        rng: &mut impl rand_core::CryptoRng,
    ) {
        let mut m = [0u8; 32];
        rng.fill_bytes(&mut m);
        self.encaps_internal(c, k, &m);
    }
}

/// ML-KEM decapsulation key (secret key).
pub struct DecapsKey {
    dk_pke: PkeDecKey,
    h: [u8; 32],
    z: [u8; 32],
}

impl DecapsKey {
    /// Byte size of the bit-packed key.
    pub const BYTE_SIZE: usize = PkeDecKey::BYTE_SIZE + PkeEncKey::BYTE_SIZE + 32 + 32;

    /// Encode key to bytes.
    pub fn to_bytes(&self, bytes: &mut [u8; Self::BYTE_SIZE], ek: &EncapsKey) {
        let (dk_bytes, bytes) = bytes.split_first_chunk_mut().unwrap();
        let (ek_bytes, bytes) = bytes.split_first_chunk_mut().unwrap();
        let (ek_hash, bytes): (&mut [u8; 32], _) =
            bytes.split_first_chunk_mut().unwrap();
        let (z, _): (&mut [u8; 32], _) = bytes.split_first_chunk_mut().unwrap();

        self.dk_pke.to_bytes(dk_bytes);
        ek.ek_pke.to_bytes(ek_bytes);
        hash::sha3_256_into(ek_hash, &[ek_bytes]);
        z.copy_from_slice(&self.z);
    }

    /// Decode key from bytes.
    pub fn from_bytes(bytes: &[u8; Self::BYTE_SIZE]) -> Self {
        let (dk_bytes, bytes) = bytes.split_first_chunk().unwrap();
        let (_ek_bytes, bytes): (&[u8; PkeEncKey::BYTE_SIZE], _) =
            bytes.split_first_chunk().unwrap();
        let (h, bytes) = bytes.split_first_chunk().unwrap();
        let (z_bytes, _) = bytes.split_first_chunk().unwrap();

        let dk_pke = PkeDecKey::from_bytes(dk_bytes);

        Self {
            dk_pke,
            h: *h,
            z: *z_bytes,
        }
    }

    /// Algorithm 21 ML-KEM.Decaps(dk, c)
    /// Algorithm 18 ML-KEM.Decaps_internal(dk, c)
    pub fn decaps(
        &self,
        k: &mut [u8; 32],
        ek: &EncapsKey,
        c: &[u8; EncapsKey::CIPHERTEXT_SIZE],
    ) {
        let mut m_prime = [0u8; 32];
        self.dk_pke.decrypt(&mut m_prime, c);

        let (k_prime, r_prime) = hash::sha3_512_split(&[&m_prime, &self.h]);

        let mut j = hash::Shake256::init();
        j.absorb_multi(&[&self.z, c]);
        k.copy_from_slice(&j.squeezeblock()[..32]);

        let mut c_prime = [0u8; EncapsKey::CIPHERTEXT_SIZE];
        ek.ek_pke.encrypt(&mut c_prime, &m_prime, &r_prime);

        cmov(k, &k_prime, bytes_is_eq(c, &c_prime));
    }
}

/// Compare two byte arrays in constant time.
/// Returns 1 if equal and 0 if not equal.
const fn bytes_is_eq<const N: usize>(a: &[u8; N], b: &[u8; N]) -> u32 {
    let mut i = 0;
    let mut cond = 0;

    while i < N {
        cond |= (a[i] ^ b[i]) as u32;

        i += 1;
    }

    (cond.wrapping_neg() >> 31) ^ 1
}

/// Move `src` into `dst` if `cond == 1` in constant time.
fn cmov<const N: usize>(dst: &mut [u8; N], src: &[u8; N], cond: u32) {
    let cond = black_box(cond).wrapping_neg() as u8;

    for (a, b) in dst.iter_mut().zip(src.iter()) {
        *a ^= cond & (*a ^ *b);
    }
}

/// Algorithm 19 ML-KEM.KeyGen()
pub fn keygen(rng: &mut impl rand_core::CryptoRng) -> (EncapsKey, DecapsKey) {
    let mut d = [0u8; 32];
    rng.fill_bytes(&mut d);

    let mut z = [0u8; 32];
    rng.fill_bytes(&mut z);

    keygen_deterministic(d, z)
}

fn keygen_deterministic(d: [u8; 32], z: [u8; 32]) -> (EncapsKey, DecapsKey) {
    let (ek_pke, dk_pke) = pke_keygen(&d);

    let ek = EncapsKey { ek_pke };

    let mut ek_bytes = [0u8; EncapsKey::BYTE_SIZE];
    ek.to_bytes(&mut ek_bytes);

    let h = hash::sha3_256(&[&ek_bytes]);

    (ek, DecapsKey { dk_pke, h, z })
}

#[cfg(test)]
mod tests {
    use serde::Deserialize;
    use std::{fs::read_to_string, path::PathBuf};

    use super::*;

    #[test]
    fn test_keygen() {
        let mut test_data_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        test_data_path.push("tests/kyber-keygen.json");

        let test_data = read_to_string(&test_data_path).unwrap();
        let test_data: Tests<KeyGenTestGroup> =
            serde_json::from_str(&test_data).unwrap();

        for test_group in test_data
            .test_groups
            .iter()
            .filter(|g| g.parameter_set == "ML-KEM-768")
        {
            for test in test_group.tests.iter() {
                // validate sizes
                assert_eq!(test.ek.len(), EncapsKey::BYTE_SIZE);
                assert_eq!(test.dk.len(), DecapsKey::BYTE_SIZE);

                let (ek, dk) = keygen_deterministic(test.d, test.z);

                // Test decoded decaps key
                let test_dk =
                    DecapsKey::from_bytes(test.dk.as_slice().try_into().unwrap());
                assert_eq!(test_dk.z, test.z);
                assert_eq!(dk.z, test.z);
                assert_eq!(test_dk.dk_pke.s, dk.dk_pke.s);

                // Test decoded encaps key
                let test_ek =
                    EncapsKey::from_bytes(test.ek.as_slice().try_into().unwrap());
                assert_eq!(test_ek.ek_pke.rho, ek.ek_pke.rho);
                assert_eq!(test_ek.ek_pke.t.vec, ek.ek_pke.t.vec);

                // Test encoding of encaps key
                let mut ek_bytes = [0u8; EncapsKey::BYTE_SIZE];
                ek.to_bytes(&mut ek_bytes);
                assert_eq!(ek_bytes, test.ek.as_slice());

                // Test encoding of decaps key
                let mut dk_bytes = [0u8; DecapsKey::BYTE_SIZE];
                dk.to_bytes(&mut dk_bytes, &ek);
                assert_eq!(dk_bytes, test.dk.as_slice());
            }
        }
    }

    #[test]
    fn test_kem() {
        let mut test_data_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        test_data_path.push("tests/kyber-kem.json");

        let test_data = read_to_string(&test_data_path).unwrap();
        let test_data: Tests<KemTestGroup> = serde_json::from_str(&test_data).unwrap();

        for test_group in test_data
            .test_groups
            .iter()
            .filter(|g| g.parameter_set == "ML-KEM-768")
        {
            match &test_group.params {
                KemTestGroupKind::Aft { tests } => {
                    for test in tests.iter() {
                        assert_eq!(test.c.len(), EncapsKey::CIPHERTEXT_SIZE);
                        let ek = EncapsKey::from_bytes(
                            test.ek.as_slice().try_into().unwrap(),
                        );
                        let dk = DecapsKey::from_bytes(
                            test.dk.as_slice().try_into().unwrap(),
                        );

                        let mut c = [0u8; EncapsKey::CIPHERTEXT_SIZE];
                        let mut k = [0u8; 32];
                        ek.encaps_internal(
                            &mut c,
                            &mut k,
                            test.m.as_slice().try_into().unwrap(),
                        );

                        assert_eq!(c, test.c.as_slice());
                        assert_eq!(k, test.k.as_slice());

                        let mut k_prime = [0u8; 32];
                        dk.decaps(&mut k_prime, &ek, &c);
                        assert_eq!(&k, &k_prime);
                    }
                }
                KemTestGroupKind::Val { tests, dk, ek } => {
                    let ek = EncapsKey::from_bytes(ek.as_slice().try_into().unwrap());
                    let dk = DecapsKey::from_bytes(dk.as_slice().try_into().unwrap());
                    for test in tests.iter() {
                        assert_eq!(test.c.len(), EncapsKey::CIPHERTEXT_SIZE);

                        let mut k = [0u8; 32];
                        dk.decaps(&mut k, &ek, test.c[..].try_into().unwrap());

                        assert_eq!(&k, &test.k[..]);
                    }
                }
            }
        }
    }

    #[test]
    fn test_kem_random() {
        let mut rng = rand::rng();
        let (ek, dk) = keygen(&mut rng);
        let mut c = [0u8; EncapsKey::CIPHERTEXT_SIZE];
        let mut k = [0u8; 32];
        ek.encaps(&mut c, &mut k, &mut rng);

        let mut k_prime = [0u8; 32];
        dk.decaps(&mut k_prime, &ek, &c);

        assert_eq!(&k, &k_prime);
    }

    fn gen_rand_bytes<const N: usize>(rng: &mut impl rand::CryptoRng) -> [u8; N] {
        let mut bytes = [0; N];
        rng.fill_bytes(&mut bytes);
        bytes
    }

    #[test]
    fn test_compress() {
        let compr_pvec = gen_rand_bytes(&mut rand::rng());
        let mut compr_pvec_prime = [0; PolyVec::COMPRESSED_BYTES];
        let pvec = PolyVec::decompress(&compr_pvec);
        pvec.compress(&mut compr_pvec_prime);
        assert_eq!(&compr_pvec, &compr_pvec_prime);

        let compr_poly = gen_rand_bytes(&mut rand::rng());
        let mut compr_poly_prime = [0; Poly::COMPRESSED_BYTES];
        let poly = Poly::decompress(&compr_poly);
        poly.compress(&mut compr_poly_prime);
        assert_eq!(&compr_poly, &compr_poly_prime)
    }

    #[derive(Deserialize)]
    struct Tests<T> {
        #[serde(rename = "isSample")]
        _is_sample: bool,

        #[serde(rename = "testGroups")]
        test_groups: Vec<T>,

        #[serde(rename = "vsId")]
        _vs_id: i64,
    }

    #[derive(Deserialize)]
    struct KeyGenTestGroup {
        #[serde(rename = "parameterSet")]
        parameter_set: String,

        #[serde(rename = "testType")]
        _test_type: String,

        tests: Vec<KeyGenTestVector>,

        #[serde(rename = "tgId")]
        _tg_id: i64,
    }

    #[derive(Deserialize)]
    struct KeyGenTestVector {
        #[serde(with = "hex")]
        d: [u8; 32],

        #[serde(with = "hex")]
        z: [u8; 32],

        #[serde(with = "hex")]
        dk: Vec<u8>,

        #[serde(with = "hex")]
        ek: Vec<u8>,

        #[serde(rename = "tcId")]
        _tc_id: i64,
    }

    #[derive(Deserialize)]
    struct KemTestVectorAft {
        #[serde(with = "hex")]
        c: Vec<u8>,

        #[serde(with = "hex")]
        dk: Vec<u8>,

        #[serde(with = "hex")]
        ek: Vec<u8>,

        #[serde(with = "hex")]
        k: Vec<u8>,

        #[serde(with = "hex")]
        m: Vec<u8>,

        #[serde(rename = "tcId")]
        _tc_id: i64,
    }

    #[derive(Deserialize)]
    struct KemTestVectorVal {
        #[serde(with = "hex")]
        c: Vec<u8>,

        #[serde(with = "hex")]
        k: Vec<u8>,

        #[serde(rename = "tcId")]
        _tc_id: i64,
    }

    #[derive(Deserialize)]
    struct KemTestGroup {
        #[serde(rename = "parameterSet")]
        parameter_set: String,

        #[serde(rename = "tgId")]
        _tg_id: i64,

        #[serde(flatten)]
        params: KemTestGroupKind,
    }

    #[derive(Deserialize)]
    #[serde(tag = "testType")]
    enum KemTestGroupKind {
        #[serde(rename = "AFT")]
        Aft { tests: Vec<KemTestVectorAft> },
        #[serde(rename = "VAL")]
        Val {
            tests: Vec<KemTestVectorVal>,

            #[serde(with = "hex")]
            dk: Vec<u8>,

            #[serde(with = "hex")]
            ek: Vec<u8>,
        },
    }
}
