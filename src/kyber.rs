use crate::{
    compress::{compr_10bit, compr_4bit, decompr_10bit, decompr_1bit, decompr_4bit},
    hash,
    reduce::{self, barrett_reduce},
};
use core::{
    array,
    fmt::Display,
    mem::{self, MaybeUninit},
    ops::Mul,
};
use rand_core::CryptoRngCore;
use sha3::digest::XofReader;

pub const N: usize = 256;
pub const K: usize = 3;
pub const ETA1: usize = 2;
pub const Q: i16 = 3329;
pub const DU: usize = 10;
pub const DV: usize = 4;

const COEFFICIENT_BITSIZE: usize = 12;

/// pre-computed zetas in montgomery form
/// ordered by ZETAS[i] = z^BitRev7(i)
/// zeta -> zeta * R (mod Q)
pub const ZETAS: [i16; 128] = [
    -1044, -758, -359, -1517, 1493, 1422, 287, 202, -171, 622, 1577, 182, 962, -1202, -1474, 1468,
    573, -1325, 264, 383, -829, 1458, -1602, -130, -681, 1017, 732, 608, -1542, 411, -205, -1571,
    1223, 652, -552, 1015, -1293, 1491, -282, -1544, 516, -8, -320, -666, -1618, -1162, 126, 1469,
    -853, -90, -271, 830, 107, -1421, -247, -951, -398, 961, -1508, -725, 448, -1065, 677, -1275,
    -1103, 430, 555, 843, -1251, 871, 1550, 105, 422, 587, 177, -235, -291, -460, 1574, 1653, -246,
    778, 1159, -147, -777, 1483, -602, 1119, -1590, 644, -872, 349, 418, 329, -156, -75, 817, 1097,
    603, 610, 1322, -1285, -1465, 384, -1215, -136, 1218, -1335, -874, 220, -1187, -1659, -1185,
    -1530, -1278, 794, -1510, -854, -870, 478, -108, -308, 996, 991, 958, -1460, 1522, 1628,
];

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

    fn sample_ntt(&mut self, mut xof: impl XofReader) {
        let f = &mut self.f;

        let mut b = [0u8; 3];

        let mut coeffs = f.iter_mut();

        loop {
            xof.read(&mut b);
            let (b0, b1, b2) = (b[0] as u16, b[1] as u16, b[2] as u16);

            let d1 = b0 | (b1 & 0xF) << 8;
            let d2 = b1 >> 4 | b2 << 4;

            if d1 < Q as u16 {
                if let Some(a) = coeffs.next() {
                    *a = d1 as i16;
                } else {
                    break;
                }
            }

            if d2 < Q as u16 {
                if let Some(a) = coeffs.next() {
                    *a = d2 as i16;
                } else {
                    break;
                }
            }
        }
    }

    fn sample_poly_cbd2(&mut self, mut xof: impl XofReader) {
        let f = &mut self.f;
        let mut le_bytes = [0u8; 4];

        for i in 0..32 {
            xof.read(&mut le_bytes);
            let t = u32::from_le_bytes(le_bytes);

            // add bits to each other in groups of two
            let d = (t & 0x55555555) + ((t >> 1) & 0x55555555);

            for j in 0..(32 / (2 * 2)) {
                // extract two 2-bit numbers
                let x = (d >> (j << 2)) & 3;
                let y = (d >> ((j << 2) + 2)) & 3;
                f[8 * i + j] = x as i16 - y as i16;
            }
        }
    }

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

    fn add(&mut self, other: &Poly) {
        for (a, b) in self.f.iter_mut().zip(other.f.iter()) {
            *a += b;
        }
    }

    fn reduce(&mut self) {
        for a in self.f.iter_mut() {
            *a = barrett_reduce(*a);
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

        for (a, b) in coeffs.chunks_mut(2).zip(bytes.chunks(3)) {
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

            *b = c[0] | c[1] << 4;
        }
    }

    fn decompress(&mut self, bytes: &[u8; Self::COMPRESSED_BYTES]) {
        const MOD_MASK: u8 = (1 << DV) - 1;

        for (a, b) in self.f.chunks_exact_mut(2).zip(bytes.iter()) {
            a[0] = decompr_4bit(b & MOD_MASK);
            a[1] = decompr_4bit(b >> DV);
        }
    }

    #[inline]
    fn generate_eta2<I>(r: &[u8; 32], nonce: &mut I) -> Self
    where
        I: Iterator<Item = usize>,
    {
        let mut poly = Poly::zero();

        let prf = hash::prf(r, nonce.next().unwrap());

        poly.sample_poly_cbd2(prf);

        poly
    }

    #[inline]
    fn from_msg(m: &[u8; 32]) -> Self {
        let mut poly = Poly::zero();

        for (coeffs, byte) in poly.f.chunks_exact_mut(8).zip(m.iter()) {
            for (a, bit) in coeffs.iter_mut().zip((0..8).map(|n| *byte >> n)) {
                *a = decompr_1bit(bit);
            }
        }

        poly
    }
}

impl Display for Poly {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut coeffs = self.f.iter().enumerate().filter(|(_, &a)| a != 0);

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
    let t0 = ((b0 as u16) | (b1 as u16) << 8) & 0xFFF;
    let t1 = (((b1 as u16) >> 4) | (b2 as u16) << 4) & 0xFFF;

    (t0 as i16, t1 as i16)
}

const fn basemul(a0: i16, a1: i16, b0: i16, b1: i16, zeta: i16) -> (i16, i16) {
    let c0 = reduce::mont_mul(a0, b0) + reduce::mont_mul(reduce::mont_mul(a1, b1), zeta);
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

    fn add(&mut self, other: &Self) {
        for (f, g) in self.vec.iter_mut().zip(other.vec.iter()) {
            f.add(g);
        }
    }

    fn reduce(&mut self) {
        for p in self.vec.iter_mut() {
            p.reduce();
        }
    }

    #[inline]
    fn ntt(&mut self) {
        for p in self.vec.iter_mut() {
            p.ntt();
        }
    }

    #[inline]
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

    fn decompress(&mut self, bytes: &[u8; Self::COMPRESSED_BYTES]) {
        for (p, b) in self
            .vec
            .iter_mut()
            .zip(bytes.chunks_exact(Self::COMPRESSED_POLY_BYTES))
        {
            for (a, b) in p.f.chunks_exact_mut(4).zip(b.chunks_exact(5)) {
                let mut t: [u16; 5] = array::from_fn(|i| b[i] as u16);
                t[0] |= t[1] << 8;
                t[1] = t[1] >> 2 | t[2] >> 6;
                t[2] = t[2] >> 4 | t[3] >> 4;
                t[3] = t[3] >> 6 | t[4] >> 3;

                for i in &t[..4] {
                    a[0] = decompr_10bit(i & 0x3FF);
                }
            }
        }
    }

    #[inline]
    fn generate_eta1<I>(r: &[u8; 32], nonce: &mut I) -> Self
    where
        I: Iterator<Item = usize>,
    {
        let mut pvec = PolyVec::zero();

        for (poly, nonce) in pvec.vec.iter_mut().zip(nonce) {
            let prf = hash::prf(r, nonce);

            poly.sample_poly_cbd2(prf);
        }

        pvec
    }

    #[inline]
    fn generate_eta2<I>(r: &[u8; 32], nonce: &mut I) -> Self
    where
        I: Iterator<Item = usize>,
    {
        let mut pvec = PolyVec::zero();

        for (poly, nonce) in pvec.vec.iter_mut().zip(nonce) {
            let prf = hash::prf(r, nonce);

            poly.sample_poly_cbd2(prf);
        }

        pvec
    }
}

impl Mul<&PolyVec> for &PolyVec {
    type Output = Poly;

    #[inline]
    fn mul(self, rhs: &PolyVec) -> Self::Output {
        let mut out = Poly::zero();

        out.multiply_acc(self, rhs);

        out
    }
}

#[derive(Debug)]
struct PolyMatrix {
    m: [PolyVec; K],
}

impl PolyMatrix {
    fn generate(rho: &[u8; 32]) -> Self {
        let mut m = [const { PolyVec::zero() }; K];

        for (i, polyvec) in m.iter_mut().enumerate() {
            for (j, poly) in polyvec.vec.iter_mut().enumerate() {
                let xof = hash::xof(rho, j, i);

                poly.sample_ntt(xof);
            }
        }

        Self { m }
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

fn generate_se(sigma: &[u8; 32]) -> (PolyVec, PolyVec) {
    let mut s = PolyVec::zero();
    let mut e = PolyVec::zero();

    for (nonce, poly) in s.vec.iter_mut().chain(e.vec.iter_mut()).enumerate() {
        let prf = hash::prf(sigma, nonce);

        poly.sample_poly_cbd2(prf);
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

    #[inline]
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
}

struct PkeDecKey {
    s: PolyVec,
}

impl PkeDecKey {
    const BYTE_SIZE: usize = K * Poly::ENCODED_BYTES;

    #[inline]
    fn to_bytes(&self, bytes: &mut [u8; Self::BYTE_SIZE]) {
        self.s.byte_encode(bytes);
    }

    fn from_bytes(bytes: &[u8; Self::BYTE_SIZE]) -> Self {
        let mut s = PolyVec::from_bytes(bytes);
        s.reduce();

        Self { s }
    }
}

fn pke_keygen(d: &[u8; 32]) -> (PkeEncKey, PkeDecKey) {
    let (rho, sigma) = hash::g(&[d, &[K as u8]]);

    let a = PolyMatrix::generate(&rho);

    let (s, e) = generate_se(&sigma);

    let mut t: PolyVec = PolyVec::zero();

    for i in 0..K {
        t.vec[i].multiply_acc(&a.m[i], &s);
        t.vec[i].montgomery_form();
    }

    t.add(&e);
    t.reduce();

    (PkeEncKey { t, rho }, PkeDecKey { s })
}

pub struct EncapsKey {
    ek_pke: PkeEncKey,
}

impl EncapsKey {
    pub const BYTE_SIZE: usize = PkeEncKey::BYTE_SIZE;

    #[inline]
    pub fn to_bytes(&self, bytes: &mut [u8; Self::BYTE_SIZE]) {
        self.ek_pke.to_bytes(bytes);
    }

    pub fn from_bytes(bytes: &[u8; Self::BYTE_SIZE]) -> Self {
        let ek_pke = PkeEncKey::from_bytes(bytes);

        Self { ek_pke }
    }
}

pub struct DecapsKey {
    dk_pke: PkeDecKey,
    z: [u8; 32],
}

impl DecapsKey {
    pub const BYTE_SIZE: usize = PkeDecKey::BYTE_SIZE + PkeEncKey::BYTE_SIZE + 32 + 32;

    #[inline]
    pub fn to_bytes(&self, bytes: &mut [u8; Self::BYTE_SIZE], ek: &EncapsKey) {
        let (dk_bytes, bytes) = bytes.split_first_chunk_mut().unwrap();
        let (ek_bytes, bytes) = bytes.split_first_chunk_mut().unwrap();
        let (ek_hash, bytes): (&mut [u8; 32], _) = bytes.split_first_chunk_mut().unwrap();
        let (z, _): (&mut [u8; 32], _) = bytes.split_first_chunk_mut().unwrap();

        self.dk_pke.to_bytes(dk_bytes);
        ek.ek_pke.to_bytes(ek_bytes);
        hash::h(ek_hash, ek_bytes);
        z.copy_from_slice(&self.z);
    }

    pub fn from_bytes(bytes: &[u8; Self::BYTE_SIZE]) -> Self {
        let (dk_bytes, bytes) = bytes.split_first_chunk().unwrap();
        let (_ek_bytes, bytes): (&[u8; PkeEncKey::BYTE_SIZE], _) =
            bytes.split_first_chunk().unwrap();
        let (_hash_bytes, bytes): (&[u8; 32], _) = bytes.split_first_chunk().unwrap();
        let (z_bytes, _) = bytes.split_first_chunk().unwrap();

        let dk_pke = PkeDecKey::from_bytes(dk_bytes);

        Self {
            dk_pke,
            z: *z_bytes,
        }
    }
}

pub fn keygen(rng: &mut impl CryptoRngCore) -> (EncapsKey, DecapsKey) {
    let mut d = [0u8; 32];
    rng.fill_bytes(&mut d);

    let mut z = [0u8; 32];
    rng.fill_bytes(&mut z);

    keygen_deterministic(d, z)
}

pub fn keygen_deterministic(d: [u8; 32], z: [u8; 32]) -> (EncapsKey, DecapsKey) {
    let (ek_pke, dk_pke) = pke_keygen(&d);

    (EncapsKey { ek_pke }, DecapsKey { dk_pke, z })
}

#[cfg(test)]
mod tests {
    use serde::{Deserialize, Serialize};
    use std::{fs::read_to_string, path::PathBuf};

    use super::*;

    #[test]
    fn keygen() {
        let mut test_data_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        test_data_path.push("tests/kyber-keygen.json");

        let test_data = read_to_string(&test_data_path).unwrap();
        let test_data: Tests = serde_json::from_str(&test_data).unwrap();

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
                let test_dk = DecapsKey::from_bytes(test.dk.as_slice().try_into().unwrap());
                assert_eq!(test_dk.z, test.z);
                assert_eq!(dk.z, test.z);
                assert_eq!(test_dk.dk_pke.s, dk.dk_pke.s);

                // Test decoded encaps key
                let test_ek = EncapsKey::from_bytes(test.ek.as_slice().try_into().unwrap());
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

    #[derive(Serialize, Deserialize)]
    struct KeyGenTestVector {
        #[serde(with = "hex")]
        d: [u8; 32],

        #[serde(with = "hex")]
        z: [u8; 32],

        deferred: bool,

        #[serde(with = "hex")]
        dk: Vec<u8>,

        #[serde(with = "hex")]
        ek: Vec<u8>,

        #[serde(rename = "tcId")]
        tc_id: i64,
    }

    #[derive(Serialize, Deserialize)]
    struct TestGroup {
        #[serde(rename = "parameterSet")]
        parameter_set: String,

        #[serde(rename = "testType")]
        test_type: String,

        tests: Vec<KeyGenTestVector>,

        #[serde(rename = "tgId")]
        tg_id: i64,
    }

    #[derive(Serialize, Deserialize)]
    struct Tests {
        algorithm: String,

        #[serde(rename = "isSample")]
        is_sample: bool,

        mode: String,

        revision: String,

        #[serde(rename = "testGroups")]
        test_groups: Vec<TestGroup>,

        #[serde(rename = "vsId")]
        vs_id: i64,
    }
}
