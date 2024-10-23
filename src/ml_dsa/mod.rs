use core::{
    mem::MaybeUninit,
    ops::{AddAssign, Mul},
};

use sha3::digest::XofReader;

mod hash;
mod reduce;

const Q: i32 = 8380417;
const N: usize = 256;
const ZETA: i32 = 1753;

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

/// ML-DSA.KeyGen()
/// Generates a public-private key pair
pub fn keygen() {}

struct KeyGenBuffers {
    rho: [u8; 32],
    rho_prime: [u8; 64],
    k: [u8; 32],
}

impl Drop for KeyGenBuffers {
    fn drop(&mut self) {}
}

mod mldsa65 {
    use core::mem::MaybeUninit;

    use super::{expand_a, expand_s, hash, KeyGenBuffers, PolyMat};

    const K: usize = 6;
    const L: usize = 5;
    const ETA: usize = 4;

    fn keygen_internal(ksi: &[u8; 32]) {
        let mut uninit_buf: MaybeUninit<KeyGenBuffers> = MaybeUninit::uninit();
        let buf = unsafe { uninit_buf.assume_init_mut() };

        hash::h(
            &mut [&mut buf.rho, &mut buf.rho_prime, &mut buf.k],
            &[ksi, &[K as u8], &[L as u8]],
        );

        let a_hat: PolyMat<K, L> = expand_a(&buf.rho);
        let (mut s1, s2) = expand_s::<K, L, ETA>(&buf.rho_prime);

        s1.ntt();
        let mut t = a_hat.multiply_ntt(&s1);
        t.reduce_invntt_tomont();

        t += &s2;
    }
}

struct Poly {
    f: [i32; N],
}

impl Poly {
    // const ENCODED_BYTES: usize = (COEFFICIENT_BITSIZE * N) / 8;
    // const COMPRESSED_BYTES: usize = (N * DV) / 8;

    /// NTT(w)
    fn ntt(&mut self) {
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

        // self.reduce();
    }

    /// NTT^-1 (w_hat)
    fn invntt_tomont(&mut self) {
        let w = &mut self.f;

        let mut m = 255;

        for len in (0..8).map(|n| 1 << n) {
            for start in (0..256).step_by(len << 1) {
                let zeta = ZETAS[m];
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

            if z0 != 0 {
                if let Some(a) = coeffs.next() {
                    *a = z0;
                }
            }

            if z1 != 0 {
                if let Some(a) = coeffs.next() {
                    *a = z1;
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

    fn reduce(&mut self) {
        for a in self.f.iter_mut() {
            *a = reduce::barrett_reduce(*a);
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

/// Convert 3 bytes into an element of Z_Q.
const fn coeff_from_bytes(b0: u8, b1: u8, b2: u8) -> i32 {
    let mut z = b0 as u32;
    z += (b1 as u32) << 8;
    z += (b2 as u32 & 0x7F) << 16;

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
const fn coeffs_from_halfbytes<const ETA: usize>(b: u8) -> (i32, i32) {
    let mut a0 = 0i32;
    let mut a1 = 0i32;

    let b0 = (b & 0xF) as u32;
    let b1 = (b >> 4) as u32;

    match ETA {
        2 => {
            if b0 < 16 {
                a0 = 2 - mod5(b0);
            }
            if b1 < 16 {
                a1 = 2 - mod5(b1);
            }
        }
        4 => {
            if b0 < 9 {
                a0 = 4 - b0 as i32;
            }
            if b1 < 9 {
                a1 = 4 - b1 as i32;
            }
        }
        _ => unreachable!(),
    }

    (a0, a1)
}

struct PolyMat<const K: usize, const L: usize> {
    m: [PolyVec<L>; K],
}

impl<const K: usize, const L: usize> PolyMat<K, L> {
    #[inline]
    fn multiply_ntt(self, v: &PolyVec<L>) -> PolyVec<K> {
        let mut uninit_w_hat: MaybeUninit<PolyVec<K>> = MaybeUninit::uninit();
        let w_hat = unsafe { uninit_w_hat.assume_init_mut() };

        w_hat.multiply_ntt(&self.m[0], v);

        for i in 1..K {
            w_hat.multiply_ntt_acc(&self.m[i], v)
        }

        unsafe { uninit_w_hat.assume_init() }
    }
}

/// ExpandA(rho)
#[inline]
fn expand_a<const K: usize, const L: usize>(rho: &[u8; 32]) -> PolyMat<K, L> {
    let mut uninit_m: MaybeUninit<PolyMat<K, L>> = MaybeUninit::uninit();
    let m = unsafe { &mut uninit_m.assume_init_mut().m };

    let mut g = hash::G::init();

    for (r, polyvec) in m.iter_mut().enumerate() {
        for (s, poly) in polyvec.v.iter_mut().enumerate() {
            let mut xof = g.absorb(&[rho, &[s as u8], &[r as u8]]);

            poly.rej_ntt(&mut xof);
        }
    }

    unsafe { uninit_m.assume_init() }
}

struct PolyVec<const K: usize> {
    v: [Poly; K],
}

impl<const K: usize> PolyVec<K> {
    fn ntt(&mut self) {
        for p in self.v.iter_mut() {
            p.ntt();
        }
    }

    fn multiply_ntt(&mut self, u: &Self, v: &Self) {
        for i in 0..K {
            self.v[i].multiply_ntt(&u.v[i], &v.v[i]);
        }
    }

    fn multiply_ntt_acc(&mut self, u: &Self, v: &Self) {
        for i in 0..K {
            self.v[i].multiply_ntt_acc(&u.v[i], &v.v[i]);
        }
    }

    fn reduce(&mut self) {
        for p in self.v.iter_mut() {
            p.reduce();
        }
    }

    fn invntt_tomont(&mut self) {
        for p in self.v.iter_mut() {
            p.invntt_tomont();
        }
    }

    fn reduce_invntt_tomont(&mut self) {
        for p in self.v.iter_mut() {
            p.reduce();
            p.invntt_tomont();
        }
    }
}

impl<const K: usize> AddAssign<&PolyVec<K>> for PolyVec<K> {
    fn add_assign(&mut self, rhs: &PolyVec<K>) {
        for (f, g) in self.v.iter_mut().zip(rhs.v.iter()) {
            *f += g;
        }
    }
}

/// ExpandS(rho)
#[inline]
fn expand_s<const K: usize, const L: usize, const ETA: usize>(
    rho: &[u8; 64],
) -> (PolyVec<L>, PolyVec<K>) {
    let mut uninit_s1: MaybeUninit<PolyVec<L>> = MaybeUninit::uninit();
    let mut uninit_s2: MaybeUninit<PolyVec<K>> = MaybeUninit::uninit();

    let (s1, s2) = unsafe { (uninit_s1.assume_init_mut(), uninit_s2.assume_init_mut()) };

    let mut h = hash::H::init();

    for (nonce, poly) in s1.v.iter_mut().chain(s2.v.iter_mut()).enumerate() {
        let mut xof = h.absorb(&[rho, &u16::to_le_bytes(nonce as u16)]);
        poly.rej_bounded::<ETA>(&mut xof);
    }

    unsafe { (uninit_s1.assume_init(), uninit_s2.assume_init()) }
}

//     /// Algorithm 8 SamplePolyCBD_2 (B)
//     fn sample_poly_cbd2(&mut self, mut xof: impl XofReader) {
//         let f = &mut self.f;
//         let mut le_bytes = [0u8; 4];

//         for i in 0..32 {
//             xof.read(&mut le_bytes);
//             let t = u32::from_le_bytes(le_bytes);

//             // add bits to each other in groups of two
//             let d = (t & 0x55555555) + ((t >> 1) & 0x55555555);

//             for j in 0..(32 / (2 * 2)) {
//                 // extract two 2-bit numbers
//                 let x = (d >> (j << 2)) & 3;
//                 let y = (d >> ((j << 2) + 2)) & 3;
//                 f[8 * i + j] = x as i16 - y as i16;
//             }
//         }
//     }

//     /// Algorithm 11 MultiplyNTTs(f_hat, g_hat)
//     fn multiply_ntts_acc(&mut self, f: &Poly, g: &Poly) {
//         let h = &mut self.f;
//         let f = &f.f;
//         let g = &g.f;

//         for i in (0..N).step_by(4) {
//             let zeta_idx = 64 + (i >> 2);

//             let a = basemul(f[i], f[i + 1], g[i], g[i + 1], ZETAS[zeta_idx]);
//             let b = basemul(f[i + 2], f[i + 3], g[i + 2], g[i + 3], -ZETAS[zeta_idx]);

//             h[i] += a.0;
//             h[i + 1] += a.1;
//             h[i + 2] += b.0;
//             h[i + 3] += b.1;
//         }
//     }

//     fn multiply_acc(&mut self, a: &PolyVec, b: &PolyVec) {
//         for (f, g) in a.vec.iter().zip(b.vec.iter()) {
//             self.multiply_ntts_acc(f, g);
//         }

//         self.reduce();
//     }

//     fn montgomery_form(&mut self) {
//         for a in self.f.iter_mut() {
//             *a = reduce::to_mont(*a);
//         }
//     }

//     fn reduce(&mut self) {
//         for a in self.f.iter_mut() {
//             *a = reduce::barrett_reduce(*a);
//         }
//     }

//     /// Encode coefficients as bits in little endian order.
//     fn byte_encode(&self, bytes: &mut [u8; Poly::ENCODED_BYTES]) {
//         for (a, b) in self.f.chunks(2).zip(bytes.chunks_mut(3)) {
//             let (b0, b1, b2) = coeffs2bytes(a[0], a[1]);

//             b[0] = b0;
//             b[1] = b1;
//             b[2] = b2;
//         }
//     }

//     #[inline]
//     fn byte_decode(bytes: &[u8; Self::ENCODED_BYTES]) -> Self {
//         let mut coeffs: [MaybeUninit<i16>; N] = [MaybeUninit::uninit(); N];

//         for (a, b) in coeffs.chunks_exact_mut(2).zip(bytes.chunks_exact(3)) {
//             let (t0, t1) = bytes2coeffs(b[0], b[1], b[2]);

//             a[0].write(t0);
//             a[1].write(t1);
//         }

//         Self {
//             f: unsafe { mem::transmute::<[MaybeUninit<i16>; N], [i16; N]>(coeffs) },
//         }
//     }

//     fn compress(&self, bytes: &mut [u8; Self::COMPRESSED_BYTES]) {
//         for (b, a) in bytes.iter_mut().zip(self.f.chunks_exact(2)) {
//             let c: [u8; 2] = array::from_fn(|i| compr_4bit(a[i]));

//             *b = c[0] | c[1] << 4;
//         }
//     }

//     #[inline]
//     fn decompress(bytes: &[u8; Self::COMPRESSED_BYTES]) -> Self {
//         const MOD_MASK: u8 = (1 << DV) - 1;

//         let mut poly = Poly::zero();

//         for (a, b) in poly.f.chunks_exact_mut(2).zip(bytes.iter()) {
//             a[0] = decompr_4bit(b & MOD_MASK);
//             a[1] = decompr_4bit(b >> DV);
//         }

//         poly
//     }

//     #[inline]
//     fn generate_eta2<I>(r: &[u8; 32], nonce: &mut I) -> Self
//     where
//         I: Iterator<Item = usize>,
//     {
//         let mut poly = Poly::zero();

//         let prf = hash::prf(r, nonce.next().unwrap());

//         poly.sample_poly_cbd2(prf);

//         poly
//     }

//     #[inline]
//     fn from_msg(m: &[u8; 32]) -> Self {
//         let mut poly = Poly::zero();

//         for (coeffs, byte) in poly.f.chunks_exact_mut(8).zip(m.iter()) {
//             for (a, bit) in coeffs.iter_mut().zip((0..8).map(|n| *byte >> n)) {
//                 *a = decompr_1bit(bit);
//             }
//         }

//         poly
//     }

//     fn to_msg(&self, m: &mut [u8; 32]) {
//         for (byte, coeffs) in m.iter_mut().zip(self.f.chunks_exact(8)) {
//             for (i, a) in coeffs.iter().enumerate() {
//                 *byte |= compr_1bit(*a) << i;
//             }
//         }
//     }
// }

// impl SubAssign<&Poly> for Poly {
//     fn sub_assign(&mut self, rhs: &Poly) {
//         for (a, b) in self.f.iter_mut().zip(rhs.f.iter()) {
//             *a -= b;
//         }
//     }
// }

// impl Display for Poly {
//     fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
//         let mut coeffs = self.f.iter().enumerate().filter(|(_, &a)| a != 0);

//         match coeffs.next() {
//             Some((_, a)) => write!(f, "f(X) = {}", a)?,
//             None => return write!(f, "f(X) = 0"),
//         };

//         for (i, a) in coeffs {
//             write!(f, " + {}X^{}", a, i)?;
//         }

//         Ok(())
//     }
// }

// /// Convert 2 integers mod Q into 3 bytes.
// const fn coeffs2bytes(a: i16, b: i16) -> (u8, u8, u8) {
//     let t0 = a + ((a >> 15) & Q);
//     let t1 = b + ((b >> 15) & Q);

//     // encode 2 coeficcients (12 bit) into 24 bits
//     (t0 as u8, ((t0 >> 8) | (t1 << 4)) as u8, (t1 >> 4) as u8)
// }

// /// Algorithm 12 BaseCaseMultiply(a_0, a_1, b_0, b_1, zeta)
// /// Compute:
// /// - c0 = (a0*b0 + a1*b1*zeta)R^-1 (mod Q)
// /// - c1 = (a0*b1 + a1*b0)R^-1 (mod Q)
// const fn basemul(a0: i16, a1: i16, b0: i16, b1: i16, zeta: i16) -> (i16, i16) {
//     let c0 = reduce::mont_mul(a0, b0) + reduce::mont_mul(reduce::mont_mul(a1, b1), zeta);
//     let c1 = reduce::mont_mul(a0, b1) + reduce::mont_mul(a1, b0);

//     (c0, c1)
// }

// impl PolyVec {
//     const BYTE_SIZE: usize = K * Poly::ENCODED_BYTES;
//     const COMPRESSED_POLY_BYTES: usize = (N * DU) / 8;
//     const COMPRESSED_BYTES: usize = K * Self::COMPRESSED_POLY_BYTES;

//     const fn zero() -> Self {
//         Self {
//             vec: [const { Poly::zero() }; K],
//         }
//     }

//     fn reduce(&mut self) {
//         for p in self.vec.iter_mut() {
//             p.reduce();
//         }
//     }

//     #[inline]
//     fn ntt(&mut self) {
//         for p in self.vec.iter_mut() {
//             p.ntt();
//         }
//     }

//     #[inline]
//     fn invntt(&mut self) {
//         for p in self.vec.iter_mut() {
//             p.invntt();
//         }
//     }

//     fn byte_encode<const BYTE_SIZE: usize>(&self, bytes: &mut [u8; BYTE_SIZE]) {
//         for (p, buf) in self
//             .vec
//             .iter()
//             .zip(bytes.chunks_exact_mut(Poly::ENCODED_BYTES))
//         {
//             p.byte_encode(buf.try_into().unwrap());
//         }
//     }

//     #[inline]
//     fn from_bytes(bytes: &[u8; K * Poly::ENCODED_BYTES]) -> Self {
//         let mut vec = [const { Poly::zero() }; K];

//         for (v, b) in vec.iter_mut().zip(bytes.chunks_exact(Poly::ENCODED_BYTES)) {
//             *v = Poly::byte_decode(unsafe { b.try_into().unwrap_unchecked() });
//         }

//         Self { vec }
//     }

//     fn compress(&self, bytes: &mut [u8; Self::COMPRESSED_BYTES]) {
//         for (p, b) in self
//             .vec
//             .iter()
//             .zip(bytes.chunks_exact_mut(Self::COMPRESSED_POLY_BYTES))
//         {
//             for (b, a) in b.chunks_exact_mut(5).zip(p.f.chunks_exact(4)) {
//                 let t: [u16; 4] = array::from_fn(|i| compr_10bit(a[i]));

//                 b[0] = t[0] as u8;
//                 b[1] = ((t[0] >> 8) | (t[1] << 2)) as u8;
//                 b[2] = ((t[1] >> 6) | (t[2] << 4)) as u8;
//                 b[3] = ((t[2] >> 4) | (t[3] << 6)) as u8;
//                 b[4] = (t[3] >> 2) as u8;
//             }
//         }
//     }

//     #[inline]
//     fn decompress(bytes: &[u8; Self::COMPRESSED_BYTES]) -> Self {
//         let mut pvec = PolyVec::zero();
//         for (p, b) in pvec
//             .vec
//             .iter_mut()
//             .zip(bytes.chunks_exact(Self::COMPRESSED_POLY_BYTES))
//         {
//             for (a, b) in p.f.chunks_exact_mut(4).zip(b.chunks_exact(5)) {
//                 let mut t: [u16; 5] = array::from_fn(|i| b[i] as u16);
//                 t[0] |= t[1] << 8;
//                 t[1] = t[1] >> 2 | t[2] << 6;
//                 t[2] = t[2] >> 4 | t[3] << 4;
//                 t[3] = t[3] >> 6 | (t[4] << 2);

//                 for (a, n) in a.iter_mut().zip(&t[..4]) {
//                     *a = decompr_10bit(n & 0x3FF);
//                 }
//             }
//         }

//         pvec
//     }

//     #[inline]
//     fn generate_eta1<I>(r: &[u8; 32], nonce: &mut I) -> Self
//     where
//         I: Iterator<Item = usize>,
//     {
//         let mut pvec = PolyVec::zero();

//         for (poly, nonce) in pvec.vec.iter_mut().zip(nonce) {
//             let prf = hash::prf(r, nonce);

//             poly.sample_poly_cbd2(prf);
//         }

//         pvec
//     }

//     #[inline]
//     fn generate_eta2<I>(r: &[u8; 32], nonce: &mut I) -> Self
//     where
//         I: Iterator<Item = usize>,
//     {
//         let mut pvec = PolyVec::zero();

//         for (poly, nonce) in pvec.vec.iter_mut().zip(nonce) {
//             let prf = hash::prf(r, nonce);

//             poly.sample_poly_cbd2(prf);
//         }

//         pvec
//     }
// }

// impl Mul<&PolyVec> for &PolyMatrix {
//     type Output = PolyVec;

//     #[inline]
//     fn mul(self, rhs: &PolyVec) -> Self::Output {
//         let mut out = PolyVec::zero();

//         for (poly, rowvec) in out.vec.iter_mut().zip(&self.m) {
//             poly.multiply_acc(rowvec, rhs);
//         }

//         out
//     }
// }

#[cfg(test)]
mod tests {
    use super::*;
}
