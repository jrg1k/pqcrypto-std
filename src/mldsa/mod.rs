//! Implementation of ML-DSA (FIPS-204).

use core::{
    array,
    mem::{transmute, transmute_copy, MaybeUninit},
    ops::{AddAssign, Mul, MulAssign, SubAssign},
};
use rand_core::CryptoRngCore;
use zeroize::Zeroize;

use crate::hash;

mod coeff;
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

trait SignerInternal {
    fn sign_internal(&self, dst: &mut [u8], m: &[u8], rnd: &[u8; 32]);
}

#[derive(Debug)]
pub enum VerifyError {
    ZoutOfBound,
    Mismatch,
    TooManyHints,
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            VerifyError::ZoutOfBound => f.write_str("z is out of bound"),
            VerifyError::Mismatch => f.write_str("signature mismatch"),
            VerifyError::TooManyHints => f.write_str("too many hints in signature"),
        }
    }
}

impl core::error::Error for VerifyError {}

trait VerifierInternal<
    const K: usize,
    const L: usize,
    const CT_BYTES: usize,
    const Z_BYTES: usize,
    const H_BYTES: usize,
    const W1_BYTES: usize,
    const SIG_SIZE: usize,
>
{
    const OMEGA: usize;
    const TAU: usize;
    const GAMMA1: usize;
    const GAMMA2: usize;
    const BETA: usize;

    fn bitunpack_z_hat(b: &[u8; Z_BYTES]) -> PolyVec<L>;

    fn w1encode(w1: &PolyVec<K>) -> [u8; W1_BYTES];

    fn use_hint(w1: &mut PolyVec<K>, h: &PolyVec<K>);

    fn pk(&self) -> &PublicKey<K, L>;

    fn verify_internal(&self, m: &[u8], sig: &[u8; SIG_SIZE]) -> Result<(), VerifyError> {
        let (c_tilde, sig) = sig.split_first_chunk::<CT_BYTES>().unwrap();
        let (z_bytes, sig) = sig.split_first_chunk::<Z_BYTES>().unwrap();
        let h_bytes: &[u8; H_BYTES] = sig.try_into().unwrap();

        let hint: PolyVec<K> = PolyVec::hint_bitunpack(h_bytes, Self::OMEGA)?;

        let mut z_hat = Self::bitunpack_z_hat(z_bytes);

        if !z_hat.norm_in_bound(Self::GAMMA1 - Self::BETA) {
            return Err(VerifyError::ZoutOfBound);
        }

        let pk = self.pk();

        let mut h = hash::Shake256::init();

        h.absorb_multi(&[&pk.tr, m]);
        let mu: [u8; 64] = h.squeeze_array();
        h.reset();

        let mut c_hat = Poly::zero();
        h.absorb(c_tilde);
        h.finalize();
        c_hat.sample_in_ball(&mut h, Self::TAU);
        h.reset();

        z_hat.ntt_inplace();

        let mut w1 = PolyVec::zero();
        w1.multiply_matvec_ntt(&pk.a_hat, &z_hat);

        c_hat.ntt_inplace();

        let mut t1 = pk.t1.shifted_left(D);
        t1.ntt_inplace();
        t1 *= &c_hat;

        w1 -= &t1;
        w1.reduce_invntt_tomont_inplace();
        Self::use_hint(&mut w1, &hint);

        let w1_bytes = Self::w1encode(&w1);

        h.absorb_multi(&[&mu, &w1_bytes]);
        let c_tilde_prime = h.squeeze_array();

        if c_tilde == &c_tilde_prime {
            Ok(())
        } else {
            Err(VerifyError::Mismatch)
        }
    }
}

pub trait Verifier<
    const K: usize,
    const L: usize,
    const CT_BYTES: usize,
    const Z_BYTES: usize,
    const H_BYTES: usize,
    const W1_BYTES: usize,
    const SIG_SIZE: usize,
>
{
    fn verify(&self, m: impl AsRef<[u8]>, sig: &[u8; SIG_SIZE]) -> Result<(), VerifyError>;
}

impl<
        T,
        const K: usize,
        const L: usize,
        const CT_BYTES: usize,
        const Z_BYTES: usize,
        const H_BYTES: usize,
        const W1_BYTES: usize,
        const SIG_SIZE: usize,
    > Verifier<K, L, CT_BYTES, Z_BYTES, H_BYTES, W1_BYTES, SIG_SIZE> for T
where
    T: VerifierInternal<K, L, CT_BYTES, Z_BYTES, H_BYTES, W1_BYTES, SIG_SIZE>,
{
    fn verify(&self, m: impl AsRef<[u8]>, sig: &[u8; SIG_SIZE]) -> Result<(), VerifyError> {
        self.verify_internal(m.as_ref(), sig)
    }
}

/// Signatory in ML-DSA.
pub trait Signer {
    /// Sign message `m` using randomness from `rng`.
    fn sign(&self, sig: &mut [u8], rng: &mut impl CryptoRngCore, m: impl AsRef<[u8]>);
}

impl<T: SignerInternal> Signer for T {
    #[inline]
    fn sign(&self, sig: &mut [u8], rng: &mut impl CryptoRngCore, m: impl AsRef<[u8]>) {
        let mut rnd = [0u8; 32];
        rng.fill_bytes(&mut rnd);

        self.sign_internal(sig, m.as_ref(), &rnd)
    }
}

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

const fn bitlen(n: usize) -> usize {
    n.ilog2() as usize + 1
}

const fn sig_size(k: usize, l: usize, lambda: usize, gamma1: usize, omega: usize) -> usize {
    lambda / 4 + l * 32 * (1 + bitlen(gamma1 - 1)) + omega + k
}

pub mod mldsa44 {
    //! ML-DSA-44 parameter set.
    use core::mem::{transmute, MaybeUninit};

    use crate::hash;

    use super::{
        bitlen, coeff, sig_size, sk_size, vk_size, Poly, PolyVec, SignerInternal, VerifierInternal,
        Q,
    };

    const K: usize = 4;
    const L: usize = 4;
    const ETA: usize = 2;
    const GAMMA1: usize = 1 << 17;
    const GAMMA2: usize = (Q as usize - 1) / 88;
    const LAMBDA: usize = 128;
    const TAU: usize = 39;
    const BETA: usize = TAU * ETA;
    const OMEGA: usize = 80;

    const CT_BYTES: usize = LAMBDA / 4;
    const Z_BYTES: usize = L * 32 * (1 + bitlen(GAMMA1 - 1));
    const H_BYTES: usize = OMEGA + K;
    const W1_BYTES: usize = K * 32 * bitlen((Q as usize - 1) / (2 * GAMMA2) - 1);

    /// Public key bytesize.
    pub const PUBKEY_SIZE: usize = vk_size(K);

    /// Private key bytesize.
    pub const PRIVKEY_SIZE: usize = sk_size(K, L, ETA);

    /// Signature bytesize.
    pub const SIG_SIZE: usize = sig_size(K, L, LAMBDA, GAMMA1, OMEGA);

    /// Private key used for signing.
    pub type PrivateKey = super::PrivateKey<K, L, ETA>;

    /// Public Key used for verifying.
    pub type PublicKey = super::PublicKey<K, L>;

    impl SignerInternal for PrivateKey {
        fn sign_internal(&self, dst: &mut [u8], m: &[u8], rnd: &[u8; 32]) {
            let (c_tilde, buf) = dst.split_first_chunk_mut::<CT_BYTES>().unwrap();
            let (w1_bytes, buf) = buf.split_first_chunk_mut::<W1_BYTES>().unwrap();
            let (mu, buf) = buf.split_first_chunk_mut::<64>().unwrap();
            let rho_prime2: &mut [u8; 64] = buf.first_chunk_mut().unwrap();

            let mut h = hash::Shake256::init();

            h.absorb_and_squeeze(mu, &[&self.tr, m]);

            h.absorb_and_squeeze(rho_prime2, &[&self.k, rnd, mu]);

            let mut y = PolyVec::zero();
            let mut y_hat = PolyVec::zero();
            let mut w = PolyVec::zero();
            let mut w1 = PolyVec::zero();
            let mut w0 = PolyVec::zero();
            let mut z = PolyVec::zero();
            let mut hint = PolyVec::zero();
            let mut c_hat = Poly::zero();

            for nonce in (0..).step_by(L) {
                y.expand_mask_2pow17(rho_prime2, nonce, &mut h);

                y_hat.ntt(&y);

                w.multiply_matvec_ntt(&self.a_hat, &y_hat);
                w.reduce_invntt_tomont_inplace();

                w.decompose_88(&mut w0, &mut w1);
                w1.pack_simple_6bit(w1_bytes);
                h.absorb_and_squeeze(c_tilde, &[mu, w1_bytes]);

                h.absorb(c_tilde);
                h.finalize();
                c_hat.f.fill(0);
                c_hat.sample_in_ball(&mut h, TAU);
                h.reset();
                c_hat.ntt_inplace();

                z.multiply_poly_ntt(&c_hat, &self.s1_hat);
                z.invntt_tomont_inplace();
                z += &y;
                z.reduce();

                if !z.norm_in_bound(GAMMA1 - BETA) {
                    continue;
                }

                hint.multiply_poly_ntt(&c_hat, &self.s2_hat);
                hint.invntt_tomont_inplace();
                w0 -= &hint;
                w0.reduce();

                if !w0.norm_in_bound(GAMMA2 - BETA) {
                    continue;
                }

                hint.multiply_poly_ntt(&c_hat, &self.t0_hat);
                hint.invntt_tomont_inplace();
                hint.reduce();

                if !hint.norm_in_bound(GAMMA2) {
                    continue;
                }

                w0 += &hint;

                let count = hint.make_hint::<{ GAMMA2 as i32 }>(&w0, &w1);

                if count >= OMEGA {
                    continue;
                }

                break;
            }

            z.bitpack_2pow17(&mut dst[CT_BYTES..]);

            hint.hint_bitpack::<OMEGA>(&mut dst[CT_BYTES + Z_BYTES..]);
        }
    }

    impl VerifierInternal<K, L, CT_BYTES, Z_BYTES, H_BYTES, W1_BYTES, SIG_SIZE> for PublicKey {
        const OMEGA: usize = OMEGA;

        const TAU: usize = TAU;

        const GAMMA1: usize = GAMMA1;

        const GAMMA2: usize = GAMMA2;

        const BETA: usize = BETA;

        fn bitunpack_z_hat(b: &[u8; Z_BYTES]) -> PolyVec<L> {
            let mut pvec = PolyVec::zero();

            for (poly, bytes) in pvec
                .v
                .iter_mut()
                .zip(b.chunks_exact(Poly::packed_bytesize(18)))
            {
                poly.bitunpack_2pow17(bytes.try_into().unwrap());
            }

            pvec
        }

        fn w1encode(w1: &PolyVec<K>) -> [u8; W1_BYTES] {
            let mut bytes = [const { MaybeUninit::uninit() }; W1_BYTES];
            for (chunk, p) in bytes
                .chunks_exact_mut(Poly::packed_bytesize(6))
                .zip(w1.v.iter())
            {
                p.pack_simple_uninit_6bit(chunk.try_into().unwrap());
            }

            unsafe { transmute(bytes) }
        }

        fn use_hint(w1: &mut PolyVec<K>, h: &PolyVec<K>) {
            for (i, poly) in w1.v.iter_mut().enumerate() {
                for (j, a) in poly.f.iter_mut().enumerate() {
                    *a = coeff::use_hint_88(h.v[i].f[j] as usize, *a);
                }
            }
        }

        fn pk(&self) -> &super::PublicKey<K, L> {
            self
        }
    }
}

pub mod mldsa65 {
    //! ML-DSA-65 parameter set.
    use core::mem::{transmute, MaybeUninit};

    use crate::hash;

    use super::{
        bitlen, coeff, sig_size, sk_size, vk_size, Poly, PolyVec, SignerInternal, VerifierInternal,
        Q,
    };

    const K: usize = 6;
    const L: usize = 5;
    const ETA: usize = 4;
    const GAMMA1: usize = 1 << 19;
    const GAMMA2: usize = (Q as usize - 1) / 32;
    const LAMBDA: usize = 192;
    const TAU: usize = 49;
    const BETA: usize = TAU * ETA;
    const OMEGA: usize = 55;

    const CT_BYTES: usize = LAMBDA / 4;
    const Z_BYTES: usize = L * 32 * (1 + bitlen(GAMMA1 - 1));
    const H_BYTES: usize = OMEGA + K;
    const W1_BYTES: usize = K * 32 * bitlen((Q as usize - 1) / (2 * GAMMA2) - 1);

    /// Public key bytesize.
    pub const PUBKEY_SIZE: usize = vk_size(K);

    /// Private key bytesize.
    pub const PRIVKEY_SIZE: usize = sk_size(K, L, ETA);

    /// Signature bytesize.
    pub const SIG_SIZE: usize = sig_size(K, L, LAMBDA, GAMMA1, OMEGA);

    /// Private key used for signing.
    pub type PrivateKey = super::PrivateKey<K, L, ETA>;

    /// Public Key used for verifying.
    pub type PublicKey = super::PublicKey<K, L>;

    impl SignerInternal for PrivateKey {
        fn sign_internal(&self, dst: &mut [u8], m: &[u8], rnd: &[u8; 32]) {
            let (c_tilde, buf) = dst.split_first_chunk_mut::<CT_BYTES>().unwrap();
            let (w1_bytes, buf) = buf.split_first_chunk_mut::<W1_BYTES>().unwrap();
            let (mu, buf) = buf.split_first_chunk_mut::<64>().unwrap();
            let rho_prime2: &mut [u8; 64] = buf.first_chunk_mut().unwrap();

            let mut h = hash::Shake256::init();

            h.absorb_and_squeeze(mu, &[&self.tr, m]);

            h.absorb_and_squeeze(rho_prime2, &[&self.k, rnd, mu]);

            let mut y = PolyVec::zero();
            let mut y_hat = PolyVec::zero();
            let mut w = PolyVec::zero();
            let mut w1 = PolyVec::zero();
            let mut w0 = PolyVec::zero();
            let mut z = PolyVec::zero();
            let mut hint = PolyVec::zero();
            let mut c_hat = Poly::zero();

            for nonce in (0..).step_by(L) {
                y.expand_mask_2pow19(rho_prime2, nonce, &mut h);

                y_hat.ntt(&y);

                w.multiply_matvec_ntt(&self.a_hat, &y_hat);
                w.reduce_invntt_tomont_inplace();

                w.decompose_32(&mut w0, &mut w1);
                w1.pack_simple_4bit(w1_bytes);
                h.absorb_and_squeeze(c_tilde, &[mu, w1_bytes]);

                h.absorb(c_tilde);
                h.finalize();
                c_hat.f.fill(0);
                c_hat.sample_in_ball(&mut h, TAU);
                h.reset();
                c_hat.ntt_inplace();

                z.multiply_poly_ntt(&c_hat, &self.s1_hat);
                z.invntt_tomont_inplace();
                z += &y;
                z.reduce();

                if !z.norm_in_bound(GAMMA1 - BETA) {
                    continue;
                }

                hint.multiply_poly_ntt(&c_hat, &self.s2_hat);
                hint.invntt_tomont_inplace();
                w0 -= &hint;
                w0.reduce();

                if !w0.norm_in_bound(GAMMA2 - BETA) {
                    continue;
                }

                hint.multiply_poly_ntt(&c_hat, &self.t0_hat);
                hint.invntt_tomont_inplace();
                hint.reduce();

                if !hint.norm_in_bound(GAMMA2) {
                    continue;
                }

                w0 += &hint;

                let count = hint.make_hint::<{ GAMMA2 as i32 }>(&w0, &w1);

                if count >= OMEGA {
                    continue;
                }

                break;
            }

            z.bitpack_2pow19(&mut dst[CT_BYTES..]);

            hint.hint_bitpack::<OMEGA>(&mut dst[CT_BYTES + Z_BYTES..]);
        }
    }

    impl VerifierInternal<K, L, CT_BYTES, Z_BYTES, H_BYTES, W1_BYTES, SIG_SIZE> for PublicKey {
        const OMEGA: usize = OMEGA;

        const TAU: usize = TAU;

        const GAMMA1: usize = GAMMA1;

        const GAMMA2: usize = GAMMA2;

        const BETA: usize = BETA;

        fn bitunpack_z_hat(b: &[u8; Z_BYTES]) -> PolyVec<L> {
            let mut pvec = PolyVec::zero();

            for (poly, bytes) in pvec
                .v
                .iter_mut()
                .zip(b.chunks_exact(Poly::packed_bytesize(20)))
            {
                poly.bitunpack_2pow19(bytes.try_into().unwrap());
            }

            pvec
        }

        fn w1encode(w1: &PolyVec<K>) -> [u8; W1_BYTES] {
            let mut bytes = [const { MaybeUninit::uninit() }; W1_BYTES];
            for (chunk, p) in bytes
                .chunks_exact_mut(Poly::packed_bytesize(4))
                .zip(w1.v.iter())
            {
                p.pack_simple_uninit_4bit(chunk.try_into().unwrap());
            }

            unsafe { transmute(bytes) }
        }

        fn use_hint(w1: &mut PolyVec<K>, h: &PolyVec<K>) {
            for (i, poly) in w1.v.iter_mut().enumerate() {
                for (j, a) in poly.f.iter_mut().enumerate() {
                    *a = coeff::use_hint_32(h.v[i].f[j] as usize, *a);
                }
            }
        }

        fn pk(&self) -> &PublicKey {
            self
        }
    }
}

pub mod mldsa87 {
    //! ML-DSA-87 parameter set.

    use core::mem::{transmute, MaybeUninit};

    use crate::hash;

    use super::{
        bitlen, coeff, sig_size, sk_size, vk_size, Poly, PolyVec, SignerInternal, VerifierInternal,
        Q,
    };

    const K: usize = 8;
    const L: usize = 7;
    const ETA: usize = 2;
    const GAMMA1: usize = 1 << 19;
    const GAMMA2: usize = (Q as usize - 1) / 32;
    const LAMBDA: usize = 256;
    const TAU: usize = 60;
    const BETA: usize = TAU * ETA;
    const OMEGA: usize = 75;

    const CT_BYTES: usize = LAMBDA / 4;
    const Z_BYTES: usize = L * 32 * (1 + bitlen(GAMMA1 - 1));
    const H_BYTES: usize = OMEGA + K;
    const W1_BYTES: usize = K * 32 * bitlen((Q as usize - 1) / (2 * GAMMA2) - 1);

    /// Public key bytesize.
    pub const PUBKEY_SIZE: usize = vk_size(K);

    /// Private key bytesize.
    pub const PRIVKEY_SIZE: usize = sk_size(K, L, ETA);

    /// Signature bytesize.
    pub const SIG_SIZE: usize = sig_size(K, L, LAMBDA, GAMMA1, OMEGA);

    /// Private key used for signing.
    pub type PrivateKey = super::PrivateKey<K, L, ETA>;

    /// Public Key used for verifying.
    pub type PublicKey = super::PublicKey<K, L>;

    impl SignerInternal for PrivateKey {
        fn sign_internal(&self, dst: &mut [u8], m: &[u8], rnd: &[u8; 32]) {
            let (c_tilde, buf) = dst.split_first_chunk_mut::<CT_BYTES>().unwrap();
            let (w1_bytes, buf) = buf.split_first_chunk_mut::<W1_BYTES>().unwrap();
            let (mu, buf) = buf.split_first_chunk_mut::<64>().unwrap();
            let rho_prime2: &mut [u8; 64] = buf.first_chunk_mut().unwrap();

            let mut h = hash::Shake256::init();

            h.absorb_and_squeeze(mu, &[&self.tr, m]);

            h.absorb_and_squeeze(rho_prime2, &[&self.k, rnd, mu]);

            let mut y = PolyVec::zero();
            let mut y_hat = PolyVec::zero();
            let mut w = PolyVec::zero();
            let mut w1 = PolyVec::zero();
            let mut w0 = PolyVec::zero();
            let mut z = PolyVec::zero();
            let mut hint = PolyVec::zero();
            let mut c_hat = Poly::zero();

            for nonce in (0..).step_by(L) {
                y.expand_mask_2pow19(rho_prime2, nonce, &mut h);

                y_hat.ntt(&y);

                w.multiply_matvec_ntt(&self.a_hat, &y_hat);
                w.reduce_invntt_tomont_inplace();

                w.decompose_32(&mut w0, &mut w1);
                w1.pack_simple_4bit(w1_bytes);
                h.absorb_and_squeeze(c_tilde, &[mu, w1_bytes]);

                h.absorb(c_tilde);
                h.finalize();
                c_hat.f.fill(0);
                c_hat.sample_in_ball(&mut h, TAU);
                h.reset();
                c_hat.ntt_inplace();

                z.multiply_poly_ntt(&c_hat, &self.s1_hat);
                z.invntt_tomont_inplace();
                z += &y;
                z.reduce();

                if !z.norm_in_bound(GAMMA1 - BETA) {
                    continue;
                }

                hint.multiply_poly_ntt(&c_hat, &self.s2_hat);
                hint.invntt_tomont_inplace();
                w0 -= &hint;
                w0.reduce();

                if !w0.norm_in_bound(GAMMA2 - BETA) {
                    continue;
                }

                hint.multiply_poly_ntt(&c_hat, &self.t0_hat);
                hint.invntt_tomont_inplace();
                hint.reduce();

                if !hint.norm_in_bound(GAMMA2) {
                    continue;
                }

                w0 += &hint;

                let count = hint.make_hint::<{ GAMMA2 as i32 }>(&w0, &w1);

                if count >= OMEGA {
                    continue;
                }

                break;
            }

            z.bitpack_2pow19(&mut dst[CT_BYTES..]);

            hint.hint_bitpack::<OMEGA>(&mut dst[CT_BYTES + Z_BYTES..]);
        }
    }

    impl VerifierInternal<K, L, CT_BYTES, Z_BYTES, H_BYTES, W1_BYTES, SIG_SIZE> for PublicKey {
        const OMEGA: usize = OMEGA;

        const TAU: usize = TAU;

        const GAMMA1: usize = GAMMA1;

        const GAMMA2: usize = GAMMA2;

        const BETA: usize = BETA;

        fn bitunpack_z_hat(b: &[u8; Z_BYTES]) -> PolyVec<L> {
            let mut pvec = PolyVec::zero();

            for (poly, bytes) in pvec
                .v
                .iter_mut()
                .zip(b.chunks_exact(Poly::packed_bytesize(20)))
            {
                poly.bitunpack_2pow19(bytes.try_into().unwrap());
            }

            pvec
        }

        fn w1encode(w1: &PolyVec<K>) -> [u8; W1_BYTES] {
            let mut bytes = [const { MaybeUninit::uninit() }; W1_BYTES];
            for (chunk, p) in bytes
                .chunks_exact_mut(Poly::packed_bytesize(4))
                .zip(w1.v.iter())
            {
                p.pack_simple_uninit_4bit(chunk.try_into().unwrap());
            }

            unsafe { transmute(bytes) }
        }

        fn use_hint(w1: &mut PolyVec<K>, h: &PolyVec<K>) {
            for (i, poly) in w1.v.iter_mut().enumerate() {
                for (j, a) in poly.f.iter_mut().enumerate() {
                    *a = coeff::use_hint_32(h.v[i].f[j] as usize, *a);
                }
            }
        }

        fn pk(&self) -> &PublicKey {
            self
        }
    }
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

/// Public key used for verifying.
pub struct PublicKey<const K: usize, const L: usize> {
    rho: [u8; 32],
    tr: [u8; 64],
    t1: PolyVec<K>,
    a_hat: PolyMat<K, L>,
}

impl<const K: usize, const L: usize> PublicKey<K, L> {
    /// Encode public key as bytes.
    pub fn encode(&self, dst: &mut [u8]) {
        vk_encode(dst, &self.rho, &self.t1)
    }

    /// Decode public key from bytes.
    pub fn decode(pk: &[u8]) -> Self {
        let rho = array::from_fn(|i| pk[i]);
        let mut t1 = PolyVec::zero();

        for (xi, z) in
            t1.v.iter_mut()
                .zip(pk[32..].chunks_exact(Poly::PACKED_10BIT))
        {
            xi.unpack_simple_10bit(z.try_into().unwrap())
        }

        let a_hat = PolyMat::expand_a(&rho);

        let mut h = hash::Shake256::init();
        h.absorb(pk);
        h.finalize();
        let tr = h.squeeze_array();

        Self { rho, tr, t1, a_hat }
    }
}

/// Private key used for signing.
pub struct PrivateKey<const K: usize, const L: usize, const ETA: usize> {
    rho: [u8; 32],
    k: [u8; 32],
    tr: [u8; 64],
    s1_hat: PolyVec<L>,
    s2_hat: PolyVec<K>,
    t0_hat: PolyVec<K>,
    a_hat: PolyMat<K, L>,
}

impl<const K: usize, const L: usize, const ETA: usize> Drop for PrivateKey<K, L, ETA> {
    fn drop(&mut self) {
        self.k.zeroize();
        self.tr.zeroize();
    }
}

impl<const K: usize, const L: usize, const ETA: usize> PrivateKey<K, L, ETA> {
    /// Private key generation.
    #[inline]
    pub fn keygen<const VK_SIZE: usize>(
        vk: &mut [u8; VK_SIZE],
        rng: &mut impl CryptoRngCore,
    ) -> Self {
        debug_assert!(vk.len() >= vk_size(K));

        let mut ksi = [0u8; 32];
        rng.fill_bytes(&mut ksi);

        let sk = Self::keygen_internal(vk, &ksi);

        ksi.zeroize();

        sk
    }

    fn keygen_internal<const PUBKEY_SIZE: usize>(
        vk: &mut [u8; PUBKEY_SIZE],
        ksi: &[u8; 32],
    ) -> Self {
        let mut h = hash::Shake256::init();
        h.absorb_multi(&[ksi, &[K as u8], &[L as u8]]);
        let rho: [u8; 32] = h.squeeze_array();
        let rho_prime: [u8; 64] = h.squeeze_array();
        let k: [u8; 32] = h.squeeze_array();

        let mut s1_hat = PolyVec::zero();
        let mut s2_hat = PolyVec::zero();
        let mut t0_hat = PolyVec::zero();
        let a_hat = PolyMat::expand_a(&rho);

        expand_s::<K, L, ETA>(&mut s1_hat, &mut s2_hat, &rho_prime);

        s1_hat.ntt_inplace();

        let mut t = PolyVec::zero();
        let mut t1 = PolyVec::zero();

        t.multiply_matvec_ntt(&a_hat, &s1_hat);
        t.reduce_invntt_tomont_inplace();

        t += &s2_hat;

        t.power2round(&mut t1, &mut t0_hat);

        vk_encode(vk, &rho, &t1);

        h.reset();
        h.absorb(vk);
        h.finalize();
        let tr: [u8; 64] = h.squeeze_array();

        s2_hat.ntt_inplace();
        t0_hat.ntt_inplace();

        Self {
            rho,
            k,
            tr,
            s1_hat,
            s2_hat,
            t0_hat,
            a_hat,
        }
    }

    /// Encode private key to bytes.
    #[inline]
    pub fn encode(&self, dst: &mut [u8]) {
        let s1 = self.s1_hat.invntt();
        let s2 = self.s2_hat.invntt();
        let t0 = self.t0_hat.invntt();

        dst[..32].copy_from_slice(&self.rho);
        dst[32..64].copy_from_slice(&self.k);
        dst[64..128].copy_from_slice(&self.tr);

        let buf = &mut dst[128..];

        match ETA {
            2 => {
                s1.pack_eta2(&mut buf[..L * Poly::PACKED_3BIT]);

                let buf = &mut buf[L * Poly::PACKED_3BIT..];
                s2.pack_eta2(&mut buf[..K * Poly::PACKED_3BIT]);

                let buf = &mut buf[K * Poly::PACKED_3BIT..];
                t0.pack_eta_2powdm1(buf)
            }
            4 => {
                s1.pack_eta4(&mut buf[..L * Poly::PACKED_4BIT]);

                let buf = &mut buf[L * Poly::PACKED_4BIT..];
                s2.pack_eta4(buf);

                let buf = &mut buf[K * Poly::PACKED_4BIT..];
                t0.pack_eta_2powdm1(buf)
            }
            _ => unreachable!(),
        }
    }

    /// Decode private key from bytes.
    #[inline]
    pub fn decode(src: &[u8]) -> Self {
        let mut rho: MaybeUninit<[u8; 32]> = MaybeUninit::uninit();
        let mut k: MaybeUninit<[u8; 32]> = MaybeUninit::uninit();
        let mut tr: MaybeUninit<[u8; 64]> = MaybeUninit::uninit();

        rho.write(src[..32].try_into().unwrap());
        k.write(src[32..64].try_into().unwrap());
        tr.write(src[64..128].try_into().unwrap());

        let (rho, k, tr) = unsafe { (rho.assume_init(), k.assume_init(), tr.assume_init()) };

        let mut s1_hat = PolyVec::zero();
        let mut s2_hat = PolyVec::zero();
        let mut t0_hat = PolyVec::zero();

        match ETA {
            2 => {
                let z = &src[128..];
                s1_hat.unpack_eta2(&z[..L * Poly::PACKED_3BIT]);

                let z = &z[L * Poly::PACKED_3BIT..];
                s2_hat.unpack_eta2(&z[..K * Poly::PACKED_3BIT]);

                let z = &z[K * Poly::PACKED_3BIT..];
                t0_hat.unpack_eta_2powdm1(z)
            }
            4 => {
                let z = &src[128..];
                s1_hat.unpack_eta4(&z[..L * Poly::PACKED_4BIT]);

                let z = &z[L * Poly::PACKED_4BIT..];
                s2_hat.unpack_eta4(&z[..K * Poly::PACKED_4BIT]);

                let z = &z[K * Poly::PACKED_4BIT..];
                t0_hat.unpack_eta_2powdm1(z)
            }
            _ => unreachable!(),
        }

        let a_hat = PolyMat::expand_a(&rho);

        s1_hat.ntt_inplace();
        s2_hat.ntt_inplace();
        t0_hat.ntt_inplace();

        Self {
            rho,
            k,
            tr,
            s1_hat,
            s2_hat,
            t0_hat,
            a_hat,
        }
    }
}

#[repr(transparent)]
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
    fn invntt(&self) -> Self {
        let mut w_hat = self.f;

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

        Self { f: w_hat }
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
    fn rej_ntt(g: &mut hash::Shake128) -> Self {
        let mut f: [MaybeUninit<i32>; N] = [MaybeUninit::uninit(); N];
        let mut idx = 0;

        while idx < N {
            let bytes = g.squeezeblock();

            for b in bytes.chunks_exact(3) {
                if let Some(a) = coeff::from_three_bytes(b[0], b[1], b[2]) {
                    f[idx].write(a);
                    idx += 1;
                }

                if idx == N {
                    break;
                }
            }
        }

        Self {
            f: unsafe { transmute::<[MaybeUninit<i32>; N], [i32; N]>(f) },
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

    /// SampleInBall(rho)
    fn sample_in_ball(&mut self, h: &mut hash::Shake256, tau: usize) {
        let mut block = h.squeezeblock();

        let mut hash = u64::from_le_bytes(block[..8].try_into().unwrap());

        let mut iter = block[8..].iter();

        let mut i = N - tau;

        while i < N {
            let j = if let Some(j) = iter.by_ref().find(|b| (**b as usize) <= i) {
                *j as usize
            } else {
                block = h.squeezeblock();
                iter = block.iter();
                continue;
            };

            self.f[i] = self.f[j];
            self.f[j] = 1 - ((hash & 1) << 1) as i32;

            hash >>= 1;
            i += 1;
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

    fn decompose_32(&self, p0: &mut Self, p1: &mut Self) {
        for i in 0..N {
            let (r1, r0) = coeff::decompose_32(self.f[i]);
            p0.f[i] = r0;
            p1.f[i] = r1;
        }
    }

    fn decompose_88(&self, p0: &mut Self, p1: &mut Self) {
        for i in 0..N {
            let (r1, r0) = coeff::decompose_88(self.f[i]);
            p0.f[i] = r0;
            p1.f[i] = r1;
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

    fn pack_simple_uninit_4bit(&self, z: &mut [MaybeUninit<u8>; Self::packed_bytesize(4)]) {
        for (b, a) in z.iter_mut().zip(self.f.chunks_exact(2)) {
            b.write((a[0] | a[1] << 4) as u8);
        }
    }

    fn pack_simple_6bit(&self, z: &mut [u8; Self::packed_bytesize(6)]) {
        for (b, a) in z.chunks_exact_mut(3).zip(self.f.chunks_exact(4)) {
            b[0] = ((a[0] >> 0) | (a[1] << 6)) as u8;
            b[1] = ((a[1] >> 2) | (a[2] << 4)) as u8;
            b[2] = ((a[2] >> 4) | (a[3] << 2)) as u8;
        }
    }

    fn pack_simple_uninit_6bit(&self, z: &mut [MaybeUninit<u8>; Self::packed_bytesize(6)]) {
        for (b, a) in z.chunks_exact_mut(3).zip(self.f.chunks_exact(4)) {
            b[0].write(((a[0] >> 0) | (a[1] << 6)) as u8);
            b[1].write(((a[1] >> 2) | (a[2] << 4)) as u8);
            b[2].write(((a[2] >> 4) | (a[3] << 2)) as u8);
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

    fn bitpack_2pow17(&self, z: &mut [u8; Self::packed_bytesize(18)]) {
        const B: i32 = 1 << 17;

        for (b, a) in z.chunks_exact_mut(9).zip(self.f.chunks_exact(4)) {
            let a0 = B - a[0];
            let a1 = B - a[1];
            let a2 = B - a[2];
            let a3 = B - a[3];

            b[0] = (a0 >> 0) as u8;
            b[1] = (a0 >> 8) as u8;
            b[2] = ((a0 >> 16) | (a1 << 2)) as u8;
            b[3] = (a1 >> 6) as u8;
            b[4] = ((a1 >> 14) | (a2 << 4)) as u8;
            b[5] = (a2 >> 4) as u8;
            b[6] = ((a2 >> 12) | (a3 << 6)) as u8;
            b[7] = (a3 >> 2) as u8;
            b[8] = (a3 >> 10) as u8;
        }
    }

    fn bitunpack_2pow17(&mut self, z: &[u8; Self::packed_bytesize(18)]) {
        const B: i32 = 1 << 17;
        const BITMASK: i32 = 0x3ffff;

        for (a, b) in self.f.chunks_exact_mut(4).zip(z.chunks_exact(9)) {
            let b: [i32; 9] = array::from_fn(|i| b[i] as i32);

            a[0] = B - (((b[0] >> 0) | (b[1] << 8) | (b[2] << 16)) & BITMASK);
            a[1] = B - (((b[2] >> 2) | (b[3] << 6) | (b[4] << 14)) & BITMASK);
            a[2] = B - (((b[4] >> 4) | (b[5] << 4) | (b[6] << 12)) & BITMASK);
            a[3] = B - ((b[6] >> 6) | (b[7] << 2) | (b[8] << 10));
        }
    }

    fn bitpack_2pow19(&self, z: &mut [u8; Self::packed_bytesize(20)]) {
        const B: i32 = 1 << 19;

        for (b, a) in z.chunks_exact_mut(5).zip(self.f.chunks_exact(2)) {
            let a0 = B - a[0];
            let a1 = B - a[1];

            b[0] = (a0 >> 0) as u8;
            b[1] = (a0 >> 8) as u8;
            b[2] = ((a0 >> 16) | (a1 << 4)) as u8;
            b[3] = (a1 >> 4) as u8;
            b[4] = (a1 >> 12) as u8;
        }
    }

    fn bitunpack_2pow19(&mut self, z: &[u8; Self::packed_bytesize(20)]) {
        const B: i32 = 1 << 19;
        const BITMASK: i32 = 0xfffff;

        for (a, b) in self.f.chunks_exact_mut(2).zip(z.chunks_exact(5)) {
            let b: [i32; 5] = array::from_fn(|i| b[i] as i32);

            a[0] = B - (((b[0] >> 0) | (b[1] << 8) | (b[2] << 16)) & BITMASK);
            a[1] = B - ((b[2] >> 4) | (b[3] << 4) | (b[4] << 12));
        }
    }

    const fn norm_in_bound(&self, bound: usize) -> bool {
        let mut i = 0;
        while i < N {
            if coeff::norm(self.f[i]) >= bound {
                return false;
            }

            i += 1;
        }

        true
    }

    fn make_hint<const G2: i32>(&mut self, p0: &Poly, p1: &Poly) -> usize {
        let mut sum = 0;

        for i in 0..N {
            let h = coeff::make_hint::<G2>(p0.f[i], p1.f[i]);

            self.f[i] = h as i32;
            sum += h;
        }

        sum
    }

    fn shifted_left(&self, d: usize) -> Self {
        let mut f = [MaybeUninit::uninit(); N];

        for (i, a) in f.iter_mut().enumerate() {
            a.write(self.f[i] << d);
        }

        Self {
            f: unsafe { transmute::<[MaybeUninit<i32>; N], [i32; N]>(f) },
        }
    }
}

impl AddAssign<&Self> for Poly {
    fn add_assign(&mut self, rhs: &Self) {
        for i in 0..N {
            self.f[i] += rhs.f[i];
        }
    }
}

impl SubAssign<&Self> for Poly {
    fn sub_assign(&mut self, rhs: &Self) {
        for i in 0..N {
            self.f[i] -= rhs.f[i];
        }
    }
}

impl MulAssign<&Self> for Poly {
    fn mul_assign(&mut self, rhs: &Self) {
        for (i, a) in self.f.iter_mut().enumerate() {
            *a = reduce::mont_mul(*a, rhs.f[i]);
        }
    }
}

#[repr(transparent)]
struct PolyMat<const K: usize, const L: usize> {
    m: [PolyVec<L>; K],
}

impl<const K: usize, const L: usize> PolyMat<K, L> {
    /// ExpandA(rho)
    fn expand_a(rho: &[u8; 32]) -> Self {
        let mut g = hash::Shake128::init();
        let mut m: [MaybeUninit<PolyVec<L>>; K] = [const { MaybeUninit::uninit() }; K];

        for (r, pvec) in m.iter_mut().enumerate() {
            let mut v: [MaybeUninit<Poly>; L] = [const { MaybeUninit::uninit() }; L];

            for (s, poly) in v.iter_mut().enumerate() {
                g.absorb_multi(&[rho, &u16::to_le_bytes(((r << 8) | s) as u16)]);

                poly.write(Poly::rej_ntt(&mut g));

                g.reset();
            }

            pvec.write(PolyVec {
                v: unsafe { transmute_copy(&v) },
            });
        }

        Self {
            m: unsafe { transmute_copy(&m) },
        }
    }
}

#[repr(transparent)]
struct PolyVec<const K: usize> {
    v: [Poly; K],
}

impl<const K: usize> PolyVec<K> {
    const fn zero() -> Self {
        Self {
            v: [const { Poly::zero() }; K],
        }
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

    fn invntt(&self) -> Self {
        let mut v = [const { MaybeUninit::uninit() }; K];

        for (i, p) in v.iter_mut().enumerate() {
            p.write(self.v[i].invntt());
        }

        Self {
            v: unsafe { transmute_copy(&v) },
        }
    }

    fn reduce(&mut self) {
        for p in self.v.iter_mut() {
            p.reduce();
        }
    }

    fn reduce_invntt_tomont_inplace(&mut self) {
        for p in self.v.iter_mut() {
            p.reduce();
            p.invntt_tomont_inplace();
        }
    }

    fn invntt_tomont_inplace(&mut self) {
        for p in self.v.iter_mut() {
            p.invntt_tomont_inplace();
        }
    }

    fn power2round(&self, t1: &mut PolyVec<K>, t0: &mut PolyVec<K>) {
        for i in 0..K {
            self.v[i].power2round(&mut t1.v[i], &mut t0.v[i]);
        }
    }

    fn decompose_32(&self, x0: &mut PolyVec<K>, x1: &mut PolyVec<K>) {
        for i in 0..K {
            self.v[i].decompose_32(&mut x0.v[i], &mut x1.v[i]);
        }
    }

    fn decompose_88(&self, x0: &mut PolyVec<K>, x1: &mut PolyVec<K>) {
        for i in 0..K {
            self.v[i].decompose_88(&mut x0.v[i], &mut x1.v[i]);
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

    fn pack_simple_6bit(&self, z: &mut [u8]) {
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

    fn multiply_poly_ntt(&mut self, p: &Poly, v: &PolyVec<K>) {
        for i in 0..K {
            self.v[i].multiply_ntt(p, &v.v[i]);
        }
    }

    fn hint_bitpack<const OMEGA: usize>(&self, dst: &mut [u8]) {
        let mut idx = 0;

        for i in 0..K {
            for j in 0..N {
                let h = self.v[i].f[j] as usize;
                dst[idx] = (j & h.wrapping_neg()) as u8;
                idx += h;
            }

            dst[OMEGA + i] = idx as u8;
        }
    }

    fn hint_bitunpack(y: &[u8], omega: usize) -> Result<PolyVec<K>, VerifyError> {
        let mut h = PolyVec::zero();

        let mut idx = 0;

        for i in 0..K {
            let num_hints = y[omega + i] as usize;

            if num_hints < idx || num_hints > omega {
                return Err(VerifyError::TooManyHints);
            }

            h.v[i].f[y[idx] as usize] = 1;
            idx += 1;

            while idx < num_hints {
                if y[idx - 1] >= y[idx] {
                    return Err(VerifyError::TooManyHints);
                }

                h.v[i].f[y[idx] as usize] = 1;
                idx += 1;
            }
        }

        if y[idx..omega].iter().any(|x| *x != 0) {
            return Err(VerifyError::TooManyHints);
        }

        Ok(h)
    }

    fn bitpack_2pow17(&self, dst: &mut [u8]) {
        for (buf, p) in dst
            .chunks_exact_mut(Poly::packed_bytesize(18))
            .zip(self.v.iter())
        {
            p.bitpack_2pow17(buf.try_into().unwrap());
        }
    }

    fn bitpack_2pow19(&self, dst: &mut [u8]) {
        for (buf, p) in dst
            .chunks_exact_mut(Poly::packed_bytesize(20))
            .zip(self.v.iter())
        {
            p.bitpack_2pow19(buf.try_into().unwrap());
        }
    }

    fn expand_mask_2pow17(&mut self, rho: &[u8; 64], mu: usize, h: &mut hash::Shake256) {
        let mut blocks = [0u8; 5 * hash::SHAKE_256_RATE];

        for (r, p) in self.v.iter_mut().enumerate() {
            h.absorb_multi(&[rho, &u16::to_le_bytes((mu + r) as u16)]);
            h.squeezeblocks(&mut blocks);

            p.bitunpack_2pow17(blocks.first_chunk_mut().unwrap());
        }
    }

    fn expand_mask_2pow19(&mut self, rho: &[u8; 64], mu: usize, h: &mut hash::Shake256) {
        let mut blocks = [0u8; 5 * hash::SHAKE_256_RATE];

        for (r, p) in self.v.iter_mut().enumerate() {
            h.absorb_multi(&[rho, &u16::to_le_bytes((mu + r) as u16)]);
            h.squeezeblocks(&mut blocks);

            p.bitunpack_2pow19(blocks.first_chunk_mut().unwrap());
        }
    }

    const fn norm_in_bound(&self, bound: usize) -> bool {
        let mut i = 0;

        while i < K {
            if !self.v[i].norm_in_bound(bound) {
                return false;
            }

            i += 1;
        }

        true
    }

    fn make_hint<const G2: i32>(&mut self, x0: &PolyVec<K>, x1: &PolyVec<K>) -> usize {
        let mut sum = 0;
        for i in 0..K {
            sum += self.v[i].make_hint::<G2>(&x0.v[i], &x1.v[i]);
        }

        sum
    }

    fn shifted_left(&self, d: usize) -> Self {
        let mut v = [const { MaybeUninit::uninit() }; K];

        for (i, poly) in v.iter_mut().enumerate() {
            poly.write(self.v[i].shifted_left(d));
        }

        Self {
            v: unsafe { transmute_copy(&v) },
        }
    }
}

impl<const K: usize> Mul<&Poly> for &PolyVec<K> {
    type Output = PolyVec<K>;

    fn mul(self, rhs: &Poly) -> Self::Output {
        let mut v = PolyVec::zero();

        for i in 0..K {
            v.v[i].multiply_ntt(&self.v[i], rhs);
        }

        v
    }
}

impl<const K: usize> MulAssign<&Poly> for PolyVec<K> {
    fn mul_assign(&mut self, rhs: &Poly) {
        for poly in self.v.iter_mut() {
            *poly *= rhs;
        }
    }
}

impl<const K: usize> AddAssign<&Self> for PolyVec<K> {
    fn add_assign(&mut self, rhs: &Self) {
        for i in 0..K {
            self.v[i] += &rhs.v[i];
        }
    }
}

impl<const K: usize> SubAssign<&Self> for PolyVec<K> {
    fn sub_assign(&mut self, rhs: &Self) {
        for i in 0..K {
            self.v[i] -= &rhs.v[i];
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
        let test_data: Tests<KeyGenTg> = serde_json::from_str(&test_data).unwrap();

        for tg in test_data.test_groups.iter() {
            match tg.parameter_set.as_str() {
                "ML-DSA-44" => {
                    for test in &tg.tests {
                        let mut vk_bytes = [0u8; mldsa44::PUBKEY_SIZE];
                        let mut sk_bytes = [0u8; mldsa44::PRIVKEY_SIZE];

                        let sk = mldsa44::PrivateKey::keygen_internal(&mut vk_bytes, &test.seed);
                        sk.encode(&mut sk_bytes);

                        assert_eq!(vk_bytes, test.pk[..]);
                        assert_eq!(sk_bytes, test.sk[..]);

                        let sk_prime = mldsa44::PrivateKey::decode(&test.sk);

                        sk_bytes.fill(0);
                        sk_prime.encode(&mut sk_bytes);

                        assert_eq!(sk_bytes, test.sk[..]);

                        let vk_prime = mldsa44::PublicKey::decode(&test.pk);

                        vk_bytes.fill(0);
                        vk_prime.encode(&mut vk_bytes);

                        assert_eq!(vk_bytes, test.pk[..]);
                    }
                }
                "ML-DSA-65" => {
                    for test in &tg.tests {
                        let mut vk_bytes = [0u8; mldsa65::PUBKEY_SIZE];
                        let mut sk_bytes = [0u8; mldsa65::PRIVKEY_SIZE];

                        let sk = mldsa65::PrivateKey::keygen_internal(&mut vk_bytes, &test.seed);
                        sk.encode(&mut sk_bytes);

                        assert_eq!(vk_bytes, test.pk[..]);
                        assert_eq!(sk_bytes, test.sk[..]);

                        let sk_prime = mldsa65::PrivateKey::decode(&test.sk);

                        sk_bytes.fill(0);
                        sk_prime.encode(&mut sk_bytes);

                        assert_eq!(sk_bytes, test.sk[..]);

                        let vk_prime = mldsa65::PublicKey::decode(&test.pk);

                        vk_bytes.fill(0);
                        vk_prime.encode(&mut vk_bytes);

                        assert_eq!(vk_bytes, test.pk[..]);
                    }
                }
                "ML-DSA-87" => {
                    for test in &tg.tests {
                        let mut vk_bytes = [0u8; mldsa87::PUBKEY_SIZE];
                        let mut sk_bytes = [0u8; mldsa87::PRIVKEY_SIZE];

                        let sk = mldsa87::PrivateKey::keygen_internal(&mut vk_bytes, &test.seed);
                        sk.encode(&mut sk_bytes);

                        assert_eq!(vk_bytes, test.pk[..]);
                        assert_eq!(sk_bytes, test.sk[..]);

                        let sk_prime = mldsa87::PrivateKey::decode(&test.sk);

                        sk_bytes.fill(0);
                        sk_prime.encode(&mut sk_bytes);

                        assert_eq!(sk_bytes, test.sk[..]);

                        let vk_prime = mldsa87::PublicKey::decode(&test.pk);

                        vk_bytes.fill(0);
                        vk_prime.encode(&mut vk_bytes);

                        assert_eq!(vk_bytes, test.pk[..]);
                    }
                }
                _ => panic!("invalid paramter set"),
            };
        }
    }

    #[test]
    fn test_siggen() {
        let mut test_data_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        test_data_path.push("tests/mldsa-sign.json");

        let test_data = read_to_string(&test_data_path).unwrap();
        let test_data: Tests<SigGenTg> = serde_json::from_str(&test_data).unwrap();

        for tg in test_data.test_groups.iter() {
            match tg.parameter_set.as_str() {
                "ML-DSA-44" => {
                    let mut sig = [0u8; mldsa44::SIG_SIZE];

                    for test in tg.tests.iter() {
                        sig.fill(0);
                        let sk = mldsa44::PrivateKey::decode(&test.sk);
                        let rnd = match &test.rnd {
                            Some(rnd) => rnd.rnd,
                            None => [0; 32],
                        };
                        sk.sign_internal(&mut sig, &test.message, &rnd);
                        assert_eq!(&sig, &test.signature[..]);
                    }
                }
                "ML-DSA-65" => {
                    let mut sig = [0u8; mldsa65::SIG_SIZE];

                    for test in tg.tests.iter() {
                        sig.fill(0);
                        let sk = mldsa65::PrivateKey::decode(&test.sk);
                        let rnd = match &test.rnd {
                            Some(rnd) => rnd.rnd,
                            None => [0; 32],
                        };
                        sk.sign_internal(&mut sig, &test.message, &rnd);
                        assert_eq!(&sig, &test.signature[..]);
                    }
                }
                "ML-DSA-87" => {
                    let mut sig = [0u8; mldsa87::SIG_SIZE];

                    for test in tg.tests.iter() {
                        sig.fill(0);
                        let sk = mldsa87::PrivateKey::decode(&test.sk);
                        let rnd = match &test.rnd {
                            Some(rnd) => rnd.rnd,
                            None => [0; 32],
                        };
                        sk.sign_internal(&mut sig, &test.message, &rnd);
                        assert_eq!(&sig, &test.signature[..]);
                    }
                }
                _ => panic!("invalid paramter set"),
            };
        }
    }

    #[test]
    fn test_sigver() {
        let mut test_data_path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        test_data_path.push("tests/mldsa-verify.json");

        let test_data = read_to_string(&test_data_path).unwrap();
        let test_data: Tests<SigVerTg> = serde_json::from_str(&test_data).unwrap();

        for tg in test_data.test_groups.iter() {
            match tg.parameter_set.as_str() {
                "ML-DSA-44" => {
                    let pk = mldsa44::PublicKey::decode(&tg.pk);

                    for test in tg.tests.iter() {
                        match pk
                            .verify_internal(&test.message, test.signature[..].try_into().unwrap())
                        {
                            Ok(_) => assert!(test.test_passed),
                            Err(VerifyError::ZoutOfBound) => assert_eq!(test.reason, "z too large"),
                            Err(VerifyError::Mismatch) => {
                                assert!(!test.test_passed)
                            }
                            Err(VerifyError::TooManyHints) => {
                                assert_eq!(test.reason, "too many hints")
                            }
                        }
                    }
                }
                "ML-DSA-65" => {
                    let pk = mldsa65::PublicKey::decode(&tg.pk);

                    for test in tg.tests.iter() {
                        match pk
                            .verify_internal(&test.message, test.signature[..].try_into().unwrap())
                        {
                            Ok(_) => assert!(test.test_passed),
                            Err(VerifyError::ZoutOfBound) => assert_eq!(test.reason, "z too large"),
                            Err(VerifyError::Mismatch) => {
                                assert!(!test.test_passed)
                            }
                            Err(VerifyError::TooManyHints) => {
                                assert_eq!(test.reason, "too many hints")
                            }
                        }
                    }
                }
                "ML-DSA-87" => {
                    let pk = mldsa87::PublicKey::decode(&tg.pk);

                    for test in tg.tests.iter() {
                        match pk
                            .verify_internal(&test.message, test.signature[..].try_into().unwrap())
                        {
                            Ok(_) => assert!(test.test_passed),
                            Err(VerifyError::ZoutOfBound) => assert_eq!(test.reason, "z too large"),
                            Err(VerifyError::Mismatch) => {
                                assert!(!test.test_passed)
                            }
                            Err(VerifyError::TooManyHints) => {
                                assert_eq!(test.reason, "too many hints")
                            }
                        }
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
    struct Tests<T> {
        #[serde(rename = "testGroups")]
        test_groups: Vec<T>,
    }

    #[derive(Deserialize)]
    struct Rnd {
        #[serde(with = "hex")]
        rnd: [u8; 32],
    }

    #[derive(Deserialize)]
    struct SigGenTV {
        #[serde(with = "hex")]
        message: Vec<u8>,

        #[serde(with = "hex")]
        signature: Vec<u8>,

        #[serde(with = "hex")]
        sk: Vec<u8>,

        #[serde(flatten)]
        rnd: Option<Rnd>,
    }
    #[derive(Deserialize)]
    struct SigGenTg {
        #[serde(rename = "parameterSet")]
        parameter_set: String,

        tests: Vec<SigGenTV>,
    }

    #[derive(Deserialize)]
    struct SigVerTV {
        #[serde(with = "hex")]
        message: Vec<u8>,

        reason: String,

        #[serde(with = "hex")]
        signature: Vec<u8>,

        #[serde(rename = "testPassed")]
        test_passed: bool,
    }

    #[derive(Deserialize)]
    struct SigVerTg {
        #[serde(rename = "parameterSet")]
        parameter_set: String,

        #[serde(with = "hex")]
        pk: Vec<u8>,

        tests: Vec<SigVerTV>,
    }
}
