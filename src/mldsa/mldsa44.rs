//! ML-DSA-44 parameter set.

use super::{
    bitlen, coeff, privkey_size, pubkey_size, sig_size, Poly, PolyVec, SigningKeyInternal,
    VerifyingKeyInternal, Q,
};
use crate::hash;
use core::mem::{transmute, MaybeUninit};

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
pub const PUBKEY_SIZE: usize = pubkey_size(K);

/// Private key bytesize.
pub const PRIVKEY_SIZE: usize = privkey_size(K, L, ETA);

/// Signature bytesize.
pub const SIG_SIZE: usize = sig_size(K, L, LAMBDA, GAMMA1, OMEGA);

/// Private key used for signing.
pub struct PrivateKey {
    key: super::PrivateKey<K, L, ETA>,
}

impl From<super::PrivateKey<K, L, ETA>> for PrivateKey {
    fn from(key: super::PrivateKey<K, L, ETA>) -> Self {
        Self { key }
    }
}

impl SigningKeyInternal<K, L, ETA, TAU, GAMMA1, GAMMA2, BETA, OMEGA, CT_BYTES, W1_BYTES, Z_BYTES>
    for PrivateKey
{
    fn privkey(&self) -> &super::PrivateKey<K, L, ETA> {
        &self.key
    }

    fn expand_mask(pvec: &mut PolyVec<L>, rho: &[u8; 64], mu: usize, h: &mut hash::Shake256) {
        pvec.expand_mask_2pow17(rho, mu, h);
    }

    fn bitpack_z(pvec: &PolyVec<L>, dst: &mut [u8; Z_BYTES]) {
        pvec.bitpack_2pow17(dst);
    }

    fn pack_simple(w1: &PolyVec<K>, z: &mut [u8; W1_BYTES]) {
        w1.pack_simple_6bit(z);
    }

    fn decompose(x: &PolyVec<K>, x0: &mut PolyVec<K>, x1: &mut PolyVec<K>) {
        x.decompose_88(x0, x1);
    }
}

pub struct PublicKey {
    key: super::PublicKey<K, L>,
}

impl VerifyingKeyInternal<K, L, CT_BYTES, Z_BYTES, H_BYTES, W1_BYTES, SIG_SIZE> for PublicKey {
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
        &self.key
    }
}

impl From<super::PublicKey<K, L>> for PublicKey {
    fn from(key: super::PublicKey<K, L>) -> Self {
        Self { key }
    }
}
