//! This library implements standardized quantum-resistand cryptographic algorithms.
//!
//! Currently supports [ML-DSA](mldsa) for signatures and [ML-KEM](mlkem) key encapsulation.

#![cfg_attr(not(test), no_std)]
#![allow(clippy::identity_op)]

pub mod mldsa;
pub mod mlkem;

mod hash;
