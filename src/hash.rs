use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Digest, Sha3_256, Sha3_512, Shake128, Shake256,
};

#[inline]
pub fn g(src: &[&[u8]]) -> ([u8; 32], [u8; 32]) {
    let mut hasher = Sha3_512::new();

    for i in src {
        Digest::update(&mut hasher, i);
    }

    let mut a = [0u8; 32];
    let mut b = [0u8; 32];

    let output = hasher.finalize();

    a.copy_from_slice(&output[..32]);
    b.copy_from_slice(&output[32..]);

    (a, b)
}

#[inline]
pub fn h(dst: &mut [u8; 32], src: &[u8]) {
    let mut hasher = Sha3_256::new();

    Digest::update(&mut hasher, src);

    hasher.finalize_into(dst.into());
}

#[inline]
pub fn xof(rho: &[u8; 32], i: usize, j: usize) -> impl XofReader {
    let mut hasher = Shake128::default();
    hasher.update(rho);
    hasher.update(&[i as u8, j as u8]);
    hasher.finalize_xof()
}

#[inline]
pub fn prf(bytes: &[u8; 32], nonce: usize) -> impl XofReader {
    let mut hasher = Shake256::default();
    hasher.update(bytes);
    hasher.update(&[nonce as u8]);
    hasher.finalize_xof()
}
