use sha3::{
    digest::{ExtendableOutput, ExtendableOutputReset, Update, XofReader},
    Shake256,
};

pub fn h(dst: &mut [&mut [u8]], src: &[&[u8]]) {
    let mut hasher = Shake256::default();
    for s in src {
        hasher.update(s);
    }
    let mut xof = hasher.finalize_xof_reset();
    for d in dst {
        xof.read(d);
    }
}
