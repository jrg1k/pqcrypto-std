use core::mem;

use sha3::{
    digest::{ExtendableOutputReset, Update, XofReader},
    Shake128, Shake256,
};

pub struct H {
    h: Shake256,
}

impl H {
    #[inline]
    pub fn init() -> Self {
        Self {
            h: Shake256::default(),
        }
    }

    pub fn absorb_and_squeeze<const N: usize, const M: usize>(
        &mut self,
        dst: &mut [u8; N],
        src: &[&[u8]; M],
    ) {
        for s in src {
            self.h.update(s);
        }
        self.h.finalize_xof_reset_into(dst);
    }

    #[inline]
    pub fn absorb<const N: usize>(&mut self, src: &[&[u8]; N]) -> impl XofReader {
        for s in src {
            self.h.update(s);
        }

        self.h.finalize_xof_reset()
    }
}

pub struct G {
    h: Shake128,
}

impl G {
    #[inline]
    pub fn init() -> Self {
        Self {
            h: Shake128::default(),
        }
    }

    #[inline]
    pub fn absorb<const N: usize>(&mut self, src: &[&[u8]; N]) -> impl XofReader {
        for s in src {
            self.h.update(s);
        }

        self.h.finalize_xof_reset()
    }
}

const SHAKE_256_RATE: usize = 136;

struct H2 {
    block: [u8; 25 * 8],
    pos: usize,
}

impl H2 {
    #[inline]
    fn init() -> Self {
        Self {
            block: [0; 25 * 8],
            pos: 0,
        }
    }

    fn absorb(&mut self, mut src: &[u8]) {
        while self.pos + src.len() >= SHAKE_256_RATE {
            for (a, b) in self.block[self.pos..SHAKE_256_RATE]
                .iter_mut()
                .zip(src.iter())
            {
                *a ^= b;
            }

            src = &src[SHAKE_256_RATE - self.pos..];

            keccak::f1600(unsafe {
                mem::transmute::<&mut [u8; 25 * 8], &mut [u64; 25]>(&mut self.block)
            });

            self.pos = 0;
        }

        for (a, b) in self.block[self.pos..].iter_mut().zip(src.iter()) {
            *a ^= b;
        }
    }

    fn finalize(&mut self) {
        self.block[self.pos] ^= 0x1F;
        self.block[SHAKE_256_RATE - 1] ^= 1 << 7;
        self.pos = SHAKE_256_RATE;
    }

    fn squeeze(&mut self, dst: &mut [u8]) {
        let mut out_idx = 0;

        while out_idx < dst.len() {
            if self.pos == SHAKE_256_RATE {
                keccak::f1600(unsafe {
                    mem::transmute::<&mut [u8; 25 * 8], &mut [u64; 25]>(&mut self.block)
                });

                self.pos = 0;
            }

            for _ in 0..(SHAKE_256_RATE - self.pos).min(dst.len() - out_idx) {
                dst[out_idx] = self.block[self.pos];
                self.pos += 1;
                out_idx += 1;
            }
        }
    }
}

const fn bytes_to_u64(b: &[u8]) -> u64 {
    let mut i = 0;
    let mut out = 0;

    while i < b.len() {
        out |= (b[i] as u64) << (i << 3);
        i += 1;
    }

    out
}

#[test]
fn test_shake() {
    let input = [1, 2, 3, 4];
    let mut out0 = [0u8; 2];
    let mut out1 = [0u8; 2];

    let mut h = H::init();
    let mut h2 = H2::init();

    h.absorb_and_squeeze(&mut out0, &[&input]);

    h2.absorb(&input);
    h2.finalize();
    h2.squeeze(&mut out1);

    assert_eq!(out0, out1);
}
