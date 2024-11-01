use core::mem;

pub const SHAKE_128_RATE: usize = 168;
pub const SHAKE_256_RATE: usize = 136;

pub type Shake128 = Shake<SHAKE_128_RATE>;
pub type Shake256 = Shake<SHAKE_256_RATE>;

const BLOCK_SIZE: usize = 25 * 8;

#[inline(always)]
fn keccak_permute_block(block: &mut [u8; BLOCK_SIZE]) {
    keccak::f1600(unsafe { mem::transmute::<&mut [u8; BLOCK_SIZE], &mut [u64; 25]>(block) });
}

pub struct Shake<const R: usize> {
    block: [u8; BLOCK_SIZE],
    pos: usize,
}

impl<const R: usize> Shake<R> {
    pub const fn init() -> Self {
        Self {
            block: [0; BLOCK_SIZE],
            pos: 0,
        }
    }

    pub fn absorb_multi<const K: usize>(&mut self, src: &[&[u8]; K]) {
        for x in src {
            self.absorb(x);
        }

        self.finalize();
    }

    pub fn absorb(&mut self, src: &[u8]) {
        let mut rem = src.len();
        let mut idx = 0;
        while self.pos + rem >= R {
            for i in self.pos..R {
                self.block[i] ^= src[idx];
                idx += 1;
                rem -= 1;
            }

            keccak_permute_block(&mut self.block);

            self.pos = 0;
        }

        while idx < src.len() {
            self.block[self.pos] ^= src[idx];

            self.pos += 1;
            idx += 1;
        }
    }

    pub fn finalize(&mut self) {
        self.block[self.pos] ^= 0x1F;
        self.block[R - 1] ^= 1 << 7;
        self.pos = R;
    }

    pub fn squeeze<const K: usize>(&mut self, dst: &mut [u8; K]) {
        let mut out_idx = 0;

        while out_idx < dst.len() {
            if self.pos == R {
                keccak_permute_block(&mut self.block);

                self.pos = 0;
            }

            let n = self.rem().min(dst.len() - out_idx);

            for _ in 0..n {
                dst[out_idx] = self.block[self.pos];
                self.pos += 1;
                out_idx += 1;
            }
        }
    }

    pub fn squeezeblock(&mut self) -> &[u8; R] {
        keccak_permute_block(&mut self.block);

        unsafe { self.block[..R].first_chunk().unwrap_unchecked() }
    }

    pub fn absorb_and_squeeze<const N: usize, const M: usize>(
        &mut self,
        dst: &mut [u8; N],
        src: &[&[u8]; M],
    ) {
        for x in src {
            self.absorb(x);
        }

        self.finalize();
        self.squeeze(dst);
        self.reset();
    }

    pub fn reset(&mut self) {
        self.block.fill(0);
        self.pos = 0;
    }

    const fn rem(&self) -> usize {
        R - self.pos
    }
}
