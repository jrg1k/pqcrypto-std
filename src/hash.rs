use core::mem::{MaybeUninit, transmute, transmute_copy};

pub const SHAKE_128_RATE: usize = 168;
pub const SHAKE_256_RATE: usize = 136;
pub const SHA3_256_RATE: usize = 136;
pub const SHA3_512_RATE: usize = 72;

const SHAKE_PAD: u8 = 0x1F;

pub type Shake128 = Keccak<SHAKE_128_RATE, SHAKE_PAD>;
pub type Shake256 = Keccak<SHAKE_256_RATE, SHAKE_PAD>;

const SHA3_PAD: u8 = 0x6;

type Sha3_256 = Keccak<SHA3_256_RATE, SHA3_PAD>;
type Sha3_512 = Keccak<SHA3_512_RATE, SHA3_PAD>;

const BLOCK_SIZE: usize = 25 * 8;

pub struct Keccak<const R: usize, const P: u8> {
    block: [u8; BLOCK_SIZE],
    pos: usize,
}

impl<const R: usize, const P: u8> Keccak<R, P> {
    pub const fn init() -> Self {
        Self {
            block: [0; BLOCK_SIZE],
            pos: 0,
        }
    }

    fn keccak_permute(&mut self) {
        keccak::f1600(unsafe {
            transmute::<&mut [u8; BLOCK_SIZE], &mut [u64; 25]>(&mut self.block)
        });
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

            self.keccak_permute();

            self.pos = 0;
        }

        while idx < src.len() {
            self.block[self.pos] ^= src[idx];

            self.pos += 1;
            idx += 1;
        }
    }

    pub fn finalize(&mut self) {
        self.block[self.pos] ^= P;
        self.block[R - 1] ^= 1 << 7;
        self.pos = R;
    }

    pub fn squeeze<const K: usize>(&mut self, dst: &mut [u8; K]) {
        let mut out_idx = 0;

        while out_idx < dst.len() {
            if self.pos == R {
                self.keccak_permute();

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

    pub fn squeeze_array<const K: usize>(&mut self) -> [u8; K] {
        let mut out: [MaybeUninit<u8>; K] = [MaybeUninit::uninit(); K];
        let mut out_idx = 0;

        while out_idx < K {
            if self.pos == R {
                self.keccak_permute();

                self.pos = 0;
            }

            let n = self.rem().min(K - out_idx);

            for _ in 0..n {
                out[out_idx].write(self.block[self.pos]);
                self.pos += 1;
                out_idx += 1;
            }
        }

        unsafe { transmute_copy::<[MaybeUninit<u8>; K], [u8; K]>(&out) }
    }

    pub fn squeezeblock(&mut self) -> &[u8; R] {
        self.keccak_permute();

        unsafe { self.block[..R].first_chunk().unwrap_unchecked() }
    }

    pub fn squeezeblocks(&mut self, dst: &mut [u8]) {
        for block in dst.chunks_exact_mut(R) {
            self.keccak_permute();
            block.copy_from_slice(&self.block[..R]);
        }

        self.reset();
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

pub fn sha3_256<const K: usize>(src: &[&[u8]; K]) -> [u8; 32] {
    let mut s = Sha3_256::init();
    s.absorb_multi(src);
    s.squeeze_array()
}

pub fn sha3_256_into<const K: usize>(dst: &mut [u8; 32], src: &[&[u8]; K]) {
    let mut s = Sha3_256::init();
    s.absorb_multi(src);
    dst.copy_from_slice(&s.squeezeblock()[..32]);
}

pub fn sha3_512_split<const K: usize>(src: &[&[u8]; K]) -> ([u8; 32], [u8; 32]) {
    let mut s = Sha3_512::init();
    s.absorb_multi(src);

    (s.squeeze_array(), s.squeeze_array())
}
