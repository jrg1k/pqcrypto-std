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
