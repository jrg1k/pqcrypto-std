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

    #[inline]
    pub fn absorb(&mut self, src: &[&[u8]]) -> impl XofReader {
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
    pub fn absorb(&mut self, src: &[&[u8]]) -> impl XofReader {
        for s in src {
            self.h.update(s);
        }

        self.h.finalize_xof_reset()
    }
}
