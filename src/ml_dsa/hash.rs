use sha3::{
    digest::{ExtendableOutputReset, Update, XofReader},
    Shake128, Shake256,
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

pub struct Xof<T: XofReader> {
    xof: T,
}

impl<T: XofReader> Xof<T> {
    pub fn squeeze(&mut self, dst: &mut [u8]) {
        self.xof.read(dst)
    }
}
