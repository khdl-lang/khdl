#[derive(Debug, Copy, Clone)]
pub enum Lattice<T> {
    Undefined,
    Defined(T),
    Different,
}

#[derive(Debug, Copy, Clone)]
pub enum LatticeMerge<T> {
    Defined(T),
    Different,
}

impl<T> Lattice<T> {
    pub fn defined(self) -> Option<T> {
        match self {
            Lattice::Defined(v) => Some(v),
            Lattice::Undefined | Lattice::Different => None,
        }
    }

    pub fn merge(self, other: Lattice<T>, mut f: impl FnMut(T, T) -> LatticeMerge<T>) -> Lattice<T> {
        match (self, other) {
            (Lattice::Undefined, v) | (v, Lattice::Undefined) => v,
            (Lattice::Different, _) | (_, Lattice::Different) => Lattice::Different,
            (Lattice::Defined(a), Lattice::Defined(b)) => match f(a, b) {
                LatticeMerge::Defined(v) => Lattice::Defined(v),
                LatticeMerge::Different => Lattice::Different,
            },
        }
    }

    pub fn merge_eq(self, other: Lattice<T>) -> Lattice<T>
    where
        T: PartialEq,
    {
        self.merge(other, |a, b| {
            if a == b {
                LatticeMerge::Defined(a)
            } else {
                LatticeMerge::Different
            }
        })
    }
}
