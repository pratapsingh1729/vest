use vstd::prelude::*;
use crate::properties::*;


verus! { 

struct UnforgeableAux {}

/// Token to allow declassification of the first n bytes of a buffer
pub struct ByteDeclassifyToken {
    /// unforgeable inner
    unforgeable: UnforgeableAux
}

impl ByteDeclassifyToken {

    /// The number of bytes to declassify
    pub closed spec fn num_bytes(self) -> usize;
    
    /// The buffer from which to declassify
    pub closed spec fn buffer(self) -> Seq<u8>;
}

/// Token representing the security policy for declassification while parsing a particular combinator
pub struct CombinatorToken<C> where C: SpecCombinator {
    /// unforgeable inner
    unforgeable: UnforgeableAux,
    pub combinator: C,
    pub buffer: Seq<u8>,
}

// impl<C> CombinatorToken<C> where C: SpecCombinator {
//     // pub spec fn view_combinator(self) -> C;
//     // pub spec fn view_buffer(self) -> Seq<u8>;
// }


}
