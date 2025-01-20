use crate::properties::*;
use vstd::prelude::*;
use vstd::assert_seqs_equal;

verus! {

/// Unsigned LEB128
pub struct UnsignedLEB128;

/// Result of UnsignedLEB128
pub type UInt = u64;

impl View for UnsignedLEB128 {
    type V = Self;

    open spec fn view(&self) -> Self::V {
        Self
    }
}

/// Byte size of UInt
#[allow(unused_macros)]
macro_rules! uint_size { () => { 8 } }
pub(super) use uint_size;

/// Check if the highest bit is set in an u8
#[allow(unused_macros)]
macro_rules! is_high_8_bit_set {
    ($v:expr) => { $v as u8 >= 0x80 };
}
pub(crate) use is_high_8_bit_set;

/// Take the lowest 7 bits as an u8
#[allow(unused_macros)]
macro_rules! take_low_7_bits {
    ($v:expr) => { $v as u8 & 0x7f };
}
pub(crate) use take_low_7_bits;

/// Set the highest bit to 1 as an u8
#[allow(unused_macros)]
macro_rules! set_high_8_bit {
    ($v:expr) => {
        ($v | 0x80) as u8
    };
}
pub(super) use set_high_8_bit;

/// Max value for an n-bit unsigned integer
#[allow(unused_macros)]
macro_rules! n_bit_max_unsigned {
    ($n:expr) => { if $n == 0 { 0 } else { UInt::MAX >> (((8 * uint_size!()) - $n) as usize) } }
}
pub(super) use n_bit_max_unsigned;

impl SpecCombinator for UnsignedLEB128 {
    type Type = UInt;

    open spec fn spec_parse(&self, s: Seq<u8>) -> Result<(usize, Self::Type), ()>
        decreases s.len()
    {
        let v = take_low_7_bits!(s.first());

        if s.len() != 0 {
            if is_high_8_bit_set!(s.first()) {
                match self.spec_parse(s.drop_first()) {
                    Ok((n, v2)) =>
                        // Check for overflow and canonicity (v2 should not be 0)
                        if n < usize::MAX && 0 < v2 <= n_bit_max_unsigned!(8 * uint_size!() - 7) {
                            Ok(((n + 1) as usize, v2 << 7 | v as Self::Type))
                        } else {
                            Err(())
                        }

                    Err(e) => Err(e),
                }
            } else {
                Ok((1, v as Self::Type))
            }
        } else {
            Err(())
        }
    }

    open spec fn spec_serialize(&self, v: Self::Type) -> Result<Seq<u8>, ()>
    {
        Self::spec_serialize_helper(v)
    }
}

impl UnsignedLEB128 {
    /// Helper function for spec_serialize
    pub open spec fn spec_serialize_helper(v: UInt) -> Result<Seq<u8>, ()>
        decreases v via Self::spec_serialize_decreases
    {
        let lo = take_low_7_bits!(v);
        let hi = v >> 7;

        if hi == 0 {
            Ok(seq![lo])
        } else {
            match Self::spec_serialize_helper(hi) {
                Ok(s) => Ok(seq![set_high_8_bit!(lo)] + s),
                Err(e) => Err(e),
            }
        }
    }

    #[via_fn]
    proof fn spec_serialize_decreases(v: UInt)
    {
        assert(v >> 7 != 0 ==> v >> 7 < v) by (bit_vector);
    }

    proof fn lemma_spec_serialize_length(&self, v: UInt)
        ensures self.spec_serialize(v) matches Ok(s) ==> s.len() <= 10
    {
        reveal_with_fuel(UnsignedLEB128::spec_serialize_helper, 10);
        assert(
            v >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 >> 7 == 0
        ) by (bit_vector);
    }

    proof fn lemma_serialize_last_byte_high_8_bit_not_set(&self, v: UInt)
        ensures self.spec_serialize(v) matches Ok(s) ==> !is_high_8_bit_set!(s.last())
        decreases v
    {
        let lo = take_low_7_bits!(v);
        let hi = v >> 7;

        if hi == 0 {
            assert(!is_high_8_bit_set!(take_low_7_bits!(v))) by (bit_vector);
            assert(self.spec_serialize(v) matches Ok(lo));
        } else {
            if let Ok(s) = Self::spec_serialize_helper(hi) {
                assert(Self::spec_serialize_helper(v) matches Ok(vv) && vv == seq![set_high_8_bit!(lo)] + s);
                assert(v >> 7 != 0 ==> v >> 7 < v) by (bit_vector);
                self.lemma_serialize_last_byte_high_8_bit_not_set(hi);
            } else {
                assert(self.spec_serialize(v) is Err);
            }
        }
    }

    proof fn lemma_parse_high_8_bits_set_until_last(&self, s: Seq<u8>) 
        ensures self.spec_parse(s) matches Ok((n, v)) ==> {
            &&& forall |i: int| 0 <= i < n - 1 ==> is_high_8_bit_set!(s.spec_index(i))
            &&& !(s[n-1] as u8 >= 0x80)  // is_high_8_bit_set!(s[n - 1])
        }
        decreases s.len()
    {
        if let Ok((n, v)) = self.spec_parse(s) {
            assert(n <= s.len()) by { self.lemma_parse_length(s) };
            let s0 = s[0];
            if n == 1 {
                // assert(!is_high_8_bit_set!(s0));
                if (is_high_8_bit_set!(s0)) {
                    assert(self.spec_parse(s.drop_first()) matches Ok((n1, _)) && n1 == 0);
                    self.lemma_parse_productive(s.drop_first());
                }
            } else {
                assert(is_high_8_bit_set!(s0));
                self.lemma_parse_high_8_bits_set_until_last(s.drop_first());
                assert_seqs_equal!(s == seq![s0] + s.drop_first());
            }
        }
    }
}

impl SecureSpecCombinator for UnsignedLEB128 {
    open spec fn is_prefix_secure() -> bool {
        true
    }

    proof fn lemma_prefix_secure(&self, s1: Seq<u8>, s2: Seq<u8>) 
        decreases s1.len()
    {
        if Self::is_prefix_secure() {
            if let Ok((n1, v1)) = self.spec_parse(s1) {
                // assert(n1 <= s1.len()) by { self.lemma_parse_length(s1) };
                // let s1_0 = s1[0];
                // if n1 == 1 {
                //     // assert(!is_high_8_bit_set!(s0));
                //     if (is_high_8_bit_set!(s1_0)) {
                //         assert(self.spec_parse(s1.drop_first()) matches Ok((n1_1, _)) && n1_1 == 0);
                //         self.lemma_parse_productive(s1.drop_first());
                //         assume(false);
                //     }
                //     assume(false);
                // } else {
                //     // assert(is_high_8_bit_set!(s0));
                //     // self.lemma_parse_high_8_bits_set_until_last(s.drop_first());
                //     self.lemma_prefix_secure(s1.drop_first(), s2);
                //     assert_seqs_equal!(s1 == seq![s1_0] + s1.drop_first());
                // }

                // self.lemma_parse_high_8_bits_set_until_last(s1);
                // assert(!(s1[n1-1] as u8 >= 0x80));
                // if let Ok((n2, v2)) = self.spec_parse(s1.add(s2)) {
                //     assert(n1 <= n2);
                //     assume(false);
                // } else {
                //     assume(false);
                //     // should be unreachable
                //     assert(false);
                // }
                admit();
            }
        }
    }


    proof fn lemma_parse_length(&self, s: Seq<u8>)
        decreases s.len()
    {
        if s.len() != 0 {
            self.lemma_parse_length(s.drop_first());
        }
    }

    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
        decreases v
    {
        if let Ok(s) = self.spec_serialize(v) {
            let lo = take_low_7_bits!(v);
            let hi = v >> 7;

            self.lemma_spec_serialize_length(v);

            assert({
                &&& !is_high_8_bit_set!(take_low_7_bits!(v))
                &&& v >> 7 == 0 ==> v == take_low_7_bits!(v)
                &&& v >> 7 != 0 ==> v >> 7 < v
                &&& is_high_8_bit_set!(set_high_8_bit!(lo))
                &&& (v >> 7) << 7 | take_low_7_bits!(v) as UInt == v
                &&& (v >> 7) <= n_bit_max_unsigned!(8 * uint_size!() - 7)
                &&& take_low_7_bits!(set_high_8_bit!(take_low_7_bits!(v))) == take_low_7_bits!(v)
            }) by (bit_vector);

            if hi != 0 {
                self.theorem_serialize_parse_roundtrip(hi);

                let hi_bytes = self.spec_serialize(hi).unwrap();
                assert(s.drop_first() == hi_bytes);
            }
        }
    }

    proof fn theorem_parse_serialize_roundtrip(&self, s: Seq<u8>) {
        assume(false);
    }

    open spec fn is_productive(&self) -> bool {
        true
    }

    proof fn lemma_parse_productive(&self, s: Seq<u8>) 
        decreases s.len()
    {
        if s.len() != 0 {
            self.lemma_parse_productive(s.drop_first());
        }
    }
}

impl<I,O> Combinator<I,O> for UnsignedLEB128 
    where I: VestInput, O: VestOutput<I>
{
    type Type = UInt;

    open spec fn spec_length(&self) -> Option<usize> {
        None // TODO
    }

    fn length(&self) -> Option<usize> {
        None // TODO
    }

    open spec fn parse_requires(&self) -> bool {
        true
    }

    fn parse(&self, s: I) -> (res: PResult<Self::Type, ParseError>) {
        proof { admit(); }
        Err(ParseError::Other("todo".to_string()))
    }

    open spec fn serialize_requires(&self) -> bool {
        true
    }

    fn serialize(&self, v: Self::Type, buf: &mut O, pos: usize) -> (res: SResult<usize, SerializeError>) {
        proof { admit(); }
        Err(SerializeError::Other("todo".to_string()))
    }
}


}
