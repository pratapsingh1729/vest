use vest::regular::builder::*;
use vest::regular::bytes::*;
use vest::regular::bytes_n::BytesN;
use vest::regular::tag::*;
use vstd::prelude::*;

verus! {

spec const SPEC_BYTES_1000_CONST: Seq<u8> = seq![1, 0, 0, 0];

exec const BYTES_1000_CONST: [u8; 4]
    ensures
        BYTES_1000_CONST@ == SPEC_BYTES_1000_CONST,
{
    let a: [u8; 4] = [1, 0, 0, 0];
    assert(a@ == SPEC_BYTES_1000_CONST);
    a
}

spec const SPEC_BYTES_16_0S_CONST: Seq<u8> = seq![0; 16];

exec const BYTES_16_0S_CONST: [u8; 16]
    ensures
        BYTES_16_0S_CONST@ == SPEC_BYTES_16_0S_CONST,
{
    let a: [u8; 16] = [0;16];
    assert(a@ == SPEC_BYTES_16_0S_CONST);
    a
}

pub struct ExampleBuilder;

impl View for ExampleBuilder {
    type V = ExampleBuilder;

    open spec fn view(&self) -> Self::V {
        ExampleBuilder
    }
}

impl Builder for ExampleBuilder {
    open spec fn value(&self) -> Seq<u8> {
        seq![0, 0, 0, 0]
    }

    proof fn value_wf(&self) {
    }

    fn length(&self) -> usize {
        4
    }

    fn into_mut_vec(&self, data: &mut Vec<u8>, pos: usize) {
        assert(pos + 4 <= old(data)@.len());
        assert(pos < old(data)@.len());
        data.set(pos, 0);
        data.set(pos + 1, 0);
        data.set(pos + 2, 0);
        data.set(pos + 3, 0);
        assert(data@ =~= old(data)@.subrange(0, pos as int).add(self.value()).add(
            old(data)@.subrange(pos + 4, old(data)@.len() as int),
        ));
    }
}

spec fn wg_msg1() -> (
    Tag<BytesN<4>, Seq<u8>>,
    (Bytes, (Bytes, (Bytes, (Bytes, (Bytes, Tag<BytesN<16>, Seq<u8>>))))),
) {
    let grouplen = 32;
    let cipherlen_group = 48;
    let cipherlen_12 = 28;
    let maclen = 16;
    let tag = Tag::spec_new(BytesN::<4>, SPEC_BYTES_1000_CONST);
    let sender = Bytes(4);
    let eph = Bytes(grouplen);
    let statik = Bytes(cipherlen_group);
    let timestamp = Bytes(cipherlen_12);
    let mac1 = Bytes(maclen);
    let mac2 = Tag::spec_new(BytesN::<16>, SPEC_BYTES_16_0S_CONST);
    (tag, (sender, (eph, (statik, (timestamp, (mac1, mac2))))))
}

fn mk_wg_msg1() -> (res: (
    Tag<BytesN<4>, [u8; 4]>,
    (Bytes, (Bytes, (Bytes, (Bytes, (Bytes, Tag<BytesN<16>, [u8; 16]>))))),
))
    ensures
        res@ == wg_msg1(),
{
    let grouplen = 32;
    let cipherlen_group = 48;
    let cipherlen_12 = 28;
    let maclen = 16;
    let tag = Tag::new(BytesN::<4>, BYTES_1000_CONST);
    let sender = Bytes(4);
    let eph = Bytes(grouplen);
    let statik = Bytes(cipherlen_group);
    let timestamp = Bytes(cipherlen_12);
    let mac1 = Bytes(maclen);
    let mac2 = Tag::new(BytesN::<16>, BYTES_16_0S_CONST);
    (tag, (sender, (eph, (statik, (timestamp, (mac1, mac2))))))
}

spec fn wg_msg1_builder() -> (
    Tag<BytesN<4>, Seq<u8>>,
    (
        Bytes,
        (Bytes, (BuilderCombinator<ExampleBuilder>, (Bytes, (Bytes, Tag<BytesN<16>, Seq<u8>>)))),
    ),
) {
    let grouplen = 32;
    let cipherlen_12 = 28;
    let maclen = 16;
    let tag = Tag::spec_new(BytesN::<4>, SPEC_BYTES_1000_CONST);
    let sender = Bytes(4);
    let eph = Bytes(grouplen);
    let statik = BuilderCombinator(ExampleBuilder);
    let timestamp = Bytes(cipherlen_12);
    let mac1 = Bytes(maclen);
    let mac2 = Tag::spec_new(BytesN::<16>, SPEC_BYTES_16_0S_CONST);
    (tag, (sender, (eph, (statik, (timestamp, (mac1, mac2))))))
}

fn mk_msg1_builder() -> (res: (
    Tag<BytesN<4>, [u8; 4]>,
    (
        Bytes,
        (Bytes, (BuilderCombinator<ExampleBuilder>, (Bytes, (Bytes, Tag<BytesN<16>, [u8; 16]>)))),
    ),
))
    ensures
        res@ == wg_msg1_builder(),
{
    let grouplen = 32;
    let cipherlen_12 = 28;
    let maclen = 16;
    let tag = Tag::new(BytesN::<4>, BYTES_1000_CONST);
    let sender = Bytes(4);
    let eph = Bytes(grouplen);
    let statik = BuilderCombinator(ExampleBuilder);
    let timestamp = Bytes(cipherlen_12);
    let mac1 = Bytes(maclen);
    let mac2 = Tag::new(BytesN::<16>, BYTES_16_0S_CONST);
    (tag, (sender, (eph, (statik, (timestamp, (mac1, mac2))))))
}

} // verus!
