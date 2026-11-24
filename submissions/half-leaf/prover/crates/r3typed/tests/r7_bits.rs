//! R7: BITS aux rows (F2) in the witness: parsing, the dependency order with `OUT` rows, the bit values.

use primitives::field::{F64, F128};
use r3typed::circuit::{AuxBits, BOut, Circuit, Ent, Src, TReg, check_aux, check_bits, parse_bits, parse_bout};
use r3typed::witness::{Aux, Step, solve_plan, solve_plan_aux, witness_full};

fn ent(o: u8, x: u32, y: u32, c: u64) -> Ent {
    Ent { o, x, y, c: F128::new(c, 0) }
}

/// Words 0–15 `com` (on `T`), word 16 `one`. Row 1: `z1 = 11`. BITS: bits 0, 1, 3 of `z1` to words 2, 3, 5.
/// Row 0 (first in the blob, but it reads bit word 3): `z4 = z3`.
fn circ() -> (Circuit, Vec<AuxBits>) {
    let t = r3core::layout::idx(r3core::layout::SLOT_T, 0);
    let mut c = Circuit {
        regs: vec![TReg { src: Src::Com, base: 0, log: 4, off: t }, TReg { src: Src::One, base: 16, log: 0, off: 0 }],
        ents: vec![ent(2, 0, 4, 1), ent(3, 0, 3, 1), ent(2, 1, 1, 1), ent(3, 1, 16, 11)],
        outs: vec![(0, 4), (1, 1)],
        qlt: Vec::new(),
    };
    c.normalize();
    c.check();
    let text = "Q6 1\nBITS 1\n1 4 2 3 - 5\nEND\n";
    let bits = parse_bits(text).unwrap();
    assert_eq!(bits, vec![AuxBits { y: 1, dst: vec![Some(2), Some(3), None, Some(5)] }]);
    check_bits(&c, &[], &bits);
    (c, bits)
}

#[test]
fn bits_order_and_values() {
    let (c, bits) = circ();
    assert_eq!(solve_plan(&c, &bits).unwrap(), vec![Step::Row(1, vec![1]), Step::Bits(0), Step::Row(0, vec![4])]);
    let mut stack = vec![F64::ZERO; 1 << r3core::layout::STACK_LOG];
    let w = witness_full(&c, &[], Aux { bits: &bits, bout: &[], link: None, csum: &[], readd: None }, &mut stack, &[]).unwrap();
    let z: Vec<u64> = w.z[..8].iter().map(|v| v.0).collect();
    assert_eq!(z, vec![0, 11, 1, 1, 1, 1, 0, 0]);
    let t = r3core::layout::idx(r3core::layout::SLOT_T, 0);
    assert_eq!(stack[t + 5].0, 1, "bit words are com words written to T");
}

#[test]
#[should_panic(expected = "defined twice")]
fn bits_may_not_redefine_out_words() {
    let (c, _) = circ();
    check_bits(&c, &[], &[AuxBits { y: 1, dst: vec![Some(4)] }]);
}

#[test]
fn bout_kinds() {
    let v = 0xF0F0_1234_5678_9ABCu64;
    let b = |k, a| BOut { y: 0, k, a, d: 0 }.apply(v);
    assert_eq!(b(0, 4), v << 4);
    assert_eq!(b(1, 60), 0xF);
    assert_eq!(b(2, 2), 1);
    assert_eq!(b(2, 0), 0);
    // fld: 8 bits from bit 4, placed at bit 16
    assert_eq!(b(3, 4 + 64 * 8 + 4096 * 16), ((v >> 4) & 0xFF) << 16);
    assert_eq!(b(0, 64), 0);
}

/// BOUT after BITS after OUT: `z6 = z5 << 3` (5 is a bit word of `z1`), `z7 = fld(z1, 1 bit from 3, at 0)`.
#[test]
fn bout_chain() {
    let (c, bits) = circ();
    let bout = parse_bout("Q6 1\nBOUT 2\n5 0 3 6\n1 3 67 7\nEND\n").unwrap();
    assert_eq!(bout[1], BOut { y: 1, k: 3, a: 67, d: 7 });
    check_aux(&c, &[], &bits, &bout);
    let plan = solve_plan_aux(&c, Aux { bits: &bits, bout: &bout, link: None, csum: &[], readd: None }).unwrap();
    assert_eq!(plan, vec![Step::Row(1, vec![1]), Step::Bits(0), Step::Row(0, vec![4]), Step::BOut(0), Step::BOut(1)]);
    let mut stack = vec![F64::ZERO; 1 << r3core::layout::STACK_LOG];
    let w = witness_full(&c, &[], Aux { bits: &bits, bout: &bout, link: None, csum: &[], readd: None }, &mut stack, &[]).unwrap();
    assert_eq!((w.z[6].0, w.z[7].0), (8, 1));
    let _ = solve_plan(&c, &bits).unwrap();
}

/// CSUM: `C = Σ (3 − d_i)` over the 128 digits `d_i = z[bd_2i] + 2·z[bd_2i+1]`; its bits go to `bw…` and `c_k`.
#[test]
fn csum_fill() {
    use r3typed::circuit::Csum;
    let t = r3core::layout::idx(r3core::layout::SLOT_T, 0);
    // words 0–511 com, 512 one; row 0 defines z1 = 3; BITS puts its bits 0, 1 into words 256, 257 (= bd_0, bd_1)
    let mut c = Circuit {
        regs: vec![TReg { src: Src::Com, base: 0, log: 9, off: t }, TReg { src: Src::One, base: 512, log: 0, off: 0 }],
        ents: vec![ent(2, 0, 1, 1), ent(3, 0, 512, 3)],
        outs: vec![(0, 1)],
        qlt: Vec::new(),
    };
    c.normalize();
    c.check();
    // bit 0 of z1 = 3 → word 256 (bd_0) = 1, bit 1 → word 257 (bd_1) = 1: d_0 = 3
    let bits = vec![AuxBits { y: 1, dst: vec![Some(256), Some(257)] }];
    let cs = Csum { bw: 128, c: (20..30).collect(), bd: (256..512).collect() };
    let csum = [cs];
    let plan = solve_plan_aux(&c, Aux { bits: &bits, bout: &[], link: None, csum: &csum, readd: None }).unwrap();
    assert_eq!(plan, vec![Step::Row(0, vec![1]), Step::Bits(0), Step::Csum(0)]);
    let mut stack = vec![F64::ZERO; 1 << r3core::layout::STACK_LOG];
    let w = witness_full(&c, &[], Aux { bits: &bits, bout: &[], link: None, csum: &csum, readd: None }, &mut stack, &[]).unwrap();
    let v: u64 = 3 * 127; // d_0 = 3, the other 127 digits 0
    assert_eq!((0..64).map(|k| w.z[128 + k].0 << k).sum::<u64>(), v);
    assert_eq!((0..10).map(|k| w.z[20 + k].0 << k).sum::<u64>(), v);
}
