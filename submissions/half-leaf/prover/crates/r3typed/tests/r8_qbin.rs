//! R8: the binary forms of `Q` (`qbin`): both encodings decode to the loaded circuit, sections included, and a
//! damaged file is refused.

use r3typed::circuit::{AuxBits, BOut, Csum, MbExport, PowBits};
use r3typed::qbin::{Loaded, decode, encode};

fn sample() -> Loaded {
    let c = r3typed::stub::generate(r3typed::stub::SEED);
    Loaded {
        c,
        pow: vec![PowBits { w: 5, bw: 1 << 20, nb: 50 }],
        bits: vec![AuxBits { y: 7, dst: vec![Some(9), None, Some(1 << 20)] }],
        bout: vec![BOut { y: 3, k: 3, a: 1 + 64 * 4 + 4096 * 8, d: 11 }],
        csum: vec![Csum { bw: 100, c: (0..10).collect(), bd: (0..256).map(|i| 1000 + i).collect() }],
        xsrc: vec![(0, 1, 77), (3, 0, 2)],
        minibus: Some(MbExport { seeds: vec![(1, 16, 1, 4, vec![123], 456)], reads: vec![(1, 2, 64, vec![65], 66)] }),
    }
}

#[test]
fn round_trip() {
    let l = sample();
    let id = [7u8; 32];
    for raw in [false, true] {
        let b = encode(&l, &id, &[3; 32], raw);
        let (did, dl) = decode(&b).unwrap();
        assert_eq!(did, id);
        assert!(dl == l, "raw {raw}");
        // every truncation and a changed length or magic are refused
        assert!(decode(&b[..b.len() - 1]).is_err());
        let mut bad = b.clone();
        bad[0] ^= 1;
        assert!(decode(&bad).is_err());
        let mut bad = b.clone();
        let n = bad.len();
        bad[n - 1] ^= 0x01;
        assert!(decode(&bad).is_err(), "END changed");
        // a changed payload byte fails the checksum
        let mut bad = b.clone();
        bad[100] ^= 0x10;
        assert!(decode(&bad).is_err(), "payload byte changed");
    }
    let mut l2 = l.clone();
    l2.minibus = None;
    assert!(decode(&encode(&l2, &id, &[0; 32], false)).unwrap().1 == l2);
}
