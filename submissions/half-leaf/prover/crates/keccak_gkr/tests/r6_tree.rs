//! lvm6 R6: `Tree::new`'s eight-way permutation gives every row's output state, and `Tree::output_claim` is leanVM's
//! `OutputClaim::of_inputs` on the rows (FORMAT6 §6.2 rows 4–5 unchanged).

use experimental_keccak_gkr::OutputClaim;
use experimental_keccak_gkr::tree::{Tree, node_lanes};
use primitives::field::F128;

#[test]
fn r6_outputs_and_output_claim() {
    let mut x = 0x0f1e_2d3c_4b5a_6978u64;
    let blocks: Vec<[u64; 4]> = (0..1 << 12)
        .map(|_| {
            std::array::from_fn(|_| {
                x ^= x << 13;
                x ^= x >> 7;
                x ^= x << 17;
                x
            })
        })
        .collect();
    let tree = Tree::new(blocks);
    for row in 0..tree.rows() {
        let mut s = tree.inputs[row];
        primitives::hash::keccak_f(&mut s);
        assert_eq!(tree.outputs[row], s, "row {row}");
        assert_eq!(tree.digests[row], [s[0], s[1], s[2], s[3]], "row {row}");
    }
    for row in 1..tree.rows() / 2 {
        assert_eq!(tree.inputs[row], node_lanes(&tree.digests[2 * row], &tree.digests[2 * row + 1]));
    }
    assert_eq!(tree.inputs[0], node_lanes(&[0; 4], &tree.digests[1]));
    // The raw slots of the stack are `raw` (written a column at a time since R6).
    let (_, stack) = tree.witness();
    let n = tree.rows();
    for m in 0..8 {
        for row in 0..n {
            assert_eq!(stack[m * n + row].0, tree.raw(row, m), "slot {m} row {row}");
        }
    }
    let instance: Vec<F128> =
        (0..tree.shape().n_log()).map(|i| F128::new(0x9e37_79b9 * (i as u64 + 1), i as u64)).collect();
    assert_eq!(tree.output_claim(instance.clone()), OutputClaim::of_inputs(tree.shape(), &tree.inputs, instance));
}
