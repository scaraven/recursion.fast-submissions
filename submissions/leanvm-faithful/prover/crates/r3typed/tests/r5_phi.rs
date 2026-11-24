//! R5: `phi_q_many` = `phi_q` point by point (the circuit in use: the stub, or `$LVM6_Q_BLOB`).
use primitives::field::F128;
use r3typed::circuit::{PHI_VARS, circuit};

#[test]
fn phi_q_many_matches_phi_q() {
    let mut s = 0x1234_5678_9abc_def0u64;
    let mut next = || {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        s
    };
    let pts: Vec<Vec<F128>> = (0..5).map(|_| (0..PHI_VARS).map(|_| F128::new(next(), next())).collect()).collect();
    let c = circuit();
    let many = c.phi_q_many(&pts);
    for (p, m) in pts.iter().zip(&many) {
        assert_eq!(c.phi_q(p), *m);
    }
    assert_eq!(c.phi_q_many(&[vec![F128::ZERO; PHI_VARS]])[0], c.phi_q(&vec![F128::ZERO; PHI_VARS]));
}

/// Dev (R5, SDE icount): §6.4a's 44 evaluations, point by point (`phi_q`) or in one pass (`phi_q_many`).
fn line_pts() -> Vec<Vec<F128>> {
    let b: Vec<F128> = (0..PHI_VARS as u64).map(|i| F128::new(0x9E37_79B9 ^ i.wrapping_mul(0x1234_5678_9ABC), i + 7)).collect();
    (0..=PHI_VARS as u64).map(|t| b.iter().map(|&x| x * F128::new(t, 0)).collect()).collect()
}

#[test]
#[ignore]
fn bench_phi_single() {
    let c = circuit();
    let v: Vec<F128> = line_pts().iter().map(|p| c.phi_q(p)).collect();
    std::hint::black_box(v);
}

#[test]
#[ignore]
fn bench_phi_many() {
    let c = circuit();
    std::hint::black_box(c.phi_q_many(&line_pts()));
}

#[test]
#[ignore]
fn bench_phi_load() {
    std::hint::black_box(circuit());
}
