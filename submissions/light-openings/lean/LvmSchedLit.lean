import LvmSchedule

/-! # `phases P20` as a literal (GOLF-MID)

The `decide +kernel` checks over `P20`'s schedule (`qcItems_P20`, `stA_P20`, `blocks_segs`, `phB20`,
`midItems_noPosB`) each rebuilt the 2,489 items of `phases P20` from `smp`/`rd`/`sumcheckI`/… (2.6M kernel
heartbeats, ≈ 0.6 s, each). They rewrite with `phases_P20_lit` instead and read the literal: one kernel comparison
here (≈ 3.6M heartbeats), about 1.3M heartbeats saved per check. -/

namespace Lvm

/-- The items of phase `.commit` at `P20`. -/
def ph20_commit : List Item := [
    .cap 8 ⟨.main, 0⟩]

/-- The items of phase `.bus` at `P20`. -/
def ph20_bus : List Item := [
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample,
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 3, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 4, .read 4, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 1, .sample, .sample, .read 44, .sample, .read 1, .sample, .sample, .sample, .sample, .sample, .read 2,
    .sample, .read 12, .sample, .sample, .sample, .read 4, .sample, .read 4, .sample, .read 12, .sample, .sample,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 12, .sample, .sample,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4,
    .sample, .read 12, .sample, .sample, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 12, .sample, .sample,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4,
    .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 4, .sample, .read 12, .sample, .sample,
    .read 1]

/-- The items of phase `.tables` at `P20`. -/
def ph20_tables : List Item := [
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 633]

/-- The items of phase `.tape` at `P20`. -/
def ph20_tape : List Item := [
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample,
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .read 25, .sample, .sample, .sample, .sample,
    .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample]

/-- The items of phase `.wire` at `P20`. -/
def ph20_wire : List Item := [
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 1, .read 2, .sample, .read 2, .sample, .read 64, .sample, .sample,
    .sample, .sample, .sample, .sample]

/-- The items of phase `.ks` at `P20`. -/
def ph20_ks : List Item := [
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample,
    .read 25, .sample, .sample, .sample, .sample, .sample, .sample, .read 1, .read 105, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 105, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 105, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 3, .sample, .read 3, .sample, .read 3,
    .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 3, .sample,
    .read 3, .sample, .read 3, .sample, .read 3, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 1, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 64, .sample, .sample, .sample, .sample, .sample, .sample]

/-- The items of phase `.ksLink` at `P20`. -/
def ph20_ksLink : List Item := [
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample,
    .sample, .sample, .sample, .sample, .sample, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 4]

/-- The items of phase `.openMain` at `P20`. -/
def ph20_openMain : List Item := [
    .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .cap 7 ⟨.main, 1⟩, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample,
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .read 1, .read 2, .sample,
    .read 1, .sample, .positions ⟨.main, 0⟩, .sample, .opening ⟨.main, 0⟩, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .cap 7 ⟨.main, 2⟩, .sample, .sample, .sample, .sample, .sample,
    .sample, .sample, .sample, .sample, .sample, .sample, .sample, .sample, .read 1, .read 2, .sample, .read 1,
    .sample, .positions ⟨.main, 1⟩, .sample, .opening ⟨.main, 1⟩, .read 2, .sample, .read 2, .sample, .read 2,
    .sample, .read 2, .sample, .read 2, .read 512, .sample, .read 1, .sample, .positions ⟨.main, 2⟩, .sample,
    .opening ⟨.main, 2⟩, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample,
    .read 2, .sample, .read 2, .sample, .read 2, .sample, .read 2, .sample]

/-- **`phases P20`**, phase by phase (`phases_P20_lit`). -/
def phases20 : List (Phase × List Item) :=
  [(.commit, ph20_commit),
   (.bus, ph20_bus),
   (.tables, ph20_tables),
   (.tape, ph20_tape),
   (.wire, ph20_wire),
   (.ks, ph20_ks),
   (.ksLink, ph20_ksLink),
   (.openMain, ph20_openMain)]

/-- **The phases at `P20` are `phases20`** (one kernel evaluation of `phases P20` and one comparison). -/
theorem phases_P20_lit : phases P20 = phases20 := by
  decide +kernel

end Lvm
