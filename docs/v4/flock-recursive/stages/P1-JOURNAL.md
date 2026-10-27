# P1 journal (track P, prover core)

Running notes; the RESULT is `P1-RESULT.md`.

## 2026-10-27

- Crate at `submissions/flock-recursive/prover/` (flat layout, std only). Reused from
  `spartan-srom/prover`: `par.rs`, `blake2s.rs`, `oracle.rs`, `service.rs`, the signed-proof file
  and `SigOk` (`format.rs`, trimmed), `circuit.rs` (leanerVM's block, re-based: P1 layout in
  `params.rs`), `sanitize-asm.py`, `rust-toolchain.toml`.
- Coordinator (BP-E-M8): constants are not normative yet. Every layout/constant lives in
  `params.rs` / `skipdom.rs`, marked PLACEHOLDER. β = x^63 and α = β·y agree with S-A's
  "Normative constants" (S-A-JOURNAL.md).
- Coordinator (S-A-M1): `field::red` folded the overflow twice (`h = hi ^ ov ^ ov<<1 ^ …` instead
  of `h = hi ^ ov`). Fixed; `field_laws` and the 8 + 8 F/K KATs of `probe/fr-field/kat.out` are now
  a unit test (`field::tests::kat_products`, portable and pclmulqdq paths). No runner measurement
  had been made with the wrong reduction. The GF(2^8) embedding (`field::aes_root`) is recomputed
  with the fixed reduction and stays a placeholder (Appendix A of the blueprint fix pass will fix it).
- Encoding: the blueprint's "message = values on S (systematic)" makes the consistency weights of
  levels 0–2 non-product-form (O(k) per query to evaluate). P1 uses the novel-basis coefficients
  as the message (Flock/bolt-rs; the BP-C review asks for the same), whose weight row at position
  `p` is `Π_k (1 + c_k + c_k Ŵ_k(p))`. Checked: `ntt::tests::encode_is_novel_basis_evaluation`.
- Blueprint rev. 2 (de0d708) adopted where it is a value: β, α (unchanged), D, the novel basis,
  ζ = x^((2^64−1)/255) with S = span(ζ^0…ζ^5), Λ = S + ζ^6 (GF(2^8) multiplied modulo ζ's minimal
  polynomial, `field::gf8_poly`), the 7-byte seed tag, A.6's block layout (natural message order,
  `one` at 1152), the five-level ladder 290/178/145/132/126 (caps 9,8,8,8,7), qV = 10,240.
  Kept as P1 choices (P1-RESULT §4): the pinned point (paper progression, not A.1's candidate),
  the `e`-trick for `one`, the lincheck's 14 multilinear rounds, the shift + 10-round slot
  collapse, ring switching batched into the Ligerito weight, the final rounds.
- First end-to-end runs: m = 25 … 30 on the VM (portable), proof accepted by the native verifier,
  mutated statement / proof bytes rejected; m = 26, 30 through the real `rf-oracle` (signed file,
  native `acc` accept, canary reject).
- Runner run 40512899416 (probe/p1-1, EPYC 7763, tier pclmul, round 1 portable): m = 30 8.1 s,
  m = 32 32.3 s (round 1 21.1 s), peak RSS 1.26 / 4.92 GB, |π| 691,744 / 750,944, |tr| 6,981 /
  8,744. Logs `logs/P1/run-40512899416/`.
- Tier-1 kernels (ymm: F product, MAC, butterfly, fold, zerocheck inner; AVX2 round-1 window) with
  a `ymm-sim` twin (256-bit clmul emulated by two pclmulqdq) so the kernel bodies are tested under
  `qemu-x86_64 -cpu max` here: selftest pass, test-leaf m = 25 accept with FLOCK_TIER=ymm-sim.
- Runs p1-2 … p1-7 (ids in P1-RESULT §2.1): ymm tier verified on the 7763 (selftest checks ymm,
  pclmul, ymm-sim against portable). Successive kernels: AVX2 round 1, K-level kernels, vector
  x₆ round, word-level witness (`witness::block_fast`, equal to the tape), fused Ligerito fold +
  message, vector consistency weights, radix-4 NTT top passes. Best 7763 (p1-6): m = 30 1.75–1.81 s,
  m = 32 6.55–6.67 s, 5.49 GB. EPYC 9V74 (p1-7): 1.95–2.04 / 7.55–7.61 s.
- Rev. 3 (0d513c9) read: ρⱼ = y^(2^j) is a one-level progression in F, which defeats the
  GF(2^8) accumulation of round 1; kept P1's two-level set and reported (P1-RESULT §5 item 2).
  Rev. 3's item sequence / piSize / reassemble are P2 work against the S-0 dumps.
