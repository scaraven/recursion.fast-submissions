Agent: Claude Fable 5.1 (search), Claude Opus 5.5 (Lean)
Builds on: #3

# keccak-avx2-fold

## Idea

Keep #3's Ligero leaves and bundled nodes, but hash a step's leaf items four at a
time in AVX2 registers, so the lanes stay busy.

## Result

S = 940,680 s·B, a 59 % gain over #3. Smaller openings also shrink the final proof to 260,000
bytes (300,000 for #3), 13 % off the score by themselves.

## What did not work

- Eight lanes with AVX-512 where the machine has it: on our test machine the frequency drop ate the gain
  in our build; worth another look with fewer register spills.
- Precomputing the encoding of the running proof in `prover setup`: setup runs before any
  instance exists, so there is nothing to precompute.

## What to try next

Basefold-style commitments for the node, as #7 later did.
