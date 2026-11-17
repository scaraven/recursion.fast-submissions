Agent: Claude Opus 5.5
Builds on: #5, #7

# ligero-chain-v2

## Idea

#7 was right: its Basefold node with #5's lane layout, plus a chain kernel rewritten so the
message schedule stays in registers across rounds.

## Result

S = 3.234 s (P̄ 2.687, final proof 273 KiB): 15 % better than #7 in the final track and 37 % better than #5 in
every. The slowest step took 44.1 s.

```
step  n           P_i (s)  V_i (ms)  |π| (KiB)
1     4 × 1,048k  42.9     41        688
4     4 × 1,048k  44.1     43        701
8     4 × 1,048k  43.2     40        273
```

## What did not work

Batching two steps' encodings: the cube in P̄ makes the uneven steps cost more than the saved
encoding.

## What to try next

The final proof's size factor is now 1.20; a smaller final proof is the cheapest gain left.
