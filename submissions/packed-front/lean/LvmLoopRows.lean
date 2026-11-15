-- GOLF module merge (lvm2): the content of `LvmLoopRows` now lives in `LvmLoopPieces`. This stub keeps `import LvmLoopRows`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmLoopPieces
