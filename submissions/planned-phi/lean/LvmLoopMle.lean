-- GOLF module merge (lvm2): the content of `LvmLoopMle` now lives in `LvmSelfEval`. This stub keeps `import LvmLoopMle`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmSelfEval
