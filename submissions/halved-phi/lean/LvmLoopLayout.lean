-- GOLF module merge (lvm2): the content of `LvmLoopLayout` now lives in `LvmLoopInterp`. This stub keeps `import LvmLoopLayout`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmLoopInterp
