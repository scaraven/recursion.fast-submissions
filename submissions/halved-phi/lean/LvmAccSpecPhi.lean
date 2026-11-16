-- GOLF module merge (lvm2): the content of `LvmAccSpecPhi` now lives in `LvmAccSpecT`. This stub keeps `import LvmAccSpecPhi`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmAccSpecT
