-- GOLF module merge (lvm2): the content of `LvmAccSpecL` now lives in `LvmAccSpecT`. This stub keeps `import LvmAccSpecL`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmAccSpecT
