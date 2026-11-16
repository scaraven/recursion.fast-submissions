-- GOLF module merge (lvm2): the content of `LvmGrandProductPoly` now lives in `LvmBus`. This stub keeps `import LvmGrandProductPoly`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmBus
