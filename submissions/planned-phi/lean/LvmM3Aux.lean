-- GOLF module merge (lvm2): the content of `LvmM3Aux` now lives in `LvmBitsTab`. This stub keeps `import LvmM3Aux`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmBitsTab
