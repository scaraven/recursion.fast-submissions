-- GOLF module merge (lvm2): the content of `LvmXInterp3` now lives in `LvmXInterp4`. This stub keeps `import LvmXInterp3`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXInterp4
