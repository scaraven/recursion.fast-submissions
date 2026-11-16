-- GOLF module merge (lvm2): the content of `LvmForest` now lives in `LvmCompileCert`. This stub keeps `import LvmForest`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCompileCert
