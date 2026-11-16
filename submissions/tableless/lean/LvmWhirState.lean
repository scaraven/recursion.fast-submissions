-- GOLF module merge (lvm2): the content of `LvmWhirState` now lives in `LvmWhirFolds`. This stub keeps `import LvmWhirState`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirFolds
