-- GOLF module merge (lvm2): the content of `LvmWhirGeneric` now lives in `LvmWhirFolds`. This stub keeps `import LvmWhirGeneric`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirFolds
