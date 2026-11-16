-- GOLF module merge (lvm2): the content of `LvmWhirEscape` now lives in `LvmWhirFolds`. This stub keeps `import LvmWhirEscape`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirFolds
