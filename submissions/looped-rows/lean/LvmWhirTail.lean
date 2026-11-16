-- GOLF module merge (lvm2): the content of `LvmWhirTail` now lives in `LvmWhirLevelFinal`. This stub keeps `import LvmWhirTail`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirLevelFinal
