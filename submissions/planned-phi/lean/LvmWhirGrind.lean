-- GOLF module merge (lvm2): the content of `LvmWhirGrind` now lives in `LvmWhirLevelMidSpec`. This stub keeps `import LvmWhirGrind`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirLevelMidSpec
