-- GOLF module merge (lvm2): the content of `LvmWhirCandBase` now lives in `LvmWhirStart`. This stub keeps `import LvmWhirCandBase`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirStart
