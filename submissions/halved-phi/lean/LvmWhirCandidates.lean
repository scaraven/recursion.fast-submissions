-- GOLF module merge (lvm2): the content of `LvmWhirCandidates` now lives in `LvmWhirStart`. This stub keeps `import LvmWhirCandidates`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirStart
