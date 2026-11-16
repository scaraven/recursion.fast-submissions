-- GOLF module merge (lvm2): the content of `LvmColumnWeight` now lives in `LvmWhirWeights`. This stub keeps `import LvmColumnWeight`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirWeights
