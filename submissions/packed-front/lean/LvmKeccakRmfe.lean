-- GOLF module merge (lvm2): the content of `LvmKeccakRmfe` now lives in `LvmKeccakLayerSum`. This stub keeps `import LvmKeccakRmfe`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmKeccakLayerSum
