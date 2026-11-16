-- GOLF module merge (lvm2): the content of `LvmKeccakLayerAlg` now lives in `LvmKeccakLayerSum`. This stub keeps `import LvmKeccakLayerAlg`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmKeccakLayerSum
