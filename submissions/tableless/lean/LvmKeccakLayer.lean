-- GOLF module merge (lvm2): the content of `LvmKeccakLayer` now lives in `LvmKeccakCandidate`. This stub keeps `import LvmKeccakLayer`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmKeccakCandidate
