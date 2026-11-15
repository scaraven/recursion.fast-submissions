-- GOLF module merge (lvm2): the content of `LvmKeccakWords` now lives in `LvmKeccakCandidate`. This stub keeps `import LvmKeccakWords`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmKeccakCandidate
