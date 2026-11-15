-- GOLF module merge (lvm2): the content of `LvmQKeccakRounds` now lives in `LvmQKeccakLayer`. This stub keeps `import LvmQKeccakRounds`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQKeccakLayer
