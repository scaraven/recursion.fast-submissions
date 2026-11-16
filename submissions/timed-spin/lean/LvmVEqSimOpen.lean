-- GOLF module merge (lvm2): the content of `LvmVEqSimOpen` now lives in `LvmVEqSim`. This stub keeps `import LvmVEqSimOpen`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmVEqSim
