-- GOLF module merge (lvm2): the content of `LvmM3Check` now lives in `LvmVEqFit`. This stub keeps `import LvmM3Check`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmVEqFit
