-- GOLF module merge (lvm2): the content of `LvmVEqPhases` now lives in `LvmVEqRel`. This stub keeps `import LvmVEqPhases`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmVEqRel
