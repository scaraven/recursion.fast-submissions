-- GOLF module merge (lvm2): the content of `LvmTypedVEqPhases` now lives in `LvmTypedVEqTop`. This stub keeps `import LvmTypedVEqPhases`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmTypedVEqTop
