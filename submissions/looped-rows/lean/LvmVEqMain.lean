-- GOLF module merge (lvm2): the content of `LvmVEqMain` now lives in `LvmTypedVEqTop`. This stub keeps `import LvmVEqMain`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmTypedVEqTop
