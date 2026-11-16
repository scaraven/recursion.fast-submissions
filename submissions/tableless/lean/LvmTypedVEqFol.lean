-- GOLF module merge (lvm2): the content of `LvmTypedVEqFol` now lives in `LvmTypedVEqTop`. This stub keeps `import LvmTypedVEqFol`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmTypedVEqTop
