-- GOLF module merge (lvm2): the content of `LvmVEqLink` now lives in `LvmVEqTop`. This stub keeps `import LvmVEqLink`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmVEqTop
