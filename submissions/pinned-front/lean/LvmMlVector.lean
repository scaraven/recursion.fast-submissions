-- GOLF module merge (lvm2): the content of `LvmMlVector` now lives in `LvmMlBasic`. This stub keeps `import LvmMlVector`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmMlBasic
