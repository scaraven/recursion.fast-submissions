-- GOLF module merge (lvm2): the content of `LvmQTypedProg` now lives in `LvmTypedLayQ`. This stub keeps `import LvmQTypedProg`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmTypedLayQ
