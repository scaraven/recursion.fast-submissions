-- GOLF module merge (lvm2): the content of `LvmQTypedSBits` now lives in `LvmTypedLayQ`. This stub keeps `import LvmQTypedSBits`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmTypedLayQ
