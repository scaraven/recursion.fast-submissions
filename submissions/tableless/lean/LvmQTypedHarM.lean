-- GOLF module merge (lvm2): the content of `LvmQTypedHarM` now lives in `LvmQTypedHarS`. This stub keeps `import LvmQTypedHarM`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQTypedHarS
