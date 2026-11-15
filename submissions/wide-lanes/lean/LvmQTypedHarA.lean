-- GOLF module merge (lvm2): the content of `LvmQTypedHarA` now lives in `LvmQTypedHarS`. This stub keeps `import LvmQTypedHarA`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQTypedHarS
