-- GOLF module merge (lvm2): the content of `LvmXSort` now lives in `LvmXLookup`. This stub keeps `import LvmXSort`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXLookup
