-- GOLF module merge (lvm2): the content of `LvmXLog` now lives in `LvmXLookup`. This stub keeps `import LvmXLog`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXLookup
