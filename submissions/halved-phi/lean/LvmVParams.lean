-- GOLF module merge (lvm2): the content of `LvmVParams` now lives in `LvmVCore`. This stub keeps `import LvmVParams`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmVCore
