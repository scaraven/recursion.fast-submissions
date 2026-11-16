-- GOLF module merge (lvm2): the content of `LvmXRead` now lives in `LvmXRead2`. This stub keeps `import LvmXRead`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXRead2
