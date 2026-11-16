-- GOLF module merge (lvm2): the content of `LvmXReadDefs` now lives in `LvmXRead2`. This stub keeps `import LvmXReadDefs`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXRead2
