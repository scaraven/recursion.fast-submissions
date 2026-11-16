-- GOLF module merge (lvm2): the content of `LvmJBSelect` now lives in `LvmJBComplete`. This stub keeps `import LvmJBSelect`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmJBComplete
