-- GOLF module merge (lvm2): the content of `LvmJBSwap` now lives in `LvmJBComplete`. This stub keeps `import LvmJBSwap`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmJBComplete
