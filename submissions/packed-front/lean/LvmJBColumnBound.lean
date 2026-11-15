-- GOLF module merge (lvm2): the content of `LvmJBColumnBound` now lives in `LvmJBComplete`. This stub keeps `import LvmJBColumnBound`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmJBComplete
