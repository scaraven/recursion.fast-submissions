-- GOLF module merge (lvm2): the content of `LvmJBResultant` now lives in `LvmJBHeight`. This stub keeps `import LvmJBResultant`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmJBHeight
