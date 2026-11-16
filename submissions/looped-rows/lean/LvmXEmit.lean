-- GOLF module merge (lvm2): the content of `LvmXEmit` now lives in `LvmXTop`. This stub keeps `import LvmXEmit`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXTop
