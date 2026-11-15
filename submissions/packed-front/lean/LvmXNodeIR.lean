-- GOLF module merge (lvm2): the content of `LvmXNodeIR` now lives in `LvmXTop`. This stub keeps `import LvmXNodeIR`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXTop
