-- GOLF module merge (lvm2): the content of `LvmDecideM3` now lives in `LvmDecideV0`. This stub keeps `import LvmDecideM3`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmDecideV0
