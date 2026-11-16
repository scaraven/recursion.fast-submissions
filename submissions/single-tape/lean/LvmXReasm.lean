-- GOLF module merge (lvm2): the content of `LvmXReasm` now lives in `LvmXSpec`. This stub keeps `import LvmXReasm`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXSpec
