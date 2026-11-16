-- GOLF module merge (lvm2): the content of `LvmFrontEqKernel` now lives in `LvmM3Mid`. This stub keeps `import LvmFrontEqKernel`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmM3Mid
