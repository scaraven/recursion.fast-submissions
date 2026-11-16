-- GOLF module merge (lvm2): the content of `LvmXSeg` now lives in `LvmXOutSeg`. This stub keeps `import LvmXSeg`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXOutSeg
