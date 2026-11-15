-- GOLF module merge (lvm2): the content of `LvmM3Phase` now lives in `LvmM3Fid`. This stub keeps `import LvmM3Phase`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmM3Fid
