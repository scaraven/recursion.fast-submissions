-- GOLF module merge (lvm2): the content of `LvmFrontBusTable` now lives in `LvmM3Fid`. This stub keeps `import LvmFrontBusTable`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmM3Fid
