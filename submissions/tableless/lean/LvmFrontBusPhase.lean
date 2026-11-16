-- GOLF module merge (lvm2): the content of `LvmFrontBusPhase` now lives in `LvmM3Fid`. This stub keeps `import LvmFrontBusPhase`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmM3Fid
