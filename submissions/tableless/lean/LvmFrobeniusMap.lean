-- GOLF module merge (lvm2): the content of `LvmFrobeniusMap` now lives in `LvmRingFidelity`. This stub keeps `import LvmFrobeniusMap`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmRingFidelity
