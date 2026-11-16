-- GOLF module merge (lvm2): the content of `LvmFrontBusDoom` now lives in `LvmFrontBusSpec`. This stub keeps `import LvmFrontBusDoom`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmFrontBusSpec
