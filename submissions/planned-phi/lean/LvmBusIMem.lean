-- GOLF module merge (lvm2): the content of `LvmBusIMem` now lives in `LvmM3Loop`. This stub keeps `import LvmBusIMem`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmM3Loop
