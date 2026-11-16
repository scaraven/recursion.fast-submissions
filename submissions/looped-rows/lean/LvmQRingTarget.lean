-- GOLF module merge (lvm2): the content of `LvmQRingTarget` now lives in `LvmQRingG`. This stub keeps `import LvmQRingTarget`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQRingG
