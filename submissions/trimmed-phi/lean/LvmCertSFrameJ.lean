-- GOLF module merge (lvm2): the content of `LvmCertSFrameJ` now lives in `LvmCertSOpenJ`. This stub keeps `import LvmCertSFrameJ`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertSOpenJ
