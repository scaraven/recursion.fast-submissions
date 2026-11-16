-- GOLF module merge (lvm2): the content of `LvmCertSMid2` now lives in `LvmCertSMid3`. This stub keeps `import LvmCertSMid2`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertSMid3
