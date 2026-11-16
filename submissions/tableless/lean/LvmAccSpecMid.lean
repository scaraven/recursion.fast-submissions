-- GOLF module merge (lvm2): the content of `LvmAccSpecMid` now lives in `LvmCertSMid3`. This stub keeps `import LvmAccSpecMid`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertSMid3
