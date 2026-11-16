-- GOLF module merge (lvm2): the content of `LvmM3MidPost` now lives in `LvmM3MidCert`. This stub keeps `import LvmM3MidPost`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmM3MidCert
