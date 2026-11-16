-- GOLF module merge (lvm2): the content of `LvmMPCertExt` now lives in `LvmMPCert`. This stub keeps `import LvmMPCertExt`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmMPCert
