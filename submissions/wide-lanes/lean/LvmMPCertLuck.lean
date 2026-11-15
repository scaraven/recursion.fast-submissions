-- GOLF module merge (lvm2): the content of `LvmMPCertLuck` now lives in `LvmMPCertSplit`. This stub keeps `import LvmMPCertLuck`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmMPCertSplit
