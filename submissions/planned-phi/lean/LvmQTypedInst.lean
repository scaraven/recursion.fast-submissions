-- GOLF module merge (lvm2): the content of `LvmQTypedInst` now lives in `LvmCertTInst`. This stub keeps `import LvmQTypedInst`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertTInst
