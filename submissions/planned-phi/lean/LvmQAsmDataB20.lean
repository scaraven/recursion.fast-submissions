-- GOLF module merge (lvm2): the content of `LvmQAsmDataB20` now lives in `LvmCertTInst`. This stub keeps `import LvmQAsmDataB20`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertTInst
