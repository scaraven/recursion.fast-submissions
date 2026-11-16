-- GOLF module merge (lvm2): the content of `LvmCertSOpen` now lives in `LvmCertSNo`. This stub keeps `import LvmCertSOpen`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertSNo
