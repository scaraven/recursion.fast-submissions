-- GOLF module merge (lvm2): the content of `LvmCompileKS` now lives in `LvmCertS`. This stub keeps `import LvmCompileKS`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertS
