-- GOLF module merge (lvm2): the content of `LvmCertS2Mid` now lives in `LvmCertSExt`. This stub keeps `import LvmCertS2Mid`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertSExt
