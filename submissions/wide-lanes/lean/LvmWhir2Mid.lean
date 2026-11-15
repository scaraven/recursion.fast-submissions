-- GOLF module merge (lvm2): the content of `LvmWhir2Mid` now lives in `LvmCertSExt`. This stub keeps `import LvmWhir2Mid`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertSExt
