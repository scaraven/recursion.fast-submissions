-- GOLF module merge (lvm2): the content of `LvmCertSLuckJ` now lives in `LvmCertSExtJSplit`. This stub keeps `import LvmCertSLuckJ`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertSExtJSplit
