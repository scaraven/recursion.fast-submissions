-- GOLF module merge (lvm2): the content of `LvmCertT20` now lives in `LvmCertM20`. This stub keeps `import LvmCertT20`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertM20
