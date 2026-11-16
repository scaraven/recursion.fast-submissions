-- GOLF module merge (lvm2): the content of `LvmMPNodePos` now lives in `LvmCertM20`. This stub keeps `import LvmMPNodePos`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertM20
