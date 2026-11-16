-- GOLF module merge (lvm2): the content of `LvmMPXTop` now lives in `LvmMPXComputes`. This stub keeps `import LvmMPXTop`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmMPXComputes
