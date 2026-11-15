-- GOLF module merge (lvm2): the content of `LvmXDecLv` now lives in `LvmXDecUd`. This stub keeps `import LvmXDecLv`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXDecUd
