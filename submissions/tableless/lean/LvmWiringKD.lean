-- GOLF module merge (lvm2): the content of `LvmWiringKD` now lives in `LvmWiring`. This stub keeps `import LvmWiringKD`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWiring
