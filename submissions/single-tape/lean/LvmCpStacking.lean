-- GOLF module merge (lvm2): the content of `LvmCpStacking` now lives in `LvmCpAmbientStacking`. This stub keeps `import LvmCpStacking`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCpAmbientStacking
