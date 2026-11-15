-- GOLF module merge (lvm2): the content of `LvmQShapeF` now lives in `LvmQShapeB`. This stub keeps `import LvmQShapeF`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQShapeB
