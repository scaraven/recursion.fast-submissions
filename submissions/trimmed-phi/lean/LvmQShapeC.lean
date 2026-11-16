-- GOLF module merge (lvm2): the content of `LvmQShapeC` now lives in `LvmQShapeB`. This stub keeps `import LvmQShapeC`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQShapeB
