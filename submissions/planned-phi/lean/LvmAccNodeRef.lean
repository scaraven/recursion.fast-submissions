-- GOLF module merge (lvm2): the content of `LvmAccNodeRef` now lives in `LvmAccNodeFold`. This stub keeps `import LvmAccNodeRef`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmAccNodeFold
