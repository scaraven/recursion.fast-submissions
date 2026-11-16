-- GOLF module merge (lvm2): the content of `LvmMPXDec0Sem` now lives in `LvmMPXNodeSem`. This stub keeps `import LvmMPXDec0Sem`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmMPXNodeSem
