-- GOLF module merge (lvm2): the content of `LvmMPXChain` now lives in `LvmMPXNodeSem`. This stub keeps `import LvmMPXChain`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmMPXNodeSem
