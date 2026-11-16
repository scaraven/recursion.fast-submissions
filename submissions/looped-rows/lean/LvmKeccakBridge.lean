-- GOLF module merge (lvm2): the content of `LvmKeccakBridge` now lives in `LvmKeccakCallerRing`. This stub keeps `import LvmKeccakBridge`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmKeccakCallerRing
