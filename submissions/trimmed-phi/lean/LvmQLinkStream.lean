-- GOLF module merge (lvm2): the content of `LvmQLinkStream` now lives in `LvmQLinkBridge`. This stub keeps `import LvmQLinkStream`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQLinkBridge
