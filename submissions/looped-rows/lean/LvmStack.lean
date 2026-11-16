-- GOLF module merge (lvm2): the content of `LvmStack` now lives in `LvmBus`. This stub keeps `import LvmStack`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmBus
