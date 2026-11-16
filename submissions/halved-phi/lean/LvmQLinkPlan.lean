-- GOLF module merge (lvm2): the content of `LvmQLinkPlan` now lives in `LvmQLinkSound`. This stub keeps `import LvmQLinkPlan`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQLinkSound
