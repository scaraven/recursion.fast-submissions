-- GOLF module merge (lvm2): the content of `LvmXDecIR3` now lives in `LvmXDecIR4`. This stub keeps `import LvmXDecIR3`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXDecIR4
