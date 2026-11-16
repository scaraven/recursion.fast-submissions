-- GOLF module merge (lvm2): the content of `LvmQAsmHarPos` now lives in `LvmFinPos`. This stub keeps `import LvmQAsmHarPos`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmFinPos
