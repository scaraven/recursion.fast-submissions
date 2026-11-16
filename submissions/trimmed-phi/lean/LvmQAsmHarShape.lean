-- GOLF module merge (lvm2): the content of `LvmQAsmHarShape` now lives in `LvmQAsmHarTails`. This stub keeps `import LvmQAsmHarShape`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQAsmHarTails
