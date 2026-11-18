-- GOLF module merge (lvm2): the content of `LvmQAsmData20` now lives in `LvmQAsmArith2`. This stub keeps `import LvmQAsmData20`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQAsmArith2
