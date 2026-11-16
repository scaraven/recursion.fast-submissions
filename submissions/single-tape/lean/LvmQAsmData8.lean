-- GOLF module merge (lvm2): the content of `LvmQAsmData8` now lives in `LvmQAsmArith2`. This stub keeps `import LvmQAsmData8`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQAsmArith2
