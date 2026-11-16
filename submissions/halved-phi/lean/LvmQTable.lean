-- GOLF module merge (lvm2): the content of `LvmQTable` now lives in `LvmQAsmArith2Tab`. This stub keeps `import LvmQTable`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQAsmArith2Tab
