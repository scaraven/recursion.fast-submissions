-- GOLF module merge (lvm2): the content of `LvmProg` now lives in `LvmCompile`. This stub keeps `import LvmProg`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCompile
