-- GOLF module merge (lvm2): the content of `LvmWhirDefs` now lives in `LvmWhirGroupEscape`. This stub keeps `import LvmWhirDefs`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirGroupEscape
