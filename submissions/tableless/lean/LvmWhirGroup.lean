-- GOLF module merge (lvm2): the content of `LvmWhirGroup` now lives in `LvmWhirGroupEscape`. This stub keeps `import LvmWhirGroup`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirGroupEscape
