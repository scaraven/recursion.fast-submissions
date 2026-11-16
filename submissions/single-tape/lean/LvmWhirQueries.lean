-- GOLF module merge (lvm2): the content of `LvmWhirQueries` now lives in `LvmWhirGroupEscape`. This stub keeps `import LvmWhirQueries`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirGroupEscape
