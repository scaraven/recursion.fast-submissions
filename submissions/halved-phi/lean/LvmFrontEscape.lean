-- GOLF module merge (lvm2): the content of `LvmFrontEscape` now lives in `LvmFrontMech`. This stub keeps `import LvmFrontEscape`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmFrontMech
