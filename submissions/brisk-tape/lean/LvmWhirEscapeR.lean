-- GOLF module merge (lvm2): the content of `LvmWhirEscapeR` now lives in `LvmWhirMidR`. This stub keeps `import LvmWhirEscapeR`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirMidR
