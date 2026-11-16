-- GOLF module merge (lvm2): the content of `LvmWhirSpecJ` now lives in `LvmWhirParamsJ`. This stub keeps `import LvmWhirSpecJ`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirParamsJ
