-- GOLF module merge (lvm2): the content of `LvmJBCTUniformFamily` now lives in `LvmWhirParamsJ`. This stub keeps `import LvmJBCTUniformFamily`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWhirParamsJ
