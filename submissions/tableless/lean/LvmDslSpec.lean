-- GOLF module merge (lvm2): the content of `LvmDslSpec` now lives in `LvmSpecRulesBasic`. This stub keeps `import LvmDslSpec`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmSpecRulesBasic
