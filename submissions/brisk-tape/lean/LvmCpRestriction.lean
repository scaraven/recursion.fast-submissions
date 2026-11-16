-- GOLF module merge (lvm2): the content of `LvmCpRestriction` now lives in `LvmGrandProductSecurity`. This stub keeps `import LvmCpRestriction`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmGrandProductSecurity
