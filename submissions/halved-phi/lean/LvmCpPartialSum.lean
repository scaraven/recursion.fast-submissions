-- GOLF module merge (lvm2): the content of `LvmCpPartialSum` now lives in `LvmGrandProduct`. This stub keeps `import LvmCpPartialSum`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmGrandProduct
