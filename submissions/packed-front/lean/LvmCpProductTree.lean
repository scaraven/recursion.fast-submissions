-- GOLF module merge (lvm2): the content of `LvmCpProductTree` now lives in `LvmGrandProduct`. This stub keeps `import LvmCpProductTree`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmGrandProduct
