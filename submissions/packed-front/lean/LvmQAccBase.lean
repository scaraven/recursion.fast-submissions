-- GOLF module merge (lvm2): the content of `LvmQAccBase` now lives in `LvmQAccParts`. This stub keeps `import LvmQAccBase`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQAccParts
