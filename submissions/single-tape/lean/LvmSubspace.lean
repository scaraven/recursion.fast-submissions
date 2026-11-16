-- GOLF module merge (lvm2): the content of `LvmSubspace` now lives in `LvmNovelBasis`. This stub keeps `import LvmSubspace`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmNovelBasis
