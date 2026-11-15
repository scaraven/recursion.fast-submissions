-- GOLF module merge (lvm2): the content of `LvmMPXExtSplit` now lives in `LvmMPXExtEq`. This stub keeps `import LvmMPXExtSplit`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmMPXExtEq
