-- GOLF module merge (lvm2): the content of `LvmQAccHdr` now lives in `LvmQAcc`. This stub keeps `import LvmQAccHdr`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQAcc
