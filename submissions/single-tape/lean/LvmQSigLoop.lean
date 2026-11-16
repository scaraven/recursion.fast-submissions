-- GOLF module merge (lvm2): the content of `LvmQSigLoop` now lives in `LvmQSig`. This stub keeps `import LvmQSigLoop`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQSig
