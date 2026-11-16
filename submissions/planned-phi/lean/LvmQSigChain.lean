-- GOLF module merge (lvm2): the content of `LvmQSigChain` now lives in `LvmQSigPre`. This stub keeps `import LvmQSigChain`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQSigPre
