-- GOLF module merge (lvm2): the content of `LvmQSigCheck` now lives in `LvmQSigDefs`. This stub keeps `import LvmQSigCheck`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQSigDefs
