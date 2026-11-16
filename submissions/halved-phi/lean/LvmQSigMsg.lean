-- GOLF module merge (lvm2): the content of `LvmQSigMsg` now lives in `LvmQSigDefs`. This stub keeps `import LvmQSigMsg`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQSigDefs
