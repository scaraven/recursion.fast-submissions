-- GOLF module merge (lvm2): the content of `LvmQSigParts` now lives in `LvmQSigDefs`. This stub keeps `import LvmQSigParts`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQSigDefs
