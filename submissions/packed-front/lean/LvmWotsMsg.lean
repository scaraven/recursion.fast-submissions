-- GOLF module merge (lvm2): the content of `LvmWotsMsg` now lives in `LvmQSigDefs`. This stub keeps `import LvmWotsMsg`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQSigDefs
