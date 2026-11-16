-- GOLF module merge (lvm2): the content of `LvmQSigXs` now lives in `LvmQSigSound`. This stub keeps `import LvmQSigXs`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQSigSound
