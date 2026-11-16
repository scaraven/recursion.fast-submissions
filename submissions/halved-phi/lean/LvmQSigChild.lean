-- GOLF module merge (lvm2): the content of `LvmQSigChild` now lives in `LvmQSigSound`. This stub keeps `import LvmQSigChild`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQSigSound
