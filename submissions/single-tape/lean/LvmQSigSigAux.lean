-- GOLF module merge (lvm2): the content of `LvmQSigSigAux` now lives in `LvmQSigSound`. This stub keeps `import LvmQSigSigAux`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQSigSound
