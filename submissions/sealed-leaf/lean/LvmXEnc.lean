-- GOLF module merge (lvm2): the content of `LvmXEnc` now lives in `LvmXDec`. This stub keeps `import LvmXEnc`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXDec
