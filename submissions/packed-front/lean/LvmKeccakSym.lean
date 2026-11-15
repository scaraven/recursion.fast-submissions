-- GOLF module merge (lvm2): the content of `LvmKeccakSym` now lives in `LvmTypedV`. This stub keeps `import LvmKeccakSym`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmTypedV
