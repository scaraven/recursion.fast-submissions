-- GOLF module merge (lvm2): the content of `LvmQKeccakParts` now lives in `LvmQKeccakLayer`. This stub keeps `import LvmQKeccakParts`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQKeccakLayer
