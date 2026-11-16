-- GOLF module merge (lvm2): the content of `LvmKeccakOpenIn` now lives in `LvmKeccakGkr`. This stub keeps `import LvmKeccakOpenIn`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmKeccakGkr
