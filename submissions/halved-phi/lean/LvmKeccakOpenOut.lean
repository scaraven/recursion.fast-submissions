-- GOLF module merge (lvm2): the content of `LvmKeccakOpenOut` now lives in `LvmKeccakGkr`. This stub keeps `import LvmKeccakOpenOut`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmKeccakGkr
