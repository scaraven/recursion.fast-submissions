-- GOLF module merge (lvm2): the content of `LvmQEqKeccakLayer` now lives in `LvmQEqKeccakGkr`. This stub keeps `import LvmQEqKeccakLayer`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQEqKeccakGkr
