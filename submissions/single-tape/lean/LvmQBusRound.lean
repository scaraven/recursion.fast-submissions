-- GOLF module merge (lvm2): the content of `LvmQBusRound` now lives in `LvmQAsmArith2Bus`. This stub keeps `import LvmQBusRound`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQAsmArith2Bus
