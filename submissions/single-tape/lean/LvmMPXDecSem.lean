-- GOLF module merge (lvm2): the content of `LvmMPXDecSem` now lives in `LvmMPXDec1Sem`. This stub keeps `import LvmMPXDecSem`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmMPXDec1Sem
