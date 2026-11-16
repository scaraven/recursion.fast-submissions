-- GOLF module merge (lvm2): the content of `LvmMPXAgree1` now lives in `LvmMPXDec1Sem`. This stub keeps `import LvmMPXAgree1`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmMPXDec1Sem
