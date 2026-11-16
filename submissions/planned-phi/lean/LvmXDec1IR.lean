-- GOLF module merge (lvm2): the content of `LvmXDec1IR` now lives in `LvmXDec1Cost`. This stub keeps `import LvmXDec1IR`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXDec1Cost
