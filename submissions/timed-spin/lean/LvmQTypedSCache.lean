-- GOLF module merge (lvm2): the content of `LvmQTypedSCache` now lives in `LvmQTypedGuard`. This stub keeps `import LvmQTypedSCache`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQTypedGuard
