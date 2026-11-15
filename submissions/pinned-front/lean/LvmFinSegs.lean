-- GOLF module merge (lvm2): the content of `LvmFinSegs` now lives in `LvmQTypedGuard`. This stub keeps `import LvmFinSegs`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQTypedGuard
