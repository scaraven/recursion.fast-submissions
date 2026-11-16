-- GOLF module merge (lvm2): the content of `LvmChainTableLink` now lives in `LvmSpongeTableLink`. This stub keeps `import LvmChainTableLink`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmSpongeTableLink
