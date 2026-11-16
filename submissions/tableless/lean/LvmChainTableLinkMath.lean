-- GOLF module merge (lvm2): the content of `LvmChainTableLinkMath` now lives in `LvmSpongeTableLink`. This stub keeps `import LvmChainTableLinkMath`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmSpongeTableLink
