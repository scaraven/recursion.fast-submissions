-- GOLF module merge (lvm2): the content of `LvmXChain` now lives in `LvmXChainL`. This stub keeps `import LvmXChain`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmXChainL
