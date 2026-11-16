-- GOLF module merge (lvm2): the content of `LvmCertSExqCodec` now lives in `LvmCertSExq2`. This stub keeps `import LvmCertSExqCodec`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertSExq2
