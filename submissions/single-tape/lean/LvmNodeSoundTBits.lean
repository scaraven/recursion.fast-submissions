-- GOLF module merge (lvm2): the content of `LvmNodeSoundTBits` now lives in `LvmNodeSoundTBV`. This stub keeps `import LvmNodeSoundTBits`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmNodeSoundTBV
