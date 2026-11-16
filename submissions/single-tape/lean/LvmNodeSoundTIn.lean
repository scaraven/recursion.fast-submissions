-- GOLF module merge (lvm2): the content of `LvmNodeSoundTIn` now lives in `LvmNodeSoundTRd`. This stub keeps `import LvmNodeSoundTIn`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmNodeSoundTRd
