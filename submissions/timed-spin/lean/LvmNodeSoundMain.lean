-- GOLF module merge (lvm2): the content of `LvmNodeSoundMain` now lives in `LvmQAsmInb`. This stub keeps `import LvmNodeSoundMain`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQAsmInb
