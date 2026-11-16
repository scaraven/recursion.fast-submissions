-- GOLF module merge (lvm2): the content of `LvmQAsmInbLink` now lives in `LvmQAsmInb`. This stub keeps `import LvmQAsmInbLink`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmQAsmInb
