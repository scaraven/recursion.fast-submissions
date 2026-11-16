-- GOLF module merge (lvm2): the content of `LvmTapeRel` now lives in `LvmWireSpec`. This stub keeps `import LvmTapeRel`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmWireSpec
