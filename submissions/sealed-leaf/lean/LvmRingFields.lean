-- GOLF module merge (lvm2): the content of `LvmRingFields` now lives in `LvmRingFidelity`. This stub keeps `import LvmRingFields`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmRingFidelity
