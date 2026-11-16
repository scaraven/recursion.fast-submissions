-- GOLF module merge (lvm2): the content of `LvmReplayDrive` now lives in `LvmReplay`. This stub keeps `import LvmReplayDrive`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmReplay
