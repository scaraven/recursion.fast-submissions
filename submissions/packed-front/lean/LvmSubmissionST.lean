-- GOLF module merge (lvm2): the content of `LvmSubmissionST` now lives in `LvmCertTInst`. This stub keeps `import LvmSubmissionST`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmCertTInst
