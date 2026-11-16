-- GOLF module merge (lvm2): the content of `LvmCertSQ` now lives in `LvmSubmissionS`. This stub keeps `import LvmCertSQ`
-- working for modules outside `Solution`'s import closure; no module in that closure imports it.
import LvmSubmissionS
