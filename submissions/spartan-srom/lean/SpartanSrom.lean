-- Ported from v3 `spartan-chain` (submissions repo, local `main` at `1f59b38`) to the v4 contract.
import SpartanSromBlake2sCircuit
import SpartanSromBlake2sCompress
import SpartanSromBlake2sGeneric
import SpartanSromBlake2sR1CS
import SpartanSromBlake2sWalk
import SpartanSromBlake2sWitness
import SpartanSromBlake2sWords
import SpartanSromChain
import SpartanSromChainCols
import SpartanSromChainEval
import SpartanSromChainHonest
import SpartanSromChainInner
import SpartanSromChainMle
import SpartanSromChainSound
import SpartanSromChainTables
import SpartanSromControls
import SpartanSromDecode
import SpartanSromField
import SpartanSromFieldBase
import SpartanSromFieldBaseCorrect
import SpartanSromFieldControls
import SpartanSromFieldExt
import SpartanSromFieldExtCorrect
import SpartanSromFinal
import SpartanSromKat
import SpartanSromLigero
import SpartanSromLigeroControls
import SpartanSromMLE
import SpartanSromMLEControls
import SpartanSromMerkle
import SpartanSromNode
import SpartanSromNodeBytes
import SpartanSromNodeControls
import SpartanSromOracle
import SpartanSromPCSBounds
import SpartanSromProver
import SpartanSromProximity
import SpartanSromQueries
import SpartanSromRS
import SpartanSromRSControls
import SpartanSromRingSwitch
import SpartanSromRingSwitchField
import SpartanSromRun
import SpartanSromSnarkQueries
import SpartanSromSoundnessChain
import SpartanSromSoundnessDefs
import SpartanSromSoundnessFinal
import SpartanSromSoundnessKS
import SpartanSromSoundnessKSBase
import SpartanSromSoundnessKSFinal
import SpartanSromSoundnessKState
import SpartanSromSoundnessLog
import SpartanSromSoundnessLogControls
import SpartanSromSoundnessPCS
import SpartanSromSoundnessPCSControls
import SpartanSromSoundnessPack
import SpartanSromSoundnessSpartan
import SpartanSromSpartanProtocol
import SpartanSromSubmission
import SpartanSromSumcheck
import SpartanSromTranscript
import SpartanSromTranscriptControls
import SpartanSromVerifier
import SpartanSromVerifierTop

/-!
# `spartan-srom`: the v4 Flock baseline entry (all modules)

v3's honest entry `spartan-chain` (Spartan R1CS sumchecks over GF(2^64)/GF(2^192), ring switching,
Ligero with unique-decoding proximity) ported to the v4 contract (the signed random oracle), with
the new node branches `C`, `N`, `B` (σ0-bundles). The certificate is `SpartanSrom.certificate`
(`SpartanSromFinal`); `Solution.lean` binds it to the rendered claim. Design:
`docs/v4/flock-baseline/BLUEPRINT.md` of the submissions repository.
-/
