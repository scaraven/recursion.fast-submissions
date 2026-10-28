-- New for `flock-recursive` (BLUEPRINT §7): imports every module of the entry.
import FRFieldBase
import FRFieldBaseCorrect
import FRField128
import FRField256
import FRFieldControls
import FRMLE
import FRMLEControls
import FRSumcheck
import FRShift
import FRRingSwitch
import FRSkip
import FRSpartan
import FRPubTarget
import FRRS
import FRRSEval
import FRProximityBW
import FRProximityLine
import FRProximityFold
import FRMerkle
import FRXDsl
import FRXField
import FRTranscriptDefs
import FRFormat
import FRVIR
import FRVIRSpec
import FRBlake2sCircuit
import FRBlake2sWords
import FRBlake2sCompress
import FRBlake2sGeneric
import FRBlake2sWalk
import FRBlake2sWitness
import FRBlockLayout
import FRBlockChain
import FRBlockStream
import FRBlockKinds
import FRLeafCircuit
import FRVIRFinals
import FRVIRCompile
import FRVIRMux
import FRWots
import FRNodeLayout
import FRVIREval
import FRNodeCircuit
import FRVIRFinalsSF
import FRVerifier
import FRVerifierImpl
import FRLog
import FRSoundnessDefs
import FRSoundnessStepA
import FRSoundnessStepB
import FRSoundnessStepC
import FRSoundnessTruths
import FRSoundnessStepD
import FRSoundnessStepE
import FRSoundnessHide
import FRKState
import FRSoundnessPIOP
import FRSoundnessWeights
import FRSoundnessWalk
import FRSoundnessPhases
import FRSoundnessLigerito
import FRSoundnessCompose
import FRVIRFinalsSG
import FRVIRChain

/-!
# `flock-recursive`

The entry's modules, flat under `lean/` with the prefix `FR` and the namespace `FR`
(`docs/v4/flock-recursive/BLUEPRINT.md` §7). Stages S-A (fields), S-C (PIOP core), S-D (PCS), S-E1 (BLAKE2s, blocks, leaf), S-H1 (extractor DSL), S-0 (interfaces), S-E2, S-F and S-G in part so far.
-/
