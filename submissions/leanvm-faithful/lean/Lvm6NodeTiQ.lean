-- New for lvm6 (INT5): the deployed base with the fast builds as its fields, for compiled code. The core's source
-- rule bans the compiler-rewrite attribute that NODE3 used to make compiled code run `progQ6Q`/`mbTDQ` in place of
-- `progQ6`/`mbTD`; here the fast twins are the instance's fields instead, and `tyBaseOfQ_eq` says it is `tyBaseOf`.
import Lvm6NodeTi
import Lvm6GspKsW

/-!
# The deployed `TyBase6`, built fast (`tyBaseOfQ`)

* `progMbQ lay` (SU2): `(progQ6Q lay, mbTDQ lay)` from one build of the families before CC (`progMbQ_fst`/`_snd`).
* `tiOfLQ lay`: `tiOfL lay` with `progQ6Q lay` and `mbTDQ lay` (ST-5's/MBF's twins, NODE3's wiring) by `progMbQ`, and
  GSP's `KS` map on a window table `ksWT (cowTbl lay)`; **`tiOfLQ_eq : tiOfLQ lay = tiOfL lay`** (`progQ6Q_eq`,
  `mbTDQ_eq`, `ksWT_eq`).
* **`tyBaseOfQ lay P`**: its `TyBase6` (the construction facts carried over from `tyBaseOf lay P`);
  **`tyBaseOfQ_eq : tyBaseOfQ lay P = tyBaseOf lay P`**, so every theorem about `tyBaseOf` (`node6V_final`) holds of it.
* INT7: `tiOfLM lay pm`/`tyBaseOfQM lay pm h P` take the prefix build `pm = progMbQ lay` as an argument
  (`tiOfLM_eq`, `tyBaseOfQM_eq`); **`progMb6 = progMbQ layQ6`** is one load-time constant read by `base6` and by
  the deployed tables **`mbT6`** (`tiOf6_mbT`, `mbT6_lin`, moved here from `Lvm6NodeTi`).
-/

set_option autoImplicit false

namespace Lvm6.Node.Ti

open Lvm6.Node.Mb Lvm6.Node.Dep Lvm6.BF

/-! ## One build for the program and the tables (SU2)

`progQ6Q lay` builds the families before CC twice (once inside `mbTDQ lay` for the tables, once for the program)
and `tiOfLQ` built `mbTDQ lay` a second time for its `mbT` field. `progMbQ lay` runs the prefix once: the state
after `famR` gives `progRF`'s program (so the tables) and is where CC continues. -/

/-- The empty builder state at `nK` (where `toProgramB nK 0` starts). -/
def st0Q : Lvm6.BF.St := ⟨⟨nK, 0⟩, #[], []⟩

/-- `toProgramB nK 0`'s program of a final state. -/
def progOfSt (s : Lvm6.BF.St) : Lvm.Loop.Program :=
  ⟨nK, 0, s.out, (List.range s.out.length).filter fun b ↦ (s.out.getD b default).dims.isEmpty⟩

theorem toProgramB_eq_progOfSt {α : Type} (m : FM α) : toProgramB nK 0 m = progOfSt (m st0Q).2 := rfl

/-- The families before CC (`node6E`'s twin, then `famR`), returning `node6E`'s outputs. -/
def preQ (lay : Lvm.Typed.Lay) : FM NodeOutE :=
  node6EF (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun o ↦ lift famR >>= fun _ ↦ pure o

/-- **The deployed program and mini-bus tables, one prefix build.** -/
def progMbQ (lay : Lvm.Typed.Lay) : Lvm.Loop.Program × List Lvm.M3.Tab :=
  let r := preQ lay st0Q
  let T := mbTLF (mbPar6 lay) (progOfSt r.2) lay
  (progOfSt (ccG18oF r.1 lay T ccbC gateC r.2).2, T)

/-- Running `m`, then `k`, returning `m`'s output: `k`'s final state. -/
theorem bind_ret_snd {α β : Type} (m : FM α) (k : FM β) (s : Lvm6.BF.St) :
    ((m >>= fun o ↦ k >>= fun _ ↦ pure o) s).2 = ((m >>= fun _ ↦ k) s).2 := rfl

/-- Continuing after `m >>= fun o ↦ k >>= fun _ ↦ pure o` is continuing after `k`, with `m`'s output. -/
theorem bind_ret_cont {α β γ : Type} (m : FM α) (k : FM β) (f : α → FM γ) (s : Lvm6.BF.St) :
    f ((m >>= fun o ↦ k >>= fun _ ↦ pure o) s).1 ((m >>= fun o ↦ k >>= fun _ ↦ pure o) s).2 =
      (m >>= fun o ↦ k >>= fun _ ↦ f o) s := rfl

theorem progMbQ_snd (lay : Lvm.Typed.Lay) : (progMbQ lay).2 = mbTDQ lay := by
  have h : progOfSt (preQ lay st0Q).2 = progRF lay :=
    (congrArg progOfSt (bind_ret_snd (node6EF (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC) (lift famR)
      st0Q)).trans (toProgramB_eq_progOfSt _).symm
  show mbTLF (mbPar6 lay) (progOfSt (preQ lay st0Q).2) lay = mbTLF (mbPar6 lay) (progRF lay) lay
  rw [h]

theorem famQ6FT_def (lay : Lvm.Typed.Lay) (T : List Lvm.M3.Tab) : famQ6FT lay T =
    (node6EF (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC >>= fun o ↦ lift famR >>= fun _ ↦
      ccG18oF o lay T ccbC gateC) := rfl

theorem progMbQ_fst_def (lay : Lvm.Typed.Lay) : (progMbQ lay).1 =
    progOfSt (ccG18oF (preQ lay st0Q).1 lay (progMbQ lay).2 ccbC gateC (preQ lay st0Q).2).2 := rfl

theorem progMbQ_fst (lay : Lvm.Typed.Lay) : (progMbQ lay).1 = progQ6Q lay := by
  rw [progMbQ_fst_def, progMbQ_snd, progQ6Q, toProgramB_eq_progOfSt, famQ6FT_def]
  unfold preQ
  have h := bind_ret_cont (node6EF (tiOf lay) (pubCOf lay) ainC yInC ownC ownYC gateC) (lift famR)
    (fun o ↦ ccG18oF o lay (mbTDQ lay) ccbC gateC) st0Q
  beta_reduce at h
  rw [h]

/-- `tiOfLQ`'s instance on a given program and tables `pm` (INT7: the deployed base passes the load-time constant
`progMb6`, so the prefix is built once per process). -/
def tiOfLM (lay : Lvm.Typed.Lay) (pm : Lvm.Loop.Program × List Lvm.M3.Tab) : Ty.TInst6 :=
  ⟨pm.1, lay, pm.2, regW6 (mbPar6 lay) lay .com, Lvm6.Gsp.ksWT (Lvm6.Gsp.cowTbl lay), regW6 (mbPar6 lay) lay .sflat,
    regW6 (mbPar6 lay) lay .sigma, fun _ ↦ 0⟩

/-- `tiOfL` with the fast builds of the program and the mini-bus tables (one prefix build, `progMbQ`). -/
def tiOfLQ (lay : Lvm.Typed.Lay) : Ty.TInst6 := tiOfLM lay (progMbQ lay)

theorem tiOfLQ_eq (lay : Lvm.Typed.Lay) : tiOfLQ lay = tiOfL lay := by
  simp only [tiOfLQ, tiOfLM, tiOfL, progMbQ_fst, progMbQ_snd, progQ6Q_eq, mbTDQ_eq, Lvm6.Gsp.ksWT_eq]

theorem tiOfLM_eq (lay : Lvm.Typed.Lay) {pm : Lvm.Loop.Program × List Lvm.M3.Tab} (h : pm = progMbQ lay) :
    tiOfLM lay pm = tiOfL lay := by
  subst h
  exact tiOfLQ_eq lay

theorem μBus_congr {L : Lvm.M3.Lay} {T T' : List Lvm.M3.Tab} (e : T = T') (h : ∀ t ∈ T, t.τ ≤ L.μ)
    (h' : ∀ t ∈ T', t.τ ≤ L.μ) : (Lvm.M3.inst L T h).μBus = (Lvm.M3.inst L T' h').μBus := by
  subst e
  rfl

/-- **The deployed base, built fast, on a given prefix build** `pm` (`= progMbQ lay`, a proof only):
`tyBaseOf lay P` with `tiOfLM lay pm` as its instance. -/
def tyBaseOfQM (lay : Lvm.Typed.Lay) (pm : Lvm.Loop.Program × List Lvm.M3.Tab) (h : pm = progMbQ lay)
    (P : Lvm6.V.PT) : Lvm6.V.TyBase6 where
  Ti := tiOfLM lay pm
  P := P
  bs := regBase6 lay .sflat
  bg := regBase6 lay .sigma
  hτ := by rw [tiOfLM_eq lay h]; exact (tyBaseOf lay P).hτ
  sc := by rw [tiOfLM_eq lay h]; exact (tyBaseOf lay P).sc
  lay := by rw [tiOfLM_eq lay h]; exact (tyBaseOf lay P).lay
  keys := by rw [tiOfLM_eq lay h]; exact (tyBaseOf lay P).keys
  fix := by rw [tiOfLM_eq lay h]; exact (tyBaseOf lay P).fix
  μBus := (μBus_congr (congrArg Ty.TInst6.mbT (tiOfLM_eq lay h)) _ _).trans (tyBaseOf lay P).μBus
  mapsReg := by rw [tiOfLM_eq lay h]; exact (tyBaseOf lay P).mapsReg

/-- **The deployed base, built fast**: `tyBaseOf lay P` with `tiOfLQ lay` as its instance. -/
def tyBaseOfQ (lay : Lvm.Typed.Lay) (P : Lvm6.V.PT) : Lvm6.V.TyBase6 := tyBaseOfQM lay (progMbQ lay) rfl P

/-- Two bases with the same instance, table and stream bases are equal (the other fields are proofs). -/
theorem tyBase6_ext {B B' : Lvm6.V.TyBase6} (hT : B.Ti = B'.Ti) (hP : B.P = B'.P) (hs : B.bs = B'.bs)
    (hg : B.bg = B'.bg) : B = B' := by
  cases B
  cases B'
  cases hT
  cases hP
  cases hs
  cases hg
  rfl

/-- `tyBaseOfQM` is `tyBaseOf`, for every prefix build equal to `progMbQ lay`. -/
theorem tyBaseOfQM_eq (lay : Lvm.Typed.Lay) {pm : Lvm.Loop.Program × List Lvm.M3.Tab} (h : pm = progMbQ lay)
    (P : Lvm6.V.PT) : tyBaseOfQM lay pm h P = tyBaseOf lay P :=
  tyBase6_ext (tiOfLM_eq lay h) rfl rfl rfl

/-- **It is `tyBaseOf`.** -/
theorem tyBaseOfQ_eq (lay : Lvm.Typed.Lay) (P : Lvm6.V.PT) : tyBaseOfQ lay P = tyBaseOf lay P :=
  tyBaseOfQM_eq lay rfl P

/-! ## The deployed prefix build, shared (INT7)

`progMb6` is a nullary constant, computed once when the program loads; the deployed base `base6` (`tyBaseOfQM layQ6
progMb6 rfl`) and the deployed tables `mbT6` both read it, so the families before CC are built once per process. -/

/-- **The deployed program and mini-bus tables, one prefix build** (`progMbQ layQ6`). -/
def progMb6 : Lvm.Loop.Program × List Lvm.M3.Tab := progMbQ Lvm6.Node.LayQ.layQ6

/-- **The deployed mini-bus tables** (the shared prefix build's tables; `progMbQ_snd`, `mbTDQ_eq` make them
`mbTD layQ6`). -/
def mbT6 : List Lvm.M3.Tab := progMb6.2

theorem tiOf6_mbT (P : Lvm6.V.PT) : (tiOf6 P).Ti.mbT = mbT6 := by
  unfold tiOf6 tyBaseOf tiOfL mbT6 progMb6
  exact ((progMbQ_snd _).trans (mbTDQ_eq _)).symm

/-- `mbLinB6` of the deployed tables (also a conjunct of the guard). -/
theorem mbT6_lin : Lvm6.Mb.mbLinB6 mbT6 = true := by
  rw [mbT6, progMb6, progMbQ_snd, mbTDQ_eq]
  exact mbTOf6_lin _ _ _

end Lvm6.Node.Ti
