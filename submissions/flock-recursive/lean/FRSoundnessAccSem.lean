-- New for `flock-recursive` (BLUEPRINT §3, A.9; stage S-G3 pass 2, `hFin` step 1).
import FRSoundnessAccPos

/-!
# `hFin`, step 1: an accepted run passes every phase and every final field

On a trace that `gen fin (.fixed κ)` consumes with verdict `true`:

* the skeleton is `refPhases` (`exec_skeleton`), every phase's flag holds, and the register file
  `R` it leaves has the size the finals start from (`genPhases_next`);
* every final field (`finRS`, then `Finals.rest` in order) runs, from a register file that
  extends `R`, to the flag `true` (**`accept_fields`**). The fields ask nothing (the `noAsk_*`
  lemmas), so each is a `pureRun` (`pureRun_noAsk`) and the run's flag is the conjunction
  (`exec_field`, `exec_ok_false`).

`runFields` is `Finals.ops`'s fold as a recursion (`foldl_step`).
-/

namespace FR.Snd
open RecursionFast

variable (impl : OpImpl) (κ : Kind) (inp : Input)

/-- `Finals.ops`'s fold over fields, as a recursion: each field's ops at the next free register,
its exports pushed. -/
def runFields (outs : Array (List Reg)) (zh : List Reg) :
    List FinField → ℕ → Array (List Reg) → List Op
  | [], _, _ => []
  | f :: fs, b, ex => (f ⟨outs, zh, ex⟩ b).1 ++
      runFields outs zh fs (b + opsOut (f ⟨outs, zh, ex⟩ b).1) (ex.push (f ⟨outs, zh, ex⟩ b).2)

theorem foldl_step (outs : Array (List Reg)) (zh : List Reg) :
    ∀ (fs : List FinField) (A : List Op) (b : ℕ) (ex : Array (List Reg)),
      (fs.foldl (fun (acc : List Op × ℕ × Array (List Reg)) (f : FinField) =>
        (acc.1 ++ (f ⟨outs, zh, acc.2.2⟩ acc.2.1).1, acc.2.1 + opsOut (f ⟨outs, zh, acc.2.2⟩ acc.2.1).1,
          acc.2.2.push (f ⟨outs, zh, acc.2.2⟩ acc.2.1).2)) (A, b, ex)).1 =
        A ++ runFields outs zh fs b ex
  | [], A, _, _ => by simp [runFields]
  | f :: fs, A, b, ex => by
    rw [List.foldl_cons, foldl_step outs zh fs, runFields, List.append_assoc]

/-- `Finals.ops` is `finRS`'s ops, then the rest's, with `finRS`'s exports as `zhat`. -/
theorem finals_ops_eq (fin : Finals) (outs : Array (List Reg)) (b : ℕ) :
    fin.ops outs b = runFields outs [] [fin.finRS] b #[] ++
      runFields outs (fin.finRS ⟨outs, [], #[]⟩ b).2 fin.rest
        (b + opsOut (fin.finRS ⟨outs, [], #[]⟩ b).1) #[(fin.finRS ⟨outs, [], #[]⟩ b).2] := by
  rw [Finals.ops]
  dsimp only
  rw [foldl_step, List.nil_append, runFields, runFields, List.append_nil]

/-- Ops that ask nothing run purely. -/
theorem pureRun_noAsk (R : Array Val) :
    ∀ (o : List Op) (L₀ : List Val), o.filterMap Op.item? = [] →
      ∃ L f, pureRun impl κ inp o R L₀ = some (L, f)
  | [], L₀, _ => ⟨L₀, true, rfl⟩
  | op :: o, L₀, h => by
    have hop : op.item? = none := by
      by_contra hne
      obtain ⟨it, hit⟩ := Option.ne_none_iff_exists'.mp hne
      simp [hit] at h
    have ho : o.filterMap Op.item? = [] := by simpa [List.filterMap_cons, hop] using h
    simp only [pureRun]
    split
    · next vs ok _ =>
      obtain ⟨L, f, hL⟩ := pureRun_noAsk R o (L₀ ++ vs) ho
      exact ⟨L, ok && f, by rw [hL]; rfl⟩
    · next q hq => exact absurd (item?_of_ask impl κ inp hq) (by simp [hop])

/-- A run whose flag is down stays down. -/
theorem exec_ok_false : ∀ (ops : List Op) (R : Array Val) (tr : Trace) (s : St) (tr' : Trace),
    exec impl κ inp ops ⟨R, false⟩ tr = some (s, tr') → s.ok = false
  | [], R, tr, s, tr', h => by simp [exec] at h; rw [← h.1]
  | op :: ops, R, tr, s, tr', h => by
    simp only [exec] at h
    split at h
    · exact exec_ok_false ops _ tr s tr' (by simpa using h)
    · split at h
      · cases h
      · split at h
        · exact exec_ok_false ops _ _ s tr' h
        · cases h

/-- **One field**: on an accepted run, a field that asks nothing has flag `true`, the flag before
it was `true`, and the run continues from the extended registers. -/
theorem field_flag {o ops : List Op} {R : Array Val} {ok : Bool} {tr : Trace} {s : St}
    {tr' : Trace} (hna : o.filterMap Op.item? = [])
    (h : exec impl κ inp (o ++ ops) ⟨R, ok⟩ tr = some (s, tr')) (hs : s.ok = true) :
    ∃ L, pureRun impl κ inp o R [] = some (L, true) ∧ ok = true ∧
      exec impl κ inp ops ⟨R ++ L.toArray, true⟩ tr = some (s, tr') := by
  obtain ⟨L, f, hL⟩ := pureRun_noAsk impl κ inp R o [] hna
  rw [exec_field impl κ inp o ops R L f ok tr hL] at h
  cases hok : ok && f
  · rw [hok] at h; rw [exec_ok_false impl κ inp ops _ tr s tr' h] at hs; cases hs
  · rw [hok] at h
    simp only [Bool.and_eq_true] at hok
    exact ⟨L, by rw [hL, hok.2], hok.1, h⟩

/-- **Every field of `runFields`** has flag `true`, each from a register file extending `R` whose
size is the field's base. -/
theorem fields_ok (outs : Array (List Reg)) (zh : List Reg) :
    ∀ (fs : List FinField) (R : Array Val) (ex : Array (List Reg)) (ok : Bool) (tail : List Op)
      (tr : Trace) (s : St) (tr' : Trace),
      (∀ f ∈ fs, ∀ fi b, (f fi b).1.filterMap Op.item? = []) →
      exec impl κ inp (runFields outs zh fs R.size ex ++ tail) ⟨R, ok⟩ tr = some (s, tr') →
      s.ok = true →
      ok = true ∧ ∀ k (hk : k < fs.length), ∃ Rk : Array Val, ∃ exk : Array (List Reg),
        ∃ L, ExtA R Rk ∧ pureRun impl κ inp ((fs[k]'hk) ⟨outs, zh, exk⟩ Rk.size).1 Rk [] =
          some (L, true)
  | [], R, ex, ok, tail, tr, s, tr', _, h, hs => by
    refine ⟨?_, fun k hk => absurd hk (by simp)⟩
    cases ok
    · rw [runFields, List.nil_append] at h
      rw [exec_ok_false impl κ inp tail R tr s tr' h] at hs; cases hs
    · rfl
  | f :: fs, R, ex, ok, tail, tr, s, tr', hna, h, hs => by
    rw [runFields, List.append_assoc] at h
    obtain ⟨L, hL, hok, h'⟩ := field_flag impl κ inp
      (hna f (List.mem_cons_self ..) _ _) h hs
    have hsz : (R ++ L.toArray).size = R.size + opsOut (f ⟨outs, zh, ex⟩ R.size).1 := by
      have hl := pureRun_len impl κ inp R _ [] L true hL
      simp [hl]
    rw [← hsz] at h'
    obtain ⟨-, hrest⟩ := fields_ok outs zh fs (R ++ L.toArray) _ true tail tr s tr'
      (fun g hg => hna g (List.mem_cons_of_mem _ hg)) h' hs
    refine ⟨hok, fun k hk => ?_⟩
    rcases k with _ | k
    · exact ⟨R, ex, L, ⟨le_rfl, fun _ _ => rfl⟩, hL⟩
    · obtain ⟨Rk, exk, Lk, hE, hk'⟩ := hrest k (by simpa using hk)
      exact ⟨Rk, exk, Lk, (ExtA.app R L).trans hE, hk'⟩

/-- The skeleton's next free register is the size of the register file it leaves. -/
theorem genPhases_next : ∀ (ps : List Phase) (n : ℕ) (c : GCtx) (r : Array Val) (tr : Trace)
    (y : List Val × List Bool × Trace), refPhases impl κ inp ps n c r tr = some y →
    c.next = r.size → StartOk ps c r → (genPhases ps n c).2.next = (r ++ y.1.toArray).size
  | [], _, c, r, tr, y, h, hb, _ => by
    simp only [refPhases, Option.some.injEq] at h; subst h; simp [genPhases, hb]
  | p :: ps, n, c, r, tr, y, h, hb, hs => by
    have hwf : (p.shape = .seed ∧ CtxOk c #[default]) ∨ CtxOk c r := by
      rcases hs with h | ⟨q, qs, he, hq, h0⟩
      · exact .inr h
      · cases he; exact .inl ⟨hq, h0⟩
    simp only [refPhases, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, y', hy', rfl⟩ := h
    obtain ⟨h1, h2, -⟩ := genPhase_ctx impl κ inp n p c r tr x hb hwf hx
    have := genPhases_next ps (n + 1) _ _ _ y' hy' h1 (.inl h2)
    simp only [genPhases]
    rw [this]
    simp [Array.size_append]

/-- **An accepted run passes every phase and every final field**: the skeleton's registers `R`,
every phase flag `true`, and each field of `finRS :: Finals.rest` runs to `true` from registers
extending `R`. -/
theorem accept_fields (fin : Finals) {tr : Trace}
    (hna : ∀ f ∈ fin.finRS :: fin.rest, ∀ fi b, (f fi b).1.filterMap Op.item? = [])
    (h : semIR impl (gen fin (.fixed κ)) inp tr = some true) :
    ∃ y, refPhases impl κ inp phases 0 ctx₀ #[] tr = some y ∧ (∀ b ∈ y.2.1, b = true) ∧
      (∃ Rk exk L, ExtA (#[] ++ y.1.toArray) Rk ∧ pureRun impl κ inp
        (fin.finRS ⟨skeleton.2.outs, [], exk⟩ Rk.size).1 Rk [] = some (L, true)) ∧
      ∃ zh, ∀ k (hk : k < fin.rest.length), ∃ Rk exk L, ExtA (#[] ++ y.1.toArray) Rk ∧
        pureRun impl κ inp ((fin.rest[k]'hk) ⟨skeleton.2.outs, zh, exk⟩ Rk.size).1 Rk [] =
          some (L, true) := by
  unfold semIR at h
  split at h
  · next s hs =>
    simp only [Option.some.injEq] at h
    rw [show (gen fin (.fixed κ)).ops =
        skeleton.1 ++ (fin.ops skeleton.2.outs skeleton.2.next ++ [.accept]) by
      simp [gen, genWith], show (gen fin (.fixed κ)).kindOn inp = κ from rfl, St.init,
      exec_skeleton] at hs
    obtain ⟨y, hy, hs'⟩ := Option.bind_eq_some_iff.1 hs
    have hn := genPhases_next impl κ inp phases 0 ctx₀ #[] tr y hy rfl
      (.inr ⟨_, _, rfl, rfl, by simp [CtxOk, ctx₀]⟩)
    have hsk : genPhases phases 0 ctx₀ = skeleton := by rw [skeleton]; rfl
    rw [hsk] at hn
    rw [hn, finals_ops_eq] at hs'
    simp only [List.append_assoc] at hs'
    have hRS := fields_ok impl κ inp skeleton.2.outs [] [fin.finRS] _ #[] _ _ _ s []
      (fun f hf => hna f (by simp_all)) hs' h
    obtain ⟨hok, hRS⟩ := hRS
    refine ⟨y, hy, ?_, ?_, ?_⟩
    · simpa using hok
    · obtain ⟨Rk, exk, L, hE, hp⟩ := hRS 0 (by simp)
      exact ⟨Rk, exk, L, hE, hp⟩
    · -- the rest, after `finRS`
      obtain ⟨L, hL, -, h2⟩ := field_flag impl κ inp
        (hna _ (List.mem_cons_self ..) _ _) (by simpa only [runFields, List.append_nil] using hs') h
      have hsz : ((#[] ++ y.1.toArray) ++ L.toArray).size = (#[] ++ y.1.toArray).size +
          opsOut (fin.finRS ⟨skeleton.2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).1 := by
        have hl := pureRun_len impl κ inp _ _ [] L true hL
        simp [hl]
      rw [← hsz] at h2
      obtain ⟨-, hrest⟩ := fields_ok impl κ inp skeleton.2.outs _ fin.rest _ _ true _ _ s []
        (fun f hf => hna f (List.mem_cons_of_mem _ hf)) h2 h
      refine ⟨(fin.finRS ⟨skeleton.2.outs, [], #[]⟩ (#[] ++ y.1.toArray).size).2, fun k hk => ?_⟩
      obtain ⟨Rk, exk, Lk, hE, hp⟩ := hrest k hk
      exact ⟨Rk, exk, Lk, (ExtA.app _ L).trans hE, hp⟩
  · cases h

end FR.Snd
