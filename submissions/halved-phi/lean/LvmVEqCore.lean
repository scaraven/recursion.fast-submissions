-- New for lvm (WP-14a): the hub of V_S ⇒ S.V: a program of the verifier language read off V_S's
-- stream with the compiled verifier's byte decoders (`ivp`), and the refinement of a native
-- decision step by such a program (`RefAt`), with its composition rules.
import LvmDecide
import LvmCompileCodec
import LvmDriver

/-!
# Reading a verifier program off the stream; refinement of the native decision

**`ivp cap occ shp P sig s`** runs the program `P` of the verifier language (over `E = BF64.Ext3`) on
V_S's stream `Σ = sig` from the reader's cursor `s` (LvmDecideBase's `RS`: `ent` the next trace
entry, `msg` the message bytes of it read so far), the way `decideProg` reads it, with the compiled
verifier's decoders (`Lvm.FS.eOfBytes`, `chalOf`, `rowOf kOfBytes`):

* `read`: the 24 message bytes at `ent + 40 + msg` (`eOfBytes`);
* `sample`: the answer after the message, `chalOf` of the digest at `ent + 40 + msg`; the cursor
  moves to the next entry;
* `commit ht w`: the cap's `32 · 2^(cap ht w)` message bytes are skipped (the driver checks the
  openings against them);
* `query i ps`: per position a leaf entry (its query is the row's last `min (occ ht wd) wd`
  words, read as the row by `padAt`) and `path` node entries of 104 bytes, the commitment's shape
  `(ht, wd) = shp i`, `path = ht − cap ht wd`;
* `ret a`: `some a`; `fail`, `grind`: `none`.

`ivp` never reads or writes the cursor's `ok` flag (`ivp_ok`, `ivp_congr`).

**`RefAt sig d P R`**: the native step `d : DM β` refines `P`: from every cursor at which `d`
ends with every check held (`ok`), the cursor was `ok` before, and `ivp P` returns `some a` at the
same `ent`, `msg`, with `R (value of d) a`. Rules: `RefAt.bind` (composition), `RefAt.pure`,
`RefAt.mono`, `RefAt.dm_left` (a native step that reads without moving), `RefAt.require` (V_S's
strict `require` against the language's `require`).
-/

set_option autoImplicit false

namespace Lvm.VEq

open LeanVM.Parameters LeanVM.Protocol.Compile

/-! ## The program on the stream -/

/-- The bytes `[o, o + n)` of `sig` (fewer at the end). -/
def sbs (sig : ByteArray) (o n : ℕ) : List UInt8 := (sig.data.toList.drop o).take n

/-- The row of `wd` words at byte `o` (a leaf entry's query, which starts 8 bytes into the entry). -/
def rowAt (sig : ByteArray) (o wd : ℕ) : List K := Lvm.FS.rowOf Lvm.FS.kOfBytes wd (sbs sig o (8 * wd))

/-- The row of `wd` words whose leaf at byte `o` carries the last `min oc wd` words (the compiled
verifier's `Scheme.padRow`): zero words, then the leaf's words. -/
def padAt (sig : ByteArray) (o wd oc : ℕ) : List K :=
  Lvm.FS.padRowOf Lvm.FS.kOfBytes wd oc (sbs sig o (8 * min oc wd))

/-- A leaf that carries the whole row is the row. -/
theorem padAt_full {sig : ByteArray} {o wd oc : ℕ} (h : wd ≤ oc) : padAt sig o wd oc = rowAt sig o wd := by
  rw [padAt, Lvm.FS.padRowOf_full _ h, Nat.min_eq_right h]
  rfl

/-- The rows of `n` openings from entry `e` of a commitment of `wd`-word rows with `oc` occupied
words: each a leaf entry of `8 + 8·min oc wd + 32` bytes and `path` node entries of `104` bytes; the
rows (`padAt`), and the entry after them. -/
def opRows (sig : ByteArray) (wd oc path : ℕ) : ℕ → ℕ → List (List K) × ℕ
  | 0, e => ([], e)
  | n + 1, e =>
    let r := opRows sig wd oc path n (e + 40 + 8 * min oc wd + 104 * path)
    (padAt sig (e + 8) wd oc :: r.1, r.2)

section Ivp

variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ)

/-- **A program of the verifier language read off the stream** (the compiled verifier's decoders). -/
def ivp {α : Type} : VerifierProgram α → ByteArray → RS → Option α × RS
  | .ret a, _, s => (some a, s)
  | .fail, _, s => (none, s)
  | .grind _ _, _, s => (none, s)
  | .read k, sig, s =>
    ivp (k (Lvm.FS.eOfBytes (sbs sig (s.ent + 40 + s.msg) 24))) sig { s with msg := s.msg + 24 }
  | .sample k, sig, s =>
    ivp (k (Lvm.FS.chalOf (digestAt sig (s.ent + 40 + s.msg)))) sig
      { s with ent := s.ent + 72 + s.msg, msg := 0 }
  | .commit ht w k, sig, s => ivp k sig { s with msg := s.msg + 32 * 2 ^ cap ht w }
  | .query i ps k, sig, s =>
    let r := opRows sig (shp i).2 (occ (shp i).1 (shp i).2) ((shp i).1 - cap (shp i).1 (shp i).2) ps.length
      s.ent
    ivp (k r.1) sig { s with ent := r.2 }

variable {cap occ shp}

/-- `ivp` keeps the cursor's flag. -/
theorem ivp_ok {α : Type} (P : VerifierProgram α) (sig : ByteArray) (s : RS) :
    (ivp cap occ shp P sig s).2.ok = s.ok := by
  induction P generalizing s with
  | ret a => rfl
  | fail => rfl
  | grind b k ih => rfl
  | read k ih => exact ih _ _
  | sample k ih => exact ih _ _
  | commit ht w k ih => exact ih _
  | query i ps k ih => exact ih _ _

/-- `ivp` reads the cursor's `ent` and `msg` only. -/
theorem ivp_congr {α : Type} (P : VerifierProgram α) (sig : ByteArray) {s s' : RS}
    (he : s.ent = s'.ent) (hm : s.msg = s'.msg) :
    (ivp cap occ shp P sig s).1 = (ivp cap occ shp P sig s').1 ∧
      (ivp cap occ shp P sig s).2.ent = (ivp cap occ shp P sig s').2.ent ∧
      (ivp cap occ shp P sig s).2.msg = (ivp cap occ shp P sig s').2.msg := by
  induction P generalizing s s' with
  | ret a => exact ⟨rfl, he, hm⟩
  | fail => exact ⟨rfl, he, hm⟩
  | grind b k ih => exact ⟨rfl, he, hm⟩
  | read k ih =>
    simp only [ivp, he, hm]
    exact ih _ rfl rfl
  | sample k ih =>
    simp only [ivp, he, hm]
    exact ih _ rfl rfl
  | commit ht w k ih =>
    simp only [ivp]
    exact ih he (by simp [hm])
  | query i ps k ih =>
    simp only [ivp, he]
    exact ih _ rfl hm

/-- `ivp` of a sequence. -/
theorem ivp_bind {α β : Type} (P : VerifierProgram α) (f : α → VerifierProgram β) (sig : ByteArray)
    (s : RS) : ivp cap occ shp (P.bind f) sig s =
      match ivp cap occ shp P sig s with
      | (some a, s') => ivp cap occ shp (f a) sig s'
      | (none, s') => (none, s') := by
  induction P generalizing s with
  | ret a => rfl
  | fail => rfl
  | grind b k ih => rfl
  | read k ih => exact ih _ _
  | sample k ih => exact ih _ _
  | commit ht w k ih => exact ih _
  | query i ps k ih => exact ih _ _

end Ivp

/-! ## The program on the stream, with read widths -/

section Ivp

variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ) (rw : ℕ → ℕ)

/-- **A program of the verifier language read off the stream with read widths `rw`**: the `i`-th read takes
`rw i` message bytes, zero-padded by `eOfBytes`. -/
def ivpW {α : Type} : VerifierProgram α → ByteArray → RS → ℕ → Option α × RS × ℕ
  | .ret a, _, s, i => (some a, s, i)
  | .fail, _, s, i => (none, s, i)
  | .grind _ _, _, s, i => (none, s, i)
  | .read k, sig, s, i =>
    ivpW (k (Lvm.FS.eOfBytes (sbs sig (s.ent + 40 + s.msg) (rw i)))) sig
      { s with msg := s.msg + rw i } (i + 1)
  | .sample k, sig, s, i =>
    ivpW (k (Lvm.FS.chalOf (digestAt sig (s.ent + 40 + s.msg)))) sig
      { s with ent := s.ent + 72 + s.msg, msg := 0 } i
  | .commit ht w k, sig, s, i => ivpW k sig { s with msg := s.msg + 32 * 2 ^ cap ht w } i
  | .query i' ps k, sig, s, i =>
    let r := opRows sig (shp i').2 (occ (shp i').1 (shp i').2) ((shp i').1 - cap (shp i').1 (shp i').2)
      ps.length s.ent
    ivpW (k r.1) sig { s with ent := r.2 } i

variable {cap occ shp rw}

/-- `ivpW` reads the cursor's `ent` and `msg` only. -/
theorem ivpW_congr {α : Type} (P : VerifierProgram α) (sig : ByteArray) {s s' : RS} (i : ℕ)
    (he : s.ent = s'.ent) (hm : s.msg = s'.msg) :
    (ivpW cap occ shp rw P sig s i).1 = (ivpW cap occ shp rw P sig s' i).1 ∧
      (ivpW cap occ shp rw P sig s i).2.1.ent = (ivpW cap occ shp rw P sig s' i).2.1.ent ∧
      (ivpW cap occ shp rw P sig s i).2.1.msg = (ivpW cap occ shp rw P sig s' i).2.1.msg ∧
      (ivpW cap occ shp rw P sig s i).2.2 = (ivpW cap occ shp rw P sig s' i).2.2 := by
  induction P generalizing s s' i with
  | ret a => exact ⟨rfl, he, hm, rfl⟩
  | fail => exact ⟨rfl, he, hm, rfl⟩
  | grind b k ih => exact ⟨rfl, he, hm, rfl⟩
  | read k ih =>
    simp only [ivpW, he, hm]
    exact ih _ _ rfl rfl
  | sample k ih =>
    simp only [ivpW, he, hm]
    exact ih _ _ rfl rfl
  | commit ht w k ih =>
    simp only [ivpW]
    exact ih _ he (by simp [hm])
  | query i' ps k ih =>
    simp only [ivpW, he]
    exact ih _ _ rfl hm

/-- `ivpW` of a sequence. -/
theorem ivpW_bind {α β : Type} (P : VerifierProgram α) (f : α → VerifierProgram β) (sig : ByteArray)
    (s : RS) (i : ℕ) : ivpW cap occ shp rw (P.bind f) sig s i =
      match ivpW cap occ shp rw P sig s i with
      | (some a, s', i') => ivpW cap occ shp rw (f a) sig s' i'
      | (none, s', i') => (none, s', i') := by
  induction P generalizing s i with
  | ret a => rfl
  | fail => rfl
  | grind b k ih => rfl
  | read k ih => exact ih _ _ _
  | sample k ih => exact ih _ _ _
  | commit ht w k ih => exact ih _ _
  | query i' ps k ih => exact ih _ _ _

end Ivp

section IvpW

variable {cap occ shp}

/-- **At 24 bytes per read `ivpW` is `ivp`** (value and cursor; the counter counts the reads). -/
theorem ivpW_ivp {α : Type} (P : VerifierProgram α) (sig : ByteArray) : ∀ (s : RS) (i : ℕ),
    (ivpW cap occ shp (fun _ ↦ 24) P sig s i).1 = (ivp cap occ shp P sig s).1 ∧
      (ivpW cap occ shp (fun _ ↦ 24) P sig s i).2.1 = (ivp cap occ shp P sig s).2 := by
  induction P with
  | ret a => intro _ _; exact ⟨rfl, rfl⟩
  | fail => intro _ _; exact ⟨rfl, rfl⟩
  | grind b k ih => intro _ _; exact ⟨rfl, rfl⟩
  | read k ih => intro s i; exact ih _ _ _
  | sample k ih => intro s i; exact ih _ _ _
  | commit ht w k ih => intro s i; exact ih _ _
  | query i' ps k ih => intro s i; exact ih _ _ _

end IvpW

/-! ## Widths -/

/-- The read widths at `i, i + 1, …` are `ws`. -/
def WAt (rw : ℕ → ℕ) (i : ℕ) (ws : List ℕ) : Prop := ∀ k < ws.length, rw (i + k) = ws.getD k 0

theorem WAt.append {rw : ℕ → ℕ} {i : ℕ} {a b : List ℕ} :
    WAt rw i (a ++ b) ↔ WAt rw i a ∧ WAt rw (i + a.length) b := by
  constructor
  · intro h
    refine ⟨fun k hk ↦ ?_, fun k hk ↦ ?_⟩
    · rw [h k (by simp; omega), List.getD_append _ _ _ _ hk]
    · rw [Nat.add_assoc, h (a.length + k) (by simp; omega), List.getD_append_right _ _ _ _ (by omega),
        Nat.add_sub_cancel_left]
  · rintro ⟨ha, hb⟩ k hk
    by_cases hka : k < a.length
    · rw [ha k hka, List.getD_append _ _ _ _ hka]
    · have := hb (k - a.length) (by simp at hk; omega)
      rw [show i + a.length + (k - a.length) = i + k by omega] at this
      rw [this, List.getD_append_right _ _ _ _ (by omega)]

theorem WAt.cons {rw : ℕ → ℕ} {i w : ℕ} {ws : List ℕ} :
    WAt rw i (w :: ws) ↔ rw i = w ∧ WAt rw (i + 1) ws := by
  rw [show w :: ws = [w] ++ ws from rfl, WAt.append]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by simpa using h1 0 (by simp), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun k hk ↦ by simp at hk; subst hk; simpa using h1, h2⟩

theorem WAt.idx_eq {rw : ℕ → ℕ} {i j : ℕ} {ws : List ℕ} (h : WAt rw i ws) (e : i = j) : WAt rw j ws :=
  e ▸ h

theorem WAt.nil {rw : ℕ → ℕ} {i : ℕ} : WAt rw i [] := fun _ hk ↦ absurd hk (by simp)


/-! ## Refinement -/

/-- A native step run from a cursor. -/
abbrev runD {β : Type} (d : DM β) (sig : ByteArray) (s : RS) : β × RS := d sig s

/-- **A native step never clears a failed check** (V_S's `require` only clears the flag). -/
def MonoD {β : Type} (d : DM β) : Prop := ∀ sig s, (runD d sig s).2.ok = true → s.ok = true

theorem MonoD.bind {β β' : Type} {d : DM β} {d' : β → DM β'} (h : MonoD d) (h' : ∀ b, MonoD (d' b)) :
    MonoD (d >>= d') := fun sig s hok ↦ h sig s (h' _ sig _ hok)

theorem MonoD.pure {β : Type} (b : β) : MonoD (Pure.pure b : DM β) := fun _ _ h ↦ h

theorem MonoD.read : MonoD (MonadReader.read : DM ByteArray) := fun _ _ h ↦ h

theorem MonoD.require (c : Bool) : MonoD (DM.require c) := fun _ s h ↦ by
  simp only [runD, DM.require, modify, modifyGet, MonadStateOf.modifyGet] at h
  exact (Bool.and_eq_true _ _ ▸ h).2

section Ref

variable (cap : ℕ → ℕ → ℕ) (occ : ℕ → ℕ → ℕ) (shp : ℕ → ℕ × ℕ)

/-- **The native step `d` refines the program `P` on the stream `sig`**: wherever `d` ends with
every check held, `P` read off the stream returns a value related to `d`'s at the same cursor. -/
def RefAt {α β : Type} (sig : ByteArray) (d : DM β) (P : VerifierProgram α) (R : β → α → Prop) :
    Prop :=
  ∀ s, (runD d sig s).2.ok = true →
    ∃ a, (ivp cap occ shp P sig s).1 = some a ∧ (ivp cap occ shp P sig s).2.ent = (runD d sig s).2.ent ∧
      (ivp cap occ shp P sig s).2.msg = (runD d sig s).2.msg ∧ R (runD d sig s).1 a

variable {cap occ shp} {sig : ByteArray}

theorem RefAt.mono {α β : Type} {d : DM β} {P : VerifierProgram α} {R R' : β → α → Prop}
    (h : RefAt cap occ shp sig d P R) (hR : ∀ b a, R b a → R' b a) : RefAt cap occ shp sig d P R' :=
  fun s hok ↦ by
    obtain ⟨a, h1, h2, h3, h4⟩ := h s hok
    exact ⟨a, h1, h2, h3, hR _ _ h4⟩

/-- **Composition** (the native continuation never clears a failed check). -/
theorem RefAt.bind {α α' β β' : Type} {d : DM β} {d' : β → DM β'} {P : VerifierProgram α}
    {P' : α → VerifierProgram α'} {R : β → α → Prop} {R' : β' → α' → Prop}
    (hm : ∀ b, MonoD (d' b)) (h : RefAt cap occ shp sig d P R)
    (h' : ∀ b a, R b a → RefAt cap occ shp sig (d' b) (P' a) R') :
    RefAt cap occ shp sig (d >>= d') (P.bind P') R' := by
  intro s hok
  have hsplit : runD (d >>= d') sig s = runD (d' (runD d sig s).1) sig (runD d sig s).2 := rfl
  rw [hsplit] at hok ⊢
  obtain ⟨a, ha, he, hmsg, hR⟩ := h s (hm _ sig _ hok)
  obtain ⟨a', ha', he', hm', hR'⟩ := h' _ _ hR _ hok
  refine ⟨a', ?_⟩
  rw [ivp_bind]
  rcases hP : ivp cap occ shp P sig s with ⟨_ | a₀, s₂⟩
  · rw [hP] at ha; exact absurd ha (by simp)
  · rw [hP] at ha he hmsg
    simp only [Option.some.injEq] at ha
    subst ha
    obtain ⟨c1, c2, c3⟩ := ivp_congr (cap := cap) (occ := occ) (shp := shp) (P' a₀) sig he hmsg
    exact ⟨c1.trans ha', c2.trans he', c3.trans hm', hR'⟩

/-- A returned value. -/
theorem RefAt.pure {α β : Type} {b : β} {a : α} {R : β → α → Prop} (h : R b a) :
    RefAt cap occ shp sig (Pure.pure b : DM β) (VerifierProgram.ret a) R :=
  fun _ _ ↦ ⟨a, rfl, rfl, rfl, h⟩

/-- A native step that reads without moving the cursor, then the rest. -/
theorem RefAt.dm_left {α β β' : Type} {d₀ : DM β'} {b₀ : β'} (h₀ : ∀ s, runD d₀ sig s = (b₀, s))
    {d : β' → DM β} {P : VerifierProgram α} {R : β → α → Prop} (h : RefAt cap occ shp sig (d b₀) P R) :
    RefAt cap occ shp sig (d₀ >>= d) P R := by
  intro s hok
  have hsplit : runD (d₀ >>= d) sig s = runD (d b₀) sig s := by
    show runD (d (runD d₀ sig s).1) sig (runD d₀ sig s).2 = _
    rw [h₀]
  rw [hsplit] at hok ⊢
  exact h s hok

/-- Reading the stream itself. -/
theorem RefAt.read_left {α β : Type} {d : ByteArray → DM β} {P : VerifierProgram α}
    {R : β → α → Prop} (h : RefAt cap occ shp sig (d sig) P R) :
    RefAt cap occ shp sig (MonadReader.read >>= d) P R :=
  RefAt.dm_left (fun _ ↦ rfl) h

/-- **V_S's strict `require` against the language's `require`.** -/
theorem RefAt.require {c : Bool} {q : Prop} [Decidable q] (h : c = true → q) :
    RefAt cap occ shp sig (DM.require c) (VerifierProgram.require q) fun _ _ ↦ True := by
  intro s hok
  have hc : c = true := by
    simp only [runD, DM.require, modify, modifyGet, MonadStateOf.modifyGet] at hok
    exact (Bool.and_eq_true _ _ ▸ hok).1
  have hq : VerifierProgram.require q = VerifierProgram.ret () := by
    simp only [VerifierProgram.require, h hc, ↓reduceIte]
  rw [hq]
  exact ⟨(), rfl, rfl, rfl, trivial⟩

end Ref

end Lvm.VEq
