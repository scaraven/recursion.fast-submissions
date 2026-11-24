-- New for lvm6 (WP W1). The deployed code facts of a WHIR level at `E2` as `TailIface`/`FinIface`
-- instances (FORMAT6 v2.2.1 §5, §6.6): the domain `K(p)` of `2^h` positions, the next tuple's
-- message (the low parts of its lanes, `lowMsgF`), the current polynomial of a message
-- (`msgPolyF`), the high part `Ŵ_κ·Σ_s φ_s X_s`, the OOD functional (the message's multilinear
-- extension, separated by Schwartz–Zippel) and the positions (`posE2`). After leanVM
-- `formal/lean_vm/LeanVM/Protocol/Whir/Sound/{LevelMid,Escape,Tuple}.lean` @ fdb317982.
import Lvm6WhirMsg
import Lvm6WhirPos
import Lvm6WhirLevel
import Lvm6WhirFinal

/-!
# The deployed levels' code facts (W1)

* `domE h`: position `p < 2^h` is the point `K(p)` (`K.ofBits p`) of `E2`.
* `vanNF κ`: the normalised subspace polynomial `Ŵ_κ` over `E2`; `highF κ ℓ hi = Ŵ_κ·Σ_{s<ℓ} hi_s X_s`.
* `keyE κ' ℓ' ko hκ U`: the message of a next tuple `U` (`ℓ'` lanes, low parts on `κ'` variables),
  on `ko + 1 = ℓ' + κ'` variables, lane bits first.
* **`tailE2`**: the `TailIface` of a level with `κ = ko + 1` message variables, `ℓ` rounds, positions
  `2^h`, next level `(κ', ℓ', h')`: `φ U = P_{key U}`, `hp = highF`, `ood z = mleEval z ∘ key`,
  `δ = ko + 1`, `pos = posE2`.
* **`finE2`**: the `FinIface` of the final level: `fpoly s = P_{s[0..2^κ)} + Ŵ_κ·Σ_{j<ℓ} s_{2^κ+j} X_j`.
-/

namespace Lvm6.Whir

open LeanVM.Parameters LeanVM.Protocol.Whir Polynomial Finset
open scoped ENNReal

/-! ## The domain and the high part -/

/-- **The domain of `2^h` positions**: `p ↦ K(p)`. -/
noncomputable def domE (h : ℕ) (hh : h ≤ 64) : Fin (2 ^ h) ↪ E2 where
  toFun p := algebraMap K E2 (K.ofBits p)
  inj' p q hpq := by
    have hp : (p : ℕ) < 2 ^ 64 := lt_of_lt_of_le p.isLt (Nat.pow_le_pow_right (by norm_num) hh)
    have hq : (q : ℕ) < 2 ^ 64 := lt_of_lt_of_le q.isLt (Nat.pow_le_pow_right (by norm_num) hh)
    exact Fin.ext (ofBits_injOn hp hq ((algebraMap K E2).injective hpq))

/-- The normalised subspace polynomial `Ŵ_κ` over `E2`. -/
noncomputable def vanNF (κ : ℕ) : E2[X] := (normVanishing κ).map (algebraMap K E2)

theorem natDegree_vanNF {κ : ℕ} (hκ : κ < 64) : (vanNF κ).natDegree = 2 ^ κ := by
  rw [vanNF, natDegree_map, natDegree_normVanishing hκ]

/-- **The high part** `Ŵ_κ·Σ_{s<ℓ} hi_s X_s` (FORMAT6 §6.7: `φ_s` is the coefficient of `Ŵ_κ X_s`). -/
noncomputable def highF (κ ℓ : ℕ) (hi : List E2) : E2[X] :=
  vanNF κ * ∑ s ∈ range ℓ, C (hi.getD s 0) * novelF s

theorem natDegree_highF_le {κ ℓ : ℕ} (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ64 : ℓ ≤ 2 ^ 64)
    (hi : List E2) : (highF κ ℓ hi).natDegree ≤ 2 ^ κ - 1 + ℓ := by
  unfold highF
  refine natDegree_mul_le.trans ?_
  rw [natDegree_vanNF hκ]
  have hs : (∑ s ∈ range ℓ, C (hi.getD s 0) * novelF (F := E2) s).natDegree ≤ ℓ - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun s hs ↦ ?_
    refine natDegree_C_mul_le _ _ |>.trans ?_
    have hs' := Finset.mem_range.mp hs
    rw [natDegree_map, natDegree_novel (by omega)]
    omega
  have : 1 ≤ 2 ^ κ := Nat.one_le_two_pow
  omega

/-! ## The next tuple's message -/

/-- **The message of a next tuple**: lane bits first (`ℓ'`), then the low part's `κ'` bits. -/
noncomputable def keyE (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) :
    Tup E2 (0 + ℓ') →ₗ[E2] ((Fin (ko + 1) → Bool) → E2) where
  toFun U w := lowMsgF κ' (U fun j ↦ w (finCongr hκ (finSumFinEquiv (Sum.inl j))))
    fun j ↦ w (finCongr hκ (finSumFinEquiv (Sum.inr j)))
  map_add' U V := by funext w; simp
  map_smul' c U := by funext w; simp

/-- The current polynomial of a next tuple's message, as a single-lane tuple. -/
noncomputable def phiE (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) :
    Tup E2 (0 + ℓ') →ₗ[E2] Tup E2 0 where
  toFun U _ := msgPolyF (ko + 1) (keyE κ' ℓ' ko hκ U)
  map_add' U V := by funext r; simp
  map_smul' c U := by funext r; simp

theorem phiE_apply (κ' ℓ' ko : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1) (U : Tup E2 (0 + ℓ'))
    (r : Fin 0 → Bool) : phiE κ' ℓ' ko hκ U r = msgPolyF (ko + 1) (keyE κ' ℓ' ko hκ U) := rfl

/-- A message polynomial plus a high part has degree at most `2^κ − 1 + ℓ`. -/
theorem natDegree_msg_high_le {κ ℓ : ℕ} (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64)
    (g : (Fin κ → Bool) → E2) (hi : List E2) :
    (msgPolyF κ g + highF κ ℓ hi).natDegree ≤ 2 ^ κ - 1 + ℓ := by
  refine (natDegree_add_le _ _).trans (max_le ?_ (natDegree_highF_le hκ hℓ
    (hℓ'.trans (Nat.lt_two_pow_self).le) hi))
  have h1 := natDegree_msgPolyF_lt (F := E2) (show κ ≤ 64 by omega) g
  by_cases h0 : msgPolyF κ g = 0
  · rw [h0, natDegree_zero]; exact Nat.zero_le _
  · have := (natDegree_lt_iff_degree_lt h0).mpr h1
    omega

open Classical in
/-- **The code facts of a deployed level** with a next one. -/
noncomputable def tailE2 (ko ℓ h κ' ℓ' h' kq t c : ℕ) (hκ : 0 + ℓ' + κ' = ko + 1)
    (hko : ko + 1 < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64) (hh : h ≤ 64) (hh' : h' ≤ 64) (hc : 0 < c)
    (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) :
    TailIface E2 (2 ^ h) (2 ^ h') (0 + ℓ') where
  dom := domE h hh
  dom' := domE h' hh'
  d := 2 ^ (ko + 1) - 1 + ℓ
  d' := 2 ^ κ' - 1 + ℓ'
  Msg := (Fin (ko + 1) → Bool) → E2
  msgDec := inferInstance
  key := keyE κ' ℓ' ko hκ
  φ := phiE κ' ℓ' ko hκ
  φ_key U V hUV := by
    funext r
    show msgPolyF (ko + 1) (keyE κ' ℓ' ko hκ U) = msgPolyF (ko + 1) (keyE κ' ℓ' ko hκ V)
    rw [hUV]
  nh := ℓ
  hp hi := fun _ ↦ highF (ko + 1) ℓ hi
  cand_deg U hi _ := fun r ↦ by
    rw [Pi.add_apply, phiE_apply]
    exact natDegree_msg_high_le hko hℓ hℓ' _ hi
  ko := ko
  ood z := mleEval z ∘ₗ keyE κ' ℓ' ko hκ
  ood_key z U V hUV := by simp [hUV]
  δ := ko + 1
  ood_sep U V _ _ hk := by
    simp only [LinearMap.coe_comp, Function.comp_apply]
    exact card_mle_eq_le hk
  kq := kq
  t := t
  pos := posE2 h c (kq + 1) t hc ht
  card_pos S := by
    have := card_posE2 hc hch ht S
    rwa [card_E2] at this ⊢

/-! ## The final level -/

/-- **The final polynomial** from `2^κ + ℓ` scalars: the message, then the high part. -/
noncomputable def fpolyE (κ ℓ : ℕ) (s : List E2) : Tup E2 0 := fun _ ↦
  msgPolyF κ (fun u ↦ s.getD (bitsToNat u) 0) + highF κ ℓ (s.drop (2 ^ κ))

open Classical in
/-- **The code facts of the final level.** -/
noncomputable def finE2 (κ ℓ h kq t c : ℕ) (hκ : κ < 64) (hℓ : 1 ≤ ℓ) (hℓ' : ℓ ≤ 64)
    (hh : h ≤ 64)
    (hc : 0 < c) (hch : c * h ≤ 128) (ht : t ≤ (kq + 1) * c) : FinIface E2 (2 ^ h) where
  dom := domE h hh
  d := 2 ^ κ - 1 + ℓ
  nf := 2 ^ κ + ℓ
  fpoly := fpolyE κ ℓ
  fdeg s := fun r ↦ natDegree_msg_high_le hκ hℓ hℓ' _ _
  kq := kq
  t := t
  pos := posE2 h c (kq + 1) t hc ht
  card_pos S := by
    have := card_posE2 hc hch ht S
    rwa [card_E2] at this ⊢

end Lvm6.Whir
