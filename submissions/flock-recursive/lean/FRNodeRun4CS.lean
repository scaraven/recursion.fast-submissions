-- New for `flock-recursive` (track SIB): `ATImp` of the siblings' generator (`sibTG`), given that the proof's
-- sibling bytes are what its rows say (`SibOk`).
import FRNodeRun4BT
import FRNodeRun4CB

/-!
# The siblings' `ATImp`

A sibling read (`piDigest` in a queries phase's `fSibs` part, `sibAt`) is an import whose value is the
proof's 32 bytes there. `sibTG`'s rows say, per 16-byte half `c`, `sib_c = r_c + b·(l_c − r_c)` (`b` the
position bit's cell, `l`, `r` the node query's halves on arena₁) at the kinds whose depth is active, and
`sib_c = 0` at the others. **`SibOk`** says the proof's bytes are that (`FRNodeRun4CD.sibOk_of` proves it at
an active slot from the reader's format); **`atImp_sib`** is then the generator's `ATImp`.
-/

namespace FR
namespace N4s
open RecursionFast Rev4 Circ TEval W4 Tpl

/-- **The proof's sibling bytes are the rows'**: at a sibling read whose checks pass, half `c` of the 32 bytes
at `o` is `r_c + b·(l_c − r_c)` where kind `ι`'s depth is active, else `0`. -/
def SibOk (T : BTab) (w : Asg) (π : ℕ) (ι : Kind) (q : ByteArray) : Prop :=
  ∀ o n i p h k, sibAt o = some (n, i, p, h, k) → itemsT[k]? = some (.node i h) →
    1 + offT.getD k 0 + (Item.node i h).slen + 64 ≤ N4c.segB → kinds.all (sibPosOk T n i p h) = true →
    ∀ c < 2, F.ofBytes (bytesAt q (o + 16 * c) 16) =
      if h < (T.lvl ι i).sib then
        w (arC π (qElT k (.node i h) + 2 + c)) + w (bitC π (posCell i p h)) *
          (w (arC π (qElT k (.node i h) + c)) - w (arC π (qElT k (.node i h) + 2 + c)))
      else 0

theorem sibRow_ev {w : Asg} {b L R s : Lin}
    (h : (⟨b, subN L R, subN s R⟩ : Row).Holds w) : s.ev w = R.ev w + b.ev w * (L.ev w - R.ev w) := by
  simp only [Row.Holds, ev_subN] at h
  rw [h]; ring

/-- **`ATImp` of the siblings' generator** (read off an extension `Xa` agreeing with the compile's at the
sibling reads), given `SibOk`. -/
theorem atImp_sib {impl : OpImpl} {X Xa : Ext} {π : ℕ} {T : BTab} {κ : Kind} {inp : Input} {w : Asg}
    (hX : ∀ P cs op, sibCov op = true → stepOut Xa P cs op = stepOut X P cs op)
    (hS : SibOk T w π κ inp.π) : ATImp impl X (sibTG Xa π T).toAT κ inp w := by
  intro P cs pre op k regs vs ok hcov hc hev himp
  have hone := hc.1.1
  have hr := hc.2.2.2
  have hcv : sibCov op = true := hcov
  cases op <;> simp only [sibCov, reduceCtorEq, Bool.false_eq_true] at hcv
  rename_i f o
  obtain ⟨⟨n, i, p, h, kk⟩, hs⟩ := Option.isSome_iff_exists.1 hcv
  have hXe := hX P cs (.piDigest f o) (by simp [sibCov, hs])
  simp only [TG.toAT, sibTG, hs, hXe] at hr
  simp only [evalOp, Res.vals.injEq] at hev; obtain ⟨rfl, -⟩ := hev
  unfold sibRowsS at hr
  split at hr
  · rename_i i' h' s₀ s₁ hit hsl
    split_ifs at hr with hg
    · obtain ⟨rfl, rfl, hb, hpos⟩ := hg
      rw [hsl]
      refine List.Forall₂.cons ⟨rfl, ?_⟩ List.Forall₂.nil
      dsimp only at hr
      have hin : ¬ h' < (T.lvl κ i').sib → kinds.any (fun ι => decide ((T.lvl ι i').sib ≤ h')) = true :=
        fun hact => List.any_eq_true.2 ⟨κ, by cases κ <;> simp [kinds], by simpa using hact⟩
      have hS0 := hS _ _ _ _ _ _ hs hit hb hpos 0 (by norm_num)
      have hS1 := hS _ _ _ _ _ _ hs hit hb hpos 1 (by norm_num)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one] at hS0 hS1
      have h0 : s₀.ev w = F.ofBytes (bytesAt inp.π (absOff f o) 16) := by
        rw [hS0]
        split_ifs with hact
        · rw [sibRow_ev (hr _ (List.mem_append_left _ List.mem_cons_self))]; simp [Lin.ev_cell]
        · rw [if_pos (hin hact)] at hr
          have := hr _ (List.mem_append_right _ List.mem_cons_self)
          simp only [Row.Holds, gateS_ev hc.1, Lin.ev_nil] at this
          rw [show decide ((T.lvl κ i').sib ≤ h') = true by simpa using hact] at this
          simpa [Circ.bitF] using this
      have h1 : s₁.ev w = F.ofBytes (bytesAt inp.π (absOff f o + 16) 16) := by
        rw [hS1]
        split_ifs with hact
        · rw [sibRow_ev (hr _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)))]
          simp [Lin.ev_cell]
        · rw [if_pos (hin hact)] at hr
          have := hr _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
          simp only [Row.Holds, gateS_ev hc.1, Lin.ev_nil] at this
          rw [show decide ((T.lvl κ i').sib ≤ h') = true by simpa using hact] at this
          simpa [Circ.bitF] using this
      simp only [List.map_cons, List.map_nil, encV, dlo, dhi, digestAt_eq, h0, h1, bytesAt_lo, bytesAt_hi]
    · exact absurd (hr _ List.mem_cons_self) (failRT_not hone)
  · exact absurd (hr _ List.mem_cons_self) (failRT_not hone)

/-- **At a sibling read, `XofA`'s output is the compile's** (no template takes a `piDigest`). -/
theorem xofA_sib (π : ℕ) (P : Params) (cs : CS) (op : Op) (hop : sibCov op = true) :
    stepOut (XofA π) P cs op = stepOut (Xof π) P cs op := by
  cases op <;> simp only [sibCov, reduceCtorEq, Bool.false_eq_true] at hop <;>
    simp only [stepOut, XofA, Xof, XofC, tplExt4A, tplExt4, tplExt4S, Ext.orElse, tplExtKM, tplExtF, tplExt, extGetK,
      Option.orElse, Option.filter]

end N4s
end FR
