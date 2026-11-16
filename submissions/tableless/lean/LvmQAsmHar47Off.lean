/- `LvmQAsmHar47Off` (GOLF2 off-path move, group 5 of 48): declarations that the certificate `certified`
   does not use, moved here verbatim (same names, same namespaces and context) from LvmFieldCorrect, LvmLoopInterp, LvmLoopPieces, LvmLoopSound, LvmSelfEval, LvmBitsTab, LvmSigBits, LvmQAsmHar47,
   so that `Solution`'s import closure need not elaborate them. Import this module where they are needed;
   the name -> module map is GOLF2's moved.tsv. -/
import LvmFieldCorrect
import LvmLoopInterp
import LvmLoopPieces
import LvmLoopSound
import LvmSelfEval
import LvmBitsTab
import LvmSigBits
import LvmQAsmHar47
import LvmMPCertOff
import LvmQTypedHarZOff
import LvmMlListLemmas

-- ===== from `LvmFieldCorrect` =====

section
namespace Lvm.FE
open CompPoly.Extension FK
local notation "C" => algebraMap BF64 BF64.Ext3
local notation "g" => BF64.ext3Gen

theorem toExt3_nsmul (n : ℕ) (x : FE) : toExt3 (n • x) = n • toExt3 x := by
  change toExt3 (nsmulRec n x) = _
  induction n with
  | zero => simp [nsmulRec]
  | succ n ih => rw [nsmulRec, toExt3_add, ih, succ_nsmul]

theorem toExt3_zsmul (n : ℤ) (x : FE) : toExt3 (n • x) = n • toExt3 x := by
  rcases n with n | n
  · exact (toExt3_nsmul n x).trans (natCast_zsmul _ _).symm
  · change toExt3 (-(nsmulRec (n + 1) x)) = _
    rw [toExt3_neg, negSucc_zsmul]
    exact congrArg _ (toExt3_nsmul (n + 1) x)

end Lvm.FE
end

section
namespace Lvm.FE
open CompPoly.Extension FK
local notation "C" => algebraMap BF64 BF64.Ext3
local notation "g" => BF64.ext3Gen

/-- `y` is the adjoined root: it maps to CompPoly's `ext3Gen`. -/
theorem toExt3_y : toExt3 y = BF64.ext3Gen := by
  rw [toExt3_eq]
  simp only [y_c, toBF64_zero, toBF64_one, map_zero, map_one, zero_add, one_mul, zero_mul,
    add_zero]

theorem frob_add (m n : ℕ) (x : FE) : frob (m + n) x = frob m (frob n x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [← Nat.add_assoc, frob, ih, frob]

/-- `y` lies in `GF(8)`: `y^(2^3) = y`, so its Frobenius powers have period three. -/
theorem frob_three_y : frob 3 y = y := by decide +kernel

theorem frob_y_mod (k : ℕ) : frob k y = frob (k % 3) y := by
  conv_lhs => rw [← Nat.mod_add_div k 3, frob_add]
  congr 1
  induction k / 3 with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ, Nat.add_comm, frob_add, ih, frob_three_y]

end Lvm.FE
end

section
namespace Lvm.FE
open CompPoly.Extension FK
local notation "C" => algebraMap BF64 BF64.Ext3
local notation "g" => BF64.ext3Gen

/-- **For every `k < 64`, `1, y^(2^k), y^(2^(k+1))` is an `FK`-basis of `FE`**: the determinant of
their `FK`-coordinates is nonzero. Kernel-decided on the word arithmetic. -/
theorem ybasis : ∀ k < 64,
    Matrix.det !![(1 : FE).c₀, (y ^ 2 ^ k).c₀, (y ^ 2 ^ (k + 1)).c₀;
      (1 : FE).c₁, (y ^ 2 ^ k).c₁, (y ^ 2 ^ (k + 1)).c₁;
      (1 : FE).c₂, (y ^ 2 ^ k).c₂, (y ^ 2 ^ (k + 1)).c₂] ≠ 0 := by
  intro k _
  rw [det_coords, ← frob_eq_pow, ← frob_eq_pow, frob_y_mod, frob_y_mod (k + 1)]
  have h3 : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have e : (k + 1) % 3 = (k % 3 + 1) % 3 := by (clear * -; omega)
  rw [e]
  generalize k % 3 = j at h3 ⊢
  interval_cases j <;> decide +kernel

/-- **The encoding is the three `BF64` encodings concatenated**, CompPoly's `ByteCodec (Ext P)`
for `Ext3`. -/
theorem toBytes_eq (x : FE) : (toBytes x).toList =
    (CompPoly.ByteCodec.toBytes (toBF64 x.c₀)).toList ++
      (CompPoly.ByteCodec.toBytes (toBF64 x.c₁)).toList ++
        (CompPoly.ByteCodec.toBytes (toBF64 x.c₂)).toList := by
  simp only [toBytes, Vector.toList_append, ← FK.toBytes_eq]

end Lvm.FE
end

section
namespace Lvm.FE
open CompPoly.Extension FK
local notation "C" => algebraMap BF64 BF64.Ext3
local notation "g" => BF64.ext3Gen

/-- **The decoding is CompPoly's**, coefficient by coefficient: each eight-byte slice is read by
`CanonicalNat.ofBytesModOrder`, as CompPoly's entrywise `Ext` decoder does. -/
theorem toExt3_ofBytes (v : Vector UInt8 24) : toExt3 (ofBytes v) = Ext.ofVector
    #v[CompPoly.CanonicalNat.ofBytesModOrder (Vector.ofFn fun i : Fin 8 => v[i.1]),
      CompPoly.CanonicalNat.ofBytesModOrder (Vector.ofFn fun i : Fin 8 => v[8 + i.1]),
      CompPoly.CanonicalNat.ofBytesModOrder (Vector.ofFn fun i : Fin 8 => v[16 + i.1])] := by
  have h0 : toBF64 (ofBytes v).c₀ = CompPoly.CanonicalNat.ofBytesModOrder
      (Vector.ofFn fun i : Fin 8 => v[i.1]) := FK.ofBytes_eq _
  have h1 : toBF64 (ofBytes v).c₁ = CompPoly.CanonicalNat.ofBytesModOrder
      (Vector.ofFn fun i : Fin 8 => v[8 + i.1]) := FK.ofBytes_eq _
  have h2 : toBF64 (ofBytes v).c₂ = CompPoly.CanonicalNat.ofBytesModOrder
      (Vector.ofFn fun i : Fin 8 => v[16 + i.1]) := FK.ofBytes_eq _
  change Ext.ofVector (P := BF64.ext3Params)
    #v[toBF64 (ofBytes v).c₀, toBF64 (ofBytes v).c₁, toBF64 (ofBytes v).c₂] = _
  rw [h0, h1, h2]

end Lvm.FE
end

-- ===== from `LvmLoopInterp` =====

section
section
namespace Lvm.Loop

theorem Block.tw_eq (B : Block) (τ : Ty) : B.tw τ = rowsW τ B.tpl := rfl

end Lvm.Loop
end
end

section
namespace Lvm.Loop
open FE

theorem Inst.clock_E (i : Inst) : i.clock .E = i.ce := rfl

end Lvm.Loop
end

-- ===== from `LvmLoopPieces` =====

section
section
namespace Lvm.Loop
open FE Program

/-- A row's shape is well typed when the row is. -/
theorem Row.shape_typeOk {r : Row} (h : r.typeOk = true) : r.shape.TypeOk := by
  rcases hop : r.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ | ⟨_ | ⟨k, k₀, k₁⟩, hh⟩
  rotate_right 2
  · simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, E2Fn.arity] at h
    simp only [Shape.TypeOk, Row.shape, Op.kind, hop, List.length_map, List.mem_map]
    refine ⟨by simpa using h.1.1, fun t ⟨a, ha, he⟩ => he ▸ ?_, by simp [h.2]⟩
    simpa using h.1.2 _ (List.mem_map_of_mem (f := fun x : Addr => x.ty) ha)
  · simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, E2Fn.arity] at h
    simp only [Shape.TypeOk, Row.shape, Op.kind, hop, List.length_map, List.mem_map]
    refine ⟨by simpa using h.1.1, fun t ⟨a, ha, he⟩ => he ▸ ?_, by simp [h.2]⟩
    simpa using h.1.2 _ (List.mem_map_of_mem (f := fun x : Addr => x.ty) ha)
  all_goals
    simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, List.all_eq_true,
      List.mem_map] at h <;>
    simp only [Shape.TypeOk, Row.shape, Op.kind, hop, List.length_map, List.mem_map] <;>
    first
    | exact ⟨h.1, h.2.imp id fun h' t ⟨a, ha, he⟩ => he ▸ (by simpa using h' t ⟨a, ha, he⟩)⟩
    | exact h
    | exact ⟨h.1, h.2⟩
    | simp_all

end Lvm.Loop
end
end

section
namespace Lvm.Loop

theorem mem_nub {α : Type} [DecidableEq α] : ∀ (l : List α) (y : α), y ∈ nub l ↔ y ∈ l
  | [], _ => by simp [nub]
  | x :: xs, y => by
    simp only [nub, List.mem_cons, List.mem_filter, mem_nub xs, decide_eq_true_eq]
    by_cases h : y = x <;> simp [h]

theorem nodup_nub {α : Type} [DecidableEq α] : ∀ (l : List α), (nub l).Nodup
  | [] => List.nodup_nil
  | x :: xs => by
    rw [nub, List.nodup_cons]
    exact ⟨fun h => by simp [List.mem_filter] at h, (nodup_nub xs).filter _⟩

/-- Filters of a nodup list by the values of a function, over a nodup list of values covering it,
are a permutation of the list. -/
theorem flatMap_filter_perm {α β : Type} [DecidableEq β] (l : List α) (hl : l.Nodup) (f : α → β)
    (S : List β) (hS : S.Nodup) (hcov : ∀ x ∈ l, f x ∈ S) :
    (S.flatMap fun s => l.filter fun x => decide (f x = s)).Perm l := by
  rw [List.perm_ext_iff_of_nodup _ hl]
  · intro x
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun ⟨_, _, h, _⟩ => h, fun h => ⟨f x, hcov x h, h, rfl⟩⟩
  · rw [List.nodup_flatMap]
    refine ⟨fun s _ => hl.filter _, ?_⟩
    refine hS.imp fun {s s'} hne => ?_
    intro x hx hx'
    simp only [List.mem_filter, decide_eq_true_eq] at hx hx'
    exact hne (hx.2.symm.trans hx'.2)

end Lvm.Loop
end

section
namespace Lvm.Loop
namespace Block
variable (B : Block)

theorem shapes_rowsOf_perm : (B.shapes.flatMap B.rowsOf).Perm (List.range B.tpl.length) := by
  apply flatMap_filter_perm _ List.nodup_range _ _ (nodup_nub _)
  intro t ht
  rw [List.mem_range] at ht
  rw [mem_nub, List.mem_map]
  exact ⟨_, by simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht,
    Option.getD_some]; exact List.getElem_mem ht, rfl⟩

theorem pieces_ts (b : Nat) : ((B.pieces b).flatMap (·.ts)).Perm (List.range B.tpl.length) := by
  have : (B.pieces b).flatMap (·.ts) = B.shapes.flatMap B.rowsOf := by
    simp only [pieces, List.flatMap_assoc, List.flatMap_map]
    congr 1; funext σ
    exact (chunks_spec _ _ (binParts_sum _)).1
  rw [this]; exact B.shapes_rowsOf_perm

end Block
end Lvm.Loop
end

section
namespace Lvm.Loop
namespace Program
variable (Q : Program)

/-- Every (block, template row) pair, through the pieces: each once. -/
theorem pieces_bt_nodup : (Q.pieces.flatMap fun p => p.ts.map (p.blk, ·)).Nodup := by
  have : (Q.pieces.flatMap fun p => p.ts.map (p.blk, ·)) =
      (List.range Q.blocks.length).flatMap fun b =>
        (((Q.blk b).pieces b).flatMap (·.ts)).map (b, ·) := by
    simp only [pieces, List.flatMap_assoc]
    congr 1; funext b
    rw [List.map_flatMap]
    apply List.flatMap_congr
    intro p hp
    rw [((Q.blk b).mem_pieces hp).1]
  rw [this, List.nodup_flatMap]
  refine ⟨fun b _ => ((Q.blk b).pieces_ts b).nodup_iff.mpr List.nodup_range |>.map
    (fun _ _ h => (Prod.mk.inj h).2), ?_⟩
  refine List.nodup_range.imp fun {b b'} hne => ?_
  intro x hx hx'
  simp only [List.mem_map] at hx hx'
  obtain ⟨_, _, rfl⟩ := hx
  obtain ⟨_, _, h⟩ := hx'
  exact hne (Prod.mk.inj h).1.symm

end Program
end Lvm.Loop
end

section
namespace Lvm.Loop
namespace Program
variable (Q : Program)

/-- **Every instance is a piece row.** -/
theorem inst_prow {b jf t : Nat} (hb : b < Q.blocks.length) (hjf : jf < (Q.blk b).size)
    (ht : t < (Q.blk b).tpl.length) :
    ∃ n p x, (n, p, x) ∈ Q.prows ∧ Q.pinst p x = Q.inst b jf t := by
  have htm : t ∈ ((Q.blk b).pieces b).flatMap (·.ts) :=
    ((Q.blk b).pieces_ts b).mem_iff.mpr (List.mem_range.mpr ht)
  obtain ⟨p, hp, htp⟩ := List.mem_flatMap.mp htm
  obtain ⟨hpb, hlen, -⟩ := (Q.blk b).mem_pieces hp
  have hpQ : p ∈ Q.pieces := List.mem_flatMap.mpr ⟨b, List.mem_range.mpr hb, hp⟩
  obtain ⟨n, hn⟩ := List.getElem?_of_mem hpQ
  obtain ⟨i, hi, hti⟩ := List.getElem_of_mem htp
  subst hpb
  have hsz : 0 < (Q.blk p.blk).size := Nat.two_pow_pos _
  refine ⟨n, p, jf + (Q.blk p.blk).size * i, (Q.mem_prows).mpr ⟨hn, ?_⟩, ?_⟩
  · rw [Q.height_eq]
    rw [hlen] at hi
    calc jf + (Q.blk p.blk).size * i < (Q.blk p.blk).size * (i + 1) := by rw [Nat.mul_succ]; (clear hb hlen hn hp hpQ hsz ht hti htm htp; omega)
      _ ≤ (Q.blk p.blk).size * 2 ^ p.a := Nat.mul_le_mul_left _ hi
      _ = 2 ^ p.a * (Q.blk p.blk).size := Nat.mul_comm _ _
  · have h1 : (jf + (Q.blk p.blk).size * i) % (Q.blk p.blk).size = jf := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hjf]
    have h2 : (jf + (Q.blk p.blk).size * i) / (Q.blk p.blk).size = i := by
      rw [Nat.add_mul_div_left _ _ hsz, Nat.div_eq_of_lt hjf, Nat.zero_add]
    simp only [pinst, h1, h2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some, hti]

theorem inst_inj {b jf t b' jf' t' : Nat} (h : Q.inst b jf t = Q.inst b' jf' t') :
    b = b' ∧ jf = jf' ∧ t = t' := by
  simp only [inst, Inst.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.2.1⟩

/-- **Two piece rows with one instance are one piece row.** -/
theorem prow_inj {n x n' x' : Nat} {p p' : Piece} (h : (n, p, x) ∈ Q.prows)
    (h' : (n', p', x') ∈ Q.prows) (he : Q.pinst p x = Q.pinst p' x') : n = n' ∧ p = p' ∧ x = x' := by
  obtain ⟨hn, hx⟩ := (Q.mem_prows).mp h
  obtain ⟨hn', hx'⟩ := (Q.mem_prows).mp h'
  obtain ⟨hb, hjf, ht⟩ := Q.inst_inj he
  have hp : p ∈ Q.pieces := List.mem_of_getElem? hn
  have hp' : p' ∈ Q.pieces := List.mem_of_getElem? hn'
  obtain ⟨-, hlen, -⟩ := Q.mem_pieces hp
  obtain ⟨-, hlen', -⟩ := Q.mem_pieces hp'
  have hsz : 0 < (Q.blk p.blk).size := Nat.two_pow_pos _
  rw [Q.height_eq] at hx hx'
  have hi : x / (Q.blk p.blk).size < p.ts.length := by
    rw [hlen, Nat.div_lt_iff_lt_mul hsz]; exact hx
  have hi' : x' / (Q.blk p'.blk).size < p'.ts.length := by
    rw [hlen', Nat.div_lt_iff_lt_mul (show 0 < (Q.blk p'.blk).size from Nat.two_pow_pos _)]
    exact hx'
  set i := x / (Q.blk p.blk).size
  set i' := x' / (Q.blk p'.blk).size
  have hti : p.ts.getD i 0 = p.ts[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  have hti' : p'.ts.getD i' 0 = p'.ts[i'] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  rw [hti, hti'] at ht
  -- the pair (block, template row) is in piece `n` and in piece `n'`
  have hnn : n = n' := by
    by_contra hne
    have hnd := Q.pieces_bt_nodup
    rw [List.nodup_flatMap] at hnd
    have hlt : n < Q.pieces.length := (List.getElem?_eq_some_iff.mp hn).1
    have hlt' : n' < Q.pieces.length := (List.getElem?_eq_some_iff.mp hn').1
    have hpn : Q.pieces[n] = p := (List.getElem?_eq_some_iff.mp hn).2
    have hpn' : Q.pieces[n'] = p' := (List.getElem?_eq_some_iff.mp hn').2
    have hy : (p.blk, p.ts[i]) ∈ p.ts.map (p.blk, ·) := List.mem_map_of_mem (List.getElem_mem hi)
    have hy' : (p.blk, p.ts[i]) ∈ p'.ts.map (p'.blk, ·) := by
      rw [hb, ht]; exact List.mem_map_of_mem (List.getElem_mem hi')
    rcases Nat.lt_or_gt_of_ne hne with hl | hl
    · have := List.pairwise_iff_getElem.mp hnd.2 n n' hlt hlt' hl
      rw [hpn, hpn'] at this
      exact this hy hy'
    · have := List.pairwise_iff_getElem.mp hnd.2 n' n hlt' hlt hl
      rw [hpn, hpn'] at this
      exact this hy' hy
  subst hnn
  have hpp : p = p' := Option.some.inj (hn.symm.trans hn')
  subst hpp
  have hnd : p.ts.Nodup := by
    have := (List.nodup_flatMap.mp Q.pieces_bt_nodup).1 p hp
    exact List.Nodup.of_map _ this
  have hii : i = i' := (hnd.getElem_inj_iff).mp ht
  refine ⟨rfl, rfl, ?_⟩
  have := Nat.div_add_mod x (Q.blk p.blk).size
  have := Nat.div_add_mod x' (Q.blk p.blk).size
  have hjf' : x % (Q.blk p.blk).size = x' % (Q.blk p.blk).size := hjf
  simp only [i, i'] at hii
  rw [← Nat.div_add_mod x (Q.blk p.blk).size, ← Nat.div_add_mod x' (Q.blk p.blk).size, hii, hjf']

end Program
end Lvm.Loop
end

-- ===== from `LvmLoopSound` =====

section
namespace Lvm.Loop
open FE Program

theorem sep_inj {τ τ' : Ty} (h : sep τ = sep τ') : τ = τ' := by
  cases τ <;> cases τ' <;> first | rfl | exact absurd h (by decide)

theorem limbsOf_inj_rd (M : Mem) {τ : Ty} {u : Nat → FK} {e : Nat}
    (h : (List.range τ.limbs).map u = limbsOf τ (M.rd τ e)) : valOf τ u = M.rd τ e := by
  cases τ
  · simp only [Ty.limbs, List.range_one, List.map_cons, List.map_nil, limbsOf, Mem.rd,
      List.cons.injEq, and_true] at h
    simp only [valOf, Mem.rd, h]; rfl
  · simp only [Ty.limbs, List.range_succ, List.range_zero, List.map_append, List.map_cons,
      List.map_nil, List.nil_append, List.cons_append, limbsOf, Mem.rd, List.cons.injEq,
      and_true] at h
    simp only [valOf, Mem.rd]
    obtain ⟨h0, h1, h2⟩ := h
    rw [h0, h1, h2]

end Lvm.Loop
end

section
namespace Lvm.Loop
open FE Program
namespace Program
variable (Q : Program)

/-- **The committed values of `W` are the cells of `M`**: at every piece row, the result value (for
a writer) and every operand value. -/
def WitnessOf (W : Witness) (M : Mem) : Prop :=
  ∀ n p x, (n, p, x) ∈ Q.prows →
    (p.shape.writes = true → p.shape.resV (Q.rowVal W n p x) = M.res (Q.pinst p x)) ∧
    ∀ o < p.shape.args.length, p.shape.argV (Q.rowVal W n p x) o = M.arg (Q.pinst p x) o

end Program
end Lvm.Loop
end

section
namespace Lvm.Loop
open FE Program
namespace Program
variable (Q : Program)

theorem writer_clock {i : Inst} (hi : i ∈ Q.insts) {τ : Ty} (hw : i.row.writes = some τ) :
    Q.nIn τ ≤ i.clock τ ∧ i.clock τ < Q.cells τ := by
  obtain ⟨hch, hK, hE⟩ := Q.chain_insts
  have hc := chain_clock_le _ _ _ hch i hi
  have hw1 := Row.w_of_writes hw
  cases τ <;> simp only [Ty.ind, if_true, if_false, reduceCtorEq] at hw1
  · have := hw1 .K; simp [Ty.ind] at this
    simp only [Inst.clock, nIn]; omega
  · have := hw1 .E; simp [Ty.ind] at this
    simp only [Inst.clock, nIn]; omega

theorem chain_writer_inj : ∀ (L : List Inst) (k e : Nat), Chain k e L → ∀ {τ : Ty} {i i' : Inst},
    i ∈ L → i' ∈ L → i.row.writes = some τ → i'.row.writes = some τ → i.clock τ = i'.clock τ →
      i = i'
  | [], _, _, _, _, _, _, h, _, _, _, _ => by simp at h
  | j :: L, k, e, ⟨hk, he, hch⟩, τ, i, i', hi, hi', hw, hw', hc => by
    have hlow : j.row.writes = some τ → ∀ i'' ∈ L, j.clock τ < i''.clock τ := by
      intro hj i'' hm
      have hc := chain_clock_le _ _ _ hch i'' hm
      have hw1 := Row.w_of_writes hj
      cases τ
      · have : j.row.w .K = 1 := (hw1 .K).trans rfl
        simp only [Inst.clock]; omega
      · have : j.row.w .E = 1 := (hw1 .E).trans rfl
        simp only [Inst.clock]; omega
    rcases List.mem_cons.mp hi with rfl | hiL <;> rcases List.mem_cons.mp hi' with rfl | hiL'
    · rfl
    · exact absurd hc (Nat.ne_of_lt (hlow hw _ hiL'))
    · exact absurd hc.symm (Nat.ne_of_lt (hlow hw' _ hiL))
    · exact chain_writer_inj L _ _ hch hiL hiL' hw hw' hc

/-- A writer piece row of memory `τ` writing cell `e`. -/
def WRow (τ : Ty) (e : Nat) (npx : Nat × Piece × Nat) : Prop :=
  npx ∈ Q.prows ∧ npx.2.1.shape.writes = true ∧ npx.2.1.shape.ty = τ ∧
    (Q.pinst npx.2.1 npx.2.2).clock τ = e

/-- **One writer row per cell.** -/
theorem wrow_unique {τ : Ty} {e : Nat} {a b : Nat × Piece × Nat} (ha : Q.WRow τ e a)
    (hb : Q.WRow τ e b) : a = b := by
  obtain ⟨ha1, ha2, ha3, ha4⟩ := ha
  obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
  have hwa := (Q.writer_row ha1 ha2).1
  have hwb := (Q.writer_row hb1 hb2).1
  rw [ha3] at hwa; rw [hb3] at hwb
  have hi := chain_writer_inj Q.insts _ _ Q.chain_insts.1 (Q.prow_inst ha1).1 (Q.prow_inst hb1).1
    hwa hwb (ha4.trans hb4.symm)
  obtain ⟨n, p, x⟩ := a
  obtain ⟨n', p', x'⟩ := b
  obtain ⟨h1, h2, h3⟩ := Q.prow_inj ha1 hb1 hi
  subst h1 h2 h3; rfl

open Classical in
/-- The value the seeds give cell `e` of memory `τ` past the inputs: its writer row's result. -/
noncomputable def wval (W : Witness) (τ : Ty) (e : Nat) : FE :=
  if h : ∃ npx, Q.WRow τ e npx then
    (Classical.choose h).2.1.shape.resV
      (Q.rowVal W (Classical.choose h).1 (Classical.choose h).2.1 (Classical.choose h).2.2)
  else 0

/-- **The memory the seeds define**: the inputs, then every cell's writer row's result. -/
noncomputable def seedMem (W : Witness) (inK : Array FK) (inE : Array FE) : Mem :=
  ⟨fun e => if e < Q.nInK then inK.getD e 0 else (Q.wval W .K e).c₀,
    fun e => if e < Q.nInE then inE.getD e 0 else Q.wval W .E e⟩

theorem wval_eq (W : Witness) {τ : Ty} {e : Nat} {npx : Nat × Piece × Nat} (h : Q.WRow τ e npx) :
    Q.wval W τ e = npx.2.1.shape.resV (Q.rowVal W npx.1 npx.2.1 npx.2.2) := by
  have hex : ∃ npx, Q.WRow τ e npx := ⟨npx, h⟩
  rw [wval, dif_pos hex, Q.wrow_unique (Classical.choose_spec hex) h]

theorem seedMem_writer (W : Witness) (inK : Array FK) (inE : Array FE) {n x : Nat} {p : Piece}
    (h : (n, p, x) ∈ Q.prows) (hw : p.shape.writes = true) :
    (Q.seedMem W inK inE).res (Q.pinst p x) = p.shape.resV (Q.rowVal W n p x) := by
  obtain ⟨hwr, hty⟩ := Q.writer_row
    (npx := (n, p, x)) h hw
  have hcl := Q.writer_clock (Q.prow_inst h).1 hwr
  have hW : Q.WRow p.shape.ty ((Q.pinst p x).clock p.shape.ty) (n, p, x) := ⟨h, hw, rfl, rfl⟩
  simp only [Mem.res]
  rw [hty]
  cases hτ : p.shape.ty
  · rw [hτ] at hW hcl
    simp only [Mem.rd, seedMem, nIn] at hcl ⊢
    rw [if_neg (by omega), Q.wval_eq W hW]
    simp only [Shape.resV, hτ, valOf]; rfl
  · rw [hτ] at hW hcl
    simp only [Mem.rd, seedMem, nIn] at hcl ⊢
    rw [if_neg (by omega), Q.wval_eq W hW]

/-- **What a seed is**: the key of cell `e < cells τ` of the seed memory. -/
theorem seed_cases (W : Witness) (inK : Array FK) (inE : Array FE) {m : Msg}
    (hm : m ∈ Q.seedMsgs W inK inE) :
    ∃ τ e, e < Q.cells τ ∧ m.sep = sep τ ∧ m.addr = FK.x ^ e ∧
      m.val = limbsOf τ ((Q.seedMem W inK inE).rd τ e) := by
  have hinK : Q.nInK ≤ Q.cells .K := by
    have := Q.chain_insts.2.1; omega
  have hinE : Q.nInE ≤ Q.cells .E := by
    have := Q.chain_insts.2.2; omega
  simp only [seedMsgs, inputSeeds, List.mem_append, List.mem_map, List.mem_range,
    List.mem_flatMap] at hm
  rcases hm with (⟨e, he, rfl⟩ | ⟨e, he, rfl⟩) | ⟨⟨n, p, x⟩, hpx, hm⟩
  · exact ⟨.K, e, by omega, rfl, rfl, by simp [limbsOf, Mem.rd, seedMem, he, FE.ofK]⟩
  · exact ⟨.E, e, by omega, rfl, rfl, by simp [limbsOf, Mem.rd, seedMem, he]⟩
  · split at hm
    · rename_i hw
      simp only [List.mem_singleton] at hm
      subst hm
      obtain ⟨hwr, hty⟩ := Q.writer_row
        (npx := (n, p, x)) hpx hw
      have hcl := Q.writer_clock (Q.prow_inst hpx).1 hwr
      refine ⟨p.shape.ty, (Q.pinst p x).clock p.shape.ty, hcl.2, rfl, ?_, ?_⟩
      · simp [Shape.seedFlush, Flush.msg, rowVal, fval, fvalBasic, hty]
      · have := Q.seedMem_writer W inK inE hpx hw
        simp only [Mem.res, hty] at this
        rw [this]
        simp only [Shape.seedFlush, Flush.msg, Shape.resVals, List.map_map]
        cases hτ : p.shape.ty
        · simp [Shape.resV, hτ, valOf, limbsOf, Ty.limbs, rowVal, FE.ofK]
        · simp [Shape.resV, hτ, valOf, limbsOf, Ty.limbs, rowVal, List.range_succ]
    · simp at hm

theorem shape_args {n x : Nat} {p : Piece} (h : (n, p, x) ∈ Q.prows) :
    p.shape.args = (Q.pinst p x).row.args.map (·.ty) := by
  rw [← (Q.prow_inst h).2]; rfl

theorem shape_arg_ty {n x : Nat} {p : Piece} (h : (n, p, x) ∈ Q.prows) {o : Nat}
    (ho : o < p.shape.args.length) : p.shape.args.getD o .K = ((Q.pinst p x).arg o).ty := by
  have ha := Q.shape_args h
  have ho' : o < (Q.pinst p x).row.args.length := by rw [ha] at ho; simpa using ho
  rw [ha]
  simp [Inst.arg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ho']

/-- The bus hypothesis, for one message. -/
theorem bus_key {W : Witness} {inK : Array FK} {inE : Array FE}
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key) {n x : Nat}
    {p : Piece} (h : (n, p, x) ∈ Q.prows) {f : Flush} (hf : f ∈ p.shape.readFlushes) :
    ∃ τ e, e < Q.cells τ ∧ f.sep = sep τ ∧ f.addr.ev (Q.rowVal W n p x) = FK.x ^ e ∧
      f.val.map (·.ev (Q.rowVal W n p x)) = limbsOf τ ((Q.seedMem W inK inE).rd τ e) := by
  have hm : f.msg (Q.rowVal W n p x) ∈ Q.readMsgs W := by
    simp only [readMsgs, List.mem_flatMap, List.mem_map]
    exact ⟨(n, p, x), h, f, hf, rfl⟩
  obtain ⟨s, hs, hk⟩ := List.mem_map.mp (hbus _ hm)
  obtain ⟨τ, e, he, h1, h2, h3⟩ := Q.seed_cases W inK inE hs
  simp only [Msg.key, Flush.msg, Prod.mk.injEq] at hk
  exact ⟨τ, e, he, hk.1.symm.trans h1, hk.2.1.symm.trans h2, hk.2.2.symm.trans h3⟩

/-- **Every operand read is the seed memory's cell.** -/
theorem read_ok (hwf : Q.wf = true) {W : Witness} {inK : Array FK} {inE : Array FE}
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) {n x : Nat} {p : Piece}
    (h : (n, p, x) ∈ Q.prows) {o : Nat} (ho : o < p.shape.args.length) :
    p.shape.argV (Q.rowVal W n p x) o = (Q.seedMem W inK inE).arg (Q.pinst p x) o := by
  have hf : (⟨false, sep (p.shape.args.getD o .K), Poly2.var (.fix (.arg o)), Poly2.var (.cnt o),
      p.shape.argVals o⟩ : Flush) ∈ p.shape.readFlushes := by
    simp only [Shape.readFlushes, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl ⟨o, ho, rfl⟩
  obtain ⟨τ, e, he, h1, h2, h3⟩ := Q.bus_key hbus h hf
  have hτ' := Q.shape_arg_ty h ho
  have hτ : ((Q.pinst p x).arg o).ty = τ := by rw [← hτ']; exact sep_inj h1
  have hok := Q.instOk_of_mem hwf (Q.prow_inst h).1
  have hmem : (Q.pinst p x).arg o ∈ (Q.pinst p x).row.args := by
    apply arg_mem; rw [Q.shape_args h] at ho; simpa using ho
  have hlt := lt_of_lt_of_le (hok.reads _ hmem) (hok.cells _)
  simp only [Poly2.ev_var, rowVal, fval, fvalBasic] at h2
  have hN : ∀ σ, Q.cells σ ≤ max (Q.cells .K) (Q.cells .E) := fun σ => by cases σ <;> simp
  rw [hτ] at hlt
  have hee : ((Q.pinst p x).arg o).at (Q.pinst p x).j = e :=
    hinj _ _ (lt_of_lt_of_le hlt (hN _)) (lt_of_lt_of_le he (hN _)) h2
  simp only [Shape.argVals, List.map_map, Function.comp_def, Poly2.ev_var] at h3
  unfold Shape.argV
  rw [Mem.arg, hτ', hτ, hee]
  rw [argLimbs_eq, hτ', hτ] at h3
  exact limbsOf_inj_rd _ h3

/-- **A computed-address read is the seed memory's cell at that address.** -/
theorem readd_ok {W : Witness} {inK : Array FK} {inE : Array FE}
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key) {n x : Nat}
    {p : Piece} (h : (n, p, x) ∈ Q.prows) (hk : p.shape.kind = .readd) :
    ∃ e < Q.cells p.shape.ty, FK.x ^ e = Q.rowVal W n p x (.arg 0 0) ∧
      p.shape.resV (Q.rowVal W n p x) = (Q.seedMem W inK inE).rd p.shape.ty e := by
  have hf : (⟨false, sep p.shape.ty, Poly2.var (.arg 0 0), Poly2.var .dcnt, p.shape.resVals⟩ : Flush)
      ∈ p.shape.readFlushes := by
    simp [Shape.readFlushes, hk]
  obtain ⟨τ, e, he, h1, h2, h3⟩ := Q.bus_key hbus h hf
  have hτ := sep_inj h1
  subst hτ
  refine ⟨e, he, by simpa using h2.symm, ?_⟩
  simp only [Shape.resVals, List.map_map, Function.comp_def, Poly2.ev_var] at h3
  exact limbsOf_inj_rd _ h3

theorem fval_k {n x : Nat} {p : Piece} {W : Witness} {k k' : FK}
    (hop : (Q.pinst p x).row.op = .lin k k') :
    Q.rowVal W n p x (.fix .k) = k ∧ Q.rowVal W n p x (.fix .k') = k' := by
  simp [rowVal, fval, fvalBasic, hop]

theorem fval_k2 {n x : Nat} {p : Piece} {W : Witness} {k k₀ k₁ : FK} {hh : Bool}
    (hop : (Q.pinst p x).row.op = .e2 (.lin k k₀ k₁) hh) :
    Q.rowVal W n p x (.fix .k) = k ∧ Q.rowVal W n p x (.fix .k') = if hh then k₁ else k₀ := by
  simp [rowVal, fval, fvalBasic, hop]

/-- **The tables give every instance's relation and assertion on the seed memory.** -/
theorem holds_seedMem (hwf : Q.wf = true) {W : Witness} {inK : Array FK} {inE : Array FE}
    (hcons : Q.ConstraintsHold W)
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) :
    Q.Holds (Q.seedMem W inK inE) ∧ Q.Asserts (Q.seedMem W inK inE) := by
  have key : ∀ i ∈ Q.insts, Q.RowDef (Q.seedMem W inK inE) i ∧
      Program.RowAssert (Q.seedMem W inK inE) i := by
    intro i hi
    obtain ⟨b, hb, jf, hjf, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
    obtain ⟨n, p, x, hpx, hpi⟩ := Q.inst_prow hb hjf ht
    rw [← hpi]
    set M := Q.seedMem W inK inE
    set v := Q.rowVal W n p x
    set i := Q.pinst p x
    have hsh : i.row.shape = p.shape := (Q.prow_inst hpx).2
    have hok := Q.instOk_of_mem hwf (Q.prow_inst hpx).1
    have hrel := constraints_sound p.shape (hsh ▸ Row.shape_typeOk hok.typeOk) v
      (fun C hC => hcons (n, p, x) hpx C hC)
    have hlen : p.shape.args.length = i.row.args.length := by
      rw [← hsh]; simp [Row.shape]
    have ha : ∀ o < i.row.args.length, p.shape.argV v o = M.arg i o :=
      fun o ho => Q.read_ok hwf hbus hinj hpx (by omega)
    have hres : p.shape.writes = true → p.shape.resV v = M.res i :=
      fun hw => (Q.seedMem_writer W inK inE hpx hw).symm
    have hkind : p.shape.kind = i.row.op.kind := by rw [← hsh]; rfl
    have hty : i.row.typeOk = true := hok.typeOk
    rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ | ⟨_ | ⟨k, k₀, k₁⟩, hh⟩ <;>
      rw [hop] at hkind <;> simp only [Op.kind] at hkind <;>
      simp only [Row.typeOk, hop, Bool.and_eq_true, beq_iff_eq, List.length_map] at hty
    · simp only [Shape.Rel, hkind] at hrel
      have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      have hl : i.row.args.length = 3 := hty.1
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      rw [← hres hw, hrel, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega)]
    · simp only [Shape.Rel, hkind] at hrel
      have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      have hl : i.row.args.length = 2 := hty.1
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      have hk1 : v (.fix .k) = k := (Q.fval_k (W := W) (n := n) hop).1
      have hk2 : v (.fix .k') = k' := (Q.fval_k (W := W) (n := n) hop).2
      rw [← hres hw, hrel, ha 0 (by omega), ha 1 (by omega), hk1, hk2]
    · simp only [Shape.Rel, hkind] at hrel
      have hl : i.row.args.length = 2 := hty
      refine ⟨by simp [RowDef, hop], ?_⟩
      simp only [RowAssert, hop]
      rw [← ha 0 (by omega), ← ha 1 (by omega)]
      exact hrel
    · simp only [Shape.Rel, hkind] at hrel
      have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      have hl : i.row.args.length = 3 := by
        have := congrArg List.length hty.1; simpa using this
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      rw [← hres hw, hrel, ha 0 (by omega), ha 1 (by omega), ha 2 (by omega)]
    · simp only [Shape.Rel, hkind] at hrel
      have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      have hF : v (.fix .F) = Q.fixMat i.j := rfl
      have hl : i.row.args.length = 2 := hty.1
      rw [← hres hw, hrel, ha 0 (by omega), ha 1 (by omega), hF]
    · have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      have hl : i.row.args.length = 1 := by
        have := congrArg List.length hty; simpa using this
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      obtain ⟨e, he, hpow, hval⟩ := Q.readd_ok hbus hpx hkind
      have htyeq : p.shape.ty = i.row.ty := (Q.writer_row (npx := (n, p, x)) hpx hw).2.symm
      have h0 := ha 0 (by omega)
      have hty' : (Q.pinst p x).row.args.map (·.ty) = [Ty.K] := hty
      have hK0 : p.shape.args.getD 0 .K = .K := by
        rw [Q.shape_args hpx, hty']; rfl
      rw [argV_K hK0] at h0
      refine ⟨e, htyeq ▸ he, ?_, ?_⟩
      · rw [← h0]; exact hpow
      · rw [← hres hw, hval, htyeq]
    -- the `E2` rows (lvm2 E2F): their operands are `K`, so the shape's operand values are the cells'
    all_goals
      simp only [Shape.Rel, hkind] at hrel
      have hw : p.shape.writes = true := by simp [Shape.writes, hkind]
      have hK : ∀ o < i.row.args.length, (M.arg i o).c₀ = v (.arg o 0) := by
        intro o ho
        have hK0 : p.shape.args.getD o .K = .K := by
          rw [Q.shape_arg_ty hpx (by rw [hlen]; exact ho)]
          exact beq_iff_eq.mp (List.all_eq_true.mp hty.1.2 _
            (List.mem_map_of_mem (f := fun a : Addr => a.ty) (arg_mem ho)))
        rw [← ha o ho, argV_K hK0]; rfl
      refine ⟨?_, by simp [RowAssert, hop]⟩
      simp only [RowDef, hop]
      rw [← hres hw, hrel, E2Fn.val_congr _ (a := fun o => (M.arg i o).c₀) (b := fun o => v (.arg o 0))
        (fun o ho => hK o (by have hl := hty.1.1; simp only [E2Fn.arity] at ho hl; omega))]
    have hk1 : v (.fix .k) = k := (Q.fval_k2 (W := W) (n := n) hop).1
    have hk2 : v (.fix .k') = if hh then k₁ else k₀ := (Q.fval_k2 (W := W) (n := n) hop).2
    rw [hk1, hk2]
    cases hh <;> rfl
  exact ⟨fun i hi => (key i hi).1, fun i hi => (key i hi).2⟩

theorem cells_pick (τ : Ty) : τ.pick (Q.cells .K) (Q.cells .E) = Q.cells τ := by cases τ <;> rfl

/-- **`loopir_sound`.** Tables that satisfy their constraints, with a bus that matches every read to
a seed, are the interpreter's run: every committed value is the interpreter's cell, and every gated
assertion holds. -/
theorem loopir_sound (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (W : Witness)
    (hcons : Q.ConstraintsHold W)
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E)))
    (hinb : (Q.interp inK inE).inb = true) :
    Q.WitnessOf W (Q.interpMem inK inE) ∧ (Q.interp inK inE).ok = true := by
  set M := Q.seedMem W inK inE
  obtain ⟨hH, hA⟩ := Q.holds_seedMem hwf hcons hbus hinj
  have hin : Q.Inputs M inK inE :=
    ⟨fun n hn => by simp [M, seedMem, hn], fun n hn => by simp [M, seedMem, hn]⟩
  obtain ⟨hag, hok⟩ := Q.interp_unique hwf inK inE hsz M hin hH hinj hinb
  refine ⟨fun n p x h => ⟨fun hw => ?_, fun o ho => ?_⟩, hok.mpr hA⟩
  · have hwr := Q.writer_row (npx := (n, p, x)) h hw
    have hcl := Q.writer_clock (Q.prow_inst h).1 hwr.1
    simp only at hwr hcl
    rw [← Q.seedMem_writer W inK inE h hw]
    simp only [Mem.res]
    rw [hwr.2]
    exact Mem.rd_agree' hag _ _ (by rw [Q.cells_pick]; exact hcl.2)
  · rw [Q.read_ok hwf hbus hinj h ho, Mem.arg]
    have hok := Q.instOk_of_mem hwf (Q.prow_inst h).1
    have hmem : (Q.pinst p x).arg o ∈ (Q.pinst p x).row.args := by
      apply arg_mem; rw [Q.shape_args h] at ho; simpa using ho
    have hlt := lt_of_lt_of_le (hok.reads _ hmem) (hok.cells _)
    exact Mem.rd_agree' hag _ _ (by rw [Q.cells_pick]; exact hlt)

end Program
end Lvm.Loop
end

-- ===== from `LvmSelfEval` =====

section
section
namespace Lvm.Loop
open FE Program

theorem mle_add (r : List FE) (u w : Nat → FE) : mle r (fun x => u x + w x) = mle r u + mle r w := by
  have := mle_lin r 1 1 u w
  simp only [one_mul] at this
  exact this

end Lvm.Loop
end
end

section
section
namespace Lvm.Loop
open FE Program

theorem ofK_one' : FE.ofK 1 = 1 := rfl

end Lvm.Loop
end
end

section
namespace Lvm.Loop
open FE Program

theorem foldl_inb_true (Q : Program) : ∀ (L : List Inst) (s : St), s.inb = true →
    (∀ i ∈ L, ∀ lo m, i.row.op ≠ .readd lo m) → (L.foldl Q.step s).inb = true
  | [], _, h, _ => h
  | i :: L, s, h, hL => by
    apply foldl_inb_true Q L
    · rcases hop : i.row.op with _ | ⟨k, k'⟩ | _ | _ | _ | ⟨lo, m⟩ <;>
        simp only [step, hop, St.put_inb] <;> first | exact h | exact absurd hop (hL i (by simp) lo m)
    · exact fun j hj => hL j (by simp [hj])

/-- No row of any block is a `readd`. -/
def Program.noReadd (Q : Program) : Bool :=
  Q.blocks.all fun B => B.tpl.all fun r => match r.op with
    | .readd .. => false
    | _ => true

theorem inb_of_noReadd (Q : Program) (h : Q.noReadd = true) (inK : Array FK) (inE : Array FE) :
    (Q.interp inK inE).inb = true := by
  refine foldl_inb_true Q _ _ rfl fun i hi lo m hop => ?_
  obtain ⟨b, hb, jf, -, t, ht, rfl⟩ := (Q.mem_insts i).mp hi
  simp only [Program.noReadd, List.all_eq_true] at h
  have hB := h _ (List.getElem_mem hb)
  rw [← Q.blk_eq hb] at hB
  have hr := hB ((Q.blk b).tpl.getD t default) (by
    rw [List.getD_eq_getElem _ _ ht]; exact List.getElem_mem ht)
  have hop' : ((Q.blk b).tpl.getD t default).op = .readd lo m := hop
  rw [hop'] at hr
  exact absurd hr (by simp)

/-- One level of an `eq` table: the cells `prev + x` (`x < 2^k`) times `1 - ρ` and `ρ` (the cells
`omr` and `rho`), plus the zero cell, written at `2x` and `2x + 1`. -/
def eqLevel (k prev rho omr zero : Nat) : Block :=
  ⟨[k], [⟨.muladd, .E, [⟨.E, prev, [1]⟩, ⟨.E, omr, []⟩, ⟨.E, zero, []⟩]⟩,
    ⟨.muladd, .E, [⟨.E, prev, [1]⟩, ⟨.E, rho, []⟩, ⟨.E, zero, []⟩]⟩]⟩

end Lvm.Loop
end

section
namespace Lvm.Loop
open FE Program

theorem eqLevel_step {Q : Program} {b k prev rho omr zero : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = eqLevel k prev rho omr zero) {M : Mem} (hM : Q.Holds M) {x : Nat}
    (hx : x < 2 ^ k) (t : Nat) (ht : t < 2) :
    M.e (Q.start .E b + (2 * x + t)) =
      M.e (prev + x) * M.e (if t = 0 then omr else rho) + M.e zero := by
  have hsz : x < (Q.blk b).size := by simp [Block.size, Block.lsize, hB, eqLevel]; exact hx
  have hi := (Q.mem_insts (Q.inst b x t)).mpr ⟨b, hb, _, hsz, t, by simp [hB, eqLevel]; (clear * - ht; omega), rfl⟩
  have hd := hM _ hi
  have hj : (Q.inst b x t).j = [x] := by
    show unflat (Q.blk b).dims x = [x]; rw [hB]; exact unflat_one hx
  have hce : (Q.inst b x t).ce = Q.start .E b + (2 * x + t) := by
    show Q.start .E b + (Q.blk b).tw .E * x + (Q.blk b).rank .E t = _
    rw [hB]
    interval_cases t <;> simp [Block.tw, Block.rank, eqLevel, Row.w, Row.writes] <;> ring
  interval_cases t
  · have hrow : (Q.inst b x 0).row =
        ⟨.muladd, .E, [⟨.E, prev, [1]⟩, ⟨.E, omr, []⟩, ⟨.E, zero, []⟩]⟩ := by
      simp [Program.inst, hB, eqLevel]
    simp only [RowDef, hrow, Mem.res, Mem.arg, Inst.arg, Inst.clock, hj, hce, Mem.rd,
      List.getD_cons_zero, List.getD_cons_succ, Addr.at, dot, Nat.one_mul, Nat.add_zero] at hd
    simpa using hd
  · have hrow : (Q.inst b x 1).row =
        ⟨.muladd, .E, [⟨.E, prev, [1]⟩, ⟨.E, rho, []⟩, ⟨.E, zero, []⟩]⟩ := by
      simp [Program.inst, hB, eqLevel]
    simp only [RowDef, hrow, Mem.res, Mem.arg, Inst.arg, Inst.clock, hj, hce, Mem.rd,
      List.getD_cons_zero, List.getD_cons_succ, Addr.at, dot, Nat.one_mul, Nat.add_zero] at hd
    simpa using hd

theorem eqLevel_spec {Q : Program} {b k prev rho omr zero : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = eqLevel k prev rho omr zero) {M : Mem} (hM : Q.Holds M) {pt : List FE}
    (hprev : ∀ x < 2 ^ k, M.e (prev + x) = eqW pt x) (hz : M.e zero = 0)
    (homr : M.e omr = 1 - M.e rho) :
    ∀ y < 2 ^ (k + 1), M.e (Q.start .E b + y) = eqW (M.e rho :: pt) y := by
  intro y hy
  have hx : y / 2 < 2 ^ k := by rw [pow_succ] at hy; (clear * - hy; omega)
  rcases Nat.mod_two_eq_zero_or_one y with h0 | h1
  · have hy2 : y = 2 * (y / 2) + 0 := by (clear * - h0; omega)
    rw [hy2, eqLevel_step hb hB hM hx 0 (by (clear * -; omega)), Nat.add_zero, eqW_even, hprev _ hx, if_pos rfl,
      homr, hz]
    ring
  · have hy2 : y = 2 * (y / 2) + 1 := by (clear * - h1; omega)
    rw [hy2, eqLevel_step hb hB hM hx 1 (by (clear * -; omega)), eqW_odd, hprev _ hx, if_neg (by (clear * -; omega)), hz]
    ring

/-- The prologue: one zero per glue column (`z + 0·z + 0`, `z` the zero cell). -/
def fixPro (dc zero : Nat) : Block :=
  ⟨[dc], [⟨.lin 0 0, .E, [⟨.E, zero, []⟩, ⟨.E, zero, []⟩]⟩]⟩

/-- The self-evaluation block: `acc[c, x] = F_c(x)·eq[x] + acc[c, x - 1]`, `acc[c, x]` the cell
`s₀ + c + 2^dc·x` (`s₀` the block's first `E` cell), `eq[x]` the cell `eb + x`. -/
def fixBlock (dc dx eb s₀ : Nat) : Block :=
  ⟨[dc, dx], [⟨.fixmul, .E, [⟨.E, eb, [0, 1]⟩, ⟨.E, s₀ - 2 ^ dc, [1, 2 ^ dc]⟩]⟩]⟩

theorem fixPro_spec {Q : Program} {b dc zero : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = fixPro dc zero) {M : Mem} (hM : Q.Holds M) (hz : M.e zero = 0) :
    ∀ c < 2 ^ dc, M.e (Q.start .E b + c) = 0 := by
  intro c hc
  have hsz : c < (Q.blk b).size := by simp [Block.size, Block.lsize, hB, fixPro]; exact hc
  have hi := (Q.mem_insts (Q.inst b c 0)).mpr ⟨b, hb, _, hsz, 0, by simp [hB, fixPro], rfl⟩
  have hd := hM _ hi
  have hrow : (Q.inst b c 0).row = ⟨.lin 0 0, .E, [⟨.E, zero, []⟩, ⟨.E, zero, []⟩]⟩ := by
    simp [Program.inst, hB, fixPro]
  have hce : (Q.inst b c 0).ce = Q.start .E b + c := by
    show Q.start .E b + (Q.blk b).tw .E * c + (Q.blk b).rank .E 0 = _
    rw [hB]; simp [Block.tw, Block.rank, fixPro, Row.w, Row.writes]
  simp only [RowDef, hrow, Mem.res, Mem.arg, Inst.arg, Inst.clock, hce, Mem.rd,
    List.getD_cons_zero, List.getD_cons_succ, Addr.at, dot, Nat.add_zero] at hd
  rw [hd, hz, show FE.ofK 0 = 0 from rfl]
  ring

theorem fixBlock_step {Q : Program} {b dc dx eb s₀ : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = fixBlock dc dx eb s₀) (hs : s₀ = Q.start .E b) {M : Mem} (hM : Q.Holds M)
    {c y : Nat} (hc : c < 2 ^ dc) (hy : y < 2 ^ dx) :
    M.e (s₀ + (c + 2 ^ dc * y)) =
      FE.ofK (Q.fixMat [c, y]) * M.e (eb + y) + M.e (s₀ - 2 ^ dc + (c + 2 ^ dc * y)) := by
  have hlt : c + 2 ^ dc * y < 2 ^ dc * 2 ^ dx := by
    have e1 : 2 ^ dc * (y + 1) = 2 ^ dc * y + 2 ^ dc := by ring
    have e2 : 2 ^ dc * (y + 1) ≤ 2 ^ dc * 2 ^ dx := Nat.mul_le_mul_left _ (by (clear * - hy; omega))
    (clear * - hc e1 e2; omega)
  have hsz : c + 2 ^ dc * y < (Q.blk b).size := by
    rw [show (Q.blk b).size = 2 ^ dc * 2 ^ dx by simp [Block.size, Block.lsize, hB, fixBlock, pow_add]]
    exact hlt
  have hi := (Q.mem_insts (Q.inst b (c + 2 ^ dc * y) 0)).mpr
    ⟨b, hb, _, hsz, 0, by simp [hB, fixBlock], rfl⟩
  have hd := hM _ hi
  have hj : (Q.inst b (c + 2 ^ dc * y) 0).j = [c, y] := by
    show unflat (Q.blk b).dims _ = _; rw [hB]; exact unflat_two hc hy
  have hrow : (Q.inst b (c + 2 ^ dc * y) 0).row =
      ⟨.fixmul, .E, [⟨.E, eb, [0, 1]⟩, ⟨.E, s₀ - 2 ^ dc, [1, 2 ^ dc]⟩]⟩ := by
    simp [Program.inst, hB, fixBlock]
  have hce : (Q.inst b (c + 2 ^ dc * y) 0).ce = s₀ + (c + 2 ^ dc * y) := by
    show Q.start .E b + (Q.blk b).tw .E * _ + (Q.blk b).rank .E 0 = _
    rw [hB, ← hs]; simp [Block.tw, Block.rank, fixBlock, Row.w, Row.writes]
  simp only [RowDef, hrow, Mem.res, Mem.arg, Inst.arg, Inst.clock, hj, hce, Mem.rd,
    List.getD_cons_zero, List.getD_cons_succ, Addr.at, dot, Nat.zero_mul, Nat.one_mul, Nat.add_zero,
    Nat.zero_add] at hd
  exact hd

/-- **The accumulator recursion**, summed. -/
theorem fixmul_acc {Q : Program} {b dc dx eb s₀ : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = fixBlock dc dx eb s₀) (hs : s₀ = Q.start .E b) (h2 : 2 ^ dc ≤ s₀)
    {M : Mem} (hM : Q.Holds M) {c : Nat} (hc : c < 2 ^ dc) :
    ∀ x < 2 ^ dx, M.e (s₀ + (c + 2 ^ dc * x)) = M.e (s₀ - 2 ^ dc + c) +
      ∑ x' ∈ Finset.range (x + 1), FE.ofK (Q.fixMat [c, x']) * M.e (eb + x') := by
  intro x hx
  induction x with
  | zero =>
    rw [fixBlock_step hb hB hs hM hc hx, Finset.sum_range_one]
    simp only [Nat.mul_zero, Nat.add_zero]
    ring
  | succ x ih =>
    rw [fixBlock_step hb hB hs hM hc hx, show s₀ - 2 ^ dc + (c + 2 ^ dc * (x + 1)) =
      s₀ + (c + 2 ^ dc * x) by rw [Nat.mul_succ]; (clear * - hs h2; omega), ih (by (clear * - hx; omega)),
      Finset.sum_range_succ _ (x + 1)]
    ring

/-- **The accumulator is the extension of the glue column.** With the `eq` cells holding `eqW r`
(`|r| = dx`) and zero initial values, the last accumulator of column `c` is `mle r F_c`. -/
theorem fixmul_mle {Q : Program} {b dc dx eb s₀ : Nat} (hb : b < Q.blocks.length)
    (hB : Q.blk b = fixBlock dc dx eb s₀) (hs : s₀ = Q.start .E b) (h2 : 2 ^ dc ≤ s₀)
    {M : Mem} (hM : Q.Holds M) {r : List FE} (hr : r.length = dx)
    (heq : ∀ x < 2 ^ dx, M.e (eb + x) = eqW r x) (hinit : ∀ c < 2 ^ dc, M.e (s₀ - 2 ^ dc + c) = 0)
    {c : Nat} (hc : c < 2 ^ dc) :
    M.e (s₀ + (c + 2 ^ dc * (2 ^ dx - 1))) = mle r (fun x => FE.ofK (Q.fixMat [c, x])) := by
  rw [fixmul_acc hb hB hs h2 hM hc _ (by have := Nat.two_pow_pos dx; (clear * - this; omega)), hinit c hc, zero_add,
    mle_eq_sum, hr, show 2 ^ dx - 1 + 1 = 2 ^ dx by have := Nat.two_pow_pos dx; (clear * - this; omega)]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [heq x (Finset.mem_range.mp hx), mul_comm]

/-- **The `fixmul` piece's multiplier column** has extension `Σ_c eq(r_c, c)·mle r_x F_c`: a
combination of the accumulators, so the self-evaluation adds no unstructured column. -/
theorem mle_fixF {Q : Program} {dc dx eb s₀ : Nat} {p : Piece}
    (hB : Q.blk p.blk = fixBlock dc dx eb s₀) (hp : p.a = 0) (rc rx : List FE) (hrc : rc.length = dc)
    (hrx : rx.length = dx) :
    mle (rc ++ rx ++ []) (fun x => FE.ofK (Q.fval p .F x)) =
      mle rc (fun c => mle rx (fun x => FE.ofK (Q.fixMat [c, x]))) := by
  rw [List.append_nil, mle_split, hrc, mle_comm]
  apply mle_congr
  intro c hcc
  apply mle_congr
  intro y hy
  rw [hrx] at hy; rw [hrc] at hcc
  have hsz : (Q.blk p.blk).size = 2 ^ dc * 2 ^ dx := by
    simp [Block.size, Block.lsize, hB, fixBlock, pow_add]
  have hlt : c + 2 ^ dc * y < 2 ^ dc * 2 ^ dx := by
    calc c + 2 ^ dc * y < 2 ^ dc * (y + 1) := by rw [Nat.mul_succ]; (clear * - hcc; omega)
      _ ≤ 2 ^ dc * 2 ^ dx := Nat.mul_le_mul_left _ hy
  show FE.ofK (Q.fixMat (unflat (Q.blk p.blk).dims ((c + 2 ^ dc * y) % (Q.blk p.blk).size))) = _
  rw [hsz, Nat.mod_eq_of_lt hlt, hB]
  simp only [fixBlock]
  rw [unflat_two hcc hy]

end Lvm.Loop
end

-- ===== from `LvmBitsTab` =====

section
section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly
open Lvm.Loop

/-- **Under `loopir_sound`'s hypotheses the seed memory is the interpreter's memory** on every
cell (the agreement `loopir_sound` proves on the way, `LvmLoopSound.lean:356`). -/
theorem seedMem_eq_interp (Q : Program) (hwf : Q.wf = true) (inK : Array FK) (inE : Array FE)
    (hsz : inK.size = Q.nInK ∧ inE.size = Q.nInE) (W : Witness) (hcons : Q.ConstraintsHold W)
    (hbus : ∀ m ∈ Q.readMsgs W, m.key ∈ (Q.seedMsgs W inK inE).map Msg.key)
    (hinj : GInj (max (Q.cells .K) (Q.cells .E))) (hinb : (Q.interp inK inE).inb = true)
    {τ : Ty} {e : ℕ} (he : e < Q.cells τ) :
    (Q.seedMem W inK inE).rd τ e = (Q.interpMem inK inE).rd τ e := by
  obtain ⟨hH, -⟩ := Q.holds_seedMem hwf hcons hbus hinj
  have hin : Q.Inputs (Q.seedMem W inK inE) inK inE :=
    ⟨fun n hn => by simp [Program.seedMem, hn], fun n hn => by simp [Program.seedMem, hn]⟩
  obtain ⟨hag, -⟩ := Q.interp_unique hwf inK inE hsz _ hin hH hinj hinb
  exact Program.Mem.rd_agree' hag _ _ (by rw [Q.cells_pick]; exact he)

end Lvm.M3
end
end

section
section
namespace Lvm.M3
open LeanVM.Parameters LeanVM.Protocol CompPoly
open Lvm.Loop
section Aux
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The hypotheses `aux_read` shares with `loop_bus` and `loopir_sound`. -/
structure AuxHyps (q : Column L.μ) : Prop where
  wf : Q.wf = true
  grp : GrpOk Q groups
  inOk : InOk Q arrs
  auxSeeds : ∀ t ∈ aux, t.seeds = []
  cnt : ∀ t ∈ lvmTabs Q pl groups arrs aux, ∀ r ∈ t.reads, r.2 < t.w
  len : nReads (lvmTabs Q pl groups arrs aux) < 2 ^ 64 - 1
  inj : GInj (max (Q.cells .K) (Q.cells .E))
  holds : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q
  inb : (Q.interp (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q)).inb = true

/-- **An auxiliary table's read is a cell of the interpreter's run** (the `BITS` bridge). At row `x`
of auxiliary table `k` (instance table `groups.length + arrs.length + k`), the read `r`'s
separator, address and value limbs, evaluated on the row, are those of cell `e` of memory `τ` of
`interpMem (inKOf q) (inEOf q)`, for some `e` below the cell count. -/
theorem aux_read (q : Column L.μ) (H : AuxHyps Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) :
    ∃ τ e, e < Q.cells τ ∧ r.1.sep = sep τ ∧
      CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x)) r.1.addr =
        FK.toBF64 (FK.x ^ e) ∧
      ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
          (r.1.val.getD l []) =
        FK.toBF64 ((limbsOf τ ((Q.interpMem (inKOf Q pl groups arrs aux L hτ q)
          (inEOf Q pl groups arrs aux L hτ q)).rd τ e)).getD l 0) := by
  set W := witOf Q pl groups arrs aux L hτ q
  set inK := inKOf Q pl groups arrs aux L hτ q
  set inE := inEOf Q pl groups arrs aux L hτ q
  have hget := get_aux Q pl groups arrs aux hk hj
  set row := (lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x
  have hrd : r ∈ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).reads := by rw [hget]; exact hr
  have hu : evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r) ∈
      readTuples L (lvmTabs Q pl groups arrs aux) hτ q := by
    simp only [readTuples, partT, List.mem_flatMap, List.mem_map]
    refine ⟨⟨_, hj⟩, List.mem_finRange _, _, ⟨_, hrd, rfl⟩, x, ?_, rfl⟩
    simp [M3Instance.executed, inst]
  obtain ⟨s, hs, hks⟩ := List.mem_map.mp (mem_lookup L (lvmTabs Q pl groups arrs aux) hτ q
    H.holds.2.1 H.holds.2.2.1 H.cnt H.len _ hu)
  obtain ⟨m', -, hm', he⟩ := seed_key Q pl groups arrs aux L hτ H.grp H.inOk H.auxSeeds q hs
  obtain ⟨τ, e, hec, h1, h2, h3⟩ := Q.seed_cases W inK inE hm'
  have hkey : keyT (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r)) =
      keyT (encT m') := hks.symm.trans he
  have hagree := seedMem_eq_interp Q H.wf inK inE
    ⟨inKOf_size Q pl groups arrs aux L hτ q, inEOf_size Q pl groups arrs aux L hτ q⟩ W
    (loop_cons Q pl groups arrs aux L hτ H.grp q H.holds) (loop_bus Q pl groups arrs aux L hτ H.grp
      H.inOk H.auxSeeds H.cnt H.len q H.holds) H.inj H.inb hec
  have hcoord : ∀ i (hi : i < 16), i ≠ 2 →
      (evalV row (((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).readVec r))[i] = (encT m')[i] :=
    fun i hi hi2 ↦ keyT_coord hkey i hi hi2
  refine ⟨τ, e, hec, ?_, ?_, fun l hl ↦ ?_⟩
  · have := hcoord 0 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      if_true, MvPolynomial.eval_C] at this
    exact (FK.toBF64_injective this).trans h1
  · have := hcoord 1 (by norm_num) (by norm_num)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show (1 : ℕ) ≠ 0 from by decide, if_true, if_false, CPoly.eval_toMv] at this
    rw [this, h2]
  · have := hcoord (l + 3) (by omega) (by omega)
    simp only [evalV, Tab.readVec, Key.vec, Vector.getElem_map, Vector.getElem_ofFn, encT,
      show l + 3 ≠ 0 from by omega, show l + 3 ≠ 1 from by omega, show l + 3 ≠ 2 from by omega,
      if_false, Nat.add_sub_cancel, CPoly.eval_toMv] at this
    rw [this, h3, hagree]

/-- **An auxiliary table's read at a known address is that cell of the interpreter's run**: if the
read names memory `τ` and evaluates its address to `g^a` with `a` below the cell count, its value
limbs are cell `a`'s. -/
theorem aux_read_at (q : Column L.μ) (H : AuxHyps Q pl groups arrs aux L hτ q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {r : Key × ℕ}
    (hr : r ∈ aux[k].reads) {τ : Ty} {a : ℕ} (hsep : r.1.sep = sep τ) (ha : a < Q.cells τ)
    (haddr : CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
      r.1.addr = FK.toBF64 (FK.x ^ a)) :
    ∀ l < 13, CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x))
        (r.1.val.getD l []) =
      FK.toBF64 ((limbsOf τ ((Q.interpMem (inKOf Q pl groups arrs aux L hτ q)
        (inEOf Q pl groups arrs aux L hτ q)).rd τ a)).getD l 0) := by
  obtain ⟨τ', e, he, h1, h2, h3⟩ := aux_read Q pl groups arrs aux L hτ q H hk hj x hr
  obtain rfl : τ' = τ := sep_inj' (h1.symm.trans hsep)
  have hN : ∀ σ, Q.cells σ ≤ max (Q.cells .K) (Q.cells .E) := fun σ ↦ by cases σ <;> simp
  obtain rfl : e = a := H.inj _ _ (lt_of_lt_of_le he (hN _)) (lt_of_lt_of_le ha (hN _))
    (FK.toBF64_injective (h2.symm.trans haddr))
  exact h3

/-- **An auxiliary table's constraints vanish on every row** (`ConstraintsVanish`, on the row as
`CPoly.evalB` reads it): WP-12's row lemma starts here. -/
theorem aux_cons (q : Column L.μ) (hM : M3Holds (lvmInst Q pl groups arrs aux L hτ) () q) {k : ℕ}
    (hk : k < aux.length)
    (hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length)
    (x : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ)) {C : CPoly} (hC : C ∈ aux[k].cons) :
    CPoly.evalB (CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ x)) C = 0 := by
  have hcm : C ∈ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).cons := by
    rw [get_aux Q pl groups arrs aux hk hj]; exact hC
  have hz := hM.1 ⟨_, hj⟩ _ (List.mem_map_of_mem hcm) x
  rwa [CPoly.eval_toMv] at hz

end Aux
end Lvm.M3
end
end

section
set_option autoImplicit false
namespace Lvm.BitsTab
open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.M3 Lvm.Loop

/-- A `CPoly`'s value at an `FK` row. -/
def evalK (v : Nat → FK) (P : CPoly) : FK := (P.map fun m => m.1 * (m.2.map v).prod).sum

/-- **`evalB` is `evalK` through `FK.toBF64`.** -/
theorem evalB_eq (u : Nat → K) (P : CPoly) :
    CPoly.evalB u P = FK.toBF64 (evalK (fun i => FK.ofBF64 (u i)) P) := by
  unfold CPoly.evalB evalK
  rw [← FK.ringEquivBF64_apply, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun m _ => ?_
  simp only [Function.comp, map_mul, map_list_prod, List.map_map, FK.ringEquivBF64_apply,
    FK.toBF64_ofBF64]
  rfl

theorem sum_range (g : Nat → FK) : ∀ n, ((List.range n).map g).sum = lsum g n
  | 0 => rfl
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, sum_range g n]; simp [lsum]

end Lvm.BitsTab
end

section
set_option autoImplicit false
namespace Lvm.BitsTab
open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.M3 Lvm.Loop
namespace BSpec
variable (S : BSpec)

theorem tab_w : S.tab.w = S.width := by simp [Tab.w, tab]

theorem tab_seeds : S.tab.seeds = [] := rfl

/-- The read-count columns lie inside the width (`AuxHyps.cnt`). -/
theorem tab_cnt : ∀ r ∈ S.tab.reads, r.2 < S.tab.w := by
  intro r hr
  rw [tab_w]
  simp only [tab, reads, List.mem_append, List.mem_map, List.mem_range] at hr
  rcases hr with h | ⟨j, hj, rfl⟩
  · split at h
    · simp only [List.mem_singleton] at h; subst h; simp only [wread, width, ab]; omega
    · simp at h
  · simp only [oread, width, ab]; omega

theorem tab_cols (c : Nat) (hc : c < S.width) : S.tab.cols[c]? = some (S.col c) := by
  simp [tab, hc]

/-- **An output's address on a row whose address columns hold their powers** is `g^{oc j x}`. -/
theorem oaddr_eval (u : Nat → K) {x : Nat} (hx : x < S.n)
    (hfix : ∀ (c : Nat) (a : Nat → Nat), c < S.width → S.col c = S.adrCol a → u c = FK.toBF64 (FK.x ^ a x))
    {j : Nat} (hj : j < S.outs.length) : CPoly.evalB u (S.oaddr j) = FK.toBF64 (FK.x ^ S.oc j x) := by
  unfold oaddr
  split
  · rename_i hjs
    have hs : S.sh ≠ 0 := by omega
    have hw : S.ab < S.width := by unfold width nA; rw [if_neg hs]; omega
    have hc := hfix S.ab (S.oc 0) hw (by unfold col ab; rw [if_neg (by omega), if_neg (by omega), if_pos ⟨hs, rfl⟩])
    rw [evalB_eq, S.hsh j hjs x hx, pow_add]
    congr 1
    simp [evalK, hc, FK.ofBF64_toBF64, mul_comm]
  · rename_i hjs
    have hw : S.ab + S.nA + (j - S.sh) < S.width := by unfold width; omega
    have hc := hfix _ (S.oc j) hw (by
      unfold col
      rw [if_neg (by unfold ab; omega), if_neg (by omega), if_neg (by unfold nA; split <;> omega)]
      congr 2; omega)
    rw [evalB_var, hc]

/-- **The closed forms are the extensions** (`FixOk`). -/
theorem fixOk_tab : FixOk [S.tab] := by
  intro t ht f ev hf r _
  simp only [List.mem_singleton] at ht; subst ht
  simp only [tab, List.mem_map, List.mem_range] at hf
  obtain ⟨c, -, hc⟩ := hf
  unfold col adrCol at hc
  split at hc
  · cases hc; rfl
  · split at hc
    · cases hc
    · split at hc <;> (cases hc; rfl)

theorem fixOk_append {a b : List Tab} (ha : FixOk a) (hb : FixOk b) : FixOk (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem fixOk_tabs (Ss : List BSpec) : FixOk (Ss.map tab) := by
  intro t ht
  obtain ⟨S, -, rfl⟩ := List.mem_map.mp ht
  exact S.fixOk_tab _ (List.mem_singleton_self _)

end BSpec
end Lvm.BitsTab
end

section
set_option autoImplicit false
namespace Lvm.BitsTab
open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.M3 Lvm.Loop

theorem evalK_wcons (v : Nat → FK) : evalK v wcons = v 0 + lsum (fun z => wt z * v (1 + z)) 64 := by
  simp only [evalK, wcons, List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_mul, sum_range]

theorem evalK_bcons (v : Nat → FK) (z : Nat) :
    evalK v (bcons z) = v (1 + z) * v (1 + z) + v (1 + z) := by
  simp [evalK, bcons]

theorem evalK_outPoly (v : Nat → FK) (o : BOut) :
    evalK v (outPoly o) = lsum (fun z => o.coef z * v (1 + z)) 64 := by
  simp only [evalK, outPoly, List.map_map, Function.comp_def, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, sum_range]

/-- The `LvmBits` row of an `FK` row of the table. -/
def rowOf (v : Nat → FK) : Bits.Row := ⟨v 0, fun z => v (1 + z)⟩

theorem rowOf_cons {v : Nat → FK} (h : ∀ C ∈ cons, evalK v C = 0) : (rowOf v).Constraints := by
  refine ⟨fun z hz => ?_, ?_⟩
  · have := h (bcons z) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨z, List.mem_range.mpr hz, rfl⟩))
    rwa [evalK_bcons] at this
  · have := h wcons (List.mem_cons_self ..)
    rwa [evalK_wcons] at this

theorem rowOf_out (v : Nat → FK) (o : BOut) : evalK v (outPoly o) = (rowOf v).out o := by
  rw [evalK_outPoly]; rfl

end Lvm.BitsTab
end

section
set_option autoImplicit false
namespace Lvm.BitsTab
open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.M3 Lvm.Loop
section Sound
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- The interpreter's `K` cells on the inputs read off the stack `q`. -/
noncomputable def memK (q : Column L.μ) : Nat → FK :=
  (Q.interpMem (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q)).k

/-- **`BITS` soundness through the bus.** At a real row `x` of a `BITS` table of `aux`, whose
cells lie below `Q.cells .K`, the row's word `w` is the word cell's value (when `rd`) and output
cell `oc j x` holds output `j`'s word function of `w`. -/
theorem out_sound (q : Column L.μ) (H : M3.AuxHyps Q pl groups arrs aux L hτ q) (S : BSpec)
    (hS : S.tab ∈ aux) {x : Nat} (hx : x < S.n) (hn : S.n ≤ 2 ^ S.τ)
    (hw : S.rd = true → S.wc x < Q.cells .K) (ho : ∀ j < S.outs.length, S.oc j x < Q.cells .K) :
    ∃ w : FK, (S.rd = true → memK Q pl groups arrs aux L hτ q (S.wc x) = w) ∧
      ∀ j < S.outs.length, (S.out j).Valid →
        memK Q pl groups arrs aux L hτ q (S.oc j x) = ⟨(S.out j).word w.val⟩ := by
  obtain ⟨k, hk, hak⟩ := List.mem_iff_getElem.mp hS
  have hj : groups.length + arrs.length + k < (lvmTabs Q pl groups arrs aux).length := by
    rw [lvmTabs_length]; omega
  have hT : (lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩ = S.tab :=
    (get_aux Q pl groups arrs aux hk hj).trans hak
  have hxT : x < 2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ := by
    rw [hT]; show x < 2 ^ S.τ; omega
  set xF : Fin (2 ^ ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).τ) := ⟨x, hxT⟩
  set u := CPoly.ext ((lvmInst Q pl groups arrs aux L hτ).row q ⟨_, hj⟩ xF) with hu
  set M := Q.interpMem (inKOf Q pl groups arrs aux L hτ q) (inEOf Q pl groups arrs aux L hτ q)
  have hrow : S.row x = x := if_pos hx
  -- the fixed address columns
  have hfix : ∀ (c : Nat) (a : Nat → Nat), c < S.width → S.col c = S.adrCol a →
      u c = FK.toBF64 (FK.x ^ a x) := by
    intro c a hc hcol
    have hcw : c < ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).w := by
      rw [hT, BSpec.tab_w]; exact hc
    have hf : ((lvmTabs Q pl groups arrs aux).get ⟨_, hj⟩).fixedOf c =
        some fun x => FK.x ^ a (S.row x) := by
      rw [hT, Tab.fixedOf, BSpec.tab_cols S c hc, hcol]; rfl
    have := row_fixed Q pl groups arrs aux L hτ q ⟨_, hj⟩ xF ⟨c, hcw⟩ hf
    rw [hu, CPoly.ext, dif_pos hcw, this, hrow]
  -- a read at a fixed address column is the cell's value
  have hread : ∀ (r : Key × Nat) (c : Nat) (a : Nat → Nat) (P : CPoly), r ∈ S.reads → r.1.sep = sep .K →
      r.1.addr = CPoly.var c → r.1.val = [P] → c < S.width → S.col c = S.adrCol a →
      a x < Q.cells .K → CPoly.evalB u P = FK.toBF64 (M.k (a x)) := by
    intro r c a P hr hsep haddr hval hc hcol hlt
    have hr' : r ∈ aux[k].reads := by rw [hak]; exact hr
    have := aux_read_at Q pl groups arrs aux L hτ q H hk hj xF hr' hsep hlt
      (by rw [haddr, evalB_var]; exact hfix c a hc hcol) 0 (by norm_num)
    rw [hval] at this
    simpa [limbsOf, Mem.rd, FE.ofK] using this
  -- a read whose address evaluates to `g^e`
  have hreadA : ∀ (r : Key × Nat) (e : Nat) (P : CPoly), r ∈ S.reads → r.1.sep = sep .K →
      CPoly.evalB u r.1.addr = FK.toBF64 (FK.x ^ e) → r.1.val = [P] →
      e < Q.cells .K → CPoly.evalB u P = FK.toBF64 (M.k e) := by
    intro r e P hr hsep haddr hval hlt
    have hr' : r ∈ aux[k].reads := by rw [hak]; exact hr
    have := aux_read_at Q pl groups arrs aux L hτ q H hk hj xF hr' hsep hlt haddr 0 (by norm_num)
    rw [hval] at this
    simpa [limbsOf, Mem.rd, FE.ofK] using this
  -- the constraints on the `FK` row
  set v : Nat → FK := fun i => FK.ofBF64 (u i)
  have hcons : ∀ C ∈ cons, evalK v C = 0 := by
    intro C hC
    have hC' : C ∈ aux[k].cons := by rw [hak]; exact hC
    have := aux_cons Q pl groups arrs aux L hτ q H.holds hk hj xF hC'
    rw [evalB_eq] at this
    exact FK.toBF64_injective (this.trans FK.toBF64_zero.symm)
  obtain ⟨-, hout⟩ := row_sound (rowOf_cons hcons)
  have hwid : 66 < S.width := by unfold BSpec.width BSpec.ab; omega
  refine ⟨(rowOf v).w, fun hrd => ?_, fun j hj' hv => ?_⟩
  · have h := hread BSpec.wread 66 S.wc (CPoly.var 0)
      (by simp [BSpec.reads, hrd]) rfl rfl rfl hwid (by simp [BSpec.col]) (hw hrd)
    rw [evalB_var] at h
    show M.k (S.wc x) = FK.ofBF64 (u 0)
    rw [h]; rfl
  · have h := hreadA (S.oread j) (S.oc j x) (outPoly (S.out j))
      (by simp only [BSpec.reads, List.mem_append, List.mem_map, List.mem_range]
          exact Or.inr ⟨j, hj', rfl⟩)
      rfl (S.oaddr_eval u hx (fun c a hc hcol => hfix c a hc hcol) hj') rfl (ho j hj')
    rw [evalB_eq, rowOf_out, hout _ hv] at h
    exact (FK.toBF64_injective h).symm

end Sound
end Lvm.BitsTab
end

section
set_option autoImplicit false
namespace Lvm.BitsTab
open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.M3 Lvm.Loop

/-- The honest `FK` row of a word: `w`, then its bits. -/
def honest (w : FK) (i : Nat) : FK :=
  if i = 0 then w else if ubit w.val (i - 1) then 1 else 0

theorem lsum_honest (w : FK) : lsum (fun z => wt z * honest w (1 + z)) 64 = w := by
  have hb : ∀ z, honest w (1 + z) = if ubit w.val z then 1 else 0 := fun z => by
    simp [honest, show 1 + z ≠ 0 by omega, show 1 + z - 1 = z by omega]
  have key : (lsum (fun z => wt z * honest w (1 + z)) 64).val = w.val := by
    apply u64_ext
    intro i hi
    apply Bool.eq_iff_iff.mpr
    rw [ubit_lsum _ (fun z => ubit w.val z) id i 64 (fun z hz => by
        rw [hb, wt, ubit_mul_bit _ (by split <;> simp), ubit_one_shl hz]
        have h01 : ((0 : FK) = 1) ↔ False := by decide
        by_cases hz' : ubit w.val z = true <;> simp [hz', h01, @eq_comm _ i z])
      (fun z _ z' _ _ _ h => h)]
    exact ⟨fun ⟨z, _, h1, h2⟩ => h2 ▸ h1, fun h1 => ⟨i, hi, h1, rfl⟩⟩
  exact congrArg FK.mk key

/-- **Completeness of the row**: the honest row of any word satisfies the constraints. -/
theorem honest_cons (w : FK) : ∀ C ∈ cons, evalK (honest w) C = 0 := by
  intro C hC
  simp only [cons, List.mem_cons, List.mem_map, List.mem_range] at hC
  rcases hC with rfl | ⟨z, -, rfl⟩
  · rw [evalK_wcons, lsum_honest]
    show w + w = 0
    exact CharTwo.add_self_eq_zero w
  · rw [evalK_bcons]
    have : honest w (1 + z) = 0 ∨ honest w (1 + z) = 1 := by
      simp only [honest, show 1 + z ≠ 0 by omega, if_false]; split <;> simp
    rcases this with h | h <;> rw [h] <;> decide

/-- **Completeness of the outputs**: on the honest row every output polynomial is the output's
word function. -/
theorem honest_out (w : FK) {o : BOut} (ho : o.Valid) : evalK (honest w) (outPoly o) = ⟨o.word w.val⟩ := by
  rw [rowOf_out, (row_sound (rowOf_cons (honest_cons w))).2 o ho]
  rfl

/-- **The honest table row satisfies the table** (as `aux_cons` reads it): on the honest row of any
word, every constraint of every `BITS` table vanishes and every output read's value polynomial is
the output's word function. -/
theorem honest_tab (S : BSpec) (w : FK) :
    (∀ C ∈ S.tab.cons, CPoly.evalB (fun i => FK.toBF64 (honest w i)) C = 0) ∧
      ∀ j < S.outs.length, (S.out j).Valid →
        CPoly.evalB (fun i => FK.toBF64 (honest w i)) (outPoly (S.out j)) =
          FK.toBF64 ⟨(S.out j).word w.val⟩ := by
  refine ⟨fun C hC => ?_, fun j _ hv => ?_⟩
  · rw [evalB_eq]
    simp only [FK.ofBF64_toBF64]
    rw [honest_cons w C hC]; rfl
  · rw [evalB_eq]
    simp only [FK.ofBF64_toBF64]
    rw [honest_out w hv]

end Lvm.BitsTab
end

-- ===== from `LvmSigBits` =====

section
set_option autoImplicit false
namespace Lvm.SigBits
open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.Loop Lvm.QSig

/-- The six tables are auxiliary tables of the instance. -/
def SigTabsIn (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) (aux : List Tab) : Prop :=
  ∀ S ∈ sigSpecs I o bpl, S.tab ∈ aux

/-- The cells the six tables name at their real rows are cells of `Q`. -/
def SigCellsLt (Q : Program) (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) : Prop :=
  ∀ S ∈ sigSpecs I o bpl, ∀ x < S.n,
    (S.rd = true → S.wc x < Q.cells .K) ∧ ∀ j < S.outs.length, S.oc j x < Q.cells .K

theorem fixOk_sig (I : SigIn) (o : SigOut) (bpl : Nat → Nat → Bool × Nat) :
    FixOk ((sigSpecs I o bpl).map BSpec.tab) := BSpec.fixOk_tabs _

end Lvm.SigBits
end

section
set_option autoImplicit false
namespace Lvm.SigBits
open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.Loop Lvm.QSig
section Ok
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- **`SigBitsOk`**: `Q_sig`'s `BITS` outputs hold in the interpreter's memory on the inputs read
off the stack `q` (the `hbits` of `qsig_sound`, with `M := Q.interpMem (inKOf q) (inEOf q)`). -/
def SigBitsOk (q : Column L.μ) (I : SigIn) (o : SigOut) : Prop :=
  SigBits I o (memK Q pl groups arrs aux L hτ q)

/-- One output of a read word (`out_sound` at a row and an output, with the cells named). -/
theorem out1_at (q : Column L.μ) (H : M3.AuxHyps Q pl groups arrs aux L hτ q) (S : BSpec)
    (hS : S.tab ∈ aux) (hn : S.n ≤ 2 ^ S.τ) (hrd : S.rd = true) (x j : Nat) (hx : x < S.n)
    (hj : j < S.outs.length) (hc : (S.rd = true → S.wc x < Q.cells .K) ∧
      ∀ j < S.outs.length, S.oc j x < Q.cells .K)
    {A B : Nat} {b : BOut} (hA : S.wc x = A) (hB : S.oc j x = B) (hb : S.out j = b) (hv : b.Valid) :
    Out1 (memK Q pl groups arrs aux L hτ q) A b B := by
  obtain ⟨w, h1, h2⟩ := out_sound Q pl groups arrs aux L hτ q H S hS hx hn hc.1 hc.2
  have := h2 j hj (hb ▸ hv)
  rw [hA, hB, hb] at *
  unfold Out1; rw [this, h1 hrd]

end Ok
end Lvm.SigBits
end

section
set_option autoImplicit false
namespace Lvm.SigBits
open LeanVM.Parameters LeanVM.Protocol Lvm Lvm.Bits Lvm.BitsTab Lvm.M3 Lvm.Loop Lvm.QSig
section Ok
variable (Q : Program) (pl : ℕ → Var → Bool × ℕ) (groups : List Grp) (arrs : List InArr)
  (aux : List Tab) (L : Lay) (hτ : ∀ t ∈ lvmTabs Q pl groups arrs aux, t.τ ≤ L.μ)

/-- **`SigBitsOk` from the bus**: the six `BITS` tables in the instance, their cells inside `Q`,
and `loopir_sound`'s hypotheses (`AuxHyps`) give `Q_sig`'s `BITS` outputs. -/
theorem sigBitsOk (q : Column L.μ) (H : M3.AuxHyps Q pl groups arrs aux L hτ q) (I : SigIn) (o : SigOut)
    (bpl : Nat → Nat → Bool × Nat) (hT : SigTabsIn I o bpl aux) (hC : SigCellsLt Q I o bpl)
    (hln : 1 ≤ I.ln ∧ I.ln ≤ 62) :
    SigBitsOk Q pl groups arrs aux L hτ q I o := by
  have mem := fun S (hS : S ∈ sigSpecs I o bpl) => And.intro (hT S hS) (hC S hS)
  obtain ⟨tI, cI⟩ := mem (sIdx I (bpl 0)) (by simp [sigSpecs])
  obtain ⟨tM, cM⟩ := mem (sMd I (bpl 1)) (by simp [sigSpecs])
  obtain ⟨tC, cC⟩ := mem (sCs I (bpl 2)) (by simp [sigSpecs])
  obtain ⟨t24, c24⟩ := mem (s24 I o (bpl 3)) (by simp [sigSpecs])
  obtain ⟨t8, c8⟩ := mem (s8 I o (bpl 4)) (by simp [sigSpecs])
  obtain ⟨tN, cN⟩ := mem (sN I (bpl 5)) (by simp [sigSpecs])
  have o1 := out1_at Q pl groups arrs aux L hτ q H
  have nI : (sIdx I (bpl 0)).n ≤ 2 ^ (sIdx I (bpl 0)).τ := by simp [sIdx]
  have nM : (sMd I (bpl 1)).n ≤ 2 ^ (sMd I (bpl 1)).τ := by simp [sMd]
  have n24 : (s24 I o (bpl 3)).n ≤ 2 ^ (s24 I o (bpl 3)).τ := by simp only [s24]; norm_num
  have n8 : (s8 I o (bpl 4)).n ≤ 2 ^ (s8 I o (bpl 4)).τ := by simp only [s8]; norm_num
  have nN : (sN I (bpl 5)).n ≤ 2 ^ (sN I (bpl 5)).τ := by simp [sN]
  have x0 : ∀ {S : BSpec}, S.n = 1 → 0 < S.n := fun h => by omega
  refine ⟨?_, fun z hz => ?_, ?_, fun r hr => ?_, ?_, fun i hi s hs l hl => ⟨?_, ?_⟩,
    fun i hi l hl => ⟨?_, ?_⟩, fun t ht u hu l hl => ⟨?_, ?_⟩, fun l hl => ⟨?_, ?_⟩, ?_, ?_,
    fun z hz => ?_, ?_, ?_, fun l hl => ⟨?_, ?_⟩, fun l hl => ⟨?_, ?_⟩⟩
  -- idx: `shl 8`, bits, `shr 16`
  · exact o1 _ tI nI rfl 0 0 (x0 rfl) (by simp [sIdx]) (cI 0 (x0 rfl)) rfl (by simp [sIdx]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tI nI rfl 0 (1 + z) (x0 rfl) (by simp [sIdx] <;> omega) (cI 0 (x0 rfl)) rfl
      (by simp [sIdx] <;> omega) (getD_idx hz) (show z < 64 by omega)
  · exact o1 _ tI nI rfl 0 17 (x0 rfl) (by simp [sIdx]) (cI 0 (x0 rfl)) rfl (by simp [sIdx]) rfl
      (by simp [BOut.Valid])
  -- md: 256 bits
  · exact o1 _ tM nM rfl (r / 64) (r % 64) (by simp [sMd] <;> omega) (by simp [sMd] <;> omega)
      (cM (r / 64) (by simp [sMd] <;> omega)) rfl (by simp only [sMd] <;> omega)
      (getD_bit (Nat.mod_lt _ (by norm_num))) (Nat.mod_lt _ (by norm_num))
  -- cs: ten bits of a free word
  · obtain ⟨w, -, h2⟩ := out_sound Q pl groups arrs aux L hτ q H _ tC (x := 0) (x0 rfl)
      (by simp [sCs]) (cC 0 (x0 rfl)).1 (cC 0 (x0 rfl)).2
    refine ⟨w.val, fun k hk => ?_⟩
    have hb : (sCs I (bpl 2)).out k = .bit k := getD_bit hk
    have := h2 k (by simp [sCs, hk]) (by rw [hb]; show k < 64; omega)
    rw [hb] at this
    exact this
  -- step inputs: `shl 24`, `shr 40`
  · exact o1 _ t24 n24 rfl (4 * (3 * i + s) + l) 0 (by simp only [s24] <;> omega) (by simp [s24])
      (c24 _ (by simp only [s24] <;> omega))
      (by simp only [s24]; rw [show (4 * (3 * i + s) + l) / 12 = i by omega,
        show (4 * (3 * i + s) + l) / 4 % 3 = s by omega, show (4 * (3 * i + s) + l) % 4 = l by omega])
      (by simp only [s24] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t24 n24 rfl (4 * (3 * i + s) + l) 1 (by simp only [s24] <;> omega) (by simp [s24])
      (c24 _ (by simp only [s24] <;> omega))
      (by simp only [s24]; rw [show (4 * (3 * i + s) + l) / 12 = i by omega,
        show (4 * (3 * i + s) + l) / 4 % 3 = s by omega, show (4 * (3 * i + s) + l) % 4 = l by omega])
      (by simp only [s24] <;> omega) rfl (by simp [BOut.Valid])
  -- chain ends
  · exact o1 _ t8 n8 rfl (4 * i + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_pos (by omega), show (4 * i + l) / 4 = i by omega,
        show (4 * i + l) % 4 = l by omega])
      (by simp only [s8]; rw [if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (4 * i + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_pos (by omega), show (4 * i + l) / 4 = i by omega,
        show (4 * i + l) % 4 = l by omega])
      (by simp only [s8]; rw [if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  -- path node halves
  · exact o1 _ t8 n8 rfl (532 + (8 * t + 4 * u + l)) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by omega, show (8 * t + 4 * u + l) % 4 = l by omega,
        show (8 * t + 4 * u + l) / 8 = t by omega])
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (532 + (8 * t + 4 * u + l)) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega), Nat.add_sub_cancel_left,
        show (8 * t + 4 * u + l) / 4 % 2 = u by omega, show (8 * t + 4 * u + l) % 4 = l by omega,
        show (8 * t + 4 * u + l) / 8 = t by omega])
      (by simp only [s8]; rw [if_neg (by omega), if_pos (by omega)] <;> omega) rfl (by simp [BOut.Valid])
  -- h'
  · exact o1 _ t8 n8 rfl (660 + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (660 + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  -- n': `shl 8`, `shr 56`, bits, top, low
  · exact o1 _ tN nN rfl 0 0 (x0 rfl) (by simp [sN]) (cN 0 (x0 rfl)) rfl (by simp [sN]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tN nN rfl 0 1 (x0 rfl) (by simp [sN]) (cN 0 (x0 rfl)) rfl (by simp [sN]) rfl
      (by simp [BOut.Valid])
  · exact o1 _ tN nN rfl 0 (2 + z) (x0 rfl) (by simp [sN] <;> omega) (cN 0 (x0 rfl)) rfl
      (by simp [sN] <;> omega) (getD_n hz) (show z < 64 by omega)
  · exact o1 _ tN nN rfl 0 (I.ln + 3) (x0 rfl) (by simp [sN]) (cN 0 (x0 rfl)) rfl
      (by simp only [sN] <;> omega) getD_n_top (by simp only [BOut.Valid]; omega)
  · exact o1 _ tN nN rfl 0 (I.ln + 4) (x0 rfl) (by simp [sN]) (cN 0 (x0 rfl)) rfl
      (by simp only [sN] <;> omega) getD_n_low (by simp only [BOut.Valid]; omega)
  -- c_L'
  · exact o1 _ t8 n8 rfl (664 + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (664 + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_pos (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  -- leafStmt lanes
  · exact o1 _ t8 n8 rfl (668 + l) 0 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])
  · exact o1 _ t8 n8 rfl (668 + l) 1 (by simp only [s8] <;> omega) (by simp [s8])
      (c8 _ (by simp only [s8] <;> omega))
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      (by simp only [s8]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)] <;> omega)
      rfl (by simp [BOut.Valid])

end Ok
end Lvm.SigBits
end

-- ===== from `LvmQAsmHar47` =====

section
set_option autoImplicit false
namespace Lvm.Har
open Lvm Lvm.Loop Lvm.Loop.Build Lvm.Q1 Lvm.QAsm DM

theorem ksPh_run (p : Params) (hn : 1 ≤ p.ksLog) (sig : ByteArray) (s : RS) :
    ksPh p sig s =
      let r := samplesAt (feAt sig) (pos s) p.ksLog
      let v := scalarsAt (feAt sig) (kV p.ksLog (pos s) + 40) lanes
      let K := vkSpec (feAt sig) p.ksLog r v (kG p.ksLog (pos s)) s.ok
      ((r, v, K.1, ringAt (feAt sig) (K.2.2 + 24 * kBits) K.1.slicePoint K.1.slices),
        ⟨K.2.2 + 24 * kBits + 72 * ringStages, 0, K.2.1⟩) :=
  kPh_run sig p.ksLog hn s

theorem ksLinkPh_run (p : Params) (m : M3) (rk : List FE) (pub : Pub) (sig : ByteArray) (s : RS)
    (hn : 1 ≤ p.ksLog) :
    ksLinkPh p m rk pub sig s =
      (m.ksLink (ksLinkView p m (feAt sig) (pos s) rk pub), ⟨ksP2 p (pos s), 96, s.ok⟩) := by
  unfold ksLinkPh
  rw [bind_run, samples_run sig _ s (by simp [laneBits])]
  dsimp only
  rw [bind_run, sumcheck_run sig 3 (by (clear * -; omega))]
  dsimp only
  rw [bind_run, readEs_run]
  dsimp only
  rw [scState_replicate_lk _ _ hn]
  simp only [Nat.add_zero, Nat.zero_add]
  unfold pos
  generalize s.ent + s.msg = P
  rw [pure_run]
  rfl

/-- **A `loadEs` cell is the stream's scalar** at lane `a + st·i`. -/
theorem loadEs_val {c : Ctx} {M : Mem} {p : Ptr} {D a st : Nat} {sig : ByteArray} {T : Nat}
    (h : SegsHold c M p (loadEs D a st p).2) (hS : Streamed M sig T) {i : Nat} (hi : i < 2 ^ D)
    (hT : a + st * i + 2 < T) :
    ((loadEs D a st p).1.cell 0 i).val M = feAt sig (8 * (a + st * i)) := by
  have hA : QB.AllE [QB.ldRow a st] := by simp [QB.AllE, QB.ldRow]
  have hrel := loop_rel h (jf := i) (t := 0) (by simpa using hi) (by simp)
  have e := QB.ldRow_val (d := D) (p := p) hA hi (by simp) (by rfl) hrel
  rw [show loadEs D a st = loop [D] [QB.ldRow a st] from rfl, QB.cell1 hA (by simp)]
  rw [e]
  apply QB.kE_lanes
  intro j hj
  rw [hS _ (by (clear * - hT hj; omega))]; rfl

/-- **The point/lane loads and the GKR of a Keccak block** (`CH`: `ls = logN`; `KS`: `ls = ksLog`): with
the reader at `P` (`8·a0 = P + 40`, the lanes at `a1`, the GKR at `a2`), the cells are `F`'s point,
lanes and `KeccakOut`, and with the gate on the GKR's checks hold. -/
theorem kblock_sound {c : Ctx} {M : Mem} {sig : ByteArray} {T ls a0 a1 a2 : Nat} {g : Cell}
    {p0 p1 p2 : Ptr} (hls : 4 ≤ ls) (hlay : layOk (ls - 4) = true) (hq : 5 ≤ a2)
    (hS : Streamed M sig T) (hT : gkrEnd (ls - 4) a2 ≤ T) (hTr : a0 + 9 * ls + 2 < T)
    (hTv : a1 + 3 * 25 + 2 < T) (hD : ls ≤ 2 ^ clog2 ls)
    (hr : SegsHold c M p0 (loadEs (clog2 ls) a0 9 p0).2)
    (hv : SegsHold c M p1 (loadEs 5 a1 3 p1).2)
    (hk : SegsHold c M p2 (Lvm.Q1.gkrGadget (ls - 4) a2 (fun i => (loadEs (clog2 ls) a0 9 p0).1.cell 0 i)
      (fun l => (loadEs 5 a1 3 p1).1.cell 0 l) g p2).2)
    (hkA : SegsAssert M p2 (Lvm.Q1.gkrGadget (ls - 4) a2 (fun i => (loadEs (clog2 ls) a0 9 p0).1.cell 0 i)
      (fun l => (loadEs 5 a1 3 p1).1.cell 0 l) g p2).2) (hg : g.val M = 1)
    (P : Nat) (h0 : P + 40 = 8 * a0) (h1 : kV ls P + 40 = 8 * a1) (h2 : kG ls P = 8 * a2 - 40) (ok : Bool) :
    samplesAt (feAt sig) P ls = (List.range ls).map (fun i => ((loadEs (clog2 ls) a0 9 p0).1.cell 0 i).val M) ∧
    scalarsAt (feAt sig) (kV ls P + 40) lanes = (List.range 25).map (fun l => ((loadEs 5 a1 3 p1).1.cell 0 l).val M) ∧
    (vkSpec (feAt sig) ls (samplesAt (feAt sig) P ls) (scalarsAt (feAt sig) (kV ls P + 40) lanes) (kG ls P) ok).1 =
      (Lvm.Q1.gkrGadget (ls - 4) a2 (fun i => (loadEs (clog2 ls) a0 9 p0).1.cell 0 i)
        (fun l => (loadEs 5 a1 3 p1).1.cell 0 l) g p2).1.vals M ∧
    (vkSpec (feAt sig) ls (samplesAt (feAt sig) P ls) (scalarsAt (feAt sig) (kV ls P + 40) lanes) (kG ls P) ok).2.2 +
      24 * kBits = 8 * gkrEnd (ls - 4) a2 - 40 ∧
    (ok = true → (vkSpec (feAt sig) ls (samplesAt (feAt sig) P ls) (scalarsAt (feAt sig) (kV ls P + 40) lanes)
      (kG ls P) ok).2.1 = true) := by
  have eR : samplesAt (feAt sig) P ls = (List.range ls).map (fun i => ((loadEs (clog2 ls) a0 9 p0).1.cell 0 i).val M) := by
    unfold samplesAt
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [loadEs_val hr hS (by (clear * - hD hi'; omega)) (by (clear * - hTr hi'; omega))]
    congr 1; (clear * - h0; omega)
  have eV : scalarsAt (feAt sig) (kV ls P + 40) lanes = (List.range 25).map (fun l => ((loadEs 5 a1 3 p1).1.cell 0 l).val M) := by
    unfold scalarsAt lanes
    refine List.map_congr_left fun l hl => ?_
    have hl' := List.mem_range.mp hl
    rw [loadEs_val hv hS (by norm_num; (clear * - hl'; omega)) (by (clear * - hTv hl'; omega))]
    congr 1; (clear * - h1; omega)
  have hls' : ls - 4 + 4 = ls := by (clear * - hls; omega)
  obtain ⟨g1, g2, g3⟩ := gkr_spec (c := c) (M := M) (p := p2) hlay hq hS hT hk ⟨kG ls P, 0, ok⟩ (by simp [h2])
  rw [verifyKeccak_run sig _ _ _ _ (kG ls P) (by simp)] at g1 g2 g3
  simp only [hls'] at g1 g2 g3
  refine ⟨eR, eV, ?_, ?_, fun hok => ?_⟩
  · rw [eR, eV]; simpa [lanes] using g1
  · rw [eR, eV]; simpa [lanes] using g2
  · rw [eR, eV]; simpa [lanes, hok] using (g3 hg).mpr ⟨hok, hkA⟩

end Lvm.Har
end
