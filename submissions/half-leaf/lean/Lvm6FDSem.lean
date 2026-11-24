-- lvm6 X1 (BLUEPRINT §3 `FD1`): one decoding end to end. New.
import Lvm6FDSemLam
import Lvm6FDSemLane
import Lvm6FDCorrect
import Lvm6FDCost
import Lvm6FDNw

/-!
# `FD1` end to end

* `wf_fd1IR`, `fd1IR_sem`: `lamIR` then `laneIR` leaves `fd1 N ℓ S y` at `outA B ℓ`;
* **`fd1IR_correct`**: with at most one error on the `k + 2` positions `S` (`OneErr`), the program
  leaves the message's novel-basis coefficients there (`fd1_correct`).

The extractor (X2) runs `lamIR` once per fold round and `laneIR` once per lane: `laneIR_sem` keeps
`LamOk` (it writes only the lane workspace), and the lane's values `y` are rewritten in between.
-/

namespace Lvm6.FD

open RecursionFast Lvm.X Lvm.Nb

theorem wf_fd1IR (N ℓ m B : ℕ) : WF (fd1IR N ℓ m B) := ⟨wf_lamIR N ℓ m B, wf_laneIR N ℓ m B⟩

/-- **`LamOk` survives** any change of the heap outside `[tbA, yA)` and `[tA, fdEnd)`: `laneIR` (it writes only the lane workspace) and the extractor's stores of the next lane's `y`. -/
theorem lamOk_of_frame {N ℓ B : ℕ} {S : List ℕ} {M M' : Mem} (hN64 : N ≤ 64) (hL : LamOk N ℓ B S M)
    (hf : ∀ x, regs ≤ x → (x < yA B ℓ ∨ tA B ℓ ≤ x) → rd M' x = rd M x) (hB : regs ≤ B)
    (hm : S.length ≤ 2 ^ ℓ) : LamOk N ℓ B S M' := by
  obtain ⟨l1, l2, l3, l4⟩ := hL
  simp only [regs] at hB
  have hNN : N * N ≤ 4096 := by have := Nat.mul_le_mul hN64 hN64; simpa using this
  refine ⟨fun v hv i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun j hj => ?_⟩
  · have : N * v + i < 4096 := by
      have := Nat.mul_le_mul_left N (show v + 1 ≤ N by omega); rw [Nat.mul_succ] at this; omega
    rw [← l1 v hv i hi]
    exact rdK_eq (hf _ (by simp only [regs, tbA]; omega) (Or.inl (by simp only [tbA, yA]; omega)))
  · rw [← l2 i hi]
    exact hf _ (by simp only [regs, sA]; omega) (Or.inl (by simp only [sA, yA]; omega))
  · rw [← l3 i hi]
    exact rdK_eq (hf _ (by simp only [regs, tA]; omega) (Or.inr (by simp only [tA]; omega)))
  · rw [← l4 j hj]
    exact rdK_eq (hf _ (by simp only [regs, iA]; omega) (Or.inr (by simp only [tA, iA]; omega)))

/-- **One decoding**: `lamIR` then `laneIR` leaves `fd1 N ℓ S y` at `outA B ℓ`. -/
theorem fd1IR_sem (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ B : ℕ} {S : List ℕ} {y : ℕ → BF64}
    (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B) (hsz : fdEnd B ℓ ≤ s.M.size)
    (h64 : fdEnd B ℓ < 2 ^ 64) (hm : S.length ≤ 2 ^ ℓ) (hSn : ∀ j ∈ S, j < 2 ^ ℓ)
    (hS : ∀ i < S.length, rd s.M (sA B + i) = toWord (S.getD i 0))
    (hy : ∀ j < 2 ^ ℓ, rdK s.M (yA B ℓ + j) = y j) :
    (∀ x < 2 ^ ℓ, rdK (semXIR I (fd1IR N ℓ S.length B) s).M (outA B ℓ + x) = fd1 N ℓ S y x) ∧
    Inv (semXIR I (fd1IR N ℓ S.length B) s).M ∧ (semXIR I (fd1IR N ℓ S.length B) s).o = s.o := by
  have hB' := hB
  simp only [regs] at hB'
  rw [fd1IR, semXIR_seq]
  obtain ⟨a1, a2, a3, a4⟩ := lamIR_sem I s hM hN hN64 hB hsz h64 hm hSn hS
  have z1 := size_sem I (lamIR N ℓ S.length B) s
  generalize semXIR I (lamIR N ℓ S.length B) s = s1 at a1 a2 a3 a4 z1
  obtain ⟨b1, b2, b3, _⟩ := laneIR_sem I s1 a2 (y := y) hN hN64 hB (by rw [z1]; exact hsz) h64 hm hSn a1
    (fun j hj => by
      rw [← hy j hj]
      exact rdK_eq (a4 _ (by simp only [regs, yA]; omega)
        (Or.inr (Or.inl ⟨by simp only [yA, sA]; omega, by simp only [yA, tA]; omega⟩))))
  exact ⟨b1, b2, b3.trans a3⟩

/-- **`FD1` on the machine decodes one error**: under `OneErr`, `lamIR` then `laneIR` leave the
message's novel-basis coefficients (zero-padded to `2^ℓ`) at `outA B ℓ`. -/
theorem fd1IR_correct (I : Array Word) (s : St) (hM : Inv s.M) {N ℓ k B : ℕ} {S : List ℕ}
    {y : ℕ → BF64} {c : Fin k → BF64} (hN : ℓ + 1 ≤ N) (hN64 : N ≤ 64) (hB : regs ≤ B)
    (hsz : fdEnd B ℓ ≤ s.M.size) (h64 : fdEnd B ℓ < 2 ^ 64) (h : OneErr ℓ k S y c)
    (hS : ∀ i < S.length, rd s.M (sA B + i) = toWord (S.getD i 0))
    (hy : ∀ j < 2 ^ ℓ, rdK s.M (yA B ℓ + j) = y j) :
    ∀ x < 2 ^ ℓ, rdK (semXIR I (fd1IR N ℓ S.length B) s).M (outA B ℓ + x) =
      if hx : x < k then c ⟨x, hx⟩ else 0 := by
  have hm : S.length ≤ 2 ^ ℓ := by
    obtain ⟨hnd, _, hSn, _⟩ := h
    rw [← List.toFinset_card_of_nodup hnd, ← Finset.card_range (2 ^ ℓ)]
    exact Finset.card_le_card fun j hj => Finset.mem_range.2 (hSn j (by simpa using hj))
  intro x hx
  rw [(fd1IR_sem I s hM hN hN64 hB hsz h64 hm h.2.2.1 hS hy).1 x hx, fd1_correct hN hN64 h x hx]

end Lvm6.FD
