module

public import BandParity.Pin
public import BandParity.FixedBase

@[expose] public section

/-!
# Coset sums and the coordinates `k`, `t` (Propositions 3.1 and 3.2)

For a quartic character `χ` modulo `p ≡ 5 (mod 8)`, `p > 5`, the class `C_z = {n : χ n = z}`
(`z ∈ {1, i, -1, -i}`) has `cosetSum χ z = ∑_{n ∈ C_z} n` (least residues). Then

* `p ∣ cosetSum χ z` (`p_dvd_cosetSum`), so `S χ z = cosetSum χ z / p` is an integer;
* each class has `(p - 1)/4` elements (`card_class`);
* `S χ z + S χ (-z) = (p - 1)/4` (`S_add_S_neg`);
* `T χ = p (k + i t)` with `k = S 1 - S (-1)`, `t = S i - S (-i)` (`T_eq`), i.e.
  `B₁,χ = k + i t`;
* `k` and `t` are odd (`odd_k`, `odd_t`);
* the conjugate character `χ ^ 3` has coordinates `(k, -t)` (`k_pow_three`, `t_pow_three`).
-/

namespace BandParity

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-- `∑_{n : χ n = z} n` over least nonnegative residues. -/
def cosetSum (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℤ :=
  ∑ n ∈ univ.filter (fun n : ZMod p => χ n = z), (n.val : ℤ)

/-- The normalized coset sum `S_z = (1/p) ∑_{n ∈ C_z} n`. -/
def S (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : ℤ := cosetSum χ z / p

/-- The real coordinate `k = S₀ - S₂`. -/
def k (χ : MulChar (ZMod p) GaussianInt) : ℤ := S χ 1 - S χ (-1)

/-- The imaginary coordinate `t = S₁ - S₃`. -/
def t (χ : MulChar (ZMod p) GaussianInt) : ℤ := S χ gi - S χ (-gi)

lemma cosetSum_eq_sum_ite (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) :
    cosetSum χ z = ∑ n : ZMod p, if χ n = z then (n.val : ℤ) else 0 := by
  rw [cosetSum, Finset.sum_filter]

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

lemma apply_eq_zero_iff {n : ZMod p} : χ n = 0 ↔ n = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ MulChar.map_zero χ⟩
  by_contra hn
  rcases quartic_values χ hχ hn with h' | h' | h' | h' <;> rw [h'] at h <;> revert h <;> decide

/-- A nontrivial element of the kernel, when `p > 5`. -/
lemma exists_kernel_ne_one (hp5 : 5 < p) : ∃ a : ZMod p, a ≠ 0 ∧ a ≠ 1 ∧ χ a = 1 := by
  obtain ⟨g, hgo, -⟩ := exists_generator (p := p)
  refine ⟨((g ^ 4 : (ZMod p)ˣ) : ZMod p), Units.ne_zero _, fun h => ?_, ?_⟩
  · have h1 : g ^ 4 = 1 := Units.ext h
    have := Nat.le_of_dvd (by norm_num) (hgo ▸ orderOf_dvd_of_pow_eq_one h1)
    omega
  · rw [Units.val_pow_eq_pow_val, map_pow]
    exact unit_apply_pow_four χ hχ g

/-- The sum of a class in `ZMod p` vanishes (multiplication by a kernel element permutes it). -/
lemma class_sum_zmod (hp5 : 5 < p) (z : GaussianInt) :
    ∑ n : ZMod p, (if χ n = z then n else 0) = 0 := by
  obtain ⟨a, ha0, ha1, hχa⟩ := exists_kernel_ne_one hχ hp5
  set s0 := ∑ n : ZMod p, (if χ n = z then n else 0)
  have h : s0 = a * s0 := by
    rw [Finset.mul_sum]
    refine (Fintype.sum_equiv (Equiv.mulLeft₀ a ha0) _ _ fun n => ?_).symm
    simp only [Equiv.mulLeft₀_apply, map_mul, hχa, one_mul, mul_ite, mul_zero]
  have : (a - 1) * s0 = 0 := by linear_combination -h
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ha1)

/-- **Proposition 3.1 (integrality).** `p ∣ ∑_{n ∈ C_z} n`. -/
theorem p_dvd_cosetSum (hp5 : 5 < p) (z : GaussianInt) : (p : ℤ) ∣ cosetSum χ z := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, cosetSum_eq_sum_ite, Int.cast_sum]
  rw [← class_sum_zmod hχ hp5 z]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> simp

lemma p_mul_S (hp5 : 5 < p) (z : GaussianInt) : (p : ℤ) * S χ z = cosetSum χ z :=
  Int.mul_ediv_cancel' (p_dvd_cosetSum hχ hp5 z)

/-- Multiplying by `c` moves `C_z` onto `C_{χ(c) z}`. -/
lemma card_class_mul {c : ZMod p} (hc : c ≠ 0) (z : GaussianInt) :
    (univ.filter (fun n : ZMod p => χ n = χ c * z)).card =
      (univ.filter (fun n : ZMod p => χ n = z)).card := by
  symm
  refine Finset.card_equiv (Equiv.mulLeft₀ c hc) fun n => ?_
  simp only [mem_filter, mem_univ, true_and, Equiv.mulLeft₀_apply, map_mul]
  have hχc : χ c ≠ 0 := fun h => hc ((apply_eq_zero_iff hχ).1 h)
  exact ⟨fun h => h ▸ rfl, fun h => mul_left_cancel₀ hχc h⟩

/-- Every class `C_z`, `z ∈ {1, i, -1, -i}`, has the size of `C_1`. -/
lemma card_class_eq (z : GaussianInt) (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    (univ.filter (fun n : ZMod p => χ n = z)).card =
      (univ.filter (fun n : ZMod p => χ n = 1)).card := by
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  have hg0 : (g : ZMod p) ≠ 0 := Units.ne_zero g
  set c : GaussianInt → ℕ := fun z => (univ.filter (fun n : ZMod p => χ n = z)).card with hc
  have step : ∀ w, c (χ g * w) = c w := fun w => card_class_mul hχ hg0 w
  rcases quartic_apply_generator χ hχ hg with h | h <;> rw [h] at step
  · have e1 := step 1; have e2 := step gi; have e3 := step (-1)
    simp only [mul_one, mul_neg, gi_sq, ← sq] at e1 e2 e3
    change c z = c 1
    rcases hz with rfl | rfl | rfl | rfl
    · rfl
    · exact e1
    · exact e2.trans e1
    · exact e3.trans (e2.trans e1)
  · have e1 := step 1; have e2 := step (-gi); have e3 := step (-1)
    simp only [mul_one, mul_neg, neg_neg, ← sq] at e1 e2 e3
    change c z = c 1
    rcases hz with rfl | rfl | rfl | rfl
    · rfl
    · exact e3.trans (e2.trans e1)
    · exact e2.trans e1
    · exact e1

/-- **Class sizes.** Each class has `(p - 1)/4` elements. -/
theorem card_class (z : GaussianInt) (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    4 * (univ.filter (fun n : ZMod p => χ n = z)).card = p - 1 := by
  rw [card_class_eq hχ z hz]
  have hpart : ∀ n : ZMod p, (1 : ℕ) = (if χ n = 0 then 1 else 0) + (if χ n = 1 then 1 else 0) +
      (if χ n = gi then 1 else 0) + (if χ n = -1 then 1 else 0) + (if χ n = -gi then 1 else 0) := by
    intro n
    by_cases hn : n = 0
    · rw [hn, MulChar.map_zero]; decide
    · rcases quartic_values χ hχ hn with h | h | h | h <;> rw [h] <;> decide
  have htot : (Fintype.card (ZMod p) : ℕ) = ∑ n : ZMod p, (1 : ℕ) := by simp
  rw [Finset.sum_congr rfl (fun n _ => hpart n)] at htot
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id] at htot
  rw [ZMod.card] at htot
  have h0 : (univ.filter (fun n : ZMod p => χ n = 0)).card = 1 := by
    rw [Finset.card_eq_one]; refine ⟨0, ?_⟩
    ext n; simp [apply_eq_zero_iff hχ]
  rw [h0, card_class_eq hχ gi (by simp), card_class_eq hχ (-1) (by simp),
    card_class_eq hχ (-gi) (by simp)] at htot
  omega

omit hχ in
/-- Negation moves `C_z` onto `C_{-z}` when `χ` is odd. -/
lemma cosetSum_add_cosetSum_neg (hodd : χ (-1) = -1) (z : GaussianInt) (hz0 : z ≠ 0) :
    cosetSum χ z + cosetSum χ (-z) =
      p * (univ.filter (fun n : ZMod p => χ n = z)).card := by
  have hneg : cosetSum χ (-z) = ∑ n : ZMod p, if χ n = z then ((p : ℤ) - n.val) else 0 := by
    rw [cosetSum_eq_sum_ite]
    refine (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun n => ?_).symm
    simp only [Equiv.neg_apply]
    have hχn : χ (-n) = -χ n := by rw [show -n = -1 * n by ring, map_mul, hodd, neg_one_mul]
    simp only [hχn, neg_inj]
    by_cases h : χ n = z
    · have hn0 : n ≠ 0 := by rintro rfl; exact hz0 (h.symm.trans (MulChar.map_zero χ))
      have := ZMod.val_lt n
      simp only [h, ↓reduceIte, val_neg_of_ne_zero hn0]
      push_cast [Nat.cast_sub this.le]; ring
    · simp [h]
  rw [hneg, cosetSum_eq_sum_ite, ← Finset.sum_add_distrib]
  rw [show (p : ℤ) * (univ.filter (fun n : ZMod p => χ n = z)).card =
      ∑ n : ZMod p, if χ n = z then (p : ℤ) else 0 by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

/-- **Proposition 3.1 (pairing).** `S_z + S_{-z} = (p - 1)/4`. -/
theorem S_add_S_neg (hp8 : p % 8 = 5) (hp5 : 5 < p) (z : GaussianInt)
    (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    S χ z + S χ (-z) = ((p - 1) / 4 : ℕ) := by
  have hodd := quartic_apply_neg_one χ hχ hp8
  have hz0 : z ≠ 0 := by rcases hz with rfl | rfl | rfl | rfl <;> decide
  have hnz : -z = 1 ∨ -z = gi ∨ -z = -1 ∨ -z = -gi := by
    rcases hz with rfl | rfl | rfl | rfl <;> simp
  have e := cosetSum_add_cosetSum_neg hodd z hz0
  have hc := card_class hχ z hz
  rw [← p_mul_S hχ hp5, ← p_mul_S hχ hp5, ← mul_add] at e
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have := mul_left_cancel₀ hp0 e
  rw [this]; congr 1; omega

/-- **Proposition 3.1 (the value).** `∑ χ(n) n = p (k + i t)`, i.e. `B₁,χ = k + i t`. -/
theorem T_eq' (hp5 : 5 < p) : T χ = (p : GaussianInt) * ((k χ : GaussianInt) + gi * (t χ)) := by
  have hsplit : T χ = (cosetSum χ 1 : GaussianInt) + gi * (cosetSum χ gi) -
      (cosetSum χ (-1)) - gi * (cosetSum χ (-gi)) := by
    unfold T
    simp only [cosetSum_eq_sum_ite, Int.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n = 0
    · subst hn; simp
    · rcases quartic_values χ hχ hn with h | h | h | h <;> rw [h] <;> simp [distinct]
  rw [hsplit, ← p_mul_S hχ hp5, ← p_mul_S hχ hp5, ← p_mul_S hχ hp5, ← p_mul_S hχ hp5, k, t]
  push_cast; ring

/-- **Proposition 3.2 (oddness of `k`).** -/
theorem odd_k' (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (k χ) := by
  have h := S_add_S_neg hχ hp8 hp5 1 (by simp)
  rw [k, show S χ (-1) = ((p - 1) / 4 : ℕ) - S χ 1 by linarith]
  have : Odd (((p - 1) / 4 : ℕ) : ℤ) := by
    rw [Int.odd_coe_nat]; exact Nat.odd_iff.2 (by omega)
  obtain ⟨j, hj⟩ := this
  exact ⟨S χ 1 - j - 1, by linarith⟩

/-- **Proposition 3.2 (oddness of `t`).** -/
theorem odd_t' (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (t χ) := by
  have h := S_add_S_neg hχ hp8 hp5 gi (by simp)
  rw [t, show S χ (-gi) = ((p - 1) / 4 : ℕ) - S χ gi by linarith]
  have : Odd (((p - 1) / 4 : ℕ) : ℤ) := by
    rw [Int.odd_coe_nat]; exact Nat.odd_iff.2 (by omega)
  obtain ⟨j, hj⟩ := this
  exact ⟨S χ gi - j - 1, by linarith⟩

/-- The conjugate character `χ ^ 3` is `star ∘ χ`. -/
lemma pow_three_apply (n : ZMod p) : (χ ^ 3) n = star (χ n) := by
  by_cases hn : n = 0
  · subst hn; simp [MulChar.map_zero]
  · rw [MulChar.pow_apply' χ (by norm_num)]
    rcases quartic_values χ hχ hn with h | h | h | h <;> rw [h] <;> decide

lemma cosetSum_pow_three (z : GaussianInt) : cosetSum (χ ^ 3) z = cosetSum χ (star z) := by
  unfold cosetSum
  congr 1; ext n
  simp only [mem_filter, mem_univ, true_and, pow_three_apply hχ]
  exact ⟨fun h => h ▸ (star_star _).symm, fun h => by rw [h, star_star]⟩

/-- **Conjugation.** `χ ↦ χ̄` fixes `k`. -/
theorem k_pow_three : k (χ ^ 3) = k χ := by
  simp only [k, S, cosetSum_pow_three hχ]; rw [show star (1 : GaussianInt) = 1 by decide,
    show star (-1 : GaussianInt) = -1 by decide]

/-- **Conjugation.** `χ ↦ χ̄` negates `t`. -/
theorem t_pow_three : t (χ ^ 3) = -t χ := by
  simp only [t, S, cosetSum_pow_three hχ]
  rw [show star gi = -gi by decide, show star (-gi) = gi by decide]; ring

end Quartic

end BandParity
