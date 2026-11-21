module

public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity

@[expose] public section

/-!
# Basic facts on characters modulo `p` with values in `ℤ[i]`

* `gi`: the Gaussian unit `i`, and the fourth roots of unity in `ℤ[i]`.
* Proposition 1.1 of the survey: characters of odd order are even
  (`apply_neg_one_of_odd_orderOf`), characters of order two are real
  (`apply_of_orderOf_two`), and a quartic character is odd exactly when
  `p ≡ 5 (mod 8)` (`quartic_apply_neg_one`).
* For a quartic character and `p ≡ 5 (mod 8)`: `χ 2 = ± i` (`quartic_apply_two`).
-/

namespace BandParity

/-- The Gaussian unit `i`. -/
def gi : GaussianInt := ⟨0, 1⟩

@[simp] lemma gi_re : gi.re = 0 := rfl
@[simp] lemma gi_im : gi.im = 1 := rfl

lemma gi_sq : gi ^ 2 = -1 := by
  rw [Zsqrtd.ext_iff]; simp [sq, gi]

lemma gi_pow_four : gi ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, gi_sq]; norm_num

lemma gi_ne_one : gi ≠ 1 := by
  intro h; have := congrArg Zsqrtd.re h; simp at this

lemma gi_ne_neg_gi : gi ≠ -gi := by
  intro h; have := congrArg Zsqrtd.im h; simp at this

lemma neg_one_ne_one : (-1 : GaussianInt) ≠ 1 := by
  intro h; have := congrArg Zsqrtd.re h; simp at this

/-- The fourth roots of unity in `ℤ[i]` are `1, i, -1, -i`. -/
lemma eq_of_pow_four_eq_one {x : GaussianInt} (h : x ^ 4 = 1) :
    x = 1 ∨ x = gi ∨ x = -1 ∨ x = -gi := by
  have e : (x - 1) * (x + 1) * (x - gi) * (x + gi) = 0 := by
    linear_combination (1 - x ^ 2) * gi_sq + h
  rcases mul_eq_zero.1 e with e | e
  · rcases mul_eq_zero.1 e with e | e
    · rcases mul_eq_zero.1 e with e | e
      · exact Or.inl (sub_eq_zero.1 e)
      · exact Or.inr (Or.inr (Or.inl (eq_neg_of_add_eq_zero_left e)))
    · exact Or.inr (Or.inl (sub_eq_zero.1 e))
  · exact Or.inr (Or.inr (Or.inr (eq_neg_of_add_eq_zero_left e)))

/-- Odd powers of `± i` are `± i`. -/
lemma pm_gi_pow_odd {u : GaussianInt} (hu : u = gi ∨ u = -gi) {e : ℕ} (he : Odd e) :
    u ^ e = gi ∨ u ^ e = -gi := by
  obtain ⟨j, rfl⟩ := he
  have hu2 : u ^ 2 = -1 := by rcases hu with rfl | rfl <;> simp [gi_sq]
  rw [pow_succ, pow_mul, hu2]
  rcases neg_one_pow_eq_or GaussianInt j with h | h <;> rw [h] <;> rcases hu with rfl | rfl <;>
    simp

/-- Even powers of `± i` are `(-1) ^ j`. -/
lemma pm_gi_pow_two_mul {u : GaussianInt} (hu : u = gi ∨ u = -gi) (j : ℕ) :
    u ^ (2 * j) = (-1) ^ j := by
  have hu2 : u ^ 2 = -1 := by rcases hu with rfl | rfl <;> simp [gi_sq]
  rw [pow_mul, hu2]

/-- The values `0, 1, i, -1, -i` are pairwise distinct (as `simp` lemmas). -/
lemma distinct :
    ((1 : GaussianInt) = gi ↔ False) ∧ ((1 : GaussianInt) = -1 ↔ False) ∧
    ((1 : GaussianInt) = -gi ↔ False) ∧ (gi = 1 ↔ False) ∧ (gi = -1 ↔ False) ∧
    (gi = -gi ↔ False) ∧ ((-1 : GaussianInt) = 1 ↔ False) ∧ ((-1 : GaussianInt) = gi ↔ False) ∧
    ((-1 : GaussianInt) = -gi ↔ False) ∧ (-gi = 1 ↔ False) ∧ (-gi = gi ↔ False) ∧
    (-gi = (-1 : GaussianInt) ↔ False) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [iff_false] <;> decide

variable {p : ℕ} [hp : Fact p.Prime]

/-- A generator of `(ZMod p)ˣ`. -/
lemma exists_generator :
    ∃ g : (ZMod p)ˣ, orderOf g = p - 1 ∧ ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨g, ?_, fun u => ?_⟩
  · rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  · exact (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 (hg u))

lemma unit_apply_pow_four {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R) (hχ : orderOf χ = 4)
    (u : (ZMod p)ˣ) : χ u ^ 4 = 1 := by
  rw [← MulChar.pow_apply' χ (by norm_num), ← hχ, pow_orderOf_eq_one, MulChar.one_apply_coe]

/-- **Proposition 1.1, odd orders.** A character of odd order is even. -/
theorem apply_neg_one_of_odd_orderOf {R : Type*} [CommRing R] (χ : MulChar (ZMod p) R)
    (h : Odd (orderOf χ)) : χ (-1) = 1 := by
  obtain ⟨k, hk⟩ := h
  have h1 : χ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h2 : χ (-1) ^ orderOf χ = 1 := by
    rw [← MulChar.pow_apply' χ (by omega), pow_orderOf_eq_one]
    exact MulChar.one_apply isUnit_one.neg
  rw [hk, pow_succ, pow_mul, h1, one_pow, one_mul] at h2
  exact h2

/-- **Proposition 1.1, order two.** A character of order two is real: its values are
`0` and `± 1`. -/
theorem apply_of_orderOf_two (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 2)
    (a : ZMod p) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases ha : a = 0
  · left; rw [ha]; exact MulChar.map_zero χ
  · right
    have : χ a * χ a = 1 := by
      rw [← sq, ← MulChar.pow_apply' χ (by norm_num), ← hχ, pow_orderOf_eq_one]
      exact MulChar.one_apply (Ne.isUnit ha)
    exact mul_self_eq_one_iff.1 this

section Quartic

variable (χ : MulChar (ZMod p) GaussianInt) (hχ : orderOf χ = 4)
include hχ

/-- Nonzero values of a quartic character are fourth roots of unity. -/
theorem quartic_values {a : ZMod p} (ha : a ≠ 0) :
    χ a = 1 ∨ χ a = gi ∨ χ a = -1 ∨ χ a = -gi :=
  eq_of_pow_four_eq_one (by simpa using unit_apply_pow_four χ hχ (Units.mk0 a ha))

/-- On a generator, a quartic character takes the value `± i`. -/
theorem quartic_apply_generator {g : (ZMod p)ˣ} (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    χ g = gi ∨ χ g = -gi := by
  rcases eq_of_pow_four_eq_one (unit_apply_pow_four χ hχ g) with h | h | h | h
  · exfalso
    have : χ ^ 2 = 1 := by
      refine MulChar.ext fun u => ?_; obtain ⟨k, rfl⟩ := hg u
      rw [MulChar.pow_apply' χ (by norm_num), Units.val_pow_eq_pow_val, map_pow, h]; simp
    have := orderOf_dvd_of_pow_eq_one this; rw [hχ] at this; norm_num at this
  · exact Or.inl h
  · exfalso
    have : χ ^ 2 = 1 := by
      refine MulChar.ext fun u => ?_; obtain ⟨k, rfl⟩ := hg u
      rw [MulChar.pow_apply' χ (by norm_num), Units.val_pow_eq_pow_val, map_pow, h,
        ← pow_mul, mul_comm, pow_mul]; simp
    have := orderOf_dvd_of_pow_eq_one this; rw [hχ] at this; norm_num at this
  · exact Or.inr h

omit hχ in
/-- `-1 = g ^ ((p - 1) / 2)` for a generator `g`. -/
lemma neg_one_eq_generator_pow (hp2 : p ≠ 2) {g : (ZMod p)ˣ} (hgo : orderOf g = p - 1) :
    ((g ^ ((p - 1) / 2) : (ZMod p)ˣ) : ZMod p) = -1 := by
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le; omega
  set x : (ZMod p)ˣ := g ^ ((p - 1) / 2) with hx
  have hx2 : (x : ZMod p) * x = 1 := by
    rw [← Units.val_mul, ← pow_add, show (p - 1) / 2 + (p - 1) / 2 = p - 1 by
      have := hp.out.eq_one_or_self_of_dvd 2
      rcases Nat.Prime.eq_two_or_odd hp.out with h | h
      · exact absurd h hp2
      · omega, ← hgo, pow_orderOf_eq_one, Units.val_one]
  rcases mul_self_eq_one_iff.1 hx2 with h | h
  · exfalso
    have h1 : x = 1 := Units.ext h
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hgo] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  · exact h

/-- **Proposition 1.1, order four.** For `p ≡ 5 (mod 8)` a quartic character is odd. -/
theorem quartic_apply_neg_one (hp8 : p % 8 = 5) : χ (-1) = -1 := by
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  have hp2 : p ≠ 2 := by omega
  rw [← neg_one_eq_generator_pow hp2 hgo, Units.val_pow_eq_pow_val, map_pow,
    show (p - 1) / 2 = 2 * (2 * (p / 8) + 1) by omega,
    pm_gi_pow_two_mul (quartic_apply_generator χ hχ hg)]
  simp [pow_succ, pow_mul]

/-- **Proposition 1.1, order four, converse.** For `p ≡ 1 (mod 8)` a quartic character is even. -/
theorem quartic_apply_neg_one_of_one (hp8 : p % 8 = 1) : χ (-1) = 1 := by
  obtain ⟨g, hgo, hg⟩ := exists_generator (p := p)
  have hp2 : p ≠ 2 := by omega
  rw [← neg_one_eq_generator_pow hp2 hgo, Units.val_pow_eq_pow_val, map_pow,
    show (p - 1) / 2 = 2 * (2 * (p / 8)) by omega,
    pm_gi_pow_two_mul (quartic_apply_generator χ hχ hg)]
  simp [pow_mul]

omit hχ in
/-- `2` is an odd power of any generator when `p ≡ 5 (mod 8)`. -/
lemma two_eq_generator_pow_odd (hp8 : p % 8 = 5) {g : (ZMod p)ˣ}
    (hg : ∀ u : (ZMod p)ˣ, ∃ k : ℕ, g ^ k = u) :
    ∃ e : ℕ, Odd e ∧ ((g ^ e : (ZMod p)ˣ) : ZMod p) = 2 := by
  have hp2 : p ≠ 2 := by omega
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this
    exact hp2 this
  obtain ⟨e, he⟩ := hg (Units.mk0 2 h20)
  refine ⟨e, ?_, by rw [he]; rfl⟩
  rcases Nat.even_or_odd e with ⟨j, rfl⟩ | h
  · exfalso
    have hsq : IsSquare (2 : ZMod p) := ⟨((g ^ j : (ZMod p)ˣ) : ZMod p), by
      rw [← Units.val_mul, ← pow_add, he]; rfl⟩
    rcases (ZMod.exists_sq_eq_two_iff hp2).1 hsq with h | h <;> omega
  · exact h

/-- For `p ≡ 5 (mod 8)`, `χ 2 = ± i`: `2` is a quadratic non-residue. -/
theorem quartic_apply_two (hp8 : p % 8 = 5) : χ 2 = gi ∨ χ 2 = -gi := by
  obtain ⟨g, -, hg⟩ := exists_generator (p := p)
  obtain ⟨e, he, h2⟩ := two_eq_generator_pow_odd hp8 hg
  rw [← h2, Units.val_pow_eq_pow_val, map_pow]
  exact pm_gi_pow_odd (quartic_apply_generator χ hχ hg) he

end Quartic

end BandParity
