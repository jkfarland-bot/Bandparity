module

public import BandParity.Defs
public import BandParity.Matching

@[expose] public section

/-!
# The band-parity laws

For a prime `p ≡ 5 (mod 8)`, `p > 5`, and the quartic character `χ` with `χ(2) = i`, write
`𝒞(p) = f + i e`. This file proves

* the parity dictionary `(-1)^{⌊n²/p⌋} = s(n) s(n²)` (`neg_one_pow_band`);
* the coset form `f = ∑_{u ∈ H} s(u) s(u²)`, `e = ∑_{u ∈ 2H} s(u) s(u²)`
  (`bandSum_re`, `bandSum_im`), where `H = C₁` and `2H = C_i` are the classes of `χ`;
* the lag identity `∑_{u ∈ 2H} s(u) s(2u) = κ` (`lag_identity`);
* **Theorem A**: `f ≡ Q` and `e ≡ κ (mod 4)` (`bandSum_re_modEq`, `bandSum_im_modEq`);
* the exact coset parities `∑_H s = k + 2t`, `∑_{2H} s = t - 2k` (`coset_parities`);
* the **Coordinate Congruence** `e ≡ Q + k + t` and `κ ≡ Q + k + t (mod 4)`
  (`bandSum_im_modEq_coords`, `coordinate_congruence`).
-/

namespace BandParity

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

/-! ### Signs and the parity dictionary -/

omit hp in
lemma parSign_eq (x : ZMod p) : parSign x = 1 ∨ parSign x = -1 :=
  neg_one_pow_eq_or ℤ _

omit hp in
lemma parSign_mul_self (x : ZMod p) : parSign x * parSign x = 1 := by
  rcases parSign_eq x with h | h <;> rw [h] <;> norm_num

lemma parSign_zero : parSign (0 : ZMod p) = 1 := by simp [parSign]

lemma parSign_neg (hp2 : p ≠ 2) {x : ZMod p} (hx : x ≠ 0) : parSign (-x) = -parSign x := by
  unfold parSign
  rw [val_neg_of_ne_zero hx]
  have hv := ZMod.val_lt x
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have h : (-1 : ℤ) ^ (p - x.val) * (-1) ^ x.val = -1 := by
    rw [← pow_add, Nat.sub_add_cancel hv.le, hpodd.neg_one_pow]
  rcases neg_one_pow_eq_or ℤ x.val with h' | h' <;> rw [h'] at h ⊢ <;> linarith

lemma val_two (hp2 : p ≠ 2) : (2 : ZMod p).val = 2 := by
  have : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, ZMod.val_natCast,
    Nat.mod_eq_of_lt this]

lemma two_ne_zero' (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h; have := val_two (p := p) hp2; rw [h, ZMod.val_zero] at this; omega

lemma val_two_mul_of_lt (hp2 : p ≠ 2) {x : ZMod p} (hx : 2 * x.val < p) :
    (2 * x).val = 2 * x.val := by
  rw [ZMod.val_mul, val_two hp2, Nat.mod_eq_of_lt hx]

lemma parSign_two_mul_of_lt (hp2 : p ≠ 2) {x : ZMod p} (hx : 2 * x.val < p) :
    parSign (2 * x) = 1 := by
  rw [parSign, val_two_mul_of_lt hp2 hx, pow_mul]; norm_num

/-- **Parity dictionary.** `(-1)^{⌊⟨x⟩²/p⌋} = s(x) s(x²)`. -/
theorem neg_one_pow_band' (hp2 : p ≠ 2) (x : ZMod p) :
    (-1 : ℤ) ^ band x = parSign x * parSign (x ^ 2) := by
  unfold parSign band
  have hsq : (x ^ 2).val = x.val ^ 2 % p := by rw [sq, ZMod.val_mul, sq]
  rw [hsq]
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  have h1 : (-1 : ℤ) ^ (x.val ^ 2) = (-1) ^ x.val := by
    rcases Nat.even_or_odd x.val with h | h
    · rw [h.neg_one_pow, (Nat.even_pow.2 ⟨h, two_ne_zero⟩).neg_one_pow]
    · rw [h.neg_one_pow, (h.pow).neg_one_pow]
  have h2 : (-1 : ℤ) ^ (x.val ^ 2) =
      (-1) ^ (x.val ^ 2 / p) * (-1) ^ (x.val ^ 2 % p) := by
    conv_lhs => rw [← Nat.div_add_mod (x.val ^ 2) p]
    rw [pow_add, pow_mul, hpodd.neg_one_pow]
  have hr : (-1 : ℤ) ^ (x.val ^ 2 % p) * (-1) ^ (x.val ^ 2 % p) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have E := h1.symm.trans h2
  linear_combination (-((-1 : ℤ) ^ (x.val ^ 2 % p))) * E + (-((-1 : ℤ) ^ (x.val ^ 2 / p))) * hr

/-! ### Sums over the half range -/

/-- An even function vanishing at `0` sums to twice its sum over `0 ≤ ⟨x⟩ < p/2`. -/
lemma sum_eq_two_nsmul_half {R : Type*} [AddCommMonoid R] (hp2 : p ≠ 2) (h : ZMod p → R)
    (h0 : h 0 = 0) (hsym : ∀ x, h (-x) = h x) :
    ∑ x, h x = 2 • ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), h x := by
  rw [← Finset.sum_filter_add_sum_filter_not univ (fun x : ZMod p => 2 * x.val < p), two_nsmul]
  congr 1
  simp only [Finset.sum_filter]
  refine (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun x => ?_).symm
  simp only [Equiv.neg_apply]
  by_cases hx : x = 0
  · subst hx; simp [h0, hp.out.pos]
  · rw [val_neg_of_ne_zero hx, hsym]
    have hv := ZMod.val_lt x
    have hpodd : p % 2 = 1 := Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
    by_cases hc : 2 * x.val < p
    · have : ¬ 2 * (p - x.val) < p := by omega
      simp [hc, this]
    · have : 2 * (p - x.val) < p := by omega
      simp [hc, this]

/-- On the half range, a function vanishing at `0` may be summed over `0 < ⟨x⟩ < p/2`. -/
lemma sum_half_eq_sum_half' {R : Type*} [AddCommMonoid R] (h : ZMod p → R) (h0 : h 0 = 0) :
    ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), h x =
      ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p), h x := by
  symm
  refine Finset.sum_subset (fun x hx => by simp at hx ⊢; exact hx.2) fun x hx hx' => ?_
  simp only [mem_filter, mem_univ, true_and, not_and, not_lt] at hx hx'
  have : x.val = 0 := by
    by_contra hne; exact absurd hx (by have := hx' (Nat.pos_of_ne_zero hne); omega)
  rw [(ZMod.val_eq_zero x).1 this, h0]

/-- Sums over residues with a condition on the least residue are sums over `ℕ`. -/
lemma sum_filter_val {R : Type*} [AddCommMonoid R] (P : ℕ → Prop) [DecidablePred P]
    (g : ℕ → R) :
    ∑ x ∈ univ.filter (fun x : ZMod p => P x.val), g x.val =
      ∑ v ∈ (range p).filter P, g v := by
  refine Finset.sum_nbij (fun x => x.val) ?_ ?_ ?_ ?_
  · intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_range] at hx ⊢
    exact ⟨ZMod.val_lt x, hx⟩
  · intro x _ y _ h; exact ZMod.val_injective p h
  · intro v hv
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hv
    refine ⟨(v : ZMod p), ?_, ZMod.val_natCast_of_lt hv.1⟩
    simp [ZMod.val_natCast_of_lt hv.1, hv.2]
  · intro _ _; rfl

omit hp in
lemma sum_Ioc_alt (m : ℕ) : ∑ v ∈ Ioc 0 (2 * m), (-1 : ℤ) ^ v = 0 := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      Finset.sum_Ioc_succ_top (by omega), Finset.sum_Ioc_succ_top (by omega), ih,
      Odd.neg_one_pow ⟨n, rfl⟩, Even.neg_one_pow ⟨n + 1, by ring⟩]
    norm_num

omit hp in
/-- `∑_{0 < v < p/2} (-1)^v = 0` when `p ≡ 1 (mod 4)`. -/
lemma sum_alt_half (hp4 : p % 4 = 1) :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p), (-1 : ℤ) ^ v = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, p = 4 * m + 1 := ⟨p / 4, by omega⟩
  have hset : (range (4 * m + 1)).filter (fun v => 0 < v ∧ 2 * v < 4 * m + 1) =
      Finset.Ioc 0 (2 * m) := by
    ext v; simp only [mem_filter, mem_range, mem_Ioc]; omega
  rw [hset, sum_Ioc_alt]

/-! ### The classes of `χ` and coset sums -/

/-- The class `C_z = {x : χ x = z}`; `C₁ = H` is the group of fourth powers and, under the pin,
`C_i = 2H`. -/
abbrev cls (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : Finset (ZMod p) :=
  univ.filter (fun x => χ x = z)

lemma gi_ne_zero : gi ≠ 0 := by decide

lemma zero_ne_gi : (0 : GaussianInt) ≠ gi := by decide

lemma zero_ne_neg_gi : (0 : GaussianInt) ≠ -gi := by decide

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

/-- Grouping `∑ χ(x) g(x)` by the four classes. -/
lemma sum_char_mul (g : ZMod p → ℤ) :
    ∑ x, χ x * (g x : GaussianInt) =
      ((∑ x ∈ cls χ 1, g x : ℤ) : GaussianInt) + gi * ((∑ x ∈ cls χ gi, g x : ℤ) : GaussianInt)
        - ((∑ x ∈ cls χ (-1), g x : ℤ) : GaussianInt)
        - gi * ((∑ x ∈ cls χ (-gi), g x : ℤ) : GaussianInt) := by
  simp only [cls, Finset.sum_filter, Int.cast_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x = 0
  · subst hx; simp [MulChar.map_zero, zero_ne_gi, gi_ne_zero]
  · rcases quartic_values χ hχ hx with h | h | h | h <;> rw [h] <;> simp [distinct]

omit hχ in
lemma char_neg (hodd : χ (-1) = -1) (x : ZMod p) : χ (-x) = -χ x := by
  rw [show -x = -1 * x by ring, map_mul, hodd, neg_one_mul]

omit hχ in
/-- For a function odd away from `0`, the class sums over `C_{-z}` and `C_z` are opposite. -/
lemma sum_cls_neg (hodd : χ (-1) = -1) (g : ZMod p → ℤ) (hg : ∀ x ≠ 0, g (-x) = -g x)
    {z : GaussianInt} (hz : z ≠ 0) :
    ∑ x ∈ cls χ (-z), g x = -∑ x ∈ cls χ z, g x := by
  simp only [cls, Finset.sum_filter, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun x => ?_
  simp only [Equiv.neg_apply, char_neg hodd]
  by_cases hx : x = 0
  · subst hx
    have h1 : ¬ (χ 0 = -z) := by rw [MulChar.map_zero]; exact fun h => hz (neg_eq_zero.1 h.symm)
    simp [MulChar.map_zero, hz, hz.symm]
  · rw [hg x hx]
    by_cases h : χ x = -z
    · simp [h]
    · have : ¬ -χ x = z := fun h' => h (by rw [← h', neg_neg])
      simp [h, this]

omit hχ in
/-- For a function even away from `0`, the class sums over `C_{-z}` and `C_z` agree. -/
lemma sum_cls_neg_even (hodd : χ (-1) = -1) (g : ZMod p → ℤ) (hg : ∀ x ≠ 0, g (-x) = g x)
    {z : GaussianInt} (hz : z ≠ 0) :
    ∑ x ∈ cls χ (-z), g x = ∑ x ∈ cls χ z, g x := by
  simp only [cls, Finset.sum_filter]
  refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun x => ?_
  simp only [Equiv.neg_apply, char_neg hodd]
  by_cases hx : x = 0
  · subst hx
    have h1 : ¬ (χ 0 = -z) := by rw [MulChar.map_zero]; exact fun h => hz (neg_eq_zero.1 h.symm)
    simp [MulChar.map_zero, hz, hz.symm]
  · rw [hg x hx]
    by_cases h : χ x = -z
    · simp [h]
    · have : ¬ -χ x = z := fun h' => h (by rw [← h', neg_neg])
      simp [h, this]

lemma sum_char_mul_odd (hodd : χ (-1) = -1) (g : ZMod p → ℤ) (hg : ∀ x ≠ 0, g (-x) = -g x) :
    ∑ x, χ x * (g x : GaussianInt) =
      2 * (((∑ x ∈ cls χ 1, g x : ℤ) : GaussianInt)
        + gi * ((∑ x ∈ cls χ gi, g x : ℤ) : GaussianInt)) := by
  rw [sum_char_mul hχ, sum_cls_neg hodd g hg one_ne_zero, sum_cls_neg hodd g hg gi_ne_zero]
  push_cast; ring

omit hp hχ in
lemma re_add_gi_mul (a b : ℤ) : ((a : GaussianInt) + gi * b).re = a := by simp [gi]

omit hp hχ in
lemma im_add_gi_mul (a b : ℤ) : ((a : GaussianInt) + gi * b).im = b := by simp [gi]

/-- **Coset form of `𝒞(p)`.** `𝒞 = ∑_{C₁} s(u)s(u²) + i ∑_{C_i} s(u)s(u²)`. -/
theorem bandSum_eq (hp8 : p % 8 = 5) :
    bandSum χ = ((∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) : ℤ) : GaussianInt)
      + gi * ((∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) : ℤ) : GaussianInt) := by
  have hp2 : p ≠ 2 := by omega
  have hodd := quartic_apply_neg_one χ hχ hp8
  set w : ZMod p → ℤ := fun x => parSign x * parSign (x ^ 2) with hw
  have hwodd : ∀ x ≠ 0, w (-x) = -w x := by
    intro x hx; simp only [hw, neg_sq, parSign_neg hp2 hx, neg_mul]
  have hfull := sum_char_mul_odd hχ hodd w hwodd
  have hhalf := sum_eq_two_nsmul_half hp2 (fun x => χ x * (w x : GaussianInt))
    (by simp [MulChar.map_zero]) (fun x => by
      by_cases hx : x = 0
      · subst hx; simp
      · simp only [hwodd x hx, char_neg hodd]; push_cast; ring)
  have hB : bandSum χ = ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p),
      χ x * (w x : GaussianInt) := by
    unfold bandSum
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hw]; simp only
    rw [← neg_one_pow_band' hp2 x]; push_cast; rfl
  rw [← hB, two_nsmul, ← two_mul, hfull] at hhalf
  exact (mul_left_cancel₀ two_ne_zero hhalf).symm

/-- `f = ∑_{u ∈ H} s(u) s(u²)`. -/
theorem bandSum_re' (hp8 : p % 8 = 5) :
    (bandSum χ).re = ∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) := by
  rw [bandSum_eq hχ hp8, re_add_gi_mul]

/-- `e = ∑_{u ∈ 2H} s(u) s(u²)`. -/
theorem bandSum_im' (hp8 : p % 8 = 5) :
    (bandSum χ).im = ∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) := by
  rw [bandSum_eq hχ hp8, im_add_gi_mul]

end Quartic

end BandParity
