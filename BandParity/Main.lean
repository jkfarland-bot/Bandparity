module

public import BandParity.Laws

@[expose] public section

/-!
# Theorem A and the Coordinate Congruence

For a prime `p ≡ 5 (mod 8)`, `p > 5`, and the quartic character `χ` with `χ(2) = i`:

* `lag_identity`: `∑_{u ∈ 2H} s(u) s(2u) = κ`, exactly;
* `bandSum_re_modEq`, `bandSum_im_modEq` (**Theorem A**): `f ≡ Q` and `e ≡ κ (mod 4)`;
* `coset_parities`: `∑_H s = k + 2t` and `∑_{2H} s = t - 2k`;
* `bandSum_im_modEq_coords`, `coordinate_congruence`: `e ≡ Q + k + t` and
  `κ ≡ Q + k + t (mod 4)`.

The real law needs no pin; the imaginary law, the coset parities and the congruences use
`χ(2) = i`.
-/

namespace BandParity

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

omit hp in
/-- An injective map between finite sets with `|t| ≤ |s|` is a bijection onto `t`. -/
lemma bijOn_of_injOn_card {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    {f : α → β} (hm : Set.MapsTo f s t) (hi : Set.InjOn f s) (hc : t.card ≤ s.card) :
    Set.BijOn f s t := by
  refine ⟨hm, hi, fun y hy => ?_⟩
  have hsub : s.image f ⊆ t := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy; exact hm hx
  have heq : s.image f = t :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hi]; exact hc)
  have hy' : y ∈ s.image f := by rw [heq]; exact hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy'
  exact ⟨x, hx, rfl⟩

/-! ### The Legendre side -/

lemma ringChar_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

lemma quadraticChar_neg (hp4 : p % 4 = 1) (x : ZMod p) :
    quadraticChar (ZMod p) (-x) = quadraticChar (ZMod p) x := by
  have hp2 : p ≠ 2 := by omega
  rw [show -x = -1 * x by ring, map_mul, quadraticChar_neg_one (ringChar_ne_two hp2), ZMod.card,
    ZMod.χ₄_nat_one_mod_four hp4, one_mul]

lemma quadraticChar_eq_legendreSym (x : ZMod p) :
    quadraticChar (ZMod p) x = legendreSym p (x.val : ℤ) := by
  unfold legendreSym; simp

/-- `∑_{0 < v < p/2} (v/p) = 0` for `p ≡ 1 (mod 4)`. -/
lemma sum_legendre_half (hp4 : p % 4 = 1) :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p), legendreSym p (v : ℤ) = 0 := by
  have hp2 : p ≠ 2 := by omega
  have h := sum_eq_two_nsmul_half hp2 (fun x => quadraticChar (ZMod p) x)
    (quadraticChar_zero) (quadraticChar_neg hp4)
  rw [quadraticChar_sum_zero (ringChar_ne_two hp2),
    sum_half_eq_sum_half' _ quadraticChar_zero] at h
  simp only [quadraticChar_eq_legendreSym] at h
  rw [sum_filter_val (fun v => 0 < v ∧ 2 * v < p) (fun v => legendreSym p (v : ℤ)),
    two_nsmul] at h
  omega

/-- `∑_{0 < v < p/2, v even} (v/p) = (2/p) κ`. -/
lemma sum_legendre_even_half :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p ∧ v % 2 = 0), legendreSym p (v : ℤ) =
      legendreSym p 2 * kappa p := by
  unfold kappa
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' (fun v => v / 2) (fun m => 2 * m) ?_ ?_ ?_ ?_ ?_
  · intro v hv; simp only [mem_filter, mem_range] at hv ⊢; omega
  · intro m hm; simp only [mem_filter, mem_range] at hm ⊢; omega
  · intro v hv; simp only [mem_filter, mem_range] at hv; omega
  · intro m _; simp
  · intro v hv
    simp only [mem_filter, mem_range] at hv
    rw [← legendreSym.mul]; congr 1; push_cast; omega

/-- `∑_{0 < v < p/2} (-1)^v (v/p) = -2κ` for `p ≡ 5 (mod 8)`. -/
lemma sum_alt_legendre (hp8 : p % 8 = 5) :
    ∑ v ∈ (range p).filter (fun v => 0 < v ∧ 2 * v < p), (-1 : ℤ) ^ v * legendreSym p (v : ℤ) =
      -2 * kappa p := by
  have hp2 : p ≠ 2 := by omega
  have h2 : legendreSym p 2 = -1 := by
    rw [legendreSym.at_two hp2, ZMod.χ₈_nat_mod_eight, hp8]; decide
  have hsplit : ∀ v : ℕ, (-1 : ℤ) ^ v * legendreSym p (v : ℤ) =
      2 * (if v % 2 = 0 then legendreSym p (v : ℤ) else 0) - legendreSym p (v : ℤ) := by
    intro v
    rcases Nat.even_or_odd v with he | ho
    · rw [he.neg_one_pow]
      split_ifs with hh
      · ring
      · exact absurd (Nat.even_iff.1 he) hh
    · have : v % 2 ≠ 0 := by rw [Nat.odd_iff] at ho; omega
      rw [ho.neg_one_pow]
      split_ifs with hh
      · exact absurd hh this
      · ring
  rw [Finset.sum_congr rfl (fun v _ => hsplit v), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.sum_filter, Finset.filter_filter, sum_legendre_half (by omega)]
  have : (range p).filter (fun v => (0 < v ∧ 2 * v < p) ∧ v % 2 = 0) =
      (range p).filter (fun v => 0 < v ∧ 2 * v < p ∧ v % 2 = 0) := by
    ext v; simp only [mem_filter]; tauto
  rw [this, sum_legendre_even_half, h2]; ring

/-! ### Squaring and doubling between classes -/

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

lemma card_cls {z : GaussianInt} (hz : z = 1 ∨ z = gi ∨ z = -1 ∨ z = -gi) :
    (cls χ z).card = (p - 1) / 4 := by
  have h := card_class hχ z hz
  change 4 * (cls χ z).card = p - 1 at h
  omega

omit hχ in
lemma mem_cls {z : GaussianInt} {x : ZMod p} : x ∈ (cls χ z : Set (ZMod p)) ↔ χ x = z := by
  simp

lemma sq_injOn (hp8 : p % 8 = 5) {z : GaussianInt} (hz : z ≠ 0) :
    Set.InjOn (fun x : ZMod p => x ^ 2) (cls χ z : Set (ZMod p)) := by
  have hodd := quartic_apply_neg_one χ hχ hp8
  intro u hu v hv h
  rw [mem_cls] at hu hv
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h with h | h
  · exact h
  · exfalso
    rw [h, char_neg hodd, hv] at hu
    exact hz (self_eq_neg.1 hu.symm)

omit hχ in
lemma sq_mapsTo_one : Set.MapsTo (fun x : ZMod p => x ^ 2) (cls χ 1 : Set (ZMod p))
    (cls χ 1 : Set (ZMod p)) := by
  intro u hu; rw [mem_cls] at hu ⊢; simp [map_pow, hu]

omit hχ in
lemma sq_mapsTo_gi : Set.MapsTo (fun x : ZMod p => x ^ 2) (cls χ gi : Set (ZMod p))
    (cls χ (-1) : Set (ZMod p)) := by
  intro u hu; rw [mem_cls] at hu ⊢; simp only [map_pow, hu, gi_sq]

omit hχ in
lemma two_mul_mapsTo_gi (hpin : χ 2 = gi) :
    Set.MapsTo (fun x : ZMod p => 2 * x) (cls χ gi : Set (ZMod p))
      (cls χ (-1) : Set (ZMod p)) := by
  intro u hu; rw [mem_cls] at hu ⊢; simp only [map_mul, hu, hpin, ← sq, gi_sq]

lemma sq_bijOn_one (hp8 : p % 8 = 5) :
    Set.BijOn (fun x : ZMod p => x ^ 2) (cls χ 1 : Set (ZMod p)) (cls χ 1 : Set (ZMod p)) :=
  bijOn_of_injOn_card (sq_mapsTo_one) (sq_injOn hχ hp8 one_ne_zero) le_rfl

lemma sq_bijOn_gi (hp8 : p % 8 = 5) :
    Set.BijOn (fun x : ZMod p => x ^ 2) (cls χ gi : Set (ZMod p))
      (cls χ (-1) : Set (ZMod p)) :=
  bijOn_of_injOn_card (sq_mapsTo_gi) (sq_injOn hχ hp8 gi_ne_zero)
    (by rw [card_cls hχ (by simp), card_cls hχ (by simp)])

lemma two_mul_bijOn_gi (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    Set.BijOn (fun x : ZMod p => 2 * x) (cls χ gi : Set (ZMod p))
      (cls χ (-1) : Set (ZMod p)) :=
  bijOn_of_injOn_card (two_mul_mapsTo_gi hpin)
    (fun _ _ _ _ h => mul_left_cancel₀ (two_ne_zero' (by omega)) h)
    (by rw [card_cls hχ (by simp), card_cls hχ (by simp)])

/-! ### Squares and the Legendre symbol -/

lemma isSquare_iff_char {x : ZMod p} (hx : x ≠ 0) : IsSquare x ↔ (χ x = 1 ∨ χ x = -1) := by
  constructor
  · rintro ⟨m, rfl⟩
    have hm : m ≠ 0 := by rintro rfl; simp at hx
    rw [map_mul]
    rcases quartic_values χ hχ hm with h | h | h | h <;> rw [h]
    · left; ring
    · right; rw [← sq, gi_sq]
    · left; ring
    · right; rw [neg_mul_neg, ← sq, gi_sq]
  · intro h
    obtain ⟨g, -, hg⟩ := exists_generator (p := p)
    obtain ⟨j, hj⟩ := hg (Units.mk0 x hx)
    have hxj : x = (g : ZMod p) ^ j := by
      have := congrArg (fun u : (ZMod p)ˣ => (u : ZMod p)) hj
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0] at this
      exact this.symm
    rcases Nat.even_or_odd j with ⟨i, rfl⟩ | hoddj
    · exact ⟨(g : ZMod p) ^ i, by rw [hxj, pow_add]⟩
    · exfalso
      have h' := pm_gi_pow_odd (quartic_apply_generator χ hχ hg) hoddj
      rw [← map_pow, ← hxj] at h'
      rcases h with h | h <;> rcases h' with h' | h' <;> rw [h] at h' <;> revert h' <;> decide

lemma quadraticChar_of_char_one {x : ZMod p} (hx : x ≠ 0) (h : χ x = 1 ∨ χ x = -1) :
    quadraticChar (ZMod p) x = 1 :=
  (quadraticChar_one_iff_isSquare hx).2 ((isSquare_iff_char hχ hx).2 h)

lemma quadraticChar_of_char_gi {x : ZMod p} (hx : x ≠ 0) (h : χ x = gi ∨ χ x = -gi) :
    quadraticChar (ZMod p) x = -1 := by
  rw [quadraticChar_neg_one_iff_not_isSquare, isSquare_iff_char hχ hx]
  rintro (h' | h') <;> rcases h with h | h <;> rw [h] at h' <;> revert h' <;> decide

/-! ### The lag identity -/

/-- **The lag identity.** Matching `2H` with `4H = -H` by multiplication by `2` has correlation
exactly `κ`: `∑_{u ∈ 2H} s(u) s(2u) = κ`. -/
theorem lag_identity' (hp8 : p % 8 = 5) (hp5 : 5 < p) :
    ∑ u ∈ cls χ gi, parSign u * parSign (2 * u) = kappa p := by
  have hp2 : p ≠ 2 := by omega
  have hp4 : p % 4 = 1 := by omega
  have hodd := quartic_apply_neg_one χ hχ hp8
  have h2 := two_ne_zero' (p := p) hp2
  set F : ZMod p → ℤ := fun x => parSign x * parSign (2 * x) with hF
  have hFeven : ∀ x ≠ 0, F (-x) = F x := by
    intro x hx
    have h2x : 2 * x ≠ 0 := mul_ne_zero h2 hx
    show parSign (-x) * parSign (2 * -x) = parSign x * parSign (2 * x)
    rw [show (2 : ZMod p) * -x = -(2 * x) by ring, parSign_neg hp2 hx, parSign_neg hp2 h2x]
    ring
  have hneg := sum_cls_neg_even hodd F hFeven gi_ne_zero
  -- pointwise: the nonresidue indicator is `(1 - (x/p))/2`
  have hpt : ∀ x : ZMod p,
      2 * ((if χ x = gi then F x else 0) + (if χ x = -gi then F x else 0)) =
        (if x = 0 then 0 else F x) - F x * quadraticChar (ZMod p) x := by
    intro x
    by_cases hx : x = 0
    · subst hx; simp [MulChar.map_zero, zero_ne_gi, gi_ne_zero]
    · rcases quartic_values χ hχ hx with h | h | h | h
      · rw [quadraticChar_of_char_one hχ hx (Or.inl h)]; simp [hx, h, distinct]
      · rw [quadraticChar_of_char_gi hχ hx (Or.inl h)]; simp [hx, h, distinct]; ring
      · rw [quadraticChar_of_char_one hχ hx (Or.inr h)]; simp [hx, h, distinct]
      · rw [quadraticChar_of_char_gi hχ hx (Or.inr h)]; simp [hx, h, distinct]; ring
  have hsum : 2 * (∑ x ∈ cls χ gi, F x + ∑ x ∈ cls χ (-gi), F x) =
      ∑ x : ZMod p, (if x = 0 then 0 else F x) - ∑ x : ZMod p, F x * quadraticChar (ZMod p) x := by
    simp only [cls, Finset.sum_filter, ← Finset.sum_add_distrib, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun x _ => hpt x
  -- the unweighted sum vanishes
  have hA : ∑ x : ZMod p, (if x = 0 then 0 else F x) = 0 := by
    have h := sum_eq_two_nsmul_half hp2 (fun x => if x = 0 then 0 else F x) (by simp)
      (fun x => by
        by_cases hx : x = 0
        · subst hx; simp
        · simp [hx, hFeven x hx])
    rw [h, sum_half_eq_sum_half' _ (by simp)]
    have : ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p),
        (if x = 0 then 0 else F x) =
        ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p), (-1 : ℤ) ^ x.val := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [mem_filter, mem_univ, true_and] at hx
      have hx0 : x ≠ 0 := fun h => by rw [h, ZMod.val_zero] at hx; omega
      simp only [hx0, ↓reduceIte]
      show parSign x * parSign (2 * x) = (-1) ^ x.val
      rw [parSign_two_mul_of_lt hp2 hx.2, mul_one]; rfl
    rw [this, sum_filter_val (fun v => 0 < v ∧ 2 * v < p) (fun v => (-1 : ℤ) ^ v),
      sum_alt_half hp4, smul_zero]
  -- the Legendre-weighted sum is `-4κ`
  have hB : ∑ x : ZMod p, F x * quadraticChar (ZMod p) x = -4 * kappa p := by
    have h := sum_eq_two_nsmul_half hp2 (fun x => F x * quadraticChar (ZMod p) x)
      (by simp)
      (fun x => by
        by_cases hx : x = 0
        · subst hx; simp
        · simp only [hFeven x hx, quadraticChar_neg hp4])
    rw [h, sum_half_eq_sum_half' _ (by simp)]
    have : ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p),
        F x * quadraticChar (ZMod p) x =
        ∑ x ∈ univ.filter (fun x : ZMod p => 0 < x.val ∧ 2 * x.val < p),
          (-1 : ℤ) ^ x.val * legendreSym p (x.val : ℤ) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [mem_filter, mem_univ, true_and] at hx
      show parSign x * parSign (2 * x) * quadraticChar (ZMod p) x = _
      rw [parSign_two_mul_of_lt hp2 hx.2, mul_one, quadraticChar_eq_legendreSym]; rfl
    rw [this, sum_filter_val (fun v => 0 < v ∧ 2 * v < p)
      (fun v => (-1 : ℤ) ^ v * legendreSym p (v : ℤ)), sum_alt_legendre hp8, two_nsmul]
    ring
  rw [hA, hB, hneg] at hsum
  linarith

/-! ### Theorem A -/

/-- **Theorem A, real part.** `f ≡ Q (mod 4)`. -/
theorem bandSum_re_modEq' (hp8 : p % 8 = 5) :
    (bandSum χ).re ≡ Q p [ZMOD 4] := by
  have hc := card_cls hχ (z := 1) (Or.inl rfl)
  have hm := matching' (cls χ 1) (cls χ 1) _ (sq_bijOn_one hχ hp8) parSign parSign
    (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)
  have hself := sum_sign_mul_modEq (cls χ 1) parSign parSign
    (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)
  simp only [parSign_mul_self, sum_const, nsmul_eq_mul, mul_one] at hself
  rw [bandSum_re' hχ hp8, Q, ← hc]
  exact hm.trans hself.symm

/-- **Theorem A, imaginary part.** `e ≡ κ (mod 4)`. -/
theorem bandSum_im_modEq' (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ kappa p [ZMOD 4] := by
  rw [bandSum_im' hχ hp8, ← lag_identity' hχ hp8 hp5]
  exact matching_indep' (cls χ gi) (cls χ (-1)) _ _ (sq_bijOn_gi hχ hp8)
    (two_mul_bijOn_gi hχ hp8 hp5 hpin) parSign parSign
    (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)

/-! ### Coset parities and the Coordinate Congruence -/

/-- **Exact coset parities.** `∑_{u ∈ H} s(u) = k + 2t` and `∑_{u ∈ 2H} s(u) = t - 2k`. -/
theorem coset_parities' (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    ∑ u ∈ cls χ 1, parSign u = k χ + 2 * t χ ∧ ∑ u ∈ cls χ gi, parSign u = t χ - 2 * k χ := by
  have hp2 : p ≠ 2 := by omega
  have hodd := quartic_apply_neg_one χ hχ hp8
  have h2 := two_ne_zero' (p := p) hp2
  have ha := sum_char_mul_odd hχ hodd parSign (fun x hx => parSign_neg hp2 hx)
  have hb : ∑ x : ZMod p, χ 2 * (χ x * (parSign (2 * x) : GaussianInt)) =
      ∑ x : ZMod p, χ x * (parSign x : GaussianInt) :=
    Fintype.sum_equiv (Equiv.mulLeft₀ (2 : ZMod p) h2) _ _ fun x => by
      simp only [Equiv.mulLeft₀_apply, map_mul]; ring
  have hc := sum_eq_two_nsmul_half hp2 (fun x => χ x * (parSign (2 * x) : GaussianInt))
    (by simp [MulChar.map_zero]) (fun x => by
      by_cases hx : x = 0
      · subst hx; simp
      · simp only [char_neg hodd, mul_neg, parSign_neg hp2 (mul_ne_zero h2 hx)]; push_cast
        ring)
  have hc' : ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p),
      χ x * (parSign (2 * x) : GaussianInt) =
      ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), χ x := by
    refine Finset.sum_congr rfl fun x hx => ?_
    simp only [mem_filter, mem_univ, true_and] at hx
    rw [parSign_two_mul_of_lt hp2 hx]; simp
  have hd := half_sum hp2 χ hodd
  rw [T_eq' hχ hp5, hpin] at hd
  have hp0 : (p : GaussianInt) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
  set half := ∑ x ∈ univ.filter (fun x : ZMod p => 2 * x.val < p), χ x with hhalf
  have hd' : gi * half = (1 - 2 * gi) * ((k χ : GaussianInt) + gi * t χ) := by
    apply mul_left_cancel₀ hp0; linear_combination hd
  rw [← Finset.mul_sum, hc, hc', two_nsmul, hpin] at hb
  rw [ha] at hb
  set A := ∑ u ∈ cls χ 1, parSign u with hA
  set B := ∑ u ∈ cls χ gi, parSign u with hB
  have key : (A : GaussianInt) + gi * B =
      ((k χ + 2 * t χ : ℤ) : GaussianInt) + gi * ((t χ - 2 * k χ : ℤ) : GaussianInt) := by
    have h2' : (2 : GaussianInt) ≠ 0 := two_ne_zero
    apply mul_left_cancel₀ h2'
    have e1 : ((k χ + 2 * t χ : ℤ) : GaussianInt) = (k χ : GaussianInt) + 2 * t χ := by push_cast; ring
    have e2 : ((t χ - 2 * k χ : ℤ) : GaussianInt) = (t χ : GaussianInt) - 2 * k χ := by push_cast; ring
    rw [e1, e2]
    linear_combination -hb + 2 * hd' + (-4 * (t χ : GaussianInt)) * gi_sq
  have kr := congrArg Zsqrtd.re key
  have ki := congrArg Zsqrtd.im key
  rw [re_add_gi_mul, re_add_gi_mul] at kr
  rw [im_add_gi_mul, im_add_gi_mul] at ki
  exact ⟨kr, ki⟩

omit hp hχ in
lemma odd_Q (hp8 : p % 8 = 5) : Odd (Q p) := by
  unfold Q
  rw [Int.odd_coe_nat]
  exact Nat.odd_iff.2 (by omega)

/-- **Coordinate Congruence, first form.** `e ≡ Q + k + t (mod 4)`. -/
theorem bandSum_im_modEq_coords' (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ Q p + k χ + t χ [ZMOD 4] := by
  have hp2 : p ≠ 2 := by omega
  have hodd := quartic_apply_neg_one χ hχ hp8
  have hc := card_cls hχ (z := gi) (by simp)
  have hm := matching' (cls χ gi) (cls χ (-1)) _ (sq_bijOn_gi hχ hp8) parSign parSign
    (fun x _ => parSign_eq x) (fun x _ => parSign_eq x)
  rw [sum_cls_neg hodd parSign (fun x hx => parSign_neg hp2 hx) one_ne_zero] at hm
  obtain ⟨h1, h2⟩ := coset_parities' hχ hp8 hp5 hpin
  rw [h1, h2, hc] at hm
  rw [bandSum_im' hχ hp8]
  refine hm.trans ?_
  obtain ⟨a, ha⟩ := odd_Q (p := p) hp8
  obtain ⟨b, hb⟩ := odd_t' hχ hp8 hp5
  have hQ : (((p - 1) / 4 : ℕ) : ℤ) = Q p := rfl
  rw [hQ]
  exact Int.modEq_iff_dvd.2 ⟨a + b + 1 + k χ, by rw [ha, hb]; ring⟩

/-- **Coordinate Congruence.** `κ ≡ Q + k + t (mod 4)`. -/
theorem coordinate_congruence' (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    kappa p ≡ Q p + k χ + t χ [ZMOD 4] :=
  (bandSum_im_modEq' hχ hp8 hp5 hpin).symm.trans (bandSum_im_modEq_coords' hχ hp8 hp5 hpin)

end Quartic

end BandParity
