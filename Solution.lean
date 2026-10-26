module

public import BandParity

public section

/-!
# Proved solution

Each declaration below has exactly the statement of its counterpart in `Challenge.lean` and is
proved from the development in `BandParity/`. The definitions used in the statements come from
`BandParity/Basic.lean`, `CosetSums.lean`, `FixedBase.lean`, `Defs.lean`, `Laws.lean` and
`OddSubgroup.lean`, and are compared with the copies in `Challenge.lean`.
-/

namespace BandParity

open Finset

/-! ### The matching lemma -/

/-- **The matching lemma.** For a bijection `π` from `X` onto `Y` and sign functions `σ` on `X`
and `τ` on `Y`, `∑_{x ∈ X} σ(x) τ(π x) ≡ ∑_X σ + ∑_Y τ - |X| (mod 4)`. -/
theorem matching {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π : ι → κ)
    (hπ : Set.BijOn π X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x + ∑ y ∈ Y, τ y - X.card [ZMOD 4] :=
  matching' X Y π hπ σ τ hσ hτ

/-- **Independence of the matching.** -/
theorem matching_indep {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π π' : ι → κ)
    (hπ : Set.BijOn π X Y) (hπ' : Set.BijOn π' X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x * τ (π' x) [ZMOD 4] :=
  matching_indep' X Y π π' hπ hπ' σ τ hσ hτ

/-! ### Results at a prime `p ≡ 5 (mod 8)` -/

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The pin.** For `p ≡ 5 (mod 8)` there is a unique quartic character with `χ 2 = i`. -/
theorem existsUnique_pinned (hp8 : p % 8 = 5) :
    ∃! χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 ∧ χ 2 = gi :=
  existsUnique_pinned' hp8

/-- **Parity dictionary.** `(-1)^{⌊⟨x⟩²/p⌋} = s(x) s(x²)`. -/
theorem neg_one_pow_band (hp2 : p ≠ 2) (x : ZMod p) :
    (-1 : ℤ) ^ band x = parSign x * parSign (x ^ 2) :=
  neg_one_pow_band' hp2 x

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

/-- `∑ χ(n) n = p (k + i t)`, i.e. `B_{1,χ} = k + i t`. -/
theorem T_eq (hp5 : 5 < p) : T χ = (p : GaussianInt) * ((k χ : GaussianInt) + gi * (t χ)) :=
  T_eq' hχ hp5

/-- `k` is odd. -/
theorem odd_k (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (k χ) :=
  odd_k' hχ hp8 hp5

/-- `t` is odd. -/
theorem odd_t (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (t χ) :=
  odd_t' hχ hp8 hp5

/-- **Coset form, real part.** `f = ∑_{u ∈ H} s(u) s(u²)`. -/
theorem bandSum_re (hp8 : p % 8 = 5) :
    (bandSum χ).re = ∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) :=
  bandSum_re' hχ hp8

/-- **Coset form, imaginary part.** `e = ∑_{u ∈ C_i} s(u) s(u²)`. -/
theorem bandSum_im (hp8 : p % 8 = 5) :
    (bandSum χ).im = ∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) :=
  bandSum_im' hχ hp8

/-- **The lag identity.** `∑_{u ∈ C_i} s(u) s(2u) = κ`. -/
theorem lag_identity (hp8 : p % 8 = 5) :
    ∑ u ∈ cls χ gi, parSign u * parSign (2 * u) = kappa p :=
  lag_identity' hχ hp8

/-- **Theorem A, real part.** `f ≡ Q (mod 4)`. -/
theorem bandSum_re_modEq (hp8 : p % 8 = 5) :
    (bandSum χ).re ≡ Q p [ZMOD 4] :=
  bandSum_re_modEq' hχ hp8

/-- **Theorem A, imaginary part.** `e ≡ κ (mod 4)`. -/
theorem bandSum_im_modEq (hp8 : p % 8 = 5) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ kappa p [ZMOD 4] :=
  bandSum_im_modEq' hχ hp8 hpin

/-- **Exact coset parities.** `∑_{u ∈ H} s(u) = k + 2t` and `∑_{u ∈ 2H} s(u) = t - 2k`. -/
theorem coset_parities (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    ∑ u ∈ cls χ 1, parSign u = k χ + 2 * t χ ∧ ∑ u ∈ cls χ gi, parSign u = t χ - 2 * k χ :=
  coset_parities' hχ hp8 hp5 hpin

/-- **Coordinate Congruence, first form.** `e ≡ Q + k + t (mod 4)`. -/
theorem bandSum_im_modEq_coords (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ Q p + k χ + t χ [ZMOD 4] :=
  bandSum_im_modEq_coords' hχ hp8 hp5 hpin

/-- **Coordinate Congruence.** `κ ≡ Q + k + t (mod 4)`. -/
theorem coordinate_congruence (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    kappa p ≡ Q p + k χ + t χ [ZMOD 4] :=
  coordinate_congruence' hχ hp8 hp5 hpin

end Quartic

end Prime

/-! ### Theorem B: any odd modulus -/

section OddModulus

variable {N : ℕ} [NeZero N] (hN : Odd N) (hN3 : 3 ≤ N)
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hN hN3 hH

/-- **Representative identity.** `T^{(e)}_{H,x}(N) = ∑_{u ∈ xH} s(u) s(u^e)` for even `e ≥ 2`. -/
theorem cosetBandSum_eq (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e = ∑ u ∈ coset H x, uSign u * uSign (u ^ e) :=
  cosetBandSum_eq' hN hN3 hH x he he0

/-- **Theorem B (the odd-subgroup congruence).**
`T^{(e)}_{H,x}(N) ≡ |H| - 2 α(xH) - 2 α((xH)^e) (mod 4)`. -/
theorem odd_subgroup_congruence (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e ≡
      (Nat.card H : ℤ) - 2 * oddCount (coset H x) - 2 * oddCount ((coset H x).image (· ^ e))
      [ZMOD 4] :=
  odd_subgroup_congruence' hN hN3 hH x he he0

end OddModulus

end BandParity
