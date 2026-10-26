module

public import Mathlib

public section

/-!
# The band-parity sum of a quartic character: statements

This file is the statement surface for the Palomar registry. It restates, with their exact
library definitions, the objects the results are about, and states each result with `sorry`.
`Solution.lean` proves every statement below with the same name and type, using the development
in `BandParity/`.

Throughout `p` is a prime, `ZMod p` its residues and `x.val` the least nonnegative residue;
`gi = i ∈ ℤ[i]`. For `p ≡ 5 (mod 8)` the quartic characters `χ : (ℤ/p) → ℤ[i]` are odd, and the
pin `χ(2) = i` selects one of the two.

## Definitions

* `cosetSum`, `S`, `k`, `t`, `T`: the coset sums and the coordinates `k`, `t` of
  `β = B_{1,χ} = k + i t`, where `T χ = ∑ χ(n) n = p β`.
* `parSign x = s(x) = (-1)^⟨x⟩`, `band x = ⌊⟨x⟩²/p⌋`.
* `bandSum χ = 𝒞(p) = ∑_{0 < n < p/2} χ(n) (-1)^{⌊n²/p⌋} = f + i e`.
* `Q p = (p - 1)/4`, `kappa p = κ = ∑_{0 < n < p/4} (n/p)`.
* `cls χ z = {x : χ x = z}`: `cls χ 1 = H` (fourth powers), `cls χ gi = 2H` under the pin.
* For an odd modulus `N`: `uSign`, `bandSignPow`, `coset`, `oddCount`, `cosetBandSum`.

## Results

* `existsUnique_pinned`: the pin exists and is unique.
* `T_eq`, `odd_k`, `odd_t`: `∑ χ(n) n = p (k + i t)`, and `k`, `t` are odd.
* `matching`, `matching_indep`: the matching lemma.
* `neg_one_pow_band`: `(-1)^{⌊⟨x⟩²/p⌋} = s(x) s(x²)`.
* `bandSum_re`, `bandSum_im`: `f = ∑_H s(u) s(u²)`, `e = ∑_{2H} s(u) s(u²)`.
* `lag_identity`: `∑_{2H} s(u) s(2u) = κ`.
* `bandSum_re_modEq`, `bandSum_im_modEq` (**Theorem A**): `f ≡ Q`, `e ≡ κ (mod 4)`.
* `coset_parities`: `∑_H s = k + 2t`, `∑_{2H} s = t - 2k`.
* `bandSum_im_modEq_coords`, `coordinate_congruence`: `e ≡ Q + k + t`, `κ ≡ Q + k + t (mod 4)`.
* `cosetBandSum_eq`, `odd_subgroup_congruence` (**Theorem B**): for odd `N ≥ 3`, `H ≤ (ℤ/N)ˣ`
  of odd order, `x` a unit and `e ≥ 2` even, `T = ∑_{xH} s(u) s(u^e)` and
  `T ≡ |H| - 2 α(xH) - 2 α((xH)^e) (mod 4)`.
-/

namespace BandParity

open Finset

/-! ### Definitions -/

/-- The Gaussian unit `i`. -/
def gi : GaussianInt := ⟨0, 1⟩

section Prime

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

section T

variable {R : Type*} [CommRing R]

/-- `T χ = ∑_{n mod p} χ(n) n`, with `n` its least nonnegative residue; `T χ = p · B₁,χ`. -/
def T (χ : MulChar (ZMod p) R) : R := ∑ n : ZMod p, χ n * (n.val : R)

end T

/-- The parity sign `s(x) = (-1)^⟨x⟩` of the least nonnegative residue. -/
def parSign (x : ZMod p) : ℤ := (-1) ^ x.val

/-- The band index `b(x) = ⌊⟨x⟩² / p⌋`. -/
def band (x : ZMod p) : ℕ := x.val ^ 2 / p

/-- **The band-parity sum** `𝒞(p) = ∑_{0 < n < p/2} χ(n) (-1)^{⌊n²/p⌋}`. -/
def bandSum (χ : MulChar (ZMod p) GaussianInt) : GaussianInt :=
  ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p), χ n * (-1) ^ band n

/-- `Q = (p - 1)/4`. -/
def Q (p : ℕ) : ℤ := ((p - 1) / 4 : ℕ)

/-- `κ = ∑_{0 < n < p/4} (n/p)`. -/
def kappa (p : ℕ) [Fact p.Prime] : ℤ :=
  ∑ n ∈ (range p).filter (fun n => 0 < n ∧ 4 * n < p), legendreSym p n

/-- The class `C_z = {x : χ x = z}`; `C₁ = H` is the group of fourth powers and, under the pin,
`C_i = 2H`. -/
abbrev cls (χ : MulChar (ZMod p) GaussianInt) (z : GaussianInt) : Finset (ZMod p) :=
  univ.filter (fun x => χ x = z)

end Prime

section OddModulus

variable {N : ℕ} [NeZero N]

/-- The parity sign `s(u) = (-1)^⟨u⟩` of a unit modulo `N`. -/
def uSign (u : (ZMod N)ˣ) : ℤ := (-1) ^ (u : ZMod N).val

/-- The band sign `ε(u) = (-1)^{⌊⟨u⟩^e / N⌋}`. -/
def bandSignPow (e : ℕ) (u : (ZMod N)ˣ) : ℤ := (-1) ^ ((u : ZMod N).val ^ e / N)

/-- The coset `xH` as a finite set of units. -/
def coset (H : Subgroup (ZMod N)ˣ) [DecidablePred (· ∈ H)] (x : (ZMod N)ˣ) :
    Finset (ZMod N)ˣ :=
  univ.filter (fun u => x⁻¹ * u ∈ H)

/-- `α(S)`: the number of elements of `S` whose least residue is odd. -/
def oddCount (S : Finset (ZMod N)ˣ) : ℕ :=
  (S.filter (fun u : (ZMod N)ˣ => Odd ((u : ZMod N).val))).card

/-- The band-parity sum `T^{(e)}_{H,x}(N)` of the pair of cosets `xH ∪ (-xH)` over `(0, N/2)`. -/
def cosetBandSum (H : Subgroup (ZMod N)ˣ) [DecidablePred (· ∈ H)] (x : (ZMod N)ˣ) (e : ℕ) :
    ℤ :=
  ∑ u ∈ univ.filter (fun u : (ZMod N)ˣ =>
      2 * (u : ZMod N).val < N ∧ (x⁻¹ * u ∈ H ∨ x⁻¹ * (-u) ∈ H)),
    (if x⁻¹ * u ∈ H then 1 else -1) * bandSignPow e u

end OddModulus

/-! ### The matching lemma -/

/-- **The matching lemma.** For a bijection `π` from `X` onto `Y` and sign functions `σ` on `X`
and `τ` on `Y`, `∑_{x ∈ X} σ(x) τ(π x) ≡ ∑_X σ + ∑_Y τ - |X| (mod 4)`. -/
theorem matching {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π : ι → κ)
    (hπ : Set.BijOn π X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x + ∑ y ∈ Y, τ y - X.card [ZMOD 4] := sorry

/-- **Independence of the matching.** -/
theorem matching_indep {ι κ : Type*} (X : Finset ι) (Y : Finset κ) (π π' : ι → κ)
    (hπ : Set.BijOn π X Y) (hπ' : Set.BijOn π' X Y) (σ : ι → ℤ) (τ : κ → ℤ)
    (hσ : ∀ x ∈ X, σ x = 1 ∨ σ x = -1) (hτ : ∀ y ∈ Y, τ y = 1 ∨ τ y = -1) :
    ∑ x ∈ X, σ x * τ (π x) ≡ ∑ x ∈ X, σ x * τ (π' x) [ZMOD 4] := sorry

/-! ### Results at a prime `p ≡ 5 (mod 8)` -/

section Prime

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The pin.** For `p ≡ 5 (mod 8)` there is a unique quartic character with `χ 2 = i`. -/
theorem existsUnique_pinned (hp8 : p % 8 = 5) :
    ∃! χ : MulChar (ZMod p) GaussianInt, orderOf χ = 4 ∧ χ 2 = gi := sorry

/-- **Parity dictionary.** `(-1)^{⌊⟨x⟩²/p⌋} = s(x) s(x²)`. -/
theorem neg_one_pow_band (hp2 : p ≠ 2) (x : ZMod p) :
    (-1 : ℤ) ^ band x = parSign x * parSign (x ^ 2) := sorry

section Quartic

variable {χ : MulChar (ZMod p) GaussianInt} (hχ : orderOf χ = 4)
include hχ

/-- `∑ χ(n) n = p (k + i t)`, i.e. `B_{1,χ} = k + i t`. -/
theorem T_eq (hp5 : 5 < p) : T χ = (p : GaussianInt) * ((k χ : GaussianInt) + gi * (t χ)) :=
  sorry

/-- `k` is odd. -/
theorem odd_k (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (k χ) := sorry

/-- `t` is odd. -/
theorem odd_t (hp8 : p % 8 = 5) (hp5 : 5 < p) : Odd (t χ) := sorry

/-- **Coset form, real part.** `f = ∑_{u ∈ H} s(u) s(u²)`. -/
theorem bandSum_re (hp8 : p % 8 = 5) :
    (bandSum χ).re = ∑ u ∈ cls χ 1, parSign u * parSign (u ^ 2) := sorry

/-- **Coset form, imaginary part.** `e = ∑_{u ∈ C_i} s(u) s(u²)`. -/
theorem bandSum_im (hp8 : p % 8 = 5) :
    (bandSum χ).im = ∑ u ∈ cls χ gi, parSign u * parSign (u ^ 2) := sorry

/-- **The lag identity.** `∑_{u ∈ C_i} s(u) s(2u) = κ`. -/
theorem lag_identity (hp8 : p % 8 = 5) (hp5 : 5 < p) :
    ∑ u ∈ cls χ gi, parSign u * parSign (2 * u) = kappa p := sorry

/-- **Theorem A, real part.** `f ≡ Q (mod 4)`. -/
theorem bandSum_re_modEq (hp8 : p % 8 = 5) :
    (bandSum χ).re ≡ Q p [ZMOD 4] := sorry

/-- **Theorem A, imaginary part.** `e ≡ κ (mod 4)`. -/
theorem bandSum_im_modEq (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ kappa p [ZMOD 4] := sorry

/-- **Exact coset parities.** `∑_{u ∈ H} s(u) = k + 2t` and `∑_{u ∈ 2H} s(u) = t - 2k`. -/
theorem coset_parities (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    ∑ u ∈ cls χ 1, parSign u = k χ + 2 * t χ ∧ ∑ u ∈ cls χ gi, parSign u = t χ - 2 * k χ :=
  sorry

/-- **Coordinate Congruence, first form.** `e ≡ Q + k + t (mod 4)`. -/
theorem bandSum_im_modEq_coords (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    (bandSum χ).im ≡ Q p + k χ + t χ [ZMOD 4] := sorry

/-- **Coordinate Congruence.** `κ ≡ Q + k + t (mod 4)`. -/
theorem coordinate_congruence (hp8 : p % 8 = 5) (hp5 : 5 < p) (hpin : χ 2 = gi) :
    kappa p ≡ Q p + k χ + t χ [ZMOD 4] := sorry

end Quartic

end Prime

/-! ### Theorem B: any odd modulus -/

section OddModulus

variable {N : ℕ} [NeZero N] (hN : Odd N) (hN3 : 3 ≤ N)
variable {H : Subgroup (ZMod N)ˣ} [DecidablePred (· ∈ H)] (hH : Odd (Nat.card H))
include hN hN3 hH

/-- **Representative identity.** `T^{(e)}_{H,x}(N) = ∑_{u ∈ xH} s(u) s(u^e)` for even `e ≥ 2`. -/
theorem cosetBandSum_eq (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e = ∑ u ∈ coset H x, uSign u * uSign (u ^ e) := sorry

/-- **Theorem B (the odd-subgroup congruence).**
`T^{(e)}_{H,x}(N) ≡ |H| - 2 α(xH) - 2 α((xH)^e) (mod 4)`. -/
theorem odd_subgroup_congruence (x : (ZMod N)ˣ) {e : ℕ} (he : Even e) (he0 : e ≠ 0) :
    cosetBandSum H x e ≡
      (Nat.card H : ℤ) - 2 * oddCount (coset H x) - 2 * oddCount ((coset H x).image (· ^ e))
      [ZMOD 4] := sorry

end OddModulus

end BandParity
