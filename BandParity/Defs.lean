module

public import BandParity.CosetSums

@[expose] public section

/-!
# Definitions

Throughout `p` is a prime, `ZMod p` its residues, and `x.val` the least nonnegative residue.

* `parSign x = s(x) = (-1)^⟨x⟩`, the parity sign of the least residue.
* `band x = b(x) = ⌊⟨x⟩² / p⌋`, the band index.
* `bandSum χ = 𝒞(p) = ∑_{0 < n < p/2} χ(n) (-1)^{b(n)}`, the band-parity sum, a Gaussian
  integer `f + i e` when `χ` takes values in `ℤ[i]`.
* `Q p = (p - 1)/4` and `kappa p = κ = ∑_{0 < n < p/4} (n/p)`, the Legendre sum over the first
  quarter (which is `h(-4p)/2` by Dirichlet's formula; that identification is not used).
-/

namespace BandParity

open Finset

variable {p : ℕ} [hp : Fact p.Prime]

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

end BandParity
