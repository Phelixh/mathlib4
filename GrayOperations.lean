import GrayNumber

/-!
# Gray Operations

This module provides the core axiom-free operations for `GrayNumber` in Grey System Theory.
It is designed to be compatible with mathlib conventions and serves as the foundational
operations layer for further algebraic development. All operations here are independent of
axiomatic extensions and are suitable for use in the lowest-level candidate layer.

## Main definitions
- `gray_eq` : Internal equality predicate for gray numbers
- `gray_add`, `gray_neg`, `gray_sub`, `gray_mul`, `gray_inv`, `gray_div`, `gray_smul` :
  Basic arithmetic operations for gray numbers

## Implementation notes
- All operations preserve the greyness interval `[0, 1]`.
- The design follows mathlib's naming and documentation style for clarity and maintainability.

## References
- Deng Julong, "Grey Systems: Basic Concepts, Theory and Applications" (1989)
- [Grey System Theory on Wikipedia](https://en.wikipedia.org/wiki/Grey_system_theory)
-/

/-- Internal equality predicate comparing the data carried by two gray numbers. -/
def gray_eq (g1 g2 : GrayNumber) : Prop :=
  g1.kernel = g2.kernel ∧ g1.greyness = g2.greyness

/-- Add two gray numbers. -/
noncomputable def gray_add (g1 g2 : GrayNumber) : GrayNumber :=
  { kernel := g1.kernel + g2.kernel
    greyness := max g1.greyness g2.greyness
    greyness_nonneg := by
      exact le_trans g1.greyness_nonneg (le_max_left _ _)
    greyness_le_one := by
      exact (max_le_iff.mpr ⟨g1.greyness_le_one, g2.greyness_le_one⟩) }

/-- Form the additive inverse of a gray number. -/
noncomputable def gray_neg (g : GrayNumber) : GrayNumber :=
  { kernel := -g.kernel
    greyness := g.greyness
    greyness_nonneg := g.greyness_nonneg
    greyness_le_one := g.greyness_le_one }

/-- Subtract one gray number from another. -/
noncomputable def gray_sub (g1 g2 : GrayNumber) : GrayNumber := gray_add g1 (gray_neg g2)

/-- Multiply two gray numbers. -/
noncomputable def gray_mul (g1 g2 : GrayNumber) : GrayNumber :=
  { kernel := g1.kernel * g2.kernel
    greyness := max g1.greyness g2.greyness
    greyness_nonneg := by
      exact le_trans g1.greyness_nonneg (le_max_left _ _)
    greyness_le_one := by
      exact (max_le_iff.mpr ⟨g1.greyness_le_one, g2.greyness_le_one⟩) }

/-- Form the reciprocal of a gray number with nonzero kernel. -/
noncomputable def gray_inv (g : GrayNumber) (_hg : g.kernel ≠ 0) : GrayNumber :=
  { kernel := 1 / g.kernel
    greyness := g.greyness
    greyness_nonneg := g.greyness_nonneg
    greyness_le_one := g.greyness_le_one }

/-- Divide one gray number by another gray number with nonzero kernel. -/
noncomputable def gray_div (g1 g2 : GrayNumber) (hg : g2.kernel ≠ 0) : GrayNumber :=
  gray_mul g1 (gray_inv g2 hg)

/-- Scale a gray number by a real scalar. -/
noncomputable def gray_smul (k : ℝ) (g : GrayNumber) : GrayNumber :=
  { kernel := k * g.kernel
    greyness := g.greyness
    greyness_nonneg := g.greyness_nonneg
    greyness_le_one := g.greyness_le_one }
