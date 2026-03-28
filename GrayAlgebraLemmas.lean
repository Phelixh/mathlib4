import GrayOperations

/-!
# Grey Theory Algebra Lemmas

This module contains the smallest proved algebraic API around `GrayNumber` kept in the
first axiom-free candidate layer.
-/

section Equality

/-- Reflexivity of `gray_eq`. -/
lemma gray_eq_refl (g : GrayNumber) : gray_eq g g := by
  simp [gray_eq]

/-- Symmetry of `gray_eq`. -/
lemma gray_eq_symm {g1 g2 : GrayNumber} : gray_eq g1 g2 → gray_eq g2 g1 := by
  unfold gray_eq
  intro h
  rcases h with ⟨h1, h2⟩
  constructor
  · exact h1.symm
  · exact h2.symm

/-- Transitivity of `gray_eq`. -/
lemma gray_eq_trans {g1 g2 g3 : GrayNumber} : gray_eq g1 g2 → gray_eq g2 g3 → gray_eq g1 g3 := by
  unfold gray_eq
  intro h1 h2
  rcases h1 with ⟨h1_ker, h1_grey⟩
  rcases h2 with ⟨h2_ker, h2_grey⟩
  constructor
  · exact Eq.trans h1_ker h2_ker
  · exact Eq.trans h1_grey h2_grey

end Equality

section DistinguishedElements

/-- The zero gray number. -/
def zero_gray : GrayNumber :=
  { kernel := 0, greyness := 0, greyness_nonneg := le_rfl, greyness_le_one := zero_le_one }

/-- The unit gray number. -/
def one_gray : GrayNumber :=
  { kernel := 1, greyness := 0, greyness_nonneg := le_rfl, greyness_le_one := zero_le_one }

end DistinguishedElements

section Additive

/-- Commutativity of `gray_add`. -/
lemma gray_add_comm (g1 g2 : GrayNumber) : gray_add g1 g2 = gray_add g2 g1 := by
  ext <;> simp [gray_add, add_comm, max_comm]

/-- Associativity of `gray_add`. -/
lemma gray_add_assoc (g1 g2 g3 : GrayNumber) : gray_add (gray_add g1 g2) g3 = gray_add g1 (gray_add g2 g3) := by
  ext <;> simp [gray_add, add_assoc, max_assoc]

/-- `zero_gray` is a right identity for `gray_add`. -/
@[simp] lemma gray_add_zero (g : GrayNumber) : gray_add g zero_gray = g := by
  ext <;> simp [gray_add, zero_gray, g.greyness_nonneg]

/-- `zero_gray` is a left identity for `gray_add`. -/
@[simp] lemma zero_gray_add (g : GrayNumber) : gray_add zero_gray g = g := by
  rw [gray_add_comm]
  exact gray_add_zero g

/-- A gray number with zero greyness cancels with its additive inverse. -/
lemma gray_add_neg (g : GrayNumber) (h : g.greyness = 0) : gray_add g (gray_neg g) = zero_gray := by
  ext <;> simp [gray_add, gray_neg, zero_gray, h]

end Additive

section Multiplicative

/-- Commutativity of `gray_mul`. -/
lemma gray_mul_comm (g1 g2 : GrayNumber) : gray_mul g1 g2 = gray_mul g2 g1 := by
  ext <;> simp [gray_mul, mul_comm, max_comm]

/-- Associativity of `gray_mul`. -/
lemma gray_mul_assoc (g1 g2 g3 : GrayNumber) : gray_mul (gray_mul g1 g2) g3 = gray_mul g1 (gray_mul g2 g3) := by
  ext <;> simp [gray_mul, mul_assoc, max_assoc]

/-- `one_gray` is a left identity for `gray_mul`. -/
@[simp] lemma one_gray_mul (g : GrayNumber) : gray_mul one_gray g = g := by
  ext <;> simp [gray_mul, one_gray, g.greyness_nonneg]

/-- `one_gray` is a right identity for `gray_mul`. -/
@[simp] lemma gray_mul_one (g : GrayNumber) : gray_mul g one_gray = g := by
  simpa [gray_mul_comm] using one_gray_mul g

/-- Left distributivity of `gray_mul` over `gray_add`. -/
lemma gray_left_distrib (g1 g2 g3 : GrayNumber) :
  gray_mul g1 (gray_add g2 g3) = gray_add (gray_mul g1 g2) (gray_mul g1 g3) := by
  ext
  · simp [gray_mul, gray_add, mul_add]
  · simp [gray_mul, gray_add, max_left_comm, max_comm]

/-- Right distributivity of `gray_mul` over `gray_add`. -/
lemma gray_right_distrib (g1 g2 g3 : GrayNumber) :
  gray_mul (gray_add g1 g2) g3 = gray_add (gray_mul g1 g3) (gray_mul g2 g3) := by
  ext
  · simp [gray_mul, gray_add, add_mul]
  · simp [gray_mul, gray_add, max_left_comm, max_comm]

end Multiplicative

section Greyness

/-- Adding a gray number with zero greyness preserves the other greyness value. -/
lemma white_gray_add_equal_greyness (w g : GrayNumber) (hw : w.greyness = 0) :
  GrayNumber.greyness (gray_add w g) = GrayNumber.greyness g := by
  simp [gray_add, hw, g.greyness_nonneg]

/-- Multiplying by a gray number with zero greyness preserves the other greyness value. -/
lemma white_gray_mul_equal_greyness (w g : GrayNumber) (hw : w.greyness = 0) :
  GrayNumber.greyness (gray_mul w g) = GrayNumber.greyness g := by
  simp [gray_mul, hw, g.greyness_nonneg]

/-- Subtracting from a gray number with zero greyness preserves the other greyness value. -/
lemma white_gray_sub_equal_greyness (w g : GrayNumber) (hw : w.greyness = 0) :
  GrayNumber.greyness (gray_sub w g) = GrayNumber.greyness g := by
  simp [gray_sub, gray_add, gray_neg, hw, g.greyness_nonneg]

/-- Dividing a zero-greyness gray number by a nonzero gray number preserves the divisor greyness. -/
lemma white_gray_div_equal_greyness (w g : GrayNumber) (hw : w.greyness = 0) (hg : g.kernel ≠ 0) :
  GrayNumber.greyness (gray_div w g hg) = GrayNumber.greyness g := by
  simp [gray_div, gray_mul, gray_inv, hw, g.greyness_nonneg]

end Greyness
