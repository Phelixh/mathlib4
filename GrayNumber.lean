import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic

/-!
# Grey Theory Basic Definitions

This module contains the core `GrayNumber` definition together with the
interval-based greyness construction used in the first candidate layer.
-/

/-- A gray number is represented by a kernel and a greyness value in the interval `[0, 1]`. -/
@[ext]
structure GrayNumber where
  kernel : ℝ
  greyness : ℝ
  greyness_nonneg : 0 ≤ greyness
  greyness_le_one : greyness ≤ 1

/--
Greyness of an interval-type gray number, measured as the ratio of the gray interval
length to the ambient domain length.
-/
noncomputable def greyness_interval
  (grey_left grey_right : ℝ)
  (domain_left domain_right : ℝ)
  (_h_grey_valid : grey_left < grey_right)
  (_h_domain_valid : domain_left < domain_right)
  (_h_contained : domain_left ≤ grey_left ∧ grey_right ≤ domain_right)
  : ℝ :=
  (grey_right - grey_left) / (domain_right - domain_left)

/-- The greyness of a valid interval-type gray number lies in `(0, 1]`. -/
lemma greyness_interval_range
  (gl gr dl dr : ℝ)
  (hg : gl < gr) (hd : dl < dr) (hc : dl ≤ gl ∧ gr ≤ dr) :
  0 < greyness_interval gl gr dl dr hg hd hc ∧
  greyness_interval gl gr dl dr hg hd hc ≤ 1 := by
  unfold greyness_interval
  have h_num : gr - gl > 0 := sub_pos.mpr hg
  have h_den : dr - dl > 0 := sub_pos.mpr hd
  have h_ratio : (gr - gl) / (dr - dl) ≤ 1 := by
    calc
      (gr - gl) / (dr - dl) ≤ (dr - dl) / (dr - dl) := by
        gcongr
        · exact hc.2
        · exact hc.1
      _ = 1 := by simpa using div_self (ne_of_gt h_den)
  constructor
  · exact div_pos h_num h_den
  · exact h_ratio

/-- Construct an interval-type gray number from interval and containment data. -/
noncomputable def mk_interval_gray_number
  (grey_left grey_right domain_left domain_right : ℝ)
  (h_grey : grey_left < grey_right)
  (h_domain : domain_left < domain_right)
  (h_contained : domain_left ≤ grey_left ∧ grey_right ≤ domain_right)
  : GrayNumber :=
  let kernel := (grey_left + grey_right) / 2
  let greyness := greyness_interval grey_left grey_right domain_left domain_right
                    h_grey h_domain h_contained
  { kernel := kernel
    greyness := greyness
    greyness_nonneg := le_of_lt (greyness_interval_range _ _ _ _ h_grey h_domain h_contained).1
    greyness_le_one := (greyness_interval_range _ _ _ _ h_grey h_domain h_contained).2 }
