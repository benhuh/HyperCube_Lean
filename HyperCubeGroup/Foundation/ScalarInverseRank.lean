import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

open scoped BigOperators

theorem scalar_three_geometric_le_sum {first second third : ℝ}
    (first_nonneg : 0 ≤ first) (second_nonneg : 0 ≤ second)
    (third_nonneg : 0 ≤ third) :
    3 * (first ^ (1 / 3 : ℝ) * second ^ (1 / 3 : ℝ) * third ^ (1 / 3 : ℝ)) ≤
      first + second + third := by
  have mean_bound := Real.geom_mean_le_arith_mean3_weighted
    (w₁ := (1 / 3 : ℝ)) (w₂ := (1 / 3 : ℝ)) (w₃ := (1 / 3 : ℝ))
    (by norm_num) (by norm_num) (by norm_num)
    first_nonneg second_nonneg third_nonneg (by norm_num)
  linarith

theorem scalar_three_geometric_eq_sum_iff {first second third : ℝ}
    (first_nonneg : 0 ≤ first) (second_nonneg : 0 ≤ second)
    (third_nonneg : 0 ≤ third) :
    3 * (first ^ (1 / 3 : ℝ) * second ^ (1 / 3 : ℝ) * third ^ (1 / 3 : ℝ)) =
      first + second + third ↔ first = second ∧ second = third := by
  have mean_equality := Real.geom_mean_eq_arith_mean_weighted_iff'
    (Finset.univ : Finset (Fin 3)) (fun _ => (1 / 3 : ℝ)) ![first, second, third]
    (by intro index membership; norm_num)
    (by norm_num [Fin.sum_univ_succ])
    (by
      intro index membership
      fin_cases index <;> simp_all)
  simp only [Fin.prod_univ_three, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at mean_equality
  dsimp at mean_equality
  constructor
  · intro equality
    have normalized_equality :
        first ^ (1 / 3 : ℝ) * second ^ (1 / 3 : ℝ) * third ^ (1 / 3 : ℝ) =
          1 / 3 * first + 1 / 3 * second + 1 / 3 * third := by linarith
    have all_equal := mean_equality.mp normalized_equality
    have first_equal := all_equal 0 (Finset.mem_univ _)
    have second_equal := all_equal 1 (Finset.mem_univ _)
    have third_equal := all_equal 2 (Finset.mem_univ _)
    exact ⟨first_equal.trans second_equal.symm, second_equal.trans third_equal.symm⟩
  · rintro ⟨rfl, rfl⟩
    have normalized_equality := mean_equality.mpr (by
      intro index membership
      fin_cases index <;> simp <;> ring)
    simp [Matrix.vecHead, Matrix.vecTail] at normalized_equality
    simp only [mul_assoc] at normalized_equality ⊢
    linarith

theorem scalar_inverse_rank_geometric_identity {α β γ t κ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ht : 0 < t) (hκ : 0 < κ) (hproduct : α * β * γ = κ * t ^ 2) :
    t ^ 2 * ((1 / α) ^ (1 / 3 : ℝ) * (1 / β) ^ (1 / 3 : ℝ) *
      (1 / γ) ^ (1 / 3 : ℝ)) = κ ^ (-1 / 3 : ℝ) * t ^ (4 / 3 : ℝ) := by
  have hroots :
      (1 / α) ^ (1 / 3 : ℝ) * (1 / β) ^ (1 / 3 : ℝ) *
        (1 / γ) ^ (1 / 3 : ℝ) = (κ * t ^ 2) ^ (-1 / 3 : ℝ) := by
    simp only [one_div]
    rw [← Real.mul_rpow (inv_nonneg.mpr hα.le) (inv_nonneg.mpr hβ.le),
      ← Real.mul_rpow (mul_nonneg (inv_nonneg.mpr hα.le) (inv_nonneg.mpr hβ.le))
        (inv_nonneg.mpr hγ.le)]
    rw [← mul_inv, ← mul_inv, Real.inv_rpow (by positivity)]
    rw [hproduct, ← Real.rpow_neg (by positivity)]
    congr 1
    norm_num
  have ht_power : (t ^ 2) ^ (-1 / 3 : ℝ) = t ^ (-2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    congr 1
    norm_num
  rw [hroots, Real.mul_rpow hκ.le (sq_nonneg t), ht_power]
  calc
    t ^ 2 * (κ ^ (-1 / 3 : ℝ) * t ^ (-2 / 3 : ℝ)) =
        κ ^ (-1 / 3 : ℝ) * (t ^ (2 : ℝ) * t ^ (-2 / 3 : ℝ)) := by
      rw [show t ^ (2 : ℝ) = t ^ (2 : ℕ) from Real.rpow_natCast t 2]
      ring
    _ = κ ^ (-1 / 3 : ℝ) * t ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_add ht]
      norm_num

theorem scalar_inverse_rank_bound {α β γ t κ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ht : 0 < t) (hκ : 0 < κ) (hproduct : α * β * γ = κ * t ^ 2) :
    3 * κ ^ (-1 / 3 : ℝ) * t ^ (4 / 3 : ℝ) ≤
      t ^ 2 * (1 / α + 1 / β + 1 / γ) := by
  have mean_bound := scalar_three_geometric_le_sum
    (first := 1 / α) (second := 1 / β) (third := 1 / γ)
    (by positivity) (by positivity) (by positivity)
  have scaled_bound := mul_le_mul_of_nonneg_left mean_bound (sq_nonneg t)
  have factoring := scalar_inverse_rank_geometric_identity hα hβ hγ ht hκ hproduct
  calc
    3 * κ ^ (-1 / 3 : ℝ) * t ^ (4 / 3 : ℝ) =
        t ^ 2 * (3 * ((1 / α) ^ (1 / 3 : ℝ) * (1 / β) ^ (1 / 3 : ℝ) *
          (1 / γ) ^ (1 / 3 : ℝ))) := by rw [mul_assoc, ← factoring]; ring
    _ ≤ t ^ 2 * (1 / α + 1 / β + 1 / γ) := scaled_bound

theorem scalar_inverse_rank_eq_iff {α β γ t κ : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ)
    (ht : 0 < t) (hκ : 0 < κ) (hproduct : α * β * γ = κ * t ^ 2) :
    3 * κ ^ (-1 / 3 : ℝ) * t ^ (4 / 3 : ℝ) =
      t ^ 2 * (1 / α + 1 / β + 1 / γ) ↔ α = β ∧ β = γ := by
  have factoring := scalar_inverse_rank_geometric_identity hα hβ hγ ht hκ hproduct
  have mean_equality := scalar_three_geometric_eq_sum_iff
    (first := 1 / α) (second := 1 / β) (third := 1 / γ)
    (by positivity) (by positivity) (by positivity)
  have scaled_identity :
      t ^ 2 * (3 * ((1 / α) ^ (1 / 3 : ℝ) * (1 / β) ^ (1 / 3 : ℝ) *
        (1 / γ) ^ (1 / 3 : ℝ))) =
        3 * κ ^ (-1 / 3 : ℝ) * t ^ (4 / 3 : ℝ) := by
    calc
      _ = 3 * (t ^ 2 * ((1 / α) ^ (1 / 3 : ℝ) * (1 / β) ^ (1 / 3 : ℝ) *
          (1 / γ) ^ (1 / 3 : ℝ))) := by ring
      _ = _ := by rw [factoring]; ring
  rw [← scaled_identity]
  constructor
  · intro equality
    have reciprocal_equalities := mean_equality.mp
      (mul_left_cancel₀ (ne_of_gt (sq_pos_of_pos ht)) equality)
    exact ⟨inv_inj.mp (by simpa only [one_div] using reciprocal_equalities.1),
      inv_inj.mp (by simpa only [one_div] using reciprocal_equalities.2)⟩
  · rintro ⟨first_equal, second_equal⟩
    apply congrArg (fun value : ℝ => t ^ 2 * value)
    exact mean_equality.mpr ⟨congrArg (fun value : ℝ => 1 / value) first_equal,
      congrArg (fun value : ℝ => 1 / value) second_equal⟩