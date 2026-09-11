-- FILE: EvenPerfectStructure/Sequential.lean
/-
IMPORT CLASSIFICATION

- EvenPerfectStructure.Basic
  defs:
    pillar
  thms:
    pillar_pos
    pillar_even

- EvenPerfectStructure.Calibration
  defs:
    theta
-/

import EvenPerfectStructure.Calibration

/-!
# EvenPerfectStructure.Sequential

Exact transition law for the structural calibration factor.

This module studies the relative change of the calibration factor

`theta L = 8 - 20/(L + 2)`

between two dyadic levels.

For exponents `a < b`, with `a ≥ 1`, the corresponding pillars are

`Lₐ = pillar a`

and

`L_b = pillar b`.

The exact transition identity is

`theta L_b / theta Lₐ - 1
   =
  5 (L_b - Lₐ) /
    ((2Lₐ - 1)(L_b + 2))`.

This is an algebraic identity between arbitrary ordered dyadic levels.

No successor condition, no no-intruder condition, and no external
classification theorem are used.
-/

namespace EvenPerfectStructure


/-!
## 1. Positivity at nontrivial dyadic levels
-/

/--
A nontrivial dyadic pillar is at least `2`.
-/
theorem sequential_two_le_pillar
    (a : ℕ)
    (ha : 1 ≤ a) :
    2 ≤ pillar a := by
  have heven :
      Even (pillar a) :=
    pillar_even a ha

  rcases heven with
    ⟨t, ht⟩

  have hpos :
      0 < pillar a :=
    pillar_pos a

  omega


/--
For a pillar `L ≥ 2`, the affine factor `2L - 1` is strictly positive
after casting to `ℚ`.
-/
theorem sequential_odd_factor_pos
    (L : ℕ)
    (hL : 2 ≤ L) :
    (0 : ℚ) <
      2 * (L : ℚ) - 1 := by
  have hcast :
      (2 : ℚ) ≤ (L : ℚ) := by
    exact_mod_cast hL

  linarith


/--
The denominator `L + 2` appearing in `theta` is always positive.
-/
theorem sequential_theta_denominator_pos
    (L : ℕ) :
    (0 : ℚ) < (L : ℚ) + 2 := by
  positivity


/-!
## 2. Rational normal form of `theta`
-/

/--
For every natural pillar `L`,

`theta L = 4(2L - 1)/(L + 2)`.
-/
theorem theta_normal_form
    (L : ℕ) :
    theta L =
      4 * (2 * (L : ℚ) - 1) /
        ((L : ℚ) + 2) := by
  unfold theta

  have hden :
      (L : ℚ) + 2 ≠ 0 := by
    positivity

  field_simp [hden]
  ring


/--
At every nontrivial dyadic level, `theta (pillar a)` is strictly positive.
-/
theorem theta_pillar_pos
    (a : ℕ)
    (ha : 1 ≤ a) :
    (0 : ℚ) < theta (pillar a) := by
  rw [theta_normal_form]

  have hL :
      2 ≤ pillar a :=
    sequential_two_le_pillar
      a
      ha

  have hnum :
      (0 : ℚ) <
        2 * (pillar a : ℚ) - 1 :=
    sequential_odd_factor_pos
      (pillar a)
      hL

  have hden :
      (0 : ℚ) <
        (pillar a : ℚ) + 2 :=
    sequential_theta_denominator_pos
      (pillar a)

  positivity


/--
Consequently, the calibration factor at a nontrivial dyadic level is
nonzero.
-/
theorem theta_pillar_ne_zero
    (a : ℕ)
    (ha : 1 ≤ a) :
    theta (pillar a) ≠ 0 := by
  exact
    ne_of_gt
      (theta_pillar_pos a ha)


/-!
## 3. Algebraic transition law
-/

/--
The relative transition of `theta` between two positive pillar values
has a closed rational form.

This lemma is stated directly for natural pillar values and is independent
of their dyadic origin.
-/
theorem theta_transition_identity
    (A B : ℕ)
    (hA : 2 ≤ A) :
    theta B / theta A - 1 =
      5 * ((B : ℚ) - (A : ℚ)) /
        (((2 : ℚ) * (A : ℚ) - 1) *
          ((B : ℚ) + 2)) := by
  have hAden :
      (A : ℚ) + 2 ≠ 0 := by
    positivity

  have hBden :
      (B : ℚ) + 2 ≠ 0 := by
    positivity

  have hAoddPos :
      (0 : ℚ) <
        2 * (A : ℚ) - 1 :=
    sequential_odd_factor_pos
      A
      hA

  have hAodd :
      (2 : ℚ) * (A : ℚ) - 1 ≠ 0 := by
    exact ne_of_gt hAoddPos

  have hthetaA :
      theta A ≠ 0 := by
    rw [theta_normal_form]

    have hdenPos :
        (0 : ℚ) < (A : ℚ) + 2 := by
      positivity

    positivity

  rw [theta_normal_form B]
  rw [theta_normal_form A]

  field_simp [hAden, hBden, hAodd]

  ring


/-!
## 4. Advertised sequential calibration theorem
-/

/--
### Calibration transition

Let `a < b` be two dyadic levels with `a ≥ 1`.

Then the exact relative change in the calibration factor is

`theta(pillar b) / theta(pillar a) - 1`

equal to

`5 (pillar b - pillar a) /
 ((2 pillar a - 1)(pillar b + 2))`.

The statement compares arbitrary ordered dyadic levels. It does not assert
that `b` is the immediate successor of `a`.
-/
theorem calibration_transition
    (a b : ℕ)
    (ha : 1 ≤ a)
    (_hab : a < b) :
    theta (pillar b) / theta (pillar a) - 1 =
      5 *
          ((pillar b : ℚ) -
            (pillar a : ℚ)) /
        (((2 : ℚ) *
            (pillar a : ℚ) - 1) *
          ((pillar b : ℚ) + 2)) := by
  have hA :
      2 ≤ pillar a :=
    sequential_two_le_pillar
      a
      ha

  exact
    theta_transition_identity
      (pillar a)
      (pillar b)
      hA


end EvenPerfectStructure