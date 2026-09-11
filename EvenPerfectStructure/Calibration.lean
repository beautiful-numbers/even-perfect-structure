-- FILE: EvenPerfectStructure/Calibration.lean
/-
IMPORT CLASSIFICATION

- EvenPerfectStructure.Basic
  defs:
    pillar
    oddPillar
    candidate
    greatestProperDivisor
  thms:
    one_le_pillar
    candidate_eq_profile
-/

import EvenPerfectStructure.Basic

/-!
# EvenPerfectStructure.Calibration

Structural calibration of the greatest proper divisor.

The calibration-specific quantities are defined in this module:

`gauge L = L(L + 2) / 8`

and

`theta L = 8 - 20/(L + 2)`.

They do not belong to `Basic.lean`, because they are specific to the
calibration layer.

Their product simplifies to

`L(2L - 1)/2`.

This gives the structural calibration scale associated with a pillar `L`.

The general bound proved below uses the stronger elementary inequality

`greatestProperDivisor N ≤ N/2`.

Thus the advertised calibration bound follows from

`N = kL`

and

`k ≤ 2L - 1`.

The coprimality and compositeness assumptions are retained in the public
statement because they describe the structural class studied by the paper,
although the formal estimate itself is stronger and does not need them.

For the recovered profile

`candidate a = pillar a * oddPillar (pillar a)`,

the calibration bound is attained exactly.

No classification theorem for even perfect numbers is used in this module.
-/

namespace EvenPerfectStructure


/-!
## 1. Calibration definitions
-/

/--
Structural gauge associated with a pillar `L`.

Mathematically:

`R(L) = L(L + 2)/8`.
-/
def gauge (L : ℕ) : ℚ :=
  (L : ℚ) * ((L : ℚ) + 2) / 8


/--
Calibration factor associated with a pillar `L`.

Mathematically:

`Θ(L) = 8 - 20/(L + 2)`.
-/
def theta (L : ℕ) : ℚ :=
  8 - 20 / ((L : ℚ) + 2)


/-!
## 2. Algebraic calibration identity
-/

/--
The product of the calibration factor and the gauge is

`L(2L - 1)/2`.
-/
theorem theta_mul_gauge
    (L : ℕ) :
    theta L * gauge L =
      (L : ℚ) *
        (2 * (L : ℚ) - 1) / 2 := by
  unfold theta gauge

  have hden :
      (L : ℚ) + 2 ≠ 0 := by
    positivity

  field_simp [hden]
  ring


/-!
## 3. Generic bound for the greatest proper divisor
-/

/--
For every `N ≥ 2`, twice the greatest proper divisor is at most `N`.
-/
theorem two_mul_greatestProperDivisor_le
    (N : ℕ)
    (hN : 2 ≤ N) :
    2 * greatestProperDivisor N ≤ N := by
  have hNne :
      N ≠ 1 := by
    omega

  have hprime :
      Nat.Prime N.minFac :=
    Nat.minFac_prime hNne

  have hmin2 :
      2 ≤ N.minFac :=
    hprime.two_le

  have hleft :
      2 * (N / N.minFac) ≤
        N.minFac * (N / N.minFac) := by
    exact
      Nat.mul_le_mul_right
        (N / N.minFac)
        hmin2

  have hright :
      N.minFac * (N / N.minFac) ≤ N := by
    have h :
        N / N.minFac * N.minFac ≤ N :=
      Nat.div_mul_le_self N N.minFac

    simpa [Nat.mul_comm] using h

  unfold greatestProperDivisor

  exact le_trans hleft hright


/-!
## 4. Public calibration bound
-/

/--
### Calibration bound

Let

`N = kL`

with `N ≥ 2` and

`k ≤ 2L - 1`.

Then

`greatestProperDivisor N ≤ theta L * gauge L`.

The public hypotheses retain coprimality and compositeness because they are
part of the structural class in which the paper states the bound.

The formal proof establishes the result through the stronger generic estimate

`greatestProperDivisor N ≤ N/2`.
-/
theorem calibration_bound
    (N k L : ℕ)
    (hN : N = k * L)
    (hNpos : 2 ≤ N)
    (_hcoprime : Nat.Coprime k L)
    (_hcomposite : ¬ Nat.Prime N)
    (hk : k ≤ 2 * L - 1) :
    (greatestProperDivisor N : ℚ) ≤
      theta L * gauge L := by
  have hLpos :
      0 < L := by
    by_contra h

    have hLzero :
        L = 0 := by
      omega

    rw [hLzero] at hN
    simp at hN
    omega

  have hgdNat :
      2 * greatestProperDivisor N ≤ N :=
    two_mul_greatestProperDivisor_le
      N
      hNpos

  have hgdQ :
      (2 : ℚ) *
          (greatestProperDivisor N : ℚ) ≤
        (N : ℚ) := by
    exact_mod_cast hgdNat

  have hoddCast :
      ((2 * L - 1 : ℕ) : ℚ) =
        2 * (L : ℚ) - 1 := by
    have hle :
        1 ≤ 2 * L := by
      omega

    rw [Nat.cast_sub hle]
    norm_num

  have hkQ :
      (k : ℚ) ≤
        2 * (L : ℚ) - 1 := by
    have h :
        (k : ℚ) ≤
          ((2 * L - 1 : ℕ) : ℚ) := by
      exact_mod_cast hk

    rw [hoddCast] at h

    exact h

  have hNQ :
      (N : ℚ) =
        (k : ℚ) * (L : ℚ) := by
    exact_mod_cast hN

  have hLQ :
      (0 : ℚ) ≤ (L : ℚ) := by
    positivity

  have hNupper :
      (N : ℚ) ≤
        (2 * (L : ℚ) - 1) *
          (L : ℚ) := by
    rw [hNQ]

    exact
      mul_le_mul_of_nonneg_right
        hkQ
        hLQ

  rw [theta_mul_gauge]

  nlinarith


/-!
## 5. The structural profile is even
-/

/--
At every nontrivial dyadic level, `2` divides the recovered structural
candidate.
-/
theorem two_dvd_candidate
    (a : ℕ)
    (ha : 1 ≤ a) :
    2 ∣ candidate a := by
  have hpow :
      2 ^ 1 ∣ 2 ^ a :=
    pow_dvd_pow 2 ha

  have hpillar :
      2 ∣ pillar a := by
    simpa [pillar] using hpow

  rw [candidate_eq_profile]

  exact
    dvd_mul_of_dvd_left
      hpillar
      (oddPillar (pillar a))


/--
The least prime factor of every nontrivial structural candidate is `2`.
-/
theorem minFac_candidate_eq_two
    (a : ℕ)
    (ha : 1 ≤ a) :
    (candidate a).minFac = 2 := by
  apply
    (Nat.minFac_eq_two_iff
      (candidate a)).2

  exact
    two_dvd_candidate
      a
      ha


/--
For every nontrivial structural candidate,

`2 * greatestProperDivisor(candidate a) = candidate a`.
-/
theorem two_mul_greatestProperDivisor_candidate
    (a : ℕ)
    (ha : 1 ≤ a) :
    2 *
        greatestProperDivisor
          (candidate a) =
      candidate a := by
  have htwo :
      2 ∣ candidate a :=
    two_dvd_candidate
      a
      ha

  have hmin :
      (candidate a).minFac = 2 :=
    minFac_candidate_eq_two
      a
      ha

  unfold greatestProperDivisor

  rw [hmin]

  have hcancel :
      candidate a / 2 * 2 =
        candidate a :=
    Nat.div_mul_cancel htwo

  simpa [Nat.mul_comm] using hcancel


/-!
## 6. Rational form of the structural profile
-/

/--
Casting the odd pillar into `ℚ` gives the ordinary affine expression
`2L - 1`.
-/
theorem oddPillar_cast
    (L : ℕ)
    (hL : 1 ≤ L) :
    ((oddPillar L : ℕ) : ℚ) =
      2 * (L : ℚ) - 1 := by
  unfold oddPillar

  have hle :
      1 ≤ 2 * L := by
    omega

  rw [Nat.cast_sub hle]
  norm_num


/--
The rational value of the structural candidate is

`L(2L - 1)`

with `L = pillar a`.
-/
theorem candidate_cast
    (a : ℕ) :
    (candidate a : ℚ) =
      (pillar a : ℚ) *
        (2 * (pillar a : ℚ) - 1) := by
  have hL :
      1 ≤ pillar a :=
    one_le_pillar a

  rw [candidate_eq_profile]

  simp only [Nat.cast_mul]

  rw [
    oddPillar_cast
      (pillar a)
      hL
  ]


/-!
## 7. Exact structural calibration
-/

/--
### Exact profile calibration identity

For every nontrivial structural candidate,

`greatestProperDivisor(candidate a)`

lies exactly on the calibration curve:

`GD(candidate a) = theta(pillar a) * gauge(pillar a)`.

This equality is algebraic and does not require primality of the recovered
odd pillar.
-/
theorem profile_calibration_identity
    (a : ℕ)
    (ha : 1 ≤ a) :
    (greatestProperDivisor
        (candidate a) : ℚ) =
      theta (pillar a) *
        gauge (pillar a) := by
  have hdoubleNat :
      2 *
          greatestProperDivisor
            (candidate a) =
        candidate a :=
    two_mul_greatestProperDivisor_candidate
      a
      ha

  have hdoubleQ :
      (2 : ℚ) *
          (greatestProperDivisor
            (candidate a) : ℚ) =
        (candidate a : ℚ) := by
    exact_mod_cast hdoubleNat

  have hcandQ :
      (candidate a : ℚ) =
        (pillar a : ℚ) *
          (2 * (pillar a : ℚ) - 1) :=
    candidate_cast a

  rw [theta_mul_gauge]
  rw [hcandQ] at hdoubleQ

  nlinarith


/-!
## 8. Monotonicity of `theta`
-/

/--
The calibration factor `theta` is strictly increasing.
-/
theorem theta_strictMono :
    StrictMono theta := by
  intro m n hmn

  unfold theta

  have hmpos :
      (0 : ℚ) <
        (m : ℚ) + 2 := by
    positivity

  have hnpos :
      (0 : ℚ) <
        (n : ℚ) + 2 := by
    positivity

  have hmnCast :
      (m : ℚ) < (n : ℚ) := by
    exact_mod_cast hmn

  have hmnQ :
      (m : ℚ) + 2 <
        (n : ℚ) + 2 := by
    linarith

  have hfrac :
      (20 : ℚ) /
          ((n : ℚ) + 2) <
        20 /
          ((m : ℚ) + 2) := by
    rw [
      div_lt_div_iff₀
        hnpos
        hmpos
    ]

    nlinarith

  linarith


/-!
## 9. Convergence of `theta`
-/

/--
The rational sequence `n ↦ n + 2` tends to `+∞`.

This proof is written directly from the definition of convergence to `atTop`,
avoiding dependence on a specialized shift theorem name.
-/
theorem tendsto_natCast_add_two_atTop :
    Filter.Tendsto
      (fun n : ℕ =>
        (n : ℚ) + 2)
      Filter.atTop
      Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]

  intro b

  obtain ⟨N : ℕ, hN⟩ :=
    exists_nat_ge b

  refine ⟨N, ?_⟩

  intro n hn

  have hcast :
      (N : ℚ) ≤ (n : ℚ) := by
    exact_mod_cast hn

  exact le_trans hN (by linarith)


/--
The inverse denominator

`1/(n+2)`

tends to zero.
-/
theorem tendsto_inverse_natCast_add_two_zero :
    Filter.Tendsto
      (fun n : ℕ =>
        (((n : ℚ) + 2)⁻¹))
      Filter.atTop
      (nhds 0) := by
  exact
    tendsto_inv_atTop_zero.comp
      tendsto_natCast_add_two_atTop


/--
The calibration correction term

`20/(n+2)`

tends to zero.
-/
theorem tendsto_calibration_error :
    Filter.Tendsto
      (fun n : ℕ =>
        (20 : ℚ) /
          ((n : ℚ) + 2))
      Filter.atTop
      (nhds 0) := by
  have hinv :
      Filter.Tendsto
        (fun n : ℕ =>
          (((n : ℚ) + 2)⁻¹))
        Filter.atTop
        (nhds 0) :=
    tendsto_inverse_natCast_add_two_zero

  have hconst :
      Filter.Tendsto
        (fun _ : ℕ => (20 : ℚ))
        Filter.atTop
        (nhds 20) :=
    tendsto_const_nhds

  have hmul :
      Filter.Tendsto
        (fun n : ℕ =>
          (20 : ℚ) *
            (((n : ℚ) + 2)⁻¹))
        Filter.atTop
        (nhds ((20 : ℚ) * 0)) :=
    hconst.mul hinv

  simpa [div_eq_mul_inv] using hmul


/--
### Calibration tends to eight

`theta` is strictly increasing and converges to `8`.
-/
theorem calibration_tends_to_eight :
    StrictMono theta ∧
      Filter.Tendsto
        theta
        Filter.atTop
        (nhds (8 : ℚ)) := by
  constructor

  · exact theta_strictMono

  · change
      Filter.Tendsto
        (fun n : ℕ =>
          (8 : ℚ) -
            20 / ((n : ℚ) + 2))
        Filter.atTop
        (nhds (8 : ℚ))

    have herror :
        Filter.Tendsto
          (fun n : ℕ =>
            (20 : ℚ) /
              ((n : ℚ) + 2))
          Filter.atTop
          (nhds 0) :=
      tendsto_calibration_error

    have hlimit :
        Filter.Tendsto
          (fun n : ℕ =>
            (8 : ℚ) -
              20 / ((n : ℚ) + 2))
          Filter.atTop
          (nhds ((8 : ℚ) - 0)) :=
      tendsto_const_nhds.sub herror

    simpa using hlimit


end EvenPerfectStructure