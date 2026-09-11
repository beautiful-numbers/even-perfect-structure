-- FILE: EvenPerfectStructure/Basic.lean
/-
IMPORT CLASSIFICATION

- Mathlib
  library:
    Nat
    Finset
    Even
    divisibility
    minFac
    Perfect
    arithmetic tactics
-/

import Mathlib

/-!
# EvenPerfectStructure — Basic definitions

This module contains the elementary arithmetic objects shared by the proof
development.

The public definitions below intentionally match the corresponding definitions
in `Challenge.lean`:

* `pillar`
* `oddPillar`
* `profile`
* `candidate`
* `lowerDyadicPattern`
* `EvenPerfect`
* `InternalStructure`
* `greatestProperDivisor`

Calibration-specific definitions (`gauge`, `theta`) belong to
`Calibration.lean`.

No substantive SR, median, primality-certification, or calibration theorem is
proved here.
-/

namespace EvenPerfectStructure


/-!
## 1. Public definitions
-/

/--
The dyadic pillar associated with exponent `a`.

Mathematically:

`L = 2^a`.
-/
def pillar (a : ℕ) : ℕ :=
  2 ^ a


/--
The canonical odd factor attached to a pillar `L`.

Mathematically:

`k = 2L - 1`.
-/
def oddPillar (L : ℕ) : ℕ :=
  2 * L - 1


/--
The canonical structural profile attached to a pillar `L`.

Mathematically:

`M = L(2L - 1)`.
-/
def profile (L : ℕ) : ℕ :=
  L * oddPillar L


/--
The canonical candidate attached to a dyadic exponent `a`.

Mathematically:

`Mₐ = 2^a (2^(a+1) - 1)`.
-/
def candidate (a : ℕ) : ℕ :=
  profile (pillar a)


/--
`lowerDyadicPattern M L a` means that the positive divisors of `M`
strictly below `L` are exactly

`1, 2, 4, ..., 2^(a-1)`.

Equivalently,

`d ∣ M ∧ d < L`

holds exactly when

`d = 2^j`

for some `j < a`.
-/
def lowerDyadicPattern (M L a : ℕ) : Prop :=
  ∀ d : ℕ,
    (d ∣ M ∧ d < L) ↔
      ∃ j : ℕ, j < a ∧ d = 2 ^ j


/--
An even perfect number, using Mathlib's standard notion of perfection.
-/
def EvenPerfect (M : ℕ) : Prop :=
  Nat.Perfect M ∧ Even M


/--
The complete internal structural certificate.

The identity `k = 2L - 1` is deliberately not included: it is a theorem
to be recovered from the dyadic pillar and median identity.
-/
def InternalStructure (M : ℕ) : Prop :=
  ∃ a k L : ℕ,
    1 ≤ a ∧
    L = 2 ^ a ∧
    M = k * L ∧
    Nat.Coprime k L ∧
    lowerDyadicPattern M L a ∧
    (∑ j ∈ Finset.range a, 2 ^ j) + L = k


/--
The largest proper divisor candidate of `n`, represented arithmetically as

`n / n.minFac`.

For `n > 1`, the lemmas below prove that this quantity really is the largest
proper positive divisor of `n`.
-/
def greatestProperDivisor (n : ℕ) : ℕ :=
  n / n.minFac


/-!
## 2. Elementary pillar facts
-/

@[simp]
theorem pillar_zero :
    pillar 0 = 1 := by
  rfl


@[simp]
theorem pillar_succ (a : ℕ) :
    pillar (a + 1) = 2 * pillar a := by
  simp [pillar, pow_succ, Nat.mul_comm]


theorem pillar_pos (a : ℕ) :
    0 < pillar a := by
  simp [pillar]


theorem pillar_ne_zero (a : ℕ) :
    pillar a ≠ 0 := by
  exact Nat.ne_of_gt (pillar_pos a)


theorem one_le_pillar (a : ℕ) :
    1 ≤ pillar a := by
  exact Nat.one_le_iff_ne_zero.mpr (pillar_ne_zero a)


theorem pillar_even
    (a : ℕ)
    (ha : 1 ≤ a) :
    Even (pillar a) := by
  obtain ⟨b, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero
      (by omega : a ≠ 0)

  simp [pillar, pow_succ]


/-!
## 3. Canonical odd pillar
-/

@[simp]
theorem oddPillar_eq (L : ℕ) :
    oddPillar L = 2 * L - 1 := by
  rfl


theorem oddPillar_pillar (a : ℕ) :
    oddPillar (pillar a) =
      2 ^ (a + 1) - 1 := by
  simp [
    oddPillar,
    pillar,
    pow_succ,
    Nat.mul_comm
  ]


theorem oddPillar_pos
    (L : ℕ)
    (hL : 1 ≤ L) :
    0 < oddPillar L := by
  simp [oddPillar]
  omega


theorem oddPillar_odd
    (L : ℕ)
    (hL : 1 ≤ L) :
    Odd (oddPillar L) := by
  refine ⟨L - 1, ?_⟩

  simp [oddPillar]
  omega


/-!
## 4. Canonical profiles
-/

@[simp]
theorem profile_eq (L : ℕ) :
    profile L =
      L * (2 * L - 1) := by
  rfl


@[simp]
theorem candidate_eq_profile (a : ℕ) :
    candidate a =
      pillar a * oddPillar (pillar a) := by
  rfl


theorem candidate_eq (a : ℕ) :
    candidate a =
      2 ^ a * (2 ^ (a + 1) - 1) := by
  simp [
    candidate,
    profile,
    pillar,
    oddPillar,
    pow_succ,
    Nat.mul_comm
  ]


theorem candidate_pos (a : ℕ) :
    0 < candidate a := by
  rw [candidate_eq_profile]

  apply Nat.mul_pos

  · exact pillar_pos a

  · exact
      oddPillar_pos
        (pillar a)
        (one_le_pillar a)


theorem candidate_even
    (a : ℕ)
    (ha : 1 ≤ a) :
    Even (candidate a) := by
  rw [candidate_eq_profile]

  exact
    Even.mul_right
      (pillar_even a ha)
      (oddPillar (pillar a))


/-!
## 5. Coprimality of the canonical pillars
-/

/--
For every positive pillar `L`, the canonical odd factor `2L - 1`
is coprime to `L`.

The positivity hypothesis is necessary: with natural-number subtraction,
`oddPillar 0 = 0`.
-/
theorem coprime_oddPillar_pillar
    (L : ℕ)
    (hL : 1 ≤ L) :
    Nat.Coprime (oddPillar L) L := by
  rw [oddPillar]

  have hle :
      L ≤ 2 * L - 1 := by
    omega

  rw [← Nat.coprime_sub_self_left hle]

  have hsub :
      2 * L - 1 - L =
        L - 1 := by
    omega

  rw [hsub]
  rw [Nat.coprime_self_sub_left hL]

  exact Nat.coprime_one_left L


theorem coprime_pillar_oddPillar
    (L : ℕ)
    (hL : 1 ≤ L) :
    Nat.Coprime L (oddPillar L) := by
  exact
    (coprime_oddPillar_pillar
      L
      hL).symm


theorem coprime_candidate_factors
    (a : ℕ) :
    Nat.Coprime
      (oddPillar (pillar a))
      (pillar a) := by
  exact
    coprime_oddPillar_pillar
      (pillar a)
      (one_le_pillar a)


/-!
## 6. Elementary consequences of the lower dyadic pattern
-/

/--
Every power `2^j` with `j < a` divides `M` and lies below `L`
whenever the lower dyadic pattern holds.
-/
theorem pow_two_mem_lowerPattern
    {M L a j : ℕ}
    (hpattern :
      lowerDyadicPattern M L a)
    (hj : j < a) :
    2 ^ j ∣ M ∧
      2 ^ j < L := by
  exact
    (hpattern (2 ^ j)).2
      ⟨j, hj, rfl⟩


/--
Every divisor of `M` strictly below `L` is one of the dyadic powers
specified by the pattern.
-/
theorem lowerPattern_eq_pow_two
    {M L a d : ℕ}
    (hpattern :
      lowerDyadicPattern M L a)
    (hdvd : d ∣ M)
    (hdlt : d < L) :
    ∃ j : ℕ,
      j < a ∧
      d = 2 ^ j := by
  exact
    (hpattern d).1
      ⟨hdvd, hdlt⟩


/-!
## 7. Semantics of `greatestProperDivisor`
-/

/--
For `n > 1`, `greatestProperDivisor n` divides `n`.
-/
theorem greatestProperDivisor_dvd
    {n : ℕ}
    (_hn : 1 < n) :
    greatestProperDivisor n ∣ n := by
  rw [greatestProperDivisor]

  refine
    ⟨n.minFac, ?_⟩

  exact
    (Nat.div_mul_cancel
      (Nat.minFac_dvd n)).symm


/--
For `n > 1`, `greatestProperDivisor n` is strictly smaller than `n`.
-/
theorem greatestProperDivisor_lt
    {n : ℕ}
    (hn : 1 < n) :
    greatestProperDivisor n < n := by
  rw [greatestProperDivisor]

  apply Nat.div_lt_self

  · omega

  · exact
      (Nat.minFac_prime
        (by omega : n ≠ 1)).two_le


/--
Every proper positive divisor of `n > 1` is bounded above by
`greatestProperDivisor n`.

Thus `greatestProperDivisor` really has the advertised maximality property.
-/
theorem le_greatestProperDivisor
    {n d : ℕ}
    (_hn : 1 < n)
    (hd : d ∣ n)
    (hproper : d < n) :
    d ≤ greatestProperDivisor n := by
  rcases hd with
    ⟨c, hc⟩

  have hdpos :
      0 < d := by
    by_contra h

    have hd0 :
        d = 0 :=
      Nat.eq_zero_of_not_pos h

    subst d

    simp at hc
    omega

  have hc_two :
      2 ≤ c := by
    nlinarith

  have hc_dvd :
      c ∣ n := by
    refine
      ⟨d, ?_⟩

    simpa [Nat.mul_comm]
      using hc

  have hmin :
      n.minFac ≤ c :=
    Nat.minFac_le_of_dvd
      hc_two
      hc_dvd

  rw [greatestProperDivisor]

  apply
    (Nat.le_div_iff_mul_le
      (Nat.minFac_pos n)).2

  calc
    d * n.minFac
        ≤ d * c :=
      Nat.mul_le_mul_left
        d
        hmin

    _ = n := by
      exact hc.symm


/-!
## 8. InternalStructure projections
-/

/--
Unpack the data carried by an internal structural certificate.
-/
theorem InternalStructure.exists_data
    {M : ℕ}
    (h : InternalStructure M) :
    ∃ a k L : ℕ,
      1 ≤ a ∧
      L = 2 ^ a ∧
      M = k * L ∧
      Nat.Coprime k L ∧
      lowerDyadicPattern M L a ∧
      (∑ j ∈ Finset.range a, 2 ^ j) + L = k := by
  exact h


end EvenPerfectStructure