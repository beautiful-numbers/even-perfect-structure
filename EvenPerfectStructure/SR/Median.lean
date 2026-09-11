-- FILE: EvenPerfectStructure/SR/Median.lean
/-
IMPORT CLASSIFICATION

- EvenPerfectStructure.Basic
  defs:
    pillar
    oddPillar
    profile
  thms:
    pillar_pos
    profile_eq

- EvenPerfectStructure.SR.Definitions
  defs:
    DyadicPillar
    MedianIdentity
    CoprimeFactorization
    StructuralWitness
  thms:
    DyadicPillar.pos
    dyadicPillar_pillar
    CoprimeFactorization.eq
-/

import EvenPerfectStructure.SR.Definitions

/-!
# EvenPerfectStructure.SR.Median

Dyadic summation and structural median identities.

This module isolates the arithmetic mechanism that recovers the canonical
odd factor from the structural median relation.

The main steps are:

* evaluate the dyadic lower-stratum sum
  `1 + 2 + ... + 2^(a-1)`;
* combine that sum with the dyadic pillar `L = 2^a`;
* recover the complementary factor `k = 2L - 1`;
* recover the canonical profile `M = L(2L - 1)`.

The divisor-pattern and primality arguments are deliberately absent here.
They belong to `DivisorPattern.lean`.

The public theorem `median_identity_recovers_profile` is proved at the end of
this file under the namespace `EvenPerfectStructure`, so its name matches the
advertised declaration in `Challenge.lean`.
-/

namespace EvenPerfectStructure
namespace SR


/-!
## 1. Dyadic geometric sum
-/

/--
The sum of the first `a` powers of two is

`1 + 2 + ... + 2^(a-1) = 2^a - 1`.
-/
theorem sum_range_pow_two
    (a : ℕ) :
    (∑ j ∈ Finset.range a, 2 ^ j) =
      2 ^ a - 1 := by
  induction a with

  | zero =>
      simp

  | succ a ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      rw [pow_succ]

      have hpowpos : 0 < 2 ^ a := by
        positivity

      omega


/--
The same geometric sum expressed using the public pillar notation.
-/
theorem sum_range_pow_two_eq_pillar_sub_one
    (a : ℕ) :
    (∑ j ∈ Finset.range a, 2 ^ j) =
      pillar a - 1 := by
  rw [sum_range_pow_two]
  rfl


/--
The dyadic lower-stratum sum is strictly smaller than the pillar.
-/
theorem sum_range_pow_two_lt_pillar
    (a : ℕ) :
    (∑ j ∈ Finset.range a, 2 ^ j) <
      pillar a := by
  rw [sum_range_pow_two_eq_pillar_sub_one]

  have hp : 0 < pillar a :=
    pillar_pos a

  omega


/-!
## 2. Median identity at a dyadic pillar
-/

/--
If `L = 2^a`, then the dyadic lower-stratum sum is exactly `L - 1`.
-/
theorem sum_range_pow_two_eq_sub_one_of_dyadicPillar
    {L a : ℕ}
    (hL : DyadicPillar L a) :
    (∑ j ∈ Finset.range a, 2 ^ j) =
      L - 1 := by
  rw [sum_range_pow_two]

  unfold DyadicPillar at hL
  rw [hL]


/--
A dyadic pillar together with the median identity forces

`k = 2L - 1`.
-/
theorem medianIdentity_recovers_oddPillar
    {k L a : ℕ}
    (hL : DyadicPillar L a)
    (hmedian : MedianIdentity k L a) :
    k = 2 * L - 1 := by
  have hsum :
      (∑ j ∈ Finset.range a, 2 ^ j) =
        L - 1 :=
    sum_range_pow_two_eq_sub_one_of_dyadicPillar hL

  unfold MedianIdentity at hmedian

  rw [hsum] at hmedian

  have hLpos : 0 < L :=
    hL.pos

  omega


/--
The factor recovered from the median identity is the public canonical
`oddPillar L`.
-/
theorem medianIdentity_recovers_oddPillar_def
    {k L a : ℕ}
    (hL : DyadicPillar L a)
    (hmedian : MedianIdentity k L a) :
    k = oddPillar L := by
  rw [oddPillar]
  exact medianIdentity_recovers_oddPillar hL hmedian


/-!
## 3. Recovering the canonical profile
-/

/--
An explicit factorization `M = kL`, together with a dyadic pillar and the
median identity, recovers the canonical structural profile

`M = L(2L - 1)`.
-/
theorem medianIdentity_recovers_profile'
    {M k L a : ℕ}
    (hL : DyadicPillar L a)
    (hM : M = k * L)
    (hmedian : MedianIdentity k L a) :
    k = 2 * L - 1 ∧
      M = L * (2 * L - 1) := by
  have hk :
      k = 2 * L - 1 :=
    medianIdentity_recovers_oddPillar hL hmedian

  constructor

  · exact hk

  · calc
      M = k * L := hM
      _ = (2 * L - 1) * L := by
        rw [hk]
      _ = L * (2 * L - 1) := by
        ac_rfl


/--
A `CoprimeFactorization` together with a dyadic pillar and median identity
recovers the canonical profile.

The coprimality component is not required for this arithmetic step; it is
retained because it is part of the surrounding structural witness.
-/
theorem coprimeFactorization_median_recovers_profile
    {M k L a : ℕ}
    (hL : DyadicPillar L a)
    (hfac : CoprimeFactorization M k L)
    (hmedian : MedianIdentity k L a) :
    k = 2 * L - 1 ∧
      M = L * (2 * L - 1) := by
  exact
    medianIdentity_recovers_profile'
      hL
      hfac.eq
      hmedian


/-!
## 4. Consequences for an explicit structural witness
-/

/--
Every explicit structural witness recovers the canonical odd factor.
-/
theorem StructuralWitness.odd_factor_eq
    {M k L a : ℕ}
    (h : StructuralWitness M k L a) :
    k = 2 * L - 1 := by
  rcases h with
    ⟨_ha, hL, _hfac, _hpattern, hmedian⟩

  exact
    medianIdentity_recovers_oddPillar
      hL
      hmedian


/--
Every explicit structural witness recovers the canonical profile.
-/
theorem StructuralWitness.profile_eq
    {M k L a : ℕ}
    (h : StructuralWitness M k L a) :
    M = L * (2 * L - 1) := by
  rcases h with
    ⟨_ha, hL, hfac, _hpattern, hmedian⟩

  exact
    (coprimeFactorization_median_recovers_profile
      hL
      hfac
      hmedian).2


/--
Every explicit structural witness recovers both the odd factor and the
canonical profile simultaneously.
-/
theorem StructuralWitness.recovers_profile
    {M k L a : ℕ}
    (h : StructuralWitness M k L a) :
    k = 2 * L - 1 ∧
      M = L * (2 * L - 1) := by
  rcases h with
    ⟨_ha, hL, hfac, _hpattern, hmedian⟩

  exact
    coprimeFactorization_median_recovers_profile
      hL
      hfac
      hmedian


/-!
## 5. Canonical form expressed with public definitions
-/

/--
If the median identity holds at the public pillar `pillar a`, then the
complementary factor is `oddPillar (pillar a)`.
-/
theorem medianIdentity_at_pillar_recovers_oddPillar
    {k a : ℕ}
    (hmedian :
      MedianIdentity k (pillar a) a) :
    k = oddPillar (pillar a) := by
  exact
    medianIdentity_recovers_oddPillar_def
      (dyadicPillar_pillar a)
      hmedian


/--
If `M = k * pillar a` and the median identity holds, then `M` is the public
canonical profile associated with that pillar.
-/
theorem medianIdentity_at_pillar_recovers_public_profile
    {M k a : ℕ}
    (hM : M = k * pillar a)
    (hmedian :
      MedianIdentity k (pillar a) a) :
    M = profile (pillar a) := by
  have hrec :=
    medianIdentity_recovers_profile'
      (M := M)
      (k := k)
      (L := pillar a)
      (a := a)
      (dyadicPillar_pillar a)
      hM
      hmedian

  rw [profile_eq]

  exact hrec.2


end SR


/-!
## 6. Advertised theorem
-/

/--
### Median identity recovers the profile

Let

`M = kL`

and assume that

`L = 2^a`.

If the median identity

`(∑ j < a, 2^j) + L = k`

holds, then the geometric sum forces

`k = 2L - 1`

and therefore

`M = L(2L - 1)`.

The assumption `a ≥ 1` is part of the advertised structural statement even
though the arithmetic implication itself is valid already for `a = 0`.
-/
theorem median_identity_recovers_profile
    (M k L a : ℕ)
    (_ha : 1 ≤ a)
    (hL : L = 2 ^ a)
    (hM : M = k * L)
    (hmedian :
      (∑ j ∈ Finset.range a, 2 ^ j) + L = k) :
    k = 2 * L - 1 ∧
      M = L * (2 * L - 1) := by
  have hL' :
      SR.DyadicPillar L a := by
    exact hL

  have hmedian' :
      SR.MedianIdentity k L a := by
    exact hmedian

  exact
    SR.medianIdentity_recovers_profile'
      hL'
      hM
      hmedian'


end EvenPerfectStructure