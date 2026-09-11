-- FILE: EvenPerfectStructure/Audit.lean
/-
IMPORT CLASSIFICATION

- EvenPerfectStructure.Main
  defs:
    pillar
    oddPillar
    candidate
    lowerDyadicPattern
    EvenPerfect
    InternalStructure
  thms:
    pillar_pos
    one_le_pillar
    oddPillar_pillar
    candidate_eq_profile
    coprime_oddPillar_pillar
    divisor_structure
    internal_structure_implies_evenPerfect
    InternalStructure.toEvenPerfect
    SR.sum_range_pow_two_eq_pillar_sub_one

- Archive.Wiedijk100Theorems.PerfectNumbers
  defs:
    mersenne
  thms:
    mersenne_odd
    Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect
    Theorems100.Nat.ne_zero_of_prime_mersenne

- Mathlib
  defs:
    Nat.factorization
  thms:
    Nat.factorization_mul
    Nat.factorization_pow
    Nat.dvd_of_factorization_pos
    Nat.not_odd_zero
    Odd.not_two_dvd_nat
-/

import EvenPerfectStructure.Main
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
# EvenPerfectStructure.Audit

Final compatibility audit.

The structural development in `Main` is oriented as

`InternalStructure M → EvenPerfect M`.

That direction is established internally:

* the median identity recovers the odd factor;
* the lower divisor pattern certifies its primality;
* divisor sums certify perfection directly.

This module is strictly downstream of that development.

Its only use of the classical classification is the reverse compatibility
direction

`EvenPerfect M → InternalStructure M`

and the reverse direction of the canonical-family audit

`EvenPerfect (candidate a) →
  lowerDyadicPattern (candidate a) (pillar a) a`.

Thus the dependency direction is

`structural theory`
        ↓
`Main`
        ↓
`Audit`
        ↓
`Solution`

and never the reverse.

No theorem in `Basic`, `SR`, `DivisorPattern`, `Certification`,
`Calibration`, or `Sequential` depends on this module.
-/

namespace EvenPerfectStructure

namespace Audit


/-!
## 1. Compatibility with Mathlib's Mersenne notation
-/

/--
At dyadic exponent `a`, the project's odd pillar agrees with Mathlib's
Mersenne number of index `a + 1`.
-/
theorem oddPillar_pillar_eq_mersenne
    (a : ℕ) :
    oddPillar (pillar a) =
      mersenne (a + 1) := by
  simpa [mersenne] using
    (oddPillar_pillar a)


/-!
## 2. External completeness data
-/

/--
An even perfect number supplies, through the external compatibility theorem,
a positive dyadic exponent, a prime odd pillar, and the canonical profile
factorization.

This theorem merely translates Mathlib's result into the vocabulary of the
project.
-/
theorem evenPerfect_exists_structural_profile
    {M : ℕ}
    (h : EvenPerfect M) :
    ∃ a : ℕ,
      1 ≤ a ∧
      Nat.Prime (oddPillar (pillar a)) ∧
      M =
        pillar a *
          oddPillar (pillar a) := by
  rcases h with
    ⟨hperfect, heven⟩

  obtain
    ⟨a, hprimeMersenne, hM⟩ :=
      Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect
        heven
        hperfect

  have ha0 :
      a ≠ 0 :=
    Theorems100.Nat.ne_zero_of_prime_mersenne
      a
      hprimeMersenne

  have ha :
      1 ≤ a := by
    omega

  have hodd :
      oddPillar (pillar a) =
        mersenne (a + 1) :=
    oddPillar_pillar_eq_mersenne a

  have hprimeOdd :
      Nat.Prime
        (oddPillar (pillar a)) := by
    rw [hodd]
    exact hprimeMersenne

  have hMprofile :
      M =
        pillar a *
          oddPillar (pillar a) := by
    calc
      M =
          2 ^ a *
            mersenne (a + 1) :=
        hM

      _ =
          pillar a *
            mersenne (a + 1) := by
        rfl

      _ =
          pillar a *
            oddPillar (pillar a) := by
        rw [hodd]

  exact
    ⟨a,
      ha,
      hprimeOdd,
      hMprofile⟩


/-!
## 3. Reconstruction of the internal certificate
-/

/--
Every externally recognized even perfect number reconstructs the exact
`InternalStructure` certificate used by the structural development.

This is the only implication in the global equivalence that uses the
external classical classification.
-/
theorem evenPerfect_to_internalStructure
    {M : ℕ}
    (h : EvenPerfect M) :
    InternalStructure M := by
  obtain
    ⟨a,
      ha,
      hprime,
      hMprofile⟩ :=
    evenPerfect_exists_structural_profile h

  let L : ℕ :=
    pillar a

  let k : ℕ :=
    oddPillar (pillar a)

  have hL :
      L = 2 ^ a := by
    rfl

  have hM :
      M = k * L := by
    dsimp [k, L]

    calc
      M =
          pillar a *
            oddPillar (pillar a) :=
        hMprofile

      _ =
          oddPillar (pillar a) *
            pillar a := by
        ac_rfl

  have hcoprime :
      Nat.Coprime k L := by
    dsimp [k, L]

    exact
      coprime_oddPillar_pillar
        (pillar a)
        (one_le_pillar a)

  have hpattern :
      lowerDyadicPattern
        M
        L
        a := by
    have hcanonical :
        lowerDyadicPattern
          (candidate a)
          (pillar a)
          a :=
      (divisor_structure a ha).2
        hprime

    have hMcandidate :
        M = candidate a := by
      calc
        M =
            pillar a *
              oddPillar (pillar a) :=
          hMprofile

        _ = candidate a := by
          rw [candidate_eq_profile]

    dsimp [L]

    rw [hMcandidate]

    exact hcanonical

  have hmedian :
      (∑ j ∈ Finset.range a, 2 ^ j) +
          L =
        k := by
    dsimp [L, k]

    rw [
      SR.sum_range_pow_two_eq_pillar_sub_one
    ]

    rw [oddPillar]

    have hp :
        0 < pillar a :=
      pillar_pos a

    omega

  exact
    ⟨a,
      k,
      L,
      ha,
      hL,
      hM,
      hcoprime,
      hpattern,
      hmedian⟩


/-!
## 4. Uniqueness of the dyadic exponent
-/

/--
If two powers of two multiplied by odd factors are equal, then their
exponents are equal.
-/
theorem two_pow_mul_odd_exponent_unique
    (a b u v : ℕ)
    (hu : Odd u)
    (hv : Odd v)
    (h :
      2 ^ a * u =
        2 ^ b * v) :
    a = b := by
  have hu0 :
      u ≠ 0 := by
    intro hzero
    subst u
    exact Nat.not_odd_zero hu

  have hv0 :
      v ≠ 0 := by
    intro hzero
    subst v
    exact Nat.not_odd_zero hv

  have hpowA0 :
      2 ^ a ≠ 0 := by
    positivity

  have hpowB0 :
      2 ^ b ≠ 0 := by
    positivity

  have hfu :
      u.factorization 2 = 0 := by
    by_contra hne

    have hdvd :
        2 ∣ u :=
      Nat.dvd_of_factorization_pos hne

    exact
      hu.not_two_dvd_nat hdvd

  have hfv :
      v.factorization 2 = 0 := by
    by_contra hne

    have hdvd :
        2 ∣ v :=
      Nat.dvd_of_factorization_pos hne

    exact
      hv.not_two_dvd_nat hdvd

  have hfacTwo :
      (Nat.factorization 2) 2 = 1 := by
    norm_num [Nat.factorization]

  have hleft :
      (2 ^ a * u).factorization 2 =
        a := by
    rw [
      Nat.factorization_mul
        hpowA0
        hu0
    ]

    rw [Nat.factorization_pow]

    simp [hfu, hfacTwo]

  have hright :
      (2 ^ b * v).factorization 2 =
        b := by
    rw [
      Nat.factorization_mul
        hpowB0
        hv0
    ]

    rw [Nat.factorization_pow]

    simp [hfv, hfacTwo]

  calc
    a =
        (2 ^ a * u).factorization 2 :=
      hleft.symm

    _ =
        (2 ^ b * v).factorization 2 := by
      rw [h]

    _ = b :=
      hright


end Audit


/-!
## 5. Public compatibility interfaces
-/

/--
### Final compatibility equivalence

The project's internal structural certificate characterizes exactly the
even perfect numbers.

The two implications deliberately have different provenance:

* `InternalStructure → EvenPerfect` is proved internally by the structural
  development before this module is imported;

* `EvenPerfect → InternalStructure` is supplied only here, as a final
  compatibility audit against Mathlib's formal classification.

Therefore the external classification establishes completeness without
participating in the structural derivation.
-/
theorem evenPerfect_iff_internalStructure
    (M : ℕ) :
    EvenPerfect M ↔
      InternalStructure M := by
  constructor

  · intro h

    exact
      Audit.evenPerfect_to_internalStructure h

  · intro h

    exact
      h.toEvenPerfect


/--
### Canonical-family compatibility

For a canonical dyadic candidate at a nontrivial level `a`, the exact lower
dyadic divisor pattern is equivalent to even perfection.

The forward implication belongs entirely to the structural development.

For the reverse implication, the final audit uses the external
classification only to obtain a canonical perfect-number exponent `b`.
Uniqueness of the power-of-two exponent forces `b = a`, and the already
proved `divisor_structure` theorem then recovers the lower-divisor pattern
at the original level `a`.
-/
theorem divisor_pattern_iff_evenPerfect
    (a : ℕ)
    (ha : 1 ≤ a) :
    lowerDyadicPattern
        (candidate a)
        (pillar a)
        a ↔
      EvenPerfect
        (candidate a) := by
  constructor

  · intro hpattern

    have hL :
        pillar a = 2 ^ a := by
      rfl

    have hM :
        candidate a =
          oddPillar (pillar a) *
            pillar a := by
      calc
        candidate a =
            pillar a *
              oddPillar (pillar a) := by
          rw [candidate_eq_profile]

        _ =
            oddPillar (pillar a) *
              pillar a := by
          ac_rfl

    have hcoprime :
        Nat.Coprime
          (oddPillar (pillar a))
          (pillar a) :=
      coprime_oddPillar_pillar
        (pillar a)
        (one_le_pillar a)

    have hmedian :
        (∑ j ∈ Finset.range a, 2 ^ j) +
            pillar a =
          oddPillar (pillar a) := by
      rw [
        SR.sum_range_pow_two_eq_pillar_sub_one
      ]

      rw [oddPillar]

      have hp :
          0 < pillar a :=
        pillar_pos a

      omega

    exact
      internal_structure_implies_evenPerfect
        (candidate a)
        (oddPillar (pillar a))
        (pillar a)
        a
        ha
        hL
        hM
        hcoprime
        hpattern
        hmedian

  · intro hperfect

    obtain
      ⟨b,
        hb,
        hprimeB,
        hcandidateB⟩ :=
      Audit.evenPerfect_exists_structural_profile
        hperfect

    have hoddA :
        Odd
          (oddPillar (pillar a)) := by
      rw [
        Audit.oddPillar_pillar_eq_mersenne
      ]

      exact
        (mersenne_odd).2
          (by omega)

    have hoddB :
        Odd
          (oddPillar (pillar b)) := by
      rw [
        Audit.oddPillar_pillar_eq_mersenne
      ]

      exact
        (mersenne_odd).2
          (by omega)

    have hfactorization :
        2 ^ a *
            oddPillar (pillar a) =
          2 ^ b *
            oddPillar (pillar b) := by
      calc
        2 ^ a *
              oddPillar (pillar a) =
            pillar a *
              oddPillar (pillar a) := by
          rfl

        _ = candidate a := by
          rw [candidate_eq_profile]

        _ =
            pillar b *
              oddPillar (pillar b) :=
          hcandidateB

        _ =
            2 ^ b *
              oddPillar (pillar b) := by
          rfl

    have hab :
        a = b :=
      Audit.two_pow_mul_odd_exponent_unique
        a
        b
        (oddPillar (pillar a))
        (oddPillar (pillar b))
        hoddA
        hoddB
        hfactorization

    subst b

    exact
      (divisor_structure a ha).2
        hprimeB


end EvenPerfectStructure