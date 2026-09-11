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

- Mathlib.NumberTheory.LucasLehmer
  defs:
    mersenne
  thms:
    mersenne_odd
    succ_mersenne

- Mathlib.NumberTheory.ArithmeticFunction.Misc
  defs:
    ArithmeticFunction.sigma
    Nat.factorization
  thms:
    ArithmeticFunction.sigma_one_apply
    Nat.perfect_iff_sum_divisors_eq_two_mul
    Nat.sum_divisors_eq_sum_properDivisors_add_self
    Nat.sum_properDivisors_dvd
    Nat.sum_properDivisors_eq_one_iff_prime
    Nat.factorization_mul
    Nat.factorization_pow
    Nat.dvd_of_factorization_pos

- Mathlib.Tactic.NormNum.Prime

- Mathlib
  thms:
    Nat.not_odd_zero
    Odd.not_two_dvd_nat
-/

import EvenPerfectStructure.Main
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Tactic.NormNum.Prime

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

For the reverse compatibility direction

`EvenPerfect M → InternalStructure M`

the classical Euler classification is reconstructed locally from standard
Mathlib number-theoretic infrastructure.

No `Archive.*` module is imported.

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

open ArithmeticFunction
open scoped sigma


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
## 2. Classical Euler classification from standard Mathlib

The following lemmas reproduce only the classical completeness argument needed
by this audit.

They use standard Mathlib number-theoretic infrastructure and do not depend on
`Archive.Wiedijk100Theorems.PerfectNumbers`.
-/

/--
The divisor sum of a power of two is the corresponding Mersenne number.
-/
private theorem sigma_two_pow_eq_mersenne_succ
    (k : ℕ) :
    σ 1 (2 ^ k) =
      mersenne (k + 1) := by
  simp_rw [
    sigma_one_apply,
    mersenne,
    ← one_add_one_eq_two,
    ← geom_sum_mul_add 1 (k + 1)
  ]
  norm_num


/--
Every positive natural number decomposes as a power of two times an odd
factor.
-/
private theorem eq_two_pow_mul_odd
    {n : ℕ}
    (hpos : 0 < n) :
    ∃ k m : ℕ,
      n = 2 ^ k * m ∧
      ¬ Even m := by
  have h :=
    Nat.finiteMultiplicity_iff.2
      ⟨Nat.prime_two.ne_one, hpos⟩

  obtain ⟨m, hm⟩ :=
    pow_multiplicity_dvd 2 n

  use multiplicity 2 n, m

  refine
    ⟨hm, ?_⟩

  rw [even_iff_two_dvd]

  have hg :=
    h.not_pow_dvd_of_multiplicity_lt
      (Nat.lt_succ_self _)

  contrapose! hg

  rcases hg with
    ⟨k, rfl⟩

  apply Dvd.intro k

  rw [
    pow_succ,
    mul_assoc,
    ← hm
  ]


/--
Euler's classification in the precise form required by the compatibility
audit: an even perfect number is a power of two times a prime Mersenne factor.

This proof is reconstructed locally in the audit from standard Mathlib.
-/
private theorem eq_two_pow_mul_prime_mersenne_of_even_perfect
    {n : ℕ}
    (ev : Even n)
    (perf : Nat.Perfect n) :
    ∃ k : ℕ,
      Nat.Prime (mersenne (k + 1)) ∧
      n =
        2 ^ k *
          mersenne (k + 1) := by
  have hpos :=
    perf.2

  rcases
      eq_two_pow_mul_odd hpos with
    ⟨k, m, rfl, hm⟩

  use k

  rw [even_iff_two_dvd] at hm

  rw [
    Nat.perfect_iff_sum_divisors_eq_two_mul hpos,
    ← sigma_one_apply,
    isMultiplicative_sigma.map_mul_of_coprime
      (Nat.prime_two.coprime_pow_of_not_dvd hm).symm,
    sigma_two_pow_eq_mersenne_succ,
    ← mul_assoc,
    ← pow_succ'
  ] at perf

  obtain
      ⟨j, rfl⟩ :=
    ((Odd.coprime_two_right (by simp)).pow_right _).dvd_of_dvd_mul_left
      (Dvd.intro _ perf)

  rw [
    ← mul_assoc,
    mul_comm _ (mersenne _),
    mul_assoc
  ] at perf

  have h :=
    mul_left_cancel₀
      (by positivity)
      perf

  rw [
    sigma_one_apply,
    Nat.sum_divisors_eq_sum_properDivisors_add_self,
    ← succ_mersenne,
    add_mul,
    one_mul,
    add_comm
  ] at h

  have hj :=
    add_left_cancel h

  cases
      Nat.sum_properDivisors_dvd
        (by
          rw [hj]
          apply Dvd.intro_left
            (mersenne (k + 1))
            rfl) with

  | inl h₁ =>
      have j1 :
          j = 1 :=
        Eq.trans hj.symm h₁

      rw [
        j1,
        mul_one,
        Nat.sum_properDivisors_eq_one_iff_prime
      ] at h₁

      simp [h₁, j1]

  | inr h₁ =>
      have jcon :=
        Eq.trans hj.symm h₁

      rw [
        ← one_mul j,
        ← mul_assoc,
        mul_one
      ] at jcon

      have jcon2 :=
        mul_right_cancel₀
          ?_
          jcon

      · exfalso

        match k with
        | 0 =>
            apply hm

            rw [
              ← jcon2,
              pow_zero,
              one_mul,
              one_mul
            ] at ev

            rw [
              ← jcon2,
              one_mul
            ]

            exact
              even_iff_two_dvd.mp ev

        | .succ k =>
            apply
              _root_.ne_of_lt
                (by
                  rw [
                    mersenne,
                    ← Nat.pred_eq_sub_one,
                    Nat.lt_pred_iff,
                    ← pow_one (Nat.succ 1)
                  ]

                  apply
                    pow_lt_pow_right₀
                      (Nat.lt_succ_self 1)
                      (Nat.succ_lt_succ k.succ_pos))
                jcon2

      · contrapose! hm

        simp [hm]


/--
A prime Mersenne factor at index `a + 1` forces `a` to be nonzero.
-/
private theorem ne_zero_of_prime_mersenne
    (a : ℕ)
    (hprime :
      Nat.Prime
        (mersenne (a + 1))) :
    a ≠ 0 := by
  intro ha

  subst a

  norm_num [mersenne] at hprime


/-!
## 3. Classical completeness data in project notation
-/

/--
An even perfect number supplies, through the classical Euler argument above,
a positive dyadic exponent, a prime odd pillar, and the canonical profile
factorization.

This theorem translates that classical result into the vocabulary of the
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
      eq_two_pow_mul_prime_mersenne_of_even_perfect
        heven
        hperfect

  have ha0 :
      a ≠ 0 :=
    ne_zero_of_prime_mersenne
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

    exact
      hprimeMersenne

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
## 4. Reconstruction of the internal certificate
-/

/--
Every classically recognized even perfect number reconstructs the exact
`InternalStructure` certificate used by the structural development.

This is the only implication in the global equivalence that uses the
classical Euler classification.
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

    exact
      hcanonical

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
## 5. Uniqueness of the dyadic exponent
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

    exact
      Nat.not_odd_zero hu

  have hv0 :
      v ≠ 0 := by
    intro hzero

    subst v

    exact
      Nat.not_odd_zero hv

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
## 6. Public compatibility interfaces
-/

/--
### Final compatibility equivalence

The project's internal structural certificate characterizes exactly the
even perfect numbers.

The two implications deliberately have different provenance:

* `InternalStructure → EvenPerfect` is proved internally by the structural
  development before this module is imported;

* `EvenPerfect → InternalStructure` is supplied only here, by a classical
  Euler completeness argument reconstructed locally from standard Mathlib.

Therefore the classical classification establishes completeness without
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

For the reverse implication, the final audit uses the locally reconstructed
classical completeness argument only to obtain a canonical perfect-number
exponent `b`. Uniqueness of the power-of-two exponent forces `b = a`, and the
already proved `divisor_structure` theorem then recovers the lower-divisor
pattern at the original level `a`.
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