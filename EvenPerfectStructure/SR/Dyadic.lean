-- FILE: EvenPerfectStructure/SR/Dyadic.lean
/-
IMPORT CLASSIFICATION

- EvenPerfectStructure.Basic
  defs:
    pillar
    oddPillar
    profile
    candidate
    lowerDyadicPattern
  thms:
    candidate_eq_profile

- EvenPerfectStructure.SR.Definitions
  defs:
    LowerDivisor
    DyadicBelow
  thms:
    DyadicBelow.pos
    lowerDivisor_of_dyadicBelow
    dyadicBelow_of_lowerDivisor
-/

import EvenPerfectStructure.SR.Definitions

/-!
# EvenPerfectStructure.SR.Dyadic

Dyadic arithmetic for the sigma-rectangle development.

This module isolates the elementary facts about powers of two that underlie
the lower dyadic divisor stratum.

It provides:

* divisibility between dyadic powers;
* monotonicity of dyadic powers;
* divisibility of lower dyadic powers into the pillar;
* divisibility of lower dyadic powers into canonical candidates;
* elementary consequences of `lowerDyadicPattern`;
* characterization of proper divisors of a dyadic pillar;
* uniqueness of dyadic exponents;
* exclusion of nontrivial odd numbers from dyadic lower layers.

No primality characterization or median argument is proved here.
Those belong to `DivisorPattern.lean` and `SR/Median.lean`.
-/

namespace EvenPerfectStructure
namespace SR


/-!
## 1. Divisibility between powers of two
-/

/--
If `i ≤ j`, then `2^i` divides `2^j`.
-/
theorem pow_two_dvd_pow_two
    {i j : ℕ}
    (hij : i ≤ j) :
    2 ^ i ∣ 2 ^ j := by
  exact pow_dvd_pow 2 hij


/--
If `i ≤ a`, then `2^i` divides the dyadic pillar `2^a`.
-/
theorem pow_two_dvd_pillar
    {i a : ℕ}
    (hia : i ≤ a) :
    2 ^ i ∣ pillar a := by
  unfold pillar
  exact pow_two_dvd_pow_two hia


/--
Every prescribed lower dyadic power divides its pillar.
-/
theorem dyadicBelow_dvd_pillar
    {a d : ℕ}
    (hd : DyadicBelow a d) :
    d ∣ pillar a := by
  rcases hd with ⟨j, hj, rfl⟩
  exact pow_two_dvd_pillar (Nat.le_of_lt hj)


/-!
## 2. Order properties of powers of two
-/

/--
Powers of two are strictly increasing in their exponent.
-/
theorem pow_two_strictMono :
    StrictMono (fun n : ℕ => (2 : ℕ) ^ n) := by
  intro i j hij
  exact Nat.pow_lt_pow_right (by norm_num : 1 < (2 : ℕ)) hij


/--
If `i < j`, then `2^i < 2^j`.
-/
theorem pow_two_lt_pow_two
    {i j : ℕ}
    (hij : i < j) :
    2 ^ i < 2 ^ j := by
  exact pow_two_strictMono hij


/--
If `j < a`, then `2^j` lies strictly below the pillar `2^a`.
-/
theorem pow_two_lt_pillar
    {j a : ℕ}
    (hja : j < a) :
    2 ^ j < pillar a := by
  unfold pillar
  exact pow_two_lt_pow_two hja


/--
A dyadic entry below level `a` is strictly below the corresponding pillar.
-/
theorem DyadicBelow.lt_pillar
    {a d : ℕ}
    (hd : DyadicBelow a d) :
    d < pillar a := by
  rcases hd with ⟨j, hj, rfl⟩
  exact pow_two_lt_pillar hj


/--
Every dyadic entry is nonzero.
-/
theorem DyadicBelow.ne_zero
    {a d : ℕ}
    (hd : DyadicBelow a d) :
    d ≠ 0 := by
  exact Nat.ne_of_gt hd.pos


/-!
## 3. Dyadic powers divide canonical profiles
-/

/--
The pillar divides its canonical profile.
-/
theorem pillar_dvd_profile
    (L : ℕ) :
    L ∣ profile L := by
  refine ⟨oddPillar L, ?_⟩
  rfl


/--
The dyadic pillar divides its canonical candidate.
-/
theorem pillar_dvd_candidate
    (a : ℕ) :
    pillar a ∣ candidate a := by
  refine ⟨oddPillar (pillar a), ?_⟩
  rw [candidate_eq_profile]


/--
Every power `2^j` with `j ≤ a` divides the canonical candidate at level `a`.
-/
theorem pow_two_dvd_candidate
    {j a : ℕ}
    (hja : j ≤ a) :
    2 ^ j ∣ candidate a := by
  exact
    dvd_trans
      (pow_two_dvd_pillar hja)
      (pillar_dvd_candidate a)


/--
Every lower dyadic entry divides the canonical candidate.
-/
theorem dyadicBelow_dvd_candidate
    {a d : ℕ}
    (hd : DyadicBelow a d) :
    d ∣ candidate a := by
  rcases hd with ⟨j, hj, rfl⟩
  exact pow_two_dvd_candidate (Nat.le_of_lt hj)


/--
Every lower dyadic entry is a lower divisor of the canonical candidate.
-/
theorem dyadicBelow_lowerDivisor_candidate
    {a d : ℕ}
    (hd : DyadicBelow a d) :
    LowerDivisor (candidate a) (pillar a) d := by
  constructor
  · exact dyadicBelow_dvd_candidate hd
  · exact hd.lt_pillar


/-!
## 4. Basic consequences of a lower dyadic pattern
-/

/--
Under a lower dyadic pattern, every prescribed dyadic entry occurs as a lower
divisor.
-/
theorem pattern_contains_dyadic
    {M L a d : ℕ}
    (hpattern : lowerDyadicPattern M L a)
    (hd : DyadicBelow a d) :
    LowerDivisor M L d := by
  exact lowerDivisor_of_dyadicBelow hpattern hd


/--
Under a lower dyadic pattern, every lower divisor is dyadic.
-/
theorem pattern_lower_is_dyadic
    {M L a d : ℕ}
    (hpattern : lowerDyadicPattern M L a)
    (hd : LowerDivisor M L d) :
    DyadicBelow a d := by
  exact dyadicBelow_of_lowerDivisor hpattern hd


/--
Under a lower dyadic pattern, `1` occurs below the pillar whenever `a ≥ 1`.
-/
theorem one_lowerDivisor_of_pattern
    {M L a : ℕ}
    (ha : 1 ≤ a)
    (hpattern : lowerDyadicPattern M L a) :
    LowerDivisor M L 1 := by
  apply lowerDivisor_of_dyadicBelow hpattern
  refine ⟨0, ?_, ?_⟩
  · omega
  · simp


/--
Under a lower dyadic pattern, the largest prescribed dyadic power
`2^(a-1)` occurs below the pillar whenever `a ≥ 1`.
-/
theorem top_dyadic_lowerDivisor
    {M L a : ℕ}
    (ha : 1 ≤ a)
    (hpattern : lowerDyadicPattern M L a) :
    LowerDivisor M L (2 ^ (a - 1)) := by
  apply lowerDivisor_of_dyadicBelow hpattern
  refine ⟨a - 1, ?_, rfl⟩
  omega


/-!
## 5. Characterization of divisors of a dyadic pillar
-/

/--
A divisor of `2^a` is itself a power of two of exponent at most `a`.
-/
theorem divisor_of_pillar_is_pow_two
    {a d : ℕ}
    (hd : d ∣ pillar a) :
    ∃ j : ℕ,
      j ≤ a ∧
      d = 2 ^ j := by
  unfold pillar at hd
  exact (Nat.dvd_prime_pow Nat.prime_two).1 hd


/--
A proper divisor of the pillar is one of the lower dyadic powers.
-/
theorem proper_divisor_of_pillar_is_dyadicBelow
    {a d : ℕ}
    (hdvd : d ∣ pillar a)
    (hdlt : d < pillar a) :
    DyadicBelow a d := by
  rcases divisor_of_pillar_is_pow_two hdvd with
    ⟨j, hja, rfl⟩

  refine ⟨j, ?_, rfl⟩

  by_contra hnot

  have haj : a ≤ j := by
    omega

  have hja_eq : j = a := by
    exact Nat.le_antisymm hja haj

  subst j

  exact (Nat.lt_irrefl (pillar a)) hdlt


/--
The proper divisors of a dyadic pillar are exactly the lower dyadic entries.
-/
theorem lowerDivisor_pillar_iff_dyadicBelow
    {a d : ℕ} :
    LowerDivisor (pillar a) (pillar a) d ↔
      DyadicBelow a d := by
  constructor

  · intro hd
    exact
      proper_divisor_of_pillar_is_dyadicBelow
        hd.dvd
        hd.lt

  · intro hd
    constructor
    · exact dyadicBelow_dvd_pillar hd
    · exact hd.lt_pillar


/-!
## 6. Uniqueness of dyadic representation
-/

/--
Two powers of two are equal only when their exponents are equal.
-/
theorem pow_two_injective :
    Function.Injective (fun n : ℕ => (2 : ℕ) ^ n) := by
  exact pow_two_strictMono.injective


/--
The exponent occurring in a `DyadicBelow` representation is unique.
-/
theorem dyadic_exponent_unique
    {a d i j : ℕ}
    (_hi : i < a)
    (_hj : j < a)
    (hdi : d = 2 ^ i)
    (hdj : d = 2 ^ j) :
    i = j := by
  apply pow_two_injective

  calc
    2 ^ i = d := hdi.symm
    _ = 2 ^ j := hdj


/-!
## 7. Canonical dyadic lower layer
-/

/--
Every prescribed dyadic entry is automatically a lower divisor of the
canonical candidate, independently of primality of the odd factor.

The difficult direction of `divisor_structure` is the converse: proving that
there are no additional lower divisors exactly when the odd factor is prime.
-/
theorem canonical_candidate_contains_dyadic_layer
    (a : ℕ) :
    ∀ d : ℕ,
      DyadicBelow a d →
        LowerDivisor (candidate a) (pillar a) d := by
  intro d hd
  exact dyadicBelow_lowerDivisor_candidate hd


/--
For the canonical candidate, the public lower dyadic pattern is equivalent to
the assertion that every lower divisor is dyadic, because the inclusion of the
dyadic layer is unconditional.
-/
theorem candidate_lowerDyadicPattern_iff_no_extra
    (a : ℕ) :
    lowerDyadicPattern (candidate a) (pillar a) a ↔
      ∀ d : ℕ,
        LowerDivisor (candidate a) (pillar a) d →
          DyadicBelow a d := by
  constructor

  · intro hpattern d hd
    exact dyadicBelow_of_lowerDivisor hpattern hd

  · intro hnoextra d
    constructor

    · intro hd
      exact hnoextra d hd

    · intro hd
      exact dyadicBelow_lowerDivisor_candidate hd


/-!
## 8. Odd numbers cannot be nontrivial dyadic entries
-/

/--
An odd power of two is necessarily equal to `1`.
-/
theorem pow_two_eq_one_of_odd
    {j : ℕ}
    (hodd : Odd ((2 : ℕ) ^ j)) :
    (2 : ℕ) ^ j = 1 := by
  by_cases hj : j = 0

  · subst j
    simp

  · have heven : Even ((2 : ℕ) ^ j) := by
      exact
        (Nat.even_pow).2
          ⟨by norm_num, hj⟩

    have hnotEven : ¬ Even ((2 : ℕ) ^ j) := by
      exact
        (Nat.not_even_iff_odd).2 hodd

    exact False.elim (hnotEven heven)


/--
An odd dyadic entry is necessarily equal to `1`.
-/
theorem DyadicBelow.eq_one_of_odd
    {a d : ℕ}
    (hd : DyadicBelow a d)
    (hodd : Odd d) :
    d = 1 := by
  rcases hd with ⟨j, _hj, rfl⟩
  exact pow_two_eq_one_of_odd hodd


/--
A nontrivial odd natural number cannot occur in a dyadic lower layer.
-/
theorem not_dyadicBelow_of_odd_of_one_lt
    {a d : ℕ}
    (hodd : Odd d)
    (hdgt : 1 < d) :
    ¬ DyadicBelow a d := by
  intro hd

  have heq : d = 1 :=
    hd.eq_one_of_odd hodd

  omega


end SR
end EvenPerfectStructure