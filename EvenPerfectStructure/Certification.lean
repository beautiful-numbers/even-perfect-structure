-- FILE: EvenPerfectStructure/Certification.lean
/-
IMPORT CLASSIFICATION

- EvenPerfectStructure.Basic
  defs:
    pillar
    oddPillar
    candidate
    lowerDyadicPattern
    EvenPerfect
    InternalStructure
  thms:
    pillar_pos
    candidate_eq_profile

- EvenPerfectStructure.SR.Median
  thms:
    sum_range_pow_two
    median_identity_recovers_profile

- EvenPerfectStructure.DivisorPattern
  thms:
    two_le_oddPillar
    proper_divisor_oddPillar_lt_pillar
    oddPillar_divisor_dvd_candidate
    divisor_structure
-/

import EvenPerfectStructure.SR.Median
import EvenPerfectStructure.DivisorPattern

/-!
# EvenPerfectStructure.Certification

Internal certification of the structurally recovered profile.

The preceding structural development starts with arbitrary factorization
data

`M = kL`

together with the dyadic pillar, coprimality, the exact lower-divisor
pattern, and the median identity.

The median relation recovers

`k = 2L - 1`

and

`M = L(2L - 1)`.

The divisor pattern then certifies primality of the recovered odd pillar.

This file performs two tasks:

1. if the recovered odd pillar is composite, construct an explicit odd
   lower-divisor intruder and certify failure of the dyadic pattern;

2. from the recovered structure and certified primality, prove directly
   that the resulting number is even and perfect.

The proof of perfection is carried out from divisor sums. No external
classification of even perfect numbers is used.

The reverse comparison

`EvenPerfect M → InternalStructure M`

does not belong to this structural certification module. It is reserved
for the final compatibility/audit layer.
-/

namespace EvenPerfectStructure


/-!
## 1. Parity of the recovered odd pillar
-/

/--
The recovered odd pillar `2L - 1` is not even.
-/
theorem oddPillar_not_even
    (a : ℕ) :
    ¬ Even (oddPillar (pillar a)) := by
  intro heven

  rcases heven with
    ⟨t, ht⟩

  have hLpos :
      0 < pillar a :=
    pillar_pos a

  rw [oddPillar] at ht

  omega


/--
Every divisor of the recovered odd pillar is odd.
-/
theorem odd_of_dvd_oddPillar
    {a q : ℕ}
    (hqdvd :
      q ∣ oddPillar (pillar a)) :
    Odd q := by
  apply (Nat.not_even_iff_odd).1

  intro hqeven

  rcases hqeven with
    ⟨t, ht⟩

  have htwo_q :
      2 ∣ q := by
    refine ⟨t, ?_⟩
    omega

  have htwo_odd :
      2 ∣ oddPillar (pillar a) :=
    dvd_trans htwo_q hqdvd

  rcases htwo_odd with
    ⟨u, hu⟩

  have hLpos :
      0 < pillar a :=
    pillar_pos a

  rw [oddPillar] at hu

  omega


/-!
## 2. Explicit lower intruder
-/

/--
If the recovered odd pillar is not prime, there exists an explicit
nontrivial odd divisor below the dyadic pillar which also divides the
full recovered profile.
-/
theorem exists_odd_intruder_of_not_prime
    (a : ℕ)
    (ha : 1 ≤ a)
    (hcomp :
      ¬ Nat.Prime (oddPillar (pillar a))) :
    ∃ q : ℕ,
      q ∣ oddPillar (pillar a) ∧
      1 < q ∧
      q < pillar a ∧
      Odd q ∧
      q ∣ candidate a := by
  have hk2 :
      2 ≤ oddPillar (pillar a) :=
    two_le_oddPillar ha

  obtain
    ⟨q, hqdvd, hq2, hqlt⟩ :=
      (Nat.not_prime_iff_exists_dvd_lt hk2).mp
        hcomp

  have hq1 :
      1 < q := by
    omega

  have hqltL :
      q < pillar a :=
    proper_divisor_oddPillar_lt_pillar
      ha
      hq2
      hqdvd
      hqlt

  have hqodd :
      Odd q :=
    odd_of_dvd_oddPillar
      hqdvd

  have hqcand :
      q ∣ candidate a :=
    oddPillar_divisor_dvd_candidate
      hqdvd

  exact
    ⟨q,
      hqdvd,
      hq1,
      hqltL,
      hqodd,
      hqcand⟩


/-!
## 3. Failure certificate for the lower dyadic pattern
-/

/--
Non-primality of the recovered odd pillar forces failure of the exact
lower dyadic divisor pattern.
-/
theorem lowerDyadicPattern_fails_of_not_prime
    (a : ℕ)
    (ha : 1 ≤ a)
    (hcomp :
      ¬ Nat.Prime (oddPillar (pillar a))) :
    ¬ lowerDyadicPattern
        (candidate a)
        (pillar a)
        a := by
  intro hpattern

  have hprime :
      Nat.Prime (oddPillar (pillar a)) :=
    (divisor_structure a ha).1
      hpattern

  exact hcomp hprime


/--
A composite recovered odd pillar simultaneously yields

* an explicit odd intruder below the pillar, and
* failure of the exact lower dyadic pattern.
-/
theorem composite_oddPillar_certificate
    (a : ℕ)
    (ha : 1 ≤ a)
    (hcomp :
      ¬ Nat.Prime (oddPillar (pillar a))) :
    (∃ q : ℕ,
      q ∣ oddPillar (pillar a) ∧
      1 < q ∧
      q < pillar a ∧
      Odd q ∧
      q ∣ candidate a) ∧
    ¬ lowerDyadicPattern
        (candidate a)
        (pillar a)
        a := by
  constructor

  · exact
      exists_odd_intruder_of_not_prime
        a
        ha
        hcomp

  · exact
      lowerDyadicPattern_fails_of_not_prime
        a
        ha
        hcomp


/-!
## 4. Advertised composite-factor certificate
-/

/--
### Composite odd factor breaks the pattern

If the structurally recovered odd pillar is not prime, a nontrivial odd
divisor occurs strictly below the dyadic pillar.

It divides both the odd pillar and the complete recovered profile, and
therefore forms an explicit non-dyadic lower-divisor intruder.
-/
theorem composite_odd_factor_breaks_pattern
    (a : ℕ)
    (ha : 1 ≤ a)
    (hcomp :
      ¬ Nat.Prime (oddPillar (pillar a))) :
    (∃ q : ℕ,
      q ∣ oddPillar (pillar a) ∧
      1 < q ∧
      q < pillar a ∧
      Odd q ∧
      q ∣ candidate a) ∧
    ¬ lowerDyadicPattern
        (candidate a)
        (pillar a)
        a := by
  exact
    composite_oddPillar_certificate
      a
      ha
      hcomp


/-!
## 5. Divisor sums of the recovered factors
-/

/--
The sum of all divisors of the dyadic pillar `2^a` is its recovered
odd pillar:

`σ(2^a) = 1 + 2 + ... + 2^a = 2^(a+1) - 1`.
-/
theorem sum_divisors_pillar
    (a : ℕ) :
    (∑ d ∈ (pillar a).divisors, d) =
      oddPillar (pillar a) := by
  rw [pillar]

  rw [
    Nat.sum_divisors_prime_pow
      (f := fun x : ℕ => x)
      Nat.prime_two
  ]

  rw [SR.sum_range_pow_two]

  rw [pow_succ]

  simp only [oddPillar]

  have hpow :
      0 < (2 : ℕ) ^ a := by
    positivity

  omega


/--
For a prime natural number `p`, the sum of its divisors is `p + 1`.
-/
theorem sum_divisors_of_prime
    {p : ℕ}
    (hp : Nat.Prime p) :
    (∑ d ∈ p.divisors, d) =
      p + 1 := by
  simpa using
    (hp.sum_divisors
      (f := fun x : ℕ => x))


/-!
## 6. Direct perfection of the recovered structural profile
-/

/--
A recovered profile with prime odd pillar is perfect.

This is proved directly from divisor sums:

* the pillar contributes divisor sum `2L - 1`;
* the prime odd factor contributes divisor sum `2L`;
* the two factors are coprime;
* hence the divisor sum of their product is twice the product.

No classification theorem for perfect numbers is used.
-/
theorem perfect_of_recovered_structure
    (M k L a : ℕ)
    (_ha : 1 ≤ a)
    (hL : L = 2 ^ a)
    (hM : M = k * L)
    (hcoprime : Nat.Coprime k L)
    (hk : k = 2 * L - 1)
    (hprime : Nat.Prime k) :
    Nat.Perfect M := by
  have hLpos :
      0 < L := by
    rw [hL]
    positivity

  have hkpos :
      0 < k :=
    hprime.pos

  have hMpos :
      0 < M := by
    rw [hM]
    exact Nat.mul_pos hkpos hLpos

  apply
    (Nat.perfect_iff_sum_divisors_eq_two_mul
      hMpos).2

  rw [hM]

  rw [hcoprime.sum_divisors_mul]

  have hsumK :
      (∑ d ∈ k.divisors, d) =
        k + 1 :=
    sum_divisors_of_prime
      hprime

  have hLp :
      L = pillar a := by
    simpa [pillar] using hL

  have hkOdd :
      k = oddPillar (pillar a) := by
    rw [oddPillar]
    rw [← hLp]
    exact hk

  have hsumL :
      (∑ d ∈ L.divisors, d) =
        k := by
    rw [hLp]
    rw [sum_divisors_pillar]
    exact hkOdd.symm

  rw [hsumK, hsumL]

  have hkSucc :
      k + 1 = 2 * L := by
    rw [hk]
    omega

  rw [hkSucc]

  ac_rfl


/--
The recovered structural profile is even whenever the dyadic level is
nontrivial.
-/
theorem even_of_recovered_structure
    (M k L a : ℕ)
    (ha : 1 ≤ a)
    (hL : L = 2 ^ a)
    (hM : M = k * L) :
    Even M := by
  have ha0 :
      a ≠ 0 := by
    omega

  have hLeven :
      Even L := by
    rw [hL]

    exact
      (Nat.even_pow).2
        ⟨by norm_num, ha0⟩

  rcases hLeven with
    ⟨t, ht⟩

  refine
    ⟨k * t, ?_⟩

  rw [hM, ht]

  simp [Nat.mul_add]


/-!
## 7. Structural certification implies even perfection
-/

/--
### Internal structure implies even perfection

Starting only from the advertised structural data:

* `a ≥ 1`,
* `L = 2^a`,
* `M = kL`,
* `gcd(k,L)=1`,
* the exact lower dyadic divisor pattern,
* the median identity,

the median first recovers

`k = 2L - 1`

and

`M = L(2L - 1)`.

The lower divisor pattern then certifies primality of `k`.

Finally, the divisor-sum computation above proves directly that `M` is
perfect, while the nontrivial dyadic pillar proves that `M` is even.
-/
theorem internal_structure_implies_evenPerfect
    (M k L a : ℕ)
    (ha : 1 ≤ a)
    (hL : L = 2 ^ a)
    (hM : M = k * L)
    (hcoprime : Nat.Coprime k L)
    (hpattern :
      lowerDyadicPattern M L a)
    (hmedian :
      (∑ j ∈ Finset.range a, 2 ^ j) + L = k) :
    EvenPerfect M := by
  have hrecover :
      k = 2 * L - 1 ∧
        M = L * (2 * L - 1) :=
    median_identity_recovers_profile
      M
      k
      L
      a
      ha
      hL
      hM
      hmedian

  have hk :
      k = 2 * L - 1 :=
    hrecover.1

  have hLp :
      L = pillar a := by
    simpa [pillar] using hL

  have hkOdd :
      k = oddPillar (pillar a) := by
    rw [oddPillar]
    rw [← hLp]
    exact hk

  have hMcandidate :
      M = candidate a := by
    calc
      M = k * L := hM
      _ = oddPillar (pillar a) * pillar a := by
        rw [hkOdd, hLp]
      _ = pillar a * oddPillar (pillar a) := by
        ac_rfl
      _ = candidate a := by
        rw [candidate_eq_profile]

  have hpatternCandidate :
      lowerDyadicPattern
        (candidate a)
        (pillar a)
        a := by
    rw [← hMcandidate]
    rw [← hLp]
    exact hpattern

  have hprimeOdd :
      Nat.Prime
        (oddPillar (pillar a)) :=
    (divisor_structure a ha).1
      hpatternCandidate

  have hprimeK :
      Nat.Prime k := by
    rw [hkOdd]
    exact hprimeOdd

  have hperfect :
      Nat.Perfect M :=
    perfect_of_recovered_structure
      M
      k
      L
      a
      ha
      hL
      hM
      hcoprime
      hk
      hprimeK

  have heven :
      Even M :=
    even_of_recovered_structure
      M
      k
      L
      a
      ha
      hL
      hM

  exact
    ⟨hperfect, heven⟩


/-!
## 8. Certification directly from `InternalStructure`
-/

/--
The bundled public structural predicate is sufficient to certify that `M`
is an even perfect number.
-/
theorem InternalStructure.toEvenPerfect
    {M : ℕ}
    (h : InternalStructure M) :
    EvenPerfect M := by
  rcases h with
    ⟨a, k, L,
      ha,
      hL,
      hM,
      hcoprime,
      hpattern,
      hmedian⟩

  exact
    internal_structure_implies_evenPerfect
      M
      k
      L
      a
      ha
      hL
      hM
      hcoprime
      hpattern
      hmedian


end EvenPerfectStructure