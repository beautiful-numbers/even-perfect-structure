-- FILE: EvenPerfectStructure/DivisorPattern.lean
/-
IMPORT CLASSIFICATION

- EvenPerfectStructure.Basic
  defs:
    pillar
    oddPillar
    candidate
    lowerDyadicPattern
  thms:
    pillar_pos
    candidate_pos
    candidate_eq_profile

- EvenPerfectStructure.SR.Definitions
  defs:
    LowerDivisor
    DyadicBelow
  thms:
    LowerDivisor.dvd
    LowerDivisor.lt

- EvenPerfectStructure.SR.Dyadic
  thms:
    pow_two_lt_pillar
    pow_two_dvd_pow_two
    proper_divisor_of_pillar_is_dyadicBelow
    dyadicBelow_lowerDivisor_candidate
-/

import EvenPerfectStructure.SR.Dyadic

/-!
# EvenPerfectStructure.DivisorPattern

Primality detection from the recovered internal divisor profile.

The structural development preceding this module starts with arbitrary
factorization data and recovers the profile

`M = L(2L - 1)`

from the dyadic pillar and median relation.

This module does not derive that profile again and does not use any external
classification theorem. Instead, it studies the divisor pattern of the
structurally recovered profile.

Using the public notation

`candidate a = pillar a * oddPillar (pillar a)`,

with

`pillar a = 2^a`

and

`oddPillar L = 2L - 1`,

we prove that the exact dyadic lower-divisor pattern is equivalent to
primality of the recovered odd pillar.

The logical role of this module is therefore:

`recovered structural profile`
    →
`internal divisor discrimination`
    →
`primality of the odd pillar`.

The explicit composite-factor obstruction is exposed separately in
`Certification.lean`.
-/

namespace EvenPerfectStructure


/-!
## 1. Size relations inside the recovered profile
-/

/--
At every nontrivial dyadic level `a ≥ 1`, the pillar is at least `2`.
-/
theorem pillar_two_le
    {a : ℕ}
    (ha : 1 ≤ a) :
    2 ≤ pillar a := by
  have hlt :
      (2 : ℕ) ^ 0 < pillar a := by
    exact
      SR.pow_two_lt_pillar
        (j := 0)
        (a := a)
        (by omega)

  simp at hlt
  omega


/--
For a nontrivial dyadic pillar, the recovered odd pillar `2L - 1`
lies strictly above `L`.
-/
theorem pillar_lt_oddPillar
    {a : ℕ}
    (ha : 1 ≤ a) :
    pillar a < oddPillar (pillar a) := by
  have hL :
      2 ≤ pillar a :=
    pillar_two_le ha

  rw [oddPillar]
  omega


/--
At every nontrivial dyadic level, the recovered odd pillar is at least `2`.
-/
theorem two_le_oddPillar
    {a : ℕ}
    (ha : 1 ≤ a) :
    2 ≤ oddPillar (pillar a) := by
  have hL :
      2 ≤ pillar a :=
    pillar_two_le ha

  rw [oddPillar]
  omega


/-!
## 2. Prime odd pillar implies the exact lower pattern
-/

/--
Assume that the recovered odd pillar is prime.

Then every divisor of the recovered profile lying strictly below the
dyadic pillar already divides the pillar itself.

A divisor of

`pillar a * oddPillar (pillar a)`

decomposes into a divisor of the pillar and a divisor of the prime odd
pillar. The odd-pillar component is therefore either `1` or the whole
odd pillar. The second possibility cannot occur below `pillar a`, because
the odd pillar is strictly larger than the pillar.
-/
theorem lower_divisor_dvd_pillar_of_prime
    {a d : ℕ}
    (ha : 1 ≤ a)
    (hprime :
      Nat.Prime (oddPillar (pillar a)))
    (hdvd :
      d ∣ candidate a)
    (hdlt :
      d < pillar a) :
    d ∣ pillar a := by
  have hcand_ne :
      candidate a ≠ 0 :=
    Nat.ne_of_gt (candidate_pos a)

  have hdmem :
      d ∈ (candidate a).divisors := by
    exact
      Nat.mem_divisors.mpr
        ⟨hdvd, hcand_ne⟩

  rw [candidate_eq_profile, Nat.divisors_mul] at hdmem

  rcases Finset.mem_mul.mp hdmem with
    ⟨x, hx, y, hy, hxy⟩

  have hxdvd :
      x ∣ pillar a :=
    (Nat.mem_divisors.mp hx).1

  have hydvd :
      y ∣ oddPillar (pillar a) :=
    (Nat.mem_divisors.mp hy).1

  by_cases hyone : y = 1

  · have hxd :
        x = d := by
      simpa [hyone] using hxy

    simpa [hxd] using hxdvd

  · have hodd_eq_y :
        oddPillar (pillar a) = y := by
      exact
        (hprime.dvd_iff_eq hyone).mp hydvd

    have hxpos :
        0 < x := by
      exact
        Nat.pos_of_dvd_of_pos
          hxdvd
          (pillar_pos a)

    have hodd_gt :
        pillar a < oddPillar (pillar a) :=
      pillar_lt_oddPillar ha

    have hxy' :
        x * oddPillar (pillar a) = d := by
      calc
        x * oddPillar (pillar a)
            = x * y := by
                rw [hodd_eq_y]
        _ = d := hxy

    nlinarith


/--
If the recovered odd pillar is prime, every lower divisor of the
structural profile is dyadic.
-/
theorem lower_divisor_is_dyadic_of_prime
    {a d : ℕ}
    (ha : 1 ≤ a)
    (hprime :
      Nat.Prime (oddPillar (pillar a)))
    (hd :
      SR.LowerDivisor
        (candidate a)
        (pillar a)
        d) :
    SR.DyadicBelow a d := by
  have hdvd_pillar :
      d ∣ pillar a :=
    lower_divisor_dvd_pillar_of_prime
      ha
      hprime
      hd.dvd
      hd.lt

  exact
    SR.proper_divisor_of_pillar_is_dyadicBelow
      hdvd_pillar
      hd.lt


/--
Primality of the recovered odd pillar implies the exact dyadic
lower-divisor pattern.
-/
theorem lowerDyadicPattern_of_prime
    {a : ℕ}
    (ha : 1 ≤ a)
    (hprime :
      Nat.Prime (oddPillar (pillar a))) :
    lowerDyadicPattern
      (candidate a)
      (pillar a)
      a := by
  intro d

  constructor

  · intro hd

    exact
      lower_divisor_is_dyadic_of_prime
        ha
        hprime
        hd

  · intro hd

    exact
      SR.dyadicBelow_lowerDivisor_candidate hd


/-!
## 3. Proper factors of the odd pillar create lower intruders
-/

/--
Every proper nontrivial divisor of the recovered odd pillar lies strictly
below the dyadic pillar.

If

`q ∣ (2L - 1)`

and `q` is a proper nontrivial divisor, then the complementary factor is
at least `2`. Hence

`2q ≤ 2L - 1`,

which forces

`q < L`.
-/
theorem proper_divisor_oddPillar_lt_pillar
    {a q : ℕ}
    (ha : 1 ≤ a)
    (_hq2 : 2 ≤ q)
    (hqdvd :
      q ∣ oddPillar (pillar a))
    (hqlt :
      q < oddPillar (pillar a)) :
    q < pillar a := by
  rcases hqdvd with
    ⟨c, hc⟩

  have hL2 :
      2 ≤ pillar a :=
    pillar_two_le ha

  have hc2 :
      2 ≤ c := by
    by_contra hnot

    have hc_le :
        c ≤ 1 := by
      omega

    interval_cases c <;>
      simp_all [oddPillar]

  have hc' :
      2 * pillar a - 1 = q * c := by
    simpa [oddPillar] using hc

  have hq2c :
      q * 2 ≤ q * c :=
    Nat.mul_le_mul_left q hc2

  have h2q :
      2 * q ≤ q * c := by
    simpa [Nat.mul_comm] using hq2c

  by_contra hnot

  have hLq :
      pillar a ≤ q := by
    omega

  have h2L2q :
      2 * pillar a ≤ 2 * q := by
    omega

  have h2Lqc :
      2 * pillar a ≤ q * c :=
    le_trans h2L2q h2q

  omega


/--
Every divisor of the recovered odd pillar also divides the recovered
structural profile.
-/
theorem oddPillar_divisor_dvd_candidate
    {a q : ℕ}
    (hq :
      q ∣ oddPillar (pillar a)) :
    q ∣ candidate a := by
  rcases hq with
    ⟨c, hc⟩

  refine
    ⟨pillar a * c, ?_⟩

  rw [candidate_eq_profile]
  rw [hc]

  ac_rfl


/--
A nontrivial divisor of the recovered odd pillar cannot be dyadic.

Indeed, if such a divisor were `2^j` with `j ≥ 1`, then `2` would divide
the recovered odd pillar `2L - 1`, which is impossible.
-/
theorem oddPillar_divisor_not_dyadic
    {a q : ℕ}
    (hq2 : 2 ≤ q)
    (hqdvd :
      q ∣ oddPillar (pillar a)) :
    ¬ SR.DyadicBelow a q := by
  intro hdyadic

  rcases hdyadic with
    ⟨j, _hja, hqpow⟩

  have hj :
      1 ≤ j := by
    by_contra hnot

    have hj0 :
        j = 0 := by
      omega

    subst j

    simp at hqpow
    omega

  have htwo_pow :
      (2 : ℕ) ∣ 2 ^ j := by
    have h :
        2 ^ 1 ∣ 2 ^ j :=
      SR.pow_two_dvd_pow_two hj

    simpa using h

  have htwo_q :
      2 ∣ q := by
    rw [hqpow]
    exact htwo_pow

  have htwo_odd :
      2 ∣ oddPillar (pillar a) :=
    dvd_trans htwo_q hqdvd

  rcases htwo_odd with
    ⟨t, ht⟩

  have hLpos :
      0 < pillar a :=
    pillar_pos a

  have ht' :
      2 * pillar a - 1 = 2 * t := by
    simpa [oddPillar] using ht

  omega


/-!
## 4. Exact lower pattern forces primality
-/

/--
If the recovered structural profile has the exact lower dyadic pattern,
then its odd pillar must be prime.

If the odd pillar were composite, it would possess a nontrivial proper
divisor `q`. The preceding structural estimates place `q` strictly below
the pillar, while `q` also divides the full profile.

The lower-divisor pattern would therefore force `q` to be dyadic, in
contradiction with the fact that a nontrivial divisor of `2L - 1` cannot
be dyadic.
-/
theorem prime_of_lowerDyadicPattern
    {a : ℕ}
    (ha : 1 ≤ a)
    (hpattern :
      lowerDyadicPattern
        (candidate a)
        (pillar a)
        a) :
    Nat.Prime (oddPillar (pillar a)) := by
  have hk2 :
      2 ≤ oddPillar (pillar a) :=
    two_le_oddPillar ha

  by_contra hnotprime

  obtain
    ⟨q, hqdvd, hq2, hqlt⟩ :=
      (Nat.not_prime_iff_exists_dvd_lt hk2).mp
        hnotprime

  have hqltL :
      q < pillar a :=
    proper_divisor_oddPillar_lt_pillar
      ha
      hq2
      hqdvd
      hqlt

  have hqcand :
      q ∣ candidate a :=
    oddPillar_divisor_dvd_candidate
      hqdvd

  have hdyadic :
      SR.DyadicBelow a q :=
    (hpattern q).1
      ⟨hqcand, hqltL⟩

  exact
    (oddPillar_divisor_not_dyadic
      hq2
      hqdvd)
      hdyadic


/-!
## 5. Advertised internal divisor theorem
-/

/--
### Internal divisor-structure theorem

For every nontrivial dyadic level `a`, consider the structural profile
previously recovered from the pillar and median constraints:

`M = 2^a (2^(a+1) - 1)`.

Its divisors strictly below the pillar `2^a` are exactly

`1, 2, 4, ..., 2^(a-1)`

if and only if its recovered odd pillar

`2^(a+1) - 1`

is prime.

Thus primality is detected internally by the absence of any non-dyadic
divisor below the structural pillar.
-/
theorem divisor_structure
    (a : ℕ)
    (ha : 1 ≤ a) :
    lowerDyadicPattern
        (candidate a)
        (pillar a)
        a ↔
      Nat.Prime
        (oddPillar (pillar a)) := by
  constructor

  · intro hpattern

    exact
      prime_of_lowerDyadicPattern
        ha
        hpattern

  · intro hprime

    exact
      lowerDyadicPattern_of_prime
        ha
        hprime


end EvenPerfectStructure