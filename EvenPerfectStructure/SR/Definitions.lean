-- FILE: EvenPerfectStructure/SR/Definitions.lean
/-
IMPORT CLASSIFICATION

- EvenPerfectStructure.Basic
  defs:
    pillar
    lowerDyadicPattern
    InternalStructure
-/

import EvenPerfectStructure.Basic

/-!
# EvenPerfectStructure.SR.Definitions

Elementary structural vocabulary for the sigma-rectangle development.

This module introduces internal predicates used by the SR proof layers:

* lower divisors;
* upper divisors;
* dyadic entries below a pillar;
* mirror pairs;
* coprime structural factorizations;
* dyadic pillars;
* the structural median identity;
* explicit structural witnesses.

No substantive divisor-pattern, primality, perfection, or calibration theorem
is proved here.

The public statement surface remains the one defined in `Challenge.lean`;
the definitions in this module are proof-development abstractions only.
-/

namespace EvenPerfectStructure
namespace SR


/-!
## 1. Divisor strata
-/

/--
`LowerDivisor M L d` means that `d` is a divisor of `M` lying strictly
below the pillar `L`.
-/
def LowerDivisor (M L d : ℕ) : Prop :=
  d ∣ M ∧ d < L


/--
`UpperDivisor M L d` means that `d` is a divisor of `M` lying strictly
above the pillar `L`.
-/
def UpperDivisor (M L d : ℕ) : Prop :=
  d ∣ M ∧ L < d


/--
`PillarDivisor M L` means that the pillar itself divides `M`.
-/
def PillarDivisor (M L : ℕ) : Prop :=
  L ∣ M


@[simp]
theorem lowerDivisor_iff
    {M L d : ℕ} :
    LowerDivisor M L d ↔
      d ∣ M ∧ d < L := by
  rfl


@[simp]
theorem upperDivisor_iff
    {M L d : ℕ} :
    UpperDivisor M L d ↔
      d ∣ M ∧ L < d := by
  rfl


@[simp]
theorem pillarDivisor_iff
    {M L : ℕ} :
    PillarDivisor M L ↔
      L ∣ M := by
  rfl


theorem LowerDivisor.dvd
    {M L d : ℕ}
    (h : LowerDivisor M L d) :
    d ∣ M := by
  exact h.1


theorem LowerDivisor.lt
    {M L d : ℕ}
    (h : LowerDivisor M L d) :
    d < L := by
  exact h.2


theorem UpperDivisor.dvd
    {M L d : ℕ}
    (h : UpperDivisor M L d) :
    d ∣ M := by
  exact h.1


theorem UpperDivisor.gt
    {M L d : ℕ}
    (h : UpperDivisor M L d) :
    L < d := by
  exact h.2


/-!
## 2. Dyadic entries
-/

/--
`DyadicBelow a d` means that `d` is one of

`1, 2, 4, ..., 2^(a-1)`.

Equivalently, `d = 2^j` for some `j < a`.
-/
def DyadicBelow (a d : ℕ) : Prop :=
  ∃ j : ℕ,
    j < a ∧
    d = 2 ^ j


@[simp]
theorem dyadicBelow_iff
    {a d : ℕ} :
    DyadicBelow a d ↔
      ∃ j : ℕ,
        j < a ∧
        d = 2 ^ j := by
  rfl


theorem dyadicBelow_of_lt
    {a j : ℕ}
    (hj : j < a) :
    DyadicBelow a (2 ^ j) := by
  exact ⟨j, hj, rfl⟩


theorem DyadicBelow.exists_exponent
    {a d : ℕ}
    (h : DyadicBelow a d) :
    ∃ j : ℕ,
      j < a ∧
      d = 2 ^ j := by
  exact h


theorem DyadicBelow.pos
    {a d : ℕ}
    (h : DyadicBelow a d) :
    0 < d := by
  rcases h with ⟨j, _hj, rfl⟩
  positivity


/-!
## 3. Bridge to the public lower-divisor pattern
-/

/--
The public predicate `lowerDyadicPattern` says precisely that the divisors
strictly below `L` are exactly the dyadic entries encoded by `DyadicBelow`.
-/
theorem lowerDyadicPattern_iff
    {M L a : ℕ} :
    lowerDyadicPattern M L a ↔
      ∀ d : ℕ,
        LowerDivisor M L d ↔
          DyadicBelow a d := by
  rfl


/--
A lower divisor is dyadic whenever the public lower-divisor pattern holds.
-/
theorem dyadicBelow_of_lowerDivisor
    {M L a d : ℕ}
    (hpattern : lowerDyadicPattern M L a)
    (hd : LowerDivisor M L d) :
    DyadicBelow a d := by
  exact (hpattern d).1 hd


/--
Every prescribed dyadic entry is a lower divisor whenever the public
lower-divisor pattern holds.
-/
theorem lowerDivisor_of_dyadicBelow
    {M L a d : ℕ}
    (hpattern : lowerDyadicPattern M L a)
    (hd : DyadicBelow a d) :
    LowerDivisor M L d := by
  exact (hpattern d).2 hd


/-!
## 4. Mirror relation
-/

/--
`MirrorPair M d e` means that `d` and `e` are complementary factors of `M`.

Mathematically:

`d * e = M`.

The quotient realization `d ↦ M / d` is developed in `SR/Mirror.lean`.
-/
def MirrorPair (M d e : ℕ) : Prop :=
  d * e = M


@[simp]
theorem mirrorPair_iff
    {M d e : ℕ} :
    MirrorPair M d e ↔
      d * e = M := by
  rfl


theorem MirrorPair.symm
    {M d e : ℕ}
    (h : MirrorPair M d e) :
    MirrorPair M e d := by
  unfold MirrorPair at h ⊢
  simpa [Nat.mul_comm] using h


/--
The left member of a mirror pair divides the ambient number.
-/
theorem MirrorPair.dvd_left
    {M d e : ℕ}
    (h : MirrorPair M d e) :
    d ∣ M := by
  unfold MirrorPair at h
  exact ⟨e, h.symm⟩


/--
The right member of a mirror pair divides the ambient number.
-/
theorem MirrorPair.dvd_right
    {M d e : ℕ}
    (h : MirrorPair M d e) :
    e ∣ M := by
  exact h.symm.dvd_left


/-!
## 5. Structural factorization
-/

/--
A structural factorization records

`M = k * L`

together with

`gcd(k,L) = 1`.
-/
def CoprimeFactorization (M k L : ℕ) : Prop :=
  M = k * L ∧
  Nat.Coprime k L


@[simp]
theorem coprimeFactorization_iff
    {M k L : ℕ} :
    CoprimeFactorization M k L ↔
      M = k * L ∧
      Nat.Coprime k L := by
  rfl


theorem CoprimeFactorization.eq
    {M k L : ℕ}
    (h : CoprimeFactorization M k L) :
    M = k * L := by
  exact h.1


theorem CoprimeFactorization.coprime
    {M k L : ℕ}
    (h : CoprimeFactorization M k L) :
    Nat.Coprime k L := by
  exact h.2


/-!
## 6. Dyadic pillar
-/

/--
`DyadicPillar L a` records that the structural pillar is exactly `2^a`.
-/
def DyadicPillar (L a : ℕ) : Prop :=
  L = 2 ^ a


@[simp]
theorem dyadicPillar_iff
    {L a : ℕ} :
    DyadicPillar L a ↔
      L = 2 ^ a := by
  rfl


theorem dyadicPillar_pillar (a : ℕ) :
    DyadicPillar (pillar a) a := by
  rfl


theorem DyadicPillar.eq_pillar
    {L a : ℕ}
    (h : DyadicPillar L a) :
    L = pillar a := by
  exact h


theorem DyadicPillar.pos
    {L a : ℕ}
    (h : DyadicPillar L a) :
    0 < L := by
  rw [h]
  positivity


/-!
## 7. Structural median identity
-/

/--
The structural median identity associated with exponent `a`, pillar `L`,
and complementary factor `k`:

`(∑ j < a, 2^j) + L = k`.

The geometric evaluation of this sum and the deduction

`k = 2L - 1`

belong to `SR/Median.lean`.
-/
def MedianIdentity (k L a : ℕ) : Prop :=
  (∑ j ∈ Finset.range a, 2 ^ j) + L = k


@[simp]
theorem medianIdentity_iff
    {k L a : ℕ} :
    MedianIdentity k L a ↔
      (∑ j ∈ Finset.range a, 2 ^ j) + L = k := by
  rfl


theorem MedianIdentity.eq
    {k L a : ℕ}
    (h : MedianIdentity k L a) :
    (∑ j ∈ Finset.range a, 2 ^ j) + L = k := by
  exact h


/-!
## 8. Structural witness
-/

/--
An explicit proof-development representation of one witness to
`InternalStructure M`.

Unlike `InternalStructure`, which existentially quantifies over `a`, `k`,
and `L`, this predicate keeps those parameters explicit.

It deliberately does not contain the conclusion

`k = 2L - 1`.
-/
def StructuralWitness
    (M k L a : ℕ) : Prop :=
  1 ≤ a ∧
  DyadicPillar L a ∧
  CoprimeFactorization M k L ∧
  lowerDyadicPattern M L a ∧
  MedianIdentity k L a


/--
Expanded characterization of `StructuralWitness`.
-/
@[simp]
theorem structuralWitness_iff
    {M k L a : ℕ} :
    StructuralWitness M k L a ↔
      1 ≤ a ∧
      L = 2 ^ a ∧
      M = k * L ∧
      Nat.Coprime k L ∧
      lowerDyadicPattern M L a ∧
      (∑ j ∈ Finset.range a, 2 ^ j) + L = k := by
  constructor

  · intro h
    rcases h with ⟨ha, hL, hfac, hpattern, hmedian⟩
    rcases hfac with ⟨hM, hcoprime⟩

    exact
      ⟨ha,
       hL,
       hM,
       hcoprime,
       hpattern,
       hmedian⟩

  · intro h
    rcases h with
      ⟨ha,
       hL,
       hM,
       hcoprime,
       hpattern,
       hmedian⟩

    exact
      ⟨ha,
       hL,
       ⟨hM, hcoprime⟩,
       hpattern,
       hmedian⟩


/--
The public predicate `InternalStructure M` is equivalent to the existence
of an explicit structural witness.
-/
theorem internalStructure_iff_exists_witness
    {M : ℕ} :
    InternalStructure M ↔
      ∃ a k L : ℕ,
        StructuralWitness M k L a := by
  constructor

  · intro h

    rcases h with
      ⟨a,
       k,
       L,
       ha,
       hL,
       hM,
       hcoprime,
       hpattern,
       hmedian⟩

    refine ⟨a, k, L, ?_⟩

    exact
      ⟨ha,
       hL,
       ⟨hM, hcoprime⟩,
       hpattern,
       hmedian⟩

  · intro h

    rcases h with ⟨a, k, L, hwitness⟩
    rcases hwitness with
      ⟨ha,
       hL,
       hfac,
       hpattern,
       hmedian⟩
    rcases hfac with ⟨hM, hcoprime⟩

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


/--
Every explicit structural witness yields the public `InternalStructure`
certificate.
-/
theorem StructuralWitness.toInternalStructure
    {M k L a : ℕ}
    (h : StructuralWitness M k L a) :
    InternalStructure M := by
  apply internalStructure_iff_exists_witness.mpr
  exact ⟨a, k, L, h⟩


/--
Every public `InternalStructure` certificate admits explicit witness data.
-/
theorem InternalStructure.exists_witness
    {M : ℕ}
    (h : InternalStructure M) :
    ∃ a k L : ℕ,
      StructuralWitness M k L a := by
  exact internalStructure_iff_exists_witness.mp h


end SR
end EvenPerfectStructure


