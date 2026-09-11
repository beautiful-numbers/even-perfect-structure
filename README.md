# EvenPerfectStructure

Machine-checked Lean 4 formalization of the structural and calibration core of:

> **Daniel Sautot, _Structural Calibration and Sigma Distribution of Even Perfect Numbers_**  
> Zenodo: https://zenodo.org/records/17548227  
> Manuscript license: CC BY 4.0

Repository maintained by **Daniel Sautot**  
GitHub: [beautiful-numbers](https://github.com/beautiful-numbers)

## Overview

This repository formalizes the structural and calibration core of the manuscript
_Structural Calibration and Sigma Distribution of Even Perfect Numbers_.

The development isolates an internal dyadic divisor pattern for even perfect
numbers and proves in Lean 4 with Mathlib that this pattern:

1. Divisor-structure theorem — formalizes the internal dyadic divisor structure through InternalStructure, recovers the canonical factorization M = L(2L - 1) from the median identity, and identifies the canonical lower-divisor pattern.
Lean interfaces: InternalStructure, median_identity_recovers_profile, divisor_structure.
2. Structural certification theorem — proves that the internal divisor pattern detects whether the recovered odd factor is prime or composite, produces an explicit obstruction in the composite case, and certifies even perfection from the internal structure. The final audit establishes the converse and hence the global equivalence
EvenPerfect M ↔ InternalStructure M.
Lean interfaces: composite_odd_factor_breaks_pattern, internal_structure_implies_evenPerfect, evenPerfect_iff_internalStructure, divisor_pattern_iff_evenPerfect.
3. Calibration theorem — associates the canonical structural profile with the exact calibration identity
greatestProperDivisor(candidate a) = theta(pillar a) * gauge(pillar a),
proves the universal calibration bound, and establishes that theta is strictly increasing with theta(L) → 8.
Lean interfaces: calibration_bound, profile_calibration_identity, calibration_tends_to_eight.
4. Sequential-calibration theorem — formalizes the exact law governing the change of calibration between two dyadic structural levels a < b; in the current Lean development this is an exact transition law for arbitrary dyadic levels, not a successor/minimality theorem.
Lean interface: calibration_transition.
5. Structural-distribution framework — developed in the manuscript as the framework for counting and weighting perfect-number structures along structural, digit, and calibration axes, but intentionally outside the scope of this first Palomar formalization.

The structural development is intentionally separated from the final classical
compatibility audit.

The direction

```text
InternalStructure M → EvenPerfect M