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

- recovers the canonical factorization
  `M = L(2L - 1)`;
- characterizes the canonical lower-divisor pattern by primality of the odd
  factor;
- detects composite odd factors through an explicit obstruction to the pattern;
- certifies even perfection directly from the recovered structural pattern;
- supports the calibration identities and asymptotic statements developed in
  the manuscript.

The structural development is intentionally separated from the final classical
compatibility audit.

The direction

```text
InternalStructure M → EvenPerfect M