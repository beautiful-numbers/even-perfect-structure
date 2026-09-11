# Contributing

Contributions to `EvenPerfectStructure` are welcome when they preserve the
mathematical scope, proof architecture, and auditability of the formalization.

## Project principles

The development is organized around a structural treatment of even perfect
numbers.

In particular:

- the core structural theory must remain independent of the classical
  classification of even perfect numbers;
- uses of the classical classification belong only in the downstream audit
  layer;
- public theorem statements should remain mathematically meaningful and easy
  to compare with the accompanying manuscript;
- proof changes should remain explicit and auditable.

The main dependency direction is:

    Basic
      ↓
    SR.Definitions
      ↓
    SR.Dyadic
      ↓
    SR.Median
      ↓
    DivisorPattern
      ↓
    Certification

    Basic
      ↓
    Calibration
      ↓
    Sequential

    Certification + Calibration + Sequential
      ↓
    Main
      ↓
    Audit

`EvenPerfectStructure/Audit.lean` is intentionally downstream of the core
structural development.

## Repository layout

The main Lean sources are:

    EvenPerfectStructure/
      Basic.lean
      DivisorPattern.lean
      Certification.lean
      Calibration.lean
      Sequential.lean
      Main.lean
      Audit.lean
      SR/
        Definitions.lean
        Dyadic.lean
        Median.lean

Palomar-facing files are:

    Challenge.lean
    Solution.lean
    comparator.json
    formalization.yaml

## Lean version

The project uses the Lean and Mathlib versions pinned by the repository.

Before contributing, use the committed toolchain and dependencies rather than
upgrading Lean or Mathlib independently.

## Building

From the repository root:

    lake build

Individual files can also be checked directly, for example:

    lake env lean EvenPerfectStructure/Audit.lean
    lake env lean Challenge.lean
    lake env lean Solution.lean

## Proof requirements

Contributions to the proof library must not introduce:

- `sorry`;
- `admit`;
- new axioms;
- unnecessary dependence on the classical audit layer.

`Challenge.lean` is the exception: its advertised theorem bodies intentionally
contain `sorry` because it serves as the independently auditable challenge
surface.

Proofs should prefer clear, local, auditable arguments over opaque automation
when practical.

## Public API

Changes to public definitions or advertised theorem statements should be made
carefully.

The current Comparator surface includes:

    EvenPerfectStructure.median_identity_recovers_profile
    EvenPerfectStructure.divisor_structure
    EvenPerfectStructure.composite_odd_factor_breaks_pattern
    EvenPerfectStructure.internal_structure_implies_evenPerfect
    EvenPerfectStructure.evenPerfect_iff_internalStructure
    EvenPerfectStructure.divisor_pattern_iff_evenPerfect
    EvenPerfectStructure.calibration_bound
    EvenPerfectStructure.profile_calibration_identity
    EvenPerfectStructure.calibration_tends_to_eight
    EvenPerfectStructure.calibration_transition

Changes to these declarations may require corresponding updates to:

    Challenge.lean
    Solution.lean
    comparator.json
    formalization.yaml
    README.md

## Imports

Avoid introducing import cycles.

In particular:

    Main → Audit

is permitted, while

    Audit → Main → Audit

is not.

The root module imports the completed public development through the audit
layer.

## File headers

Lean source files should retain the project header style:

    -- FILE: EvenPerfectStructure/Example.lean
    /-
    IMPORT CLASSIFICATION

    - EvenPerfectStructure.Basic
      defs:
        ...
      thms:
        ...
    -/

List the project declarations actually used by the file.

## Dependency changes

After modifying Lake dependencies, regenerate the manifest:

    lake update

Commit dependency changes together with the resulting `lake-manifest.json`.

## Validation

Before opening a pull request or submitting a patch, check at least:

    lake build

For changes affecting the Palomar surface, also verify:

- `Challenge.lean`;
- `Solution.lean`;
- `comparator.json`;
- permitted axioms;
- Comparator;
- NanoDa when available.

## Scope

The current formalization covers the structural and calibration core of:

> Daniel Sautot, *Structural Calibration and Sigma Distribution of Even Perfect Numbers*

The present Palomar scope does not include the manuscript's full
structural-distribution framework, enumeration, digit-based distribution, or
algorithmic scanning.

Contributions extending those areas should be kept modular and should not alter
the meaning of the existing structural core without discussion.

## Attribution

The project and mathematical architecture are by Daniel Sautot.

When contributing substantial mathematical or formalization changes, describe
clearly what was changed and why, including any effect on the correspondence
between Lean statements and the manuscript.