# Contributing

Contributions to `EvenPerfectStructure` are welcome when they preserve the
mathematical scope, proof architecture, dependency direction, and auditability
of the formalization.

## Project principles

The development is organized around a structural treatment of even perfect
numbers.

In particular:

- the core structural theory must remain independent of the classical
  classification of even perfect numbers;
- any use of the classical Euler classification belongs only in the downstream
  audit layer;
- public theorem statements should remain mathematically meaningful, stable,
  and easy to compare with the accompanying manuscript;
- proof changes should remain explicit, local, and auditable;
- changes should preserve the distinction between the structural theory and
  the downstream completeness audit.

The intended dependency structure is:

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
      ↓
    Solution

`EvenPerfectStructure/Audit.lean` is intentionally downstream of the core
structural development.

The structural implication

    InternalStructure M → EvenPerfect M

must remain established independently of the classical classification.

The reverse compatibility implication

    EvenPerfect M → InternalStructure M

belongs to `Audit.lean`, where the classical Euler completeness argument is
reconstructed from standard Mathlib infrastructure.

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

Additional project files include:

    README.md
    CONTRIBUTING.md
    LICENSE
    lakefile.toml
    lake-manifest.json
    lean-toolchain

## Lean version and dependencies

The project uses the Lean and Mathlib versions pinned by the repository.

Before contributing, use the committed toolchain and dependency manifest rather
than upgrading Lean or Mathlib independently.

Do not change the Lean or Mathlib revision unless the change is intentional,
tested, and committed together with all resulting dependency updates.

## Building

From the repository root:

    lake build

Individual modules can also be checked directly, for example:

    lake env lean EvenPerfectStructure/Audit.lean
    lake env lean Challenge.lean
    lake env lean Solution.lean

For module-specific debugging, it is also useful to run:

    lake build EvenPerfectStructure.Audit
    lake build Solution

## Proof requirements

Contributions to the proof library must not introduce:

- `sorry`;
- `admit`;
- new project axioms;
- unnecessary dependence on the downstream audit layer;
- hidden reliance on the classical classification in upstream structural
  modules.

`Challenge.lean` is the deliberate exception: its advertised theorem bodies
contain `sorry` because it is the independently auditable challenge surface
used by Comparator.

Proofs should prefer clear, local, kernel-checkable arguments over opaque
automation when practical.

Use of standard Lean/Mathlib axioms such as:

    propext
    Quot.sound
    Classical.choice

is permitted where required by the imported mathematical library and by the
Comparator configuration.

## Public API

Changes to public definitions or advertised theorem statements should be made
carefully.

The current Comparator theorem surface includes:

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

The current Comparator definition surface includes:

    EvenPerfectStructure.pillar
    EvenPerfectStructure.oddPillar
    EvenPerfectStructure.profile
    EvenPerfectStructure.candidate
    EvenPerfectStructure.lowerDyadicPattern
    EvenPerfectStructure.EvenPerfect
    EvenPerfectStructure.InternalStructure
    EvenPerfectStructure.greatestProperDivisor
    EvenPerfectStructure.gauge
    EvenPerfectStructure.theta

Changes to any of these declarations may require corresponding updates to:

    Challenge.lean
    Solution.lean
    comparator.json
    formalization.yaml
    README.md

When a public theorem is changed, check that its name and type remain exactly
aligned between the Challenge and Solution environments.

## Imports and dependency direction

Avoid introducing import cycles.

The intended downstream dependency direction is:

    Main
      ↓
    Audit
      ↓
    Solution

That is:

- `Audit.lean` may import `Main.lean`;
- `Main.lean` must never import `Audit.lean`;
- `Solution.lean` may import `Audit.lean`;
- no upstream structural module may depend on `Audit.lean`.

In particular, the following modules must remain independent of the audit
layer:

    Basic
    SR.Definitions
    SR.Dyadic
    SR.Median
    DivisorPattern
    Certification
    Calibration
    Sequential
    Main

This separation is mathematically significant: it ensures that the structural
derivation is not circularly dependent on the classical completeness audit.

## Classical audit policy

`EvenPerfectStructure/Audit.lean` is the only module allowed to reconstruct
the classical Euler completeness direction.

The audit currently uses standard Mathlib modules, including arithmetic
functions and Mersenne-number infrastructure, and does not import
`Archive.Wiedijk100Theorems.PerfectNumbers` or any other `Archive.*` module.

Do not reintroduce `Archive.*` dependencies without checking compatibility with
the Palomar build environment.

The audit should remain downstream and should not be used to prove upstream
structural theorems.

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

The import-classification block should list the project declarations actually
used by the file.

Do not list obsolete imports or declarations.

## Dependency changes

After intentionally modifying Lake dependencies, regenerate the manifest with:

    lake update

Commit dependency changes together with the resulting:

    lake-manifest.json

Avoid running dependency updates unnecessarily, because Palomar verification
is performed against the exact committed dependency graph.

## Palomar validation

Before opening a pull request or submitting a patch, check at least:

    lake build

For changes affecting the Palomar-facing surface, also verify:

- `Challenge.lean` builds;
- `Solution.lean` builds;
- `comparator.json` lists the intended declarations;
- Challenge and Solution expose the same compared statement types;
- the permitted axiom list is still accurate;
- `formalization.yaml` validates against the current schema;
- Comparator succeeds;
- NanoDa succeeds when available.

A typical metadata validation command is:

    python -m check_jsonschema \
      --schemafile https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json \
      formalization.yaml

For final Palomar submission, validation must be performed against the exact
commit being submitted.

## Scope

The current formalization covers the structural and calibration core of:

> Daniel Sautot, *Structural Calibration and Sigma Distribution of Even Perfect Numbers*

The present Palomar scope includes:

- the internal dyadic structural certificate;
- recovery of the canonical profile from the median identity;
- characterization of the canonical lower-divisor pattern by primality of the
  odd factor;
- explicit obstruction in the composite odd-factor case;
- direct certification
  `InternalStructure → EvenPerfect`;
- downstream completeness audit
  `EvenPerfect → InternalStructure`;
- the global equivalence
  `EvenPerfect ↔ InternalStructure`;
- the canonical-family equivalence between lower dyadic divisor pattern and
  even perfection;
- the universal calibration bound;
- the exact canonical-profile calibration identity;
- monotonicity and convergence of the calibration factor to `8`;
- the exact calibration transition identity between arbitrary dyadic levels.

The current formalization intentionally does not include the manuscript's full:

- structural-distribution framework;
- enumeration theory;
- digit-based distribution theory;
- algorithmic scanning framework;
- structural-successor/minimality theorem;
- no-intermediate-certified-pillar theorem.

Extensions in those directions should be modular and should not alter the
meaning of the existing structural core without explicit discussion and
corresponding metadata updates.

## Fidelity to the manuscript

Contributions should preserve a clear distinction between:

- statements formalized exactly as in the manuscript;
- statements proved in a stronger form;
- statements formalized only in a restricted form;
- manuscript results intentionally outside the current Palomar scope.

If a contribution changes that relationship, update:

    formalization.yaml
    README.md

and, when relevant:

    Challenge.lean
    comparator.json

The current project deliberately documents known divergences and strengthened
statements in `formalization.yaml`.

## Attribution

The project and mathematical architecture are by Daniel Sautot.

When contributing substantial mathematical or formalization changes, describe
clearly:

- what was changed;
- why it was changed;
- whether the public theorem surface changed;
- whether the dependency structure changed;
- whether the correspondence between Lean statements and the manuscript
  changed;
- whether Palomar metadata or Comparator configuration must also be updated.

Substantial changes should preserve the auditability and provenance of the
formalization.