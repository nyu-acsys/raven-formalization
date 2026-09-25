# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- A typed verification-language intermediate representation with symbolic
  stores, typed expressions, procedure contracts, invariant operations,
  trusted atomic blocks, calls, and spawns.
- A resource Hoare calculus that represents the program stack separately
  from core separation-logic assertions and supports prenex resource binders.
- A certificate-producing atomicity and invariant-mask analysis, including
  structured certificates for conditionals, invariant access, and trusted
  atomic blocks.
- Resource-derivation normalization and a generic completeness theorem that
  connects successful restricted analysis to the structured runtime proof.
- An Iris interpretation of resource assertions and an end-to-end library
  soundness interface for registered Raven procedures.
- Generic runtime support for invariant-token allocation and ghost-resource
  factories.
- A typed monotonic-counter development exercising procedure contracts,
  invariant access, ghost updates, trusted atomic blocks, and analyzed-program
  packaging.
- Raven-like surface notation for the typed verification language.

### Changed

- Invariant masks are owned by the atomicity-analysis certificate rather than
  duplicated in Hoare derivations.
- Fold and unfold are explicit verification-language operations whose runtime
  erasure is coordinated by the analyzer and justified by Iris invariant
  reasoning.
- Trusted atomic blocks are treated as a language/runtime trust boundary;
  examples no longer provide their own transition-refinement assumptions.
- Procedure entry stores, contracts, executable registrations, and runtime
  layouts are connected through one authoritative resource-contract
  environment.
- Runtime soundness is parameterized directly by registration and runtime
  data, without proof-irrelevant operational evidence packages.
- The monotonic-counter example now uses the typed resource calculus and the
  generic analyzed-library soundness path.
- Verification-language erasure is total: every statement maps to a runtime
  statement, with proof-only operations represented by the terminal unit
  value and smart sequence/conditional constructors preserving zero-step
  erasure.

### Removed

- The abandoned conditional-soundness and slice experiments superseded by
  the resource normalization architecture.
- The compatibility-stage assertion Hoare calculus, its contract adapter,
  parallel validity machinery, and old certified bundles from the redesigned
  development.
- Program-specific trusted-atomic classifiers and transition obligations.
- Obsolete assertion-shaped runtime-validity lemmas retained alongside the
  resource-native soundness proof.
- The unused `RUNTIME_RESOURCES` compatibility bundle and its parallel model,
  control-operation, execution, and invariant-operation functors.
- `skip` constructors and reduction rules from both languages; `done` is now
  the structural empty continuation and is never charged as a physical step.
- The archived pre-redesign calculus and its translation, soundness, and
  monotonic-counter developments.
- The superseded parallel atomicity-analysis module.

### Fixed

- Procedure-entry correspondence now uses canonical entry frames whose atom
  environment agrees with the symbolic entry store.
- Ghost resources are indexed by the active runtime ghost state, allowing
  allocation witnesses to carry the intended separation content.
- Procedure contract instantiation, argument stability, and invariant access
  are discharged generically rather than recreated as example-specific
  soundness obligations.

[Unreleased]: https://github.com/nyu-acsys/raven-formalization/commits/dev
