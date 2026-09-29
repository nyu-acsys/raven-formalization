# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Changed

- Conditionals whose branches finish with different available masks are
  accepted; the joined mask is their intersection. Module analyses now state
  registry coverage for each procedure's required mask and statically
  allocated invariants instead of its exit mask.
- Core entailment duplicates any duplicable assertion (pure facts,
  invariant knowledge, and their conjunctions, existentials, and
  conditionals) through `CESDuplicate`, which replaces `CESInvariantDup`.
- Program locals are indexed by a declaration context recording each
  local's phase (runtime or ghost) and mutability (`val` or `var`).
  Runtime statements read only runtime locals; proof-only statements may
  read every local. Write statements carry an initialization flag, and only
  an initializing write may target a runtime `val`. Procedure-level locals
  must be runtime locals (`procedure_wf`).
- The trusted atomic-block transition depends only on the erasure of the
  block, so proof-only rewrites of a block cannot change it.

### Added

- Scoped ghost values: `ghost val x := e; s` (optionally annotated with a
  type) elaborates to `TGhostVal`, with a Hoare rule, analysis and
  normalization support, and an Iris soundness proof in which ghost locals
  have no runtime frame slot.
- Invariant-argument snapshots: procedure elaboration binds the arguments of
  every `unfold I(args)` to ghost `val`s, unfolds and folds the instance at
  the snapshot, and asserts after the matching fold that its written
  arguments equal the snapshot. An access whose argument variables are
  reassigned inside it is thereby accepted by the normalizer. The rewrite
  erases exactly to the source program (`snapshot_accesses_erasure`). A
  conditional whose branches close an open access also saves its control
  result in a ghost `val` at its evaluation point.
  Derived rules `RTGhostValVar` and `RTAssertTrue` discharge the generated
  binders and checks, as in the counter example's `read` and `incr`.
- Immutable runtime locals: a procedure body may declare
  `val x : T := e;` or `val x : T := new(...);`, elaborated to a runtime
  `val` local and its initializing write. The counter example's `make`
  declares its allocated counter this way.
- Analyzer regression tests for asymmetric allocation in conditionals and
  for snapshotted invariant arguments (`dune build @tests`).

## [1.0.0] - 2026-09-28

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
- A Dune build with focused `@soundness` and `@examples` aliases.

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
- Verification statements are identified structurally rather than carrying
  node labels, and elaboration no longer threads a node counter.
- Procedure contracts use one canonical derived cost model; clients no longer
  provide program-specific cost models or coherence proofs.
- Procedure invariant masks are inferred from contract assertions, including
  invariants reached through predicate bodies; clients no longer declare
  required or granted masks separately.
- The resource calculus is now exposed as `RavenHoareRules.RavenHoareTriple`,
  with redundant resource-specific qualifiers removed from its public names.
- Runtime-model modules and aliases use `Runtime*` terminology consistently;
  “legacy” is reserved for genuinely historical code.
- The development now lives under the single `raven` logical root, organized
  into surface, verification, analysis, runtime, soundness, and example
  namespaces.
- Configuration is supplied through type classes and section parameters
  rather than a deeply nested hierarchy of generative functors; client
  developments no longer pay a large per-program instantiation cost.
- Certificates derive leaf costs from the active analysis environment rather
  than carrying a redundant cost index.
- The soundness development is split by responsibility into rule validity,
  procedure validity, and adequacy modules, with elaboration, erasure, and
  structured certificates likewise separated from their former aggregate
  modules.
- Raven module declarations now elaborate fields, predicates, invariants,
  procedures, contracts, coherence, predicate semantics, and executable
  registration through one module-indexed interface.
- Runtime procedure bodies are direct, stack-indexed erasures of verification
  procedures; call and spawn validity uniformly support both value and
  non-value bodies.
- Module elaboration derives its name environment internally, and rejects
  contracts whose invariant dependencies are not declared by the module.
- Module analysis evidence consists solely of procedure-body certificates;
  runtime registration coverage is derived generically at the soundness
  boundary.
- Typed free symbolic names use `symbol`/`symbol_valuation` terminology,
  distinguishing constant symbols from call-local procedure-entry symbols.

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
- Node identifiers and their associated well-formedness and bookkeeping
  obligations.
- Unused continuation-executor records left behind by the earlier soundness
  architecture.
- Dead module-level semantic interfaces superseded by the live term-level
  records and sections.
- The `_CoqProject`/generated-Makefile build path, superseded by Dune.
- The secondary runtime-statement syntax, its reification and restacking
  machinery, and partial procedure-registrability checks.
- Example-specific runtime-registration packages, including the monotonic
  counter's registration alias and registrability proof.
- Redundant analysis-builder and adequacy forwarding interfaces, including
  the artificial dependency of syntactic analysis evidence on `runtimeG`.

### Fixed

- Procedure-entry correspondence now uses canonical entry frames whose symbol
  valuation agrees with the symbolic entry store.
- Ghost resources are indexed by the active runtime ghost state, allowing
  allocation witnesses to carry the intended separation content.
- Procedure contract instantiation, argument stability, and invariant access
  are discharged generically rather than recreated as example-specific
  soundness obligations.

[Unreleased]: https://github.com/nyu-acsys/raven-formalization/compare/v1.0.0...HEAD
[1.0.0]: https://github.com/nyu-acsys/raven-formalization/releases/tag/v1.0.0
