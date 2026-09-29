# Architecture and soundness

This document gives a high-level account of the Raven formalization and the
structure of its module-level soundness proof. It is intended as a map of the
mechanization rather than a replacement for the definitions and theorem
statements in the Rocq sources.

## 1. What is formalized

Raven is a modeling language for concurrent systems. Its program logic uses
separation logic, user-defined resource algebras, predicates, invariants, and
trusted descriptions of atomic hardware behavior. The frontend also performs
an atomicity analysis: while an invariant is open, a thread may take at most
one physical atomic step and may not take a non-atomic step.

The mechanization covers the path from Raven-like module declarations to an
Iris interpretation of their procedure contracts:

```text
surface declarations
        |
        v
typed module, statements, and assertions
        |
        +-----------------------+
        |                       |
        v                       v
resource Hoare derivations   executable atomicity analysis
        |                       |
        +-----------+-----------+
                    v
         aligned normalization
     raw fold/unfold -> structured access
                    |
                    v
       validity of structured rules in Iris
                    |
                    v
        verified procedure specifications
                    |
                    v
        initialized global world context
```

The Hoare logic does not carry atomicity-analysis masks. The derivation proves
the functional and resource behavior of a statement; the independently
computed certificate proves that its invariant accesses and physical steps
are admissible. Normalization aligns these two witnesses before Iris validity
is applied.

## 2. Surface language and elaboration

[`surface/syntax.v`](../theories/surface/syntax.v) provides Raven-like Rocq
notation for fields, predicates, invariants, procedures, expressions,
assertions, and statements.
[`surface/elaboration.v`](../theories/surface/elaboration.v) resolves names
and checks types, producing the intrinsically typed IR.

A module declaration determines:

- its logic signature and identifiers;
- predicate and invariant declarations;
- typed procedures and their contracts;
- procedure-local variable layouts;
- the contract environment used by call and spawn rules; and
- the canonical runtime registration obtained by erasing procedure bodies.

This derived packaging is important at the public boundary: examples do not
provide separate coherence proofs connecting contracts, procedures, and
runtime registration.

## 3. Typed verification language

The core language is defined in
[`verification/ir.v`](../theories/verification/ir.v). Expressions and
symbolic references are indexed by their types and contexts. Statements
include:

- local assignment;
- field reads and writes;
- allocation;
- procedure calls and spawning;
- conditionals and sequencing;
- trusted atomic blocks;
- ghost resource updates;
- predicate fold/unfold; and
- invariant fold/unfold.

Proof-only operations erase to the terminal runtime value. Smart sequencing
and conditional erasure preserve this zero-step behavior, so erasure is total
without introducing an executable `skip` command.

The runtime language in [`runtime/lang.v`](../theories/runtime/lang.v) is a
smaller concurrent language with concrete stacks, heaps, calls, spawning, and
trusted atomic transitions. Its Iris lifting rules are in
[`runtime/lifting.v`](../theories/runtime/lifting.v).

## 4. Assertions and resources

Assertions are split into two layers:

- core assertions describe ordinary logical and separation resources; and
- resource assertions pair exactly one symbolic stack store with a core
  assertion.

The separation is represented in
[`verification/resources.v`](../theories/verification/resources.v). It makes
the exclusive runtime stack explicit and prevents stack ownership from being
hidden arbitrarily under conjunctions. Prenex resource binders support values
introduced by reads, allocation, calls, and logical existential reasoning
without duplicating stack ownership.

Core assertions include pure facts, separating conjunction, quantifiers,
predicate applications, invariant ownership, physical heap ownership, and
ghost ownership. Their Iris interpretation is defined in
[`soundness/interpretation.v`](../theories/soundness/interpretation.v).

Predicates denote a least timeless fixed point of their positive unfolding
functional. Invariants and predicates are distinct: predicate unfolding is
logical, whereas invariant unfolding is governed by the atomicity analysis
and Iris masks.

## 5. Resource Hoare logic

[`verification/hoare_rules.v`](../theories/verification/hoare_rules.v)
defines `RavenHoareRules.RavenHoareTriple`. Its rules cover the language
primitives, structural reasoning, resource framing and consequence,
existential binders, calls, spawn, trusted atomic blocks, and explicit
fold/unfold operations.

The rules are deliberately independent of Raven masks. For example, an
invariant fold rule proves the local resource transformation associated with
closing or allocating an invariant, but does not itself claim that this fold
matches a particular earlier unfold. That global fact is supplied by the
analysis and normalization layers.

Procedure contracts and module construction live in
[`verification/procedures.v`](../theories/verification/procedures.v). The
module checks that contract dependencies refer to declared invariants and
derives one coherent resource-contract environment.

## 6. Atomicity analysis

[`analysis/atomicity.v`](../theories/analysis/atomicity.v) contains an
executable, certificate-producing analysis. Its state records:

- the available mask entries: an entry names either every instance of an
  invariant declaration or one instance, keyed by its arguments when each
  argument is a local (by its de Bruijn level) or a literal;
- the open accesses, innermost first, each with its instance and the entry
  it consumed;
- whether a physical atomic step has been taken while an invariant is open;
  and
- whether traversal is inside a trusted atomic block.

The essential policy is:

- fold and unfold are proof-only operations;
- with an invariant open, at most one physical atomic step may occur;
- a non-atomic physical operation is forbidden while an invariant is open;
- closing the last open invariant resets step accounting;
- both conditional branches start from the same state;
- an unfold consumes the exact entry of its instance, or else the
  declaration-wide entry; a fold closes the innermost open access, which
  must be the same instance, and restores the consumed entry, or allocates
  an instance of an invariant that is not open;
- leaving the scope of a local forgets the entries it made available that
  name the local, and no open access may name it;
- branch entries are joined by keeping each entry of either branch that is
  covered in both, so an invariant allocated in only one branch is
  unavailable after the conditional;
- branch step flags are joined by disjunction; and
- procedures must return with no invariant left open.

Calls and spawn receive effects derived from the callee contracts. Trusted
atomic blocks count as one physical atomic step to the surrounding context;
step counting inside the block is suspended, while invariant-opening state is
still tracked.

The Iris interpretation reads only the declaration-level projections of this
state: the available and the open declarations.

## 7. Why normalization is necessary

Raven source programs contain separate `unfold` and `fold` statements. Iris
invariant reasoning is naturally scoped: opening an invariant yields a
resource and a linear closing capability that must be used around the
admissible physical step.

The normalizer bridges the representations. The source:

```raven
unfold I(x);
body;
fold I(x)
```

is related to a structured verification statement morally of the form:

```text
TInvAccess I(x) body
```

An access may also be closed in each branch of a conditional. When nothing
physical precedes the conditional, the access moves into the branches:

```raven
unfold I(x); q;
if (b) { t; fold I(x); k1 } else { e; fold I(x); k2 }
```

becomes, morally, `if (b) { TInvAccess I(x) (q; t); k1 } else { TInvAccess
I(x) (q; e); k2 }`. After a physical step `p`, the branch prefixes `t` and
`e` must be proof-only, and the access is factored out of the conditional:
`TInvAccess I(x) (p; if (b) {t} else {e}); if (b) {k1} else {k2}`, where
the access closes through the guard and the guard is tested again for the
continuations. Access bodies and prefixes may themselves contain balanced
invariant accesses, which are normalized recursively. Procedure elaboration
first puts every access into this canonical layout: it groups the
statements before the access's close into one body or prefix, groups a
closing conditional with its unfold when further statements follow, and
inserts `done` for missing pieces, in each case only where the runtime
erasure is unchanged
([`verification/access_layout.v`](../theories/verification/access_layout.v)).

An access that spans a trusted atomic block,
`atomic { unfold I(x); body; fold I(x) }`, is moved around the block by the
same layout pass, giving `unfold I(x); atomic { body }; fold I(x)`: the
invariant is held across the block's single physical step, and the block's
erased body, hence its trusted transition, is unchanged.

The transformation is proof-producing. It retains:

- the source Hoare derivation;
- the analyzer certificate;
- equality of runtime erasures;
- coverage of every invariant used by the transformed program; and
- evidence that structured accesses occur only in supported positions.

The base checks and the balance of accepted regions are in
[`analysis/normalization_base.v`](../theories/analysis/normalization_base.v).
The aligned transformation and its completeness theorem are in
[`analysis/normalization.v`](../theories/analysis/normalization.v).
Structured certificates are defined in
[`analysis/structured_certificates.v`](../theories/analysis/structured_certificates.v).

Normalization is internal to the soundness theorem. A module supplies Hoare
derivations and successful analysis evidence, not hand-built normalized
programs or Iris compatibility lemmas.

## 8. Iris interpretation

The runtime model in
[`soundness/runtime_model.v`](../theories/soundness/runtime_model.v) connects
the typed verification objects to the concrete runtime language. It defines:

- the runtime stack context used to interpret symbolic stores;
- invariant-token ownership and registered invariant namespaces;
- physical and ghost heap ownership;
- procedure registration and persistent procedure specifications;
- active Iris masks corresponding to the analyzer state; and
- the operational interpretation of leaves, calls, spawning, and invariant
  operations.

[`soundness/entailment_validity.v`](../theories/soundness/entailment_validity.v)
proves core entailment sound.

[`soundness/rule_validity.v`](../theories/soundness/rule_validity.v) proves
the structured Hoare rules valid in Iris. Important cases include:

- stack assignment and heap operations;
- ghost allocation and frame-preserving update;
- call and spawn;
- conditionals and sequencing;
- fresh invariant allocation;
- matched invariant access around an admissible atomic step; and
- trusted atomic blocks.

The induction consumes structured certificates rather than attempting to
interpret arbitrary unmatched fold/unfold syntax directly.

## 9. Procedure and module soundness

[`soundness/procedure_validity.v`](../theories/soundness/procedure_validity.v)
lifts rule validity to procedure bodies. For each procedure it combines:

1. the declared resource Hoare derivation;
2. successful atomicity analysis;
3. normalization completeness;
4. equality between source and normalized runtime erasure; and
5. the canonical runtime procedure registration.

The result is a persistent Iris specification for the registered procedure.
Callers may invoke the procedure from any runtime context satisfying its
precondition and the analyzer-derived mask requirements; there is no single
distinguished entry procedure.

[`soundness/adequacy.v`](../theories/soundness/adequacy.v) packages the module
boundary. A `module_analysis M` contains successful analyzed bodies for every
declared procedure and proves that the invariants each procedure requires or
may allocate (by folding or through call grants) are covered by the module's
invariant declarations. Contract coherence, predicate semantics,
normalization completeness, and executable registration are derived
internally.

The main theorem is:

```coq
Adequacy.raven_module_soundness
```

It is quantified over a compatible initial runtime state and an arbitrary
symbol valuation. It allocates the runtime heap, stack, procedure, ghost
domain, and invariant-token ghost names, establishes the concrete state
interpretation, allocates the invariant world, and installs the persistent
specifications of all registered procedures in `global_world_context`.

This is a library-style soundness theorem: it verifies all procedures as
callable components rather than proving safety only for one closed main
program. Standard Iris adequacy can subsequently be applied to a client and
initial thread that use this world context.

## 10. Trusted atomic blocks

Trusted atomic blocks are a genuine language feature, not an unfinished proof
of a derived construct. Raven is intended to model concurrency substrates,
so a module may define a trusted atomic transition corresponding to its chosen
hardware abstraction.

The generic backend assumes:

1. a runtime transition associated with each trusted block; and
2. a refinement principle connecting the verified body to the WP of that
   transition.

These assumptions are uniform framework assumptions. Individual modules and
examples do not provide per-block Iris refinement proofs. CAS-like operations
can be built as trusted blocks with higher-level resource specifications.

Trusted physical atomicity should not be confused with a logically atomic
procedure specification. The latter describes an abstract linearization
point for a potentially multi-step implementation and is not yet part of the
formalized fragment.

## 11. Monotonic-counter example

[`examples/counter_monotonic.v`](../theories/examples/counter_monotonic.v)
defines one Raven module containing:

- a physical integer field;
- a monotone ghost resource;
- a counter invariant relating physical and ghost state;
- procedures for construction, reading, and incrementing; and
- a client procedure.

The example exercises surface elaboration, invariant allocation and access,
trusted atomic behavior, ghost updates, calls, procedure packaging, executable
analysis, and the final module theorem. Its exported endpoint is
`counter_module_soundness`, an application of `raven_module_soundness`.

## 12. Trust and axioms

`Print Assumptions Adequacy.raven_module_soundness` reports the expected Rocq
principles used by the development, including proof irrelevance, dependent
functional extensionality, dependent equality, and constructive indefinite
description. The two Raven-specific assumptions are the backend transition
assigned to a trusted atomic block and the generic refinement law for such a
block.

These assumptions delimit the intended hardware-model trust boundary. The
soundness of ordinary Hoare rules, invariant reasoning, resource updates,
procedure calls, analysis normalization, and runtime initialization is proved
within Rocq and Iris.

No theorem in the retained development uses `Admitted`.

## 13. Current limitations

The current release deliberately formalizes a conservative subset of Raven's
analysis:

- invariant accesses must be LIFO;
- instance keys are exact only for arguments that are locals or literals,
  and the Iris interpretation uses one namespace per declaration;
- only one instance of a declaration can be open at once;
- the normalizer does not yet cover every branch-local fold/unfold placement
  accepted by Raven: after the common prefix has consumed an access's
  physical-step budget, the branch prefixes of the resulting factored access
  must be proof-only and may not open invariants;
- ghost locals are immutable (`ghost val`); Raven's ghost `var`s are not
  yet supported;
- an invariant access inside a trusted atomic block must span the block,
  up to trailing proof-only statements; and
- logically atomic procedure specifications and atomic-update tokens are not
  yet formalized.

These restrictions make the accepted fragment smaller; they do not add
unproved obligations to the public soundness theorem. Future extensions can
strengthen the analysis/certification layer while preserving the mask-free
Hoare interface.

## 14. Build and checking boundaries

The Dune aliases expose two useful verification boundaries:

```console
dune build -j 1 @soundness
dune build -j 1 @examples
```

The first checks the generic theorem through `raven_module_soundness`; the
second additionally checks the monotonic-counter development. A full
`dune build` checks every retained `.v` file.

The build is memory-intensive. Serial checking is recommended for release and
continuous-integration jobs unless the available memory is known to support a
larger job count.
