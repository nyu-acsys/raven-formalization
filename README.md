<table>
<tr>
<td width="200"><img width="200" alt="Raven logo" src="https://raw.githubusercontent.com/nyu-acsys/raven-lang/main/.github/assets/logo.png"/></td>
<td>

# Raven Formalization

This repository contains a mechanization in [Rocq](https://rocq-prover.org/)
and [Iris](https://iris-project.org/) of the program logic and atomicity
analysis used by [Raven](https://github.com/nyu-acsys/raven), a modeling and
verification language for concurrent systems.

</td>
</tr>
</table>

## Overview

The development connects four levels:

1. a typed, Raven-like verification language with procedures, separation
   logic assertions, invariants, ghost resources, calls, spawning, and trusted
   atomic blocks;
2. a resource Hoare logic for proving procedure bodies;
3. an executable atomicity and invariant-access analysis, followed by a
   proof-producing normalization pass; and
4. an Iris interpretation and module-level soundness theorem for the erased
   concurrent runtime program.

The central theorem is `Adequacy.raven_module_soundness` in
[`theories/soundness/adequacy.v`](theories/soundness/adequacy.v). Given a
well-formed Raven module, Hoare derivations for its procedures, successful
analysis certificates, a runtime ghost-resource factory, and a compatible
initial runtime state, it allocates the Iris ghost state and establishes the
global world context containing the verified specifications of every
registered procedure.

For a guided account of the languages, analyses, trust boundary, and proof
pipeline, see [Architecture and soundness](docs/architecture.md).

## Status

The repository is a research formalization of a substantial Raven subset. It
currently includes:

- typed expressions, symbolic stores, and Raven-like surface elaboration;
- typed procedure, predicate, invariant, and field declarations;
- a resource Hoare logic separating exclusive stack ownership from ordinary
  separation-logic assertions;
- calls, spawning, allocation, heap access, ghost updates, conditionals, and
  trusted atomic blocks;
- explicit invariant `unfold` and `fold` operations;
- executable atomicity analysis with physical-step accounting, conditional
  joins, and invariant-access checking;
- proof-producing normalization from raw fold/unfold programs to structured
  invariant-access regions;
- Iris interpretations of assertions, runtime state, procedures, invariant
  tokens, and ghost resources; and
- a monotonic-counter module as an end-to-end example.

The current release intentionally retains a LIFO restriction on invariant
accesses. Masks distinguish invariant declarations but not yet individual
argument-indexed instances, and logically atomic procedure specifications are
not yet formalized. These are precision and coverage limitations of the
accepted fragment, not additional premises imposed on verified examples. See
[Current limitations](docs/architecture.md#13-current-limitations) for details.

## Repository layout

The development is one Rocq theory, `raven`, divided into qualified
sub-namespaces:

| Directory | Purpose |
| --- | --- |
| [`theories/surface`](theories/surface) | Raven-like concrete syntax and elaboration |
| [`theories/verification`](theories/verification) | Typed IR, assertions, resources, procedures, and Hoare rules |
| [`theories/analysis`](theories/analysis) | Atomicity analysis, certificates, and normalization |
| [`theories/runtime`](theories/runtime) | Concurrent runtime language, erasure, ghost state, and Iris lifting |
| [`theories/soundness`](theories/soundness) | Semantic interpretation, rule validity, procedure validity, and adequacy |
| [`theories/examples`](theories/examples) | Verified monotonic-counter module and its resource algebra |

## Building

The development is known to work with:

- Coq/Rocq compatibility package `coq.8.19.2`;
- `coq-iris.4.4.0`;
- `coq-stdpp.1.12.0`; and
- Dune 3.23.1 (the project uses Dune language version 3.8).

After installing the dependencies in the active opam switch:

```console
dune build -j 2
```

Useful focused targets are:

```console
dune build -j 2 @soundness  # generic development through module soundness
dune build -j 2 @examples   # verified examples and their dependencies
```

Rocq compilation can consume substantial memory. On machines with limited
RAM, use `-j 1` or another small job count. Compiled artifacts are placed
under `_build/default/theories`.

## Reading the development

A useful route through the code is:

1. [`theories/surface/syntax.v`](theories/surface/syntax.v) and
   [`theories/surface/elaboration.v`](theories/surface/elaboration.v);
2. [`theories/verification/ir.v`](theories/verification/ir.v),
   [`theories/verification/resources.v`](theories/verification/resources.v),
   and [`theories/verification/hoare_rules.v`](theories/verification/hoare_rules.v);
3. [`theories/analysis/atomicity.v`](theories/analysis/atomicity.v) and
   [`theories/analysis/normalization.v`](theories/analysis/normalization.v);
4. [`theories/soundness/rule_validity.v`](theories/soundness/rule_validity.v),
   [`theories/soundness/procedure_validity.v`](theories/soundness/procedure_validity.v),
   and [`theories/soundness/adequacy.v`](theories/soundness/adequacy.v); then
5. [`theories/examples/counter_monotonic.v`](theories/examples/counter_monotonic.v).

## Trusted boundary

Trusted atomic blocks are an intentional Raven language feature: they let a
model define the abstract hardware transitions on which higher-level proofs
are built. The formalization therefore assumes a runtime transition for each
trusted block and a generic refinement law connecting verified block bodies
to those transitions. Ordinary invariant, procedure, and resource reasoning
is proved in Iris.

The complete assumptions and their role are described in
[Trust and axioms](docs/architecture.md#12-trust-and-axioms).

## Changes

See [`CHANGELOG.md`](CHANGELOG.md) for the release history and future release
notes.

## License

Source code is distributed under the BSD 3-Clause License. Documentation in
`docs/` is distributed under the Creative Commons Attribution 4.0
International License. See [`LICENSE.md`](LICENSE.md) for details.
