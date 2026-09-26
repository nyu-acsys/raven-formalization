Known to work with `coq.8.19.2`, `coq-iris.4.4.0`, `coq-stdpp.1.12.0` and
`dune.3.23.1` (Dune 3.8 or newer is required).

The development is a single Rocq theory, `raven`, in `theories/`, with one
sub-namespace per directory (`raven.runtime`, `raven.verification`,
`raven.analysis`, `raven.soundness`, `raven.surface`, `raven.examples`).

To build:
```
$ dune build -j 2              # everything
$ dune build -j 2 @soundness   # the library soundness theorem, no examples
$ dune build -j 2 @examples    # the verified examples
```

The builds are memory-hungry; keep the job count small.  Compiled files are
placed under `_build/default/theories`.
