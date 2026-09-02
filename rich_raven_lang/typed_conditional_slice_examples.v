From Coq Require Import List.
From raven_iris.rich_raven_lang Require Import typed_conditional_slice.

Import ListNotations.

(** A concrete, deliberately small payload for the conditional slice.

    States and invariant names are naturals.  The action labels are also
    naturals; their values are irrelevant to the typing examples, but keeping
    them in the constructors makes the four traces easy to inspect. *)
Module NatConditionalPayload <: CONDITIONAL_SLICE_PAYLOAD.
  Definition state := nat.
  Definition marker := nat.

  Inductive chunk_action : state -> list marker -> state -> list marker -> Type :=
  | ChunkNeutral (s : state) (stack : list marker) (label : nat) :
      chunk_action s stack s stack
  | ChunkAtomic (entry exit : state) (stack : list marker) (label : nat) :
      chunk_action entry stack exit stack
  | ChunkNonAtomic (entry exit : state) (stack : list marker) (label : nat) :
      chunk_action entry stack exit stack
  | ChunkOpen (entry exit : state) (focused : marker)
      (tail : list marker) (label : nat) :
      chunk_action entry tail exit (focused :: tail)
  | ChunkClose (entry exit : state) (focused : marker)
      (tail : list marker) (label : nat) :
      chunk_action entry (focused :: tail) exit tail.

  Definition chunk := chunk_action.

  (** Only physical chunks which keep the focus continuously open count as a
      focused prefix.  In particular, an open/close pair cannot be used as a
      prefix merely because it has the same endpoints. *)
  Inductive preserves_evidence : forall focused tail entry exit,
      chunk_action entry (focused :: tail) exit (focused :: tail) -> Prop :=
  | PreservesNeutral focused tail s label :
      preserves_evidence focused tail s s
        (ChunkNeutral s (focused :: tail) label)
  | PreservesAtomic focused tail entry exit label :
      preserves_evidence focused tail entry exit
        (ChunkAtomic entry exit (focused :: tail) label)
  | PreservesNonAtomic focused tail entry exit label :
      preserves_evidence focused tail entry exit
        (ChunkNonAtomic entry exit (focused :: tail) label).

  Definition preserves := preserves_evidence.

  Inductive opens_evidence : forall focused tail entry exit,
      chunk_action entry tail exit (focused :: tail) -> Prop :=
  | OpensChunk entry exit focused tail label :
      opens_evidence focused tail entry exit
        (ChunkOpen entry exit focused tail label).

  Definition opens := opens_evidence.

  Inductive closes_evidence : forall focused tail entry exit,
      chunk_action entry (focused :: tail) exit tail -> Prop :=
  | ClosesChunk entry exit focused tail label :
      closes_evidence focused tail entry exit
        (ChunkClose entry exit focused tail label).

  Definition closes := closes_evidence.

  (** The [guard] records a concrete witness for which conditional is being
      represented.  It is intentionally not interpreted by this structural
      slice. *)
  Inductive conditional_witness : state -> state -> state -> state -> Type :=
  | ConditionalWitness (entry then_exit else_exit join : state)
      (guard : bool) :
      conditional_witness entry then_exit else_exit join.

  Definition conditional := conditional_witness.
End NatConditionalPayload.

Module NatSlice := ConditionalSlice NatConditionalPayload.
Import NatConditionalPayload NatSlice.

Definition focus : marker := 10.
Definition tail : list marker := [].

(** Example 1: [atomic; close] versus [skip; atomic; close]. *)
Definition ex1_open : chunk 0 tail 1 (focus :: tail) :=
  ChunkOpen 0 1 focus tail 100.

Definition ex1_open_ok : opens focus tail 0 1 ex1_open :=
  OpensChunk 0 1 focus tail 100.

Definition ex1_then_atomic : chunk 1 (focus :: tail) 2 (focus :: tail) :=
  ChunkAtomic 1 2 (focus :: tail) 101.

Definition ex1_then_atomic_ok :
    preserves focus tail 1 2 ex1_then_atomic :=
  PreservesAtomic focus tail 1 2 101.

Definition ex1_close : chunk 2 (focus :: tail) 3 tail :=
  ChunkClose 2 3 focus tail 102.

Definition ex1_close_ok : closes focus tail 2 3 ex1_close :=
  ClosesChunk 2 3 focus tail 102.

Definition ex1_then : focused_execution focus tail 1 3 :=
  FocusedPrefix focus tail 1 2 3 ex1_then_atomic ex1_then_atomic_ok
    (FocusedClose focus tail 2 3 ex1_close ex1_close_ok).

Definition ex1_else_skip : chunk 1 (focus :: tail) 1 (focus :: tail) :=
  ChunkNeutral 1 (focus :: tail) 103.

Definition ex1_else_skip_ok :
    preserves focus tail 1 1 ex1_else_skip :=
  PreservesNeutral focus tail 1 103.

Definition ex1_else_atomic : chunk 1 (focus :: tail) 2 (focus :: tail) :=
  ChunkAtomic 1 2 (focus :: tail) 104.

Definition ex1_else_atomic_ok :
    preserves focus tail 1 2 ex1_else_atomic :=
  PreservesAtomic focus tail 1 2 104.

Definition ex1_else : focused_execution focus tail 1 3 :=
  FocusedPrefix focus tail 1 1 3 ex1_else_skip ex1_else_skip_ok
    (FocusedPrefix focus tail 1 2 3 ex1_else_atomic ex1_else_atomic_ok
      (FocusedClose focus tail 2 3 ex1_close ex1_close_ok)).

Definition ex1_test : conditional 1 3 3 3 :=
  ConditionalWitness 1 3 3 3 true.

Definition ex1 : execution 0 tail 3 tail :=
  ExecAccess focus tail 0 1 3 3 ex1_open ex1_open_ok
    (FocusedConditional focus tail 1 3 3 3 3 3 tail 3 ex1_test
      (ClosedBranch focus tail 1 3 3 tail ex1_then (ExecDone 3 tail))
      (ClosedBranch focus tail 1 3 3 tail ex1_else (ExecDone 3 tail))
      (ExecDone 3 tail))
    (ExecDone 3 tail).

(** Example 2: both arms close first and then retain a non-atomic suffix. *)
Definition ex2_open : chunk 0 tail 1 (focus :: tail) :=
  ChunkOpen 0 1 focus tail 200.

Definition ex2_open_ok : opens focus tail 0 1 ex2_open :=
  OpensChunk 0 1 focus tail 200.

Definition ex2_close_then : chunk 1 (focus :: tail) 2 tail :=
  ChunkClose 1 2 focus tail 201.

Definition ex2_close_then_ok : closes focus tail 1 2 ex2_close_then :=
  ClosesChunk 1 2 focus tail 201.

Definition ex2_close_else : chunk 1 (focus :: tail) 2 tail :=
  ChunkClose 1 2 focus tail 202.

Definition ex2_close_else_ok : closes focus tail 1 2 ex2_close_else :=
  ClosesChunk 1 2 focus tail 202.

Definition ex2_then_first : focused_execution focus tail 1 2 :=
  FocusedClose focus tail 1 2 ex2_close_then ex2_close_then_ok.

Definition ex2_else_first : focused_execution focus tail 1 2 :=
  FocusedClose focus tail 1 2 ex2_close_else ex2_close_else_ok.

Definition ex2_then_nonatomic : chunk 2 tail 3 tail :=
  ChunkNonAtomic 2 3 tail 203.

Definition ex2_else_nonatomic : chunk 2 tail 4 tail :=
  ChunkNonAtomic 2 4 tail 204.

Definition ex2_then_post : execution 2 tail 3 tail :=
  ExecChunk 2 tail 3 3 tail ex2_then_nonatomic (ExecDone 3 tail).

Definition ex2_else_post : execution 2 tail 4 tail :=
  ExecChunk 2 tail 4 4 tail ex2_else_nonatomic (ExecDone 4 tail).

Definition ex2_test : conditional 1 3 4 5 :=
  ConditionalWitness 1 3 4 5 false.

Definition ex2 : execution 0 tail 5 tail :=
  ExecAccess focus tail 0 1 5 5 ex2_open ex2_open_ok
    (FocusedConditional focus tail 1 2 3 2 4 5 tail 5 ex2_test
      (ClosedBranch focus tail 1 2 3 tail ex2_then_first ex2_then_post)
      (ClosedBranch focus tail 1 2 4 tail ex2_else_first ex2_else_post)
      (ExecDone 5 tail))
    (ExecDone 5 tail).

(** Example 3: after the first close, one arm reopens the same marker and
    closes it again before reaching its branch exit. *)
Definition ex3_open : chunk 0 tail 1 (focus :: tail) :=
  ChunkOpen 0 1 focus tail 300.

Definition ex3_open_ok : opens focus tail 0 1 ex3_open :=
  OpensChunk 0 1 focus tail 300.

Definition ex3_first_close : chunk 1 (focus :: tail) 2 tail :=
  ChunkClose 1 2 focus tail 301.

Definition ex3_first_close_ok : closes focus tail 1 2 ex3_first_close :=
  ClosesChunk 1 2 focus tail 301.

Definition ex3_reopen : chunk 2 tail 3 (focus :: tail) :=
  ChunkOpen 2 3 focus tail 302.

Definition ex3_reopen_ok : opens focus tail 2 3 ex3_reopen :=
  OpensChunk 2 3 focus tail 302.

Definition ex3_atomic : chunk 3 (focus :: tail) 4 (focus :: tail) :=
  ChunkAtomic 3 4 (focus :: tail) 303.

Definition ex3_atomic_ok : preserves focus tail 3 4 ex3_atomic :=
  PreservesAtomic focus tail 3 4 303.

Definition ex3_second_close : chunk 4 (focus :: tail) 5 tail :=
  ChunkClose 4 5 focus tail 304.

Definition ex3_second_close_ok : closes focus tail 4 5 ex3_second_close :=
  ClosesChunk 4 5 focus tail 304.

Definition ex3_first : focused_execution focus tail 1 2 :=
  FocusedClose focus tail 1 2 ex3_first_close ex3_first_close_ok.

Definition ex3_second : focused_execution focus tail 3 5 :=
  FocusedPrefix focus tail 3 4 5 ex3_atomic ex3_atomic_ok
    (FocusedClose focus tail 4 5 ex3_second_close ex3_second_close_ok).

Definition ex3_then_post : execution 2 tail 5 tail :=
  ExecAccess focus tail 2 3 5 5 ex3_reopen ex3_reopen_ok ex3_second
    (ExecDone 5 tail).

Definition ex3_test : conditional 1 5 2 5 :=
  ConditionalWitness 1 5 2 5 true.

Definition ex3 : execution 0 tail 5 tail :=
  ExecAccess focus tail 0 1 5 5 ex3_open ex3_open_ok
    (FocusedConditional focus tail 1 2 5 2 2 5 tail 5 ex3_test
      (ClosedBranch focus tail 1 2 5 tail ex3_first ex3_then_post)
      (ClosedBranch focus tail 1 2 2 tail ex3_first (ExecDone 2 tail))
      (ExecDone 5 tail))
    (ExecDone 5 tail).

(** Example 4: a conditional nested while [focus] is open.  The outer then
    arm closes immediately; its else arm contains a second conditional whose
    arms close after different focused prefixes. *)
Definition ex4_open : chunk 0 tail 1 (focus :: tail) :=
  ChunkOpen 0 1 focus tail 400.

Definition ex4_open_ok : opens focus tail 0 1 ex4_open :=
  OpensChunk 0 1 focus tail 400.

Definition ex4_outer_then_close : chunk 1 (focus :: tail) 3 tail :=
  ChunkClose 1 3 focus tail 401.

Definition ex4_outer_then_close_ok :
    closes focus tail 1 3 ex4_outer_then_close :=
  ClosesChunk 1 3 focus tail 401.

Definition ex4_inner_then_skip : chunk 1 (focus :: tail) 1 (focus :: tail) :=
  ChunkNeutral 1 (focus :: tail) 402.

Definition ex4_inner_then_skip_ok :
    preserves focus tail 1 1 ex4_inner_then_skip :=
  PreservesNeutral focus tail 1 402.

Definition ex4_inner_then_close : chunk 1 (focus :: tail) 2 tail :=
  ChunkClose 1 2 focus tail 403.

Definition ex4_inner_then_close_ok :
    closes focus tail 1 2 ex4_inner_then_close :=
  ClosesChunk 1 2 focus tail 403.

Definition ex4_inner_else_atomic :
    chunk 1 (focus :: tail) 2 (focus :: tail) :=
  ChunkAtomic 1 2 (focus :: tail) 404.

Definition ex4_inner_else_atomic_ok :
    preserves focus tail 1 2 ex4_inner_else_atomic :=
  PreservesAtomic focus tail 1 2 404.

Definition ex4_inner_else_close : chunk 2 (focus :: tail) 4 tail :=
  ChunkClose 2 4 focus tail 405.

Definition ex4_inner_else_close_ok :
    closes focus tail 2 4 ex4_inner_else_close :=
  ClosesChunk 2 4 focus tail 405.

Definition ex4_inner_test : conditional 1 2 4 4 :=
  ConditionalWitness 1 2 4 4 false.

Definition ex4_inner : focused_execution focus tail 1 4 :=
  FocusedConditional focus tail 1 2 2 4 4 4 tail 4 ex4_inner_test
    (ClosedBranch focus tail 1 2 2 tail
      (FocusedPrefix focus tail 1 1 2 ex4_inner_then_skip
        ex4_inner_then_skip_ok
        (FocusedClose focus tail 1 2 ex4_inner_then_close
          ex4_inner_then_close_ok))
      (ExecDone 2 tail))
    (ClosedBranch focus tail 1 4 4 tail
      (FocusedPrefix focus tail 1 2 4 ex4_inner_else_atomic
        ex4_inner_else_atomic_ok
        (FocusedClose focus tail 2 4 ex4_inner_else_close
          ex4_inner_else_close_ok))
      (ExecDone 4 tail))
    (ExecDone 4 tail).

Definition ex4_outer_test : conditional 1 3 4 5 :=
  ConditionalWitness 1 3 4 5 true.

Definition ex4 : execution 0 tail 5 tail :=
  ExecAccess focus tail 0 1 5 5 ex4_open ex4_open_ok
    (FocusedConditional focus tail 1 3 3 4 4 5 tail 5 ex4_outer_test
      (ClosedBranch focus tail 1 3 3 tail
        (FocusedClose focus tail 1 3 ex4_outer_then_close
          ex4_outer_then_close_ok)
        (ExecDone 3 tail))
      (ClosedBranch focus tail 1 4 4 tail ex4_inner (ExecDone 4 tail))
      (ExecDone 5 tail))
    (ExecDone 5 tail).

(** Example 5 is the continuation-sensitive counterexample.  The then arm
    closes the original accessor and reopens [focus], while the else arm
    keeps the original accessor open.  The shared close is consequently the
    second accessor's close in the then arm and the original accessor's close
    in the else arm. *)
Definition ex5_open : chunk 0 tail 1 (focus :: tail) :=
  ChunkOpen 0 1 focus tail 500.
Definition ex5_open_ok : opens focus tail 0 1 ex5_open :=
  OpensChunk 0 1 focus tail 500.
Definition ex5_then_close : chunk 1 (focus :: tail) 2 tail :=
  ChunkClose 1 2 focus tail 501.
Definition ex5_then_close_ok : closes focus tail 1 2 ex5_then_close :=
  ClosesChunk 1 2 focus tail 501.
Definition ex5_then_reopen : chunk 2 tail 4 (focus :: tail) :=
  ChunkOpen 2 4 focus tail 502.
Definition ex5_then_reopen_ok : opens focus tail 2 4 ex5_then_reopen :=
  OpensChunk 2 4 focus tail 502.
Definition ex5_else_skip : chunk 1 (focus :: tail) 1 (focus :: tail) :=
  ChunkNeutral 1 (focus :: tail) 503.
Definition ex5_else_skip_ok : preserves focus tail 1 1 ex5_else_skip :=
  PreservesNeutral focus tail 1 503.
Definition ex5_shared_close : chunk 4 (focus :: tail) 5 tail :=
  ChunkClose 4 5 focus tail 504.
Definition ex5_shared_close_ok : closes focus tail 4 5 ex5_shared_close :=
  ClosesChunk 4 5 focus tail 504.
Definition ex5_test : conditional 1 4 1 4 :=
  ConditionalWitness 1 4 1 4 true.
Definition ex5 : execution 0 tail 5 tail :=
  ExecAccess focus tail 0 1 5 5 ex5_open ex5_open_ok
    (FocusedConditionalContinue focus tail 1 4 1 4 5 ex5_test
      (OutcomeClosedReopened focus tail 1 2 2 4 4
        (FocusedClose focus tail 1 2 ex5_then_close ex5_then_close_ok)
        (ExecDone 2 tail) ex5_then_reopen ex5_then_reopen_ok
        (FocusedPrefixDone focus tail 4))
      (OutcomeStillOpen focus tail 1 1
        (FocusedPrefixChunk focus tail 1 1 1 ex5_else_skip
          ex5_else_skip_ok (FocusedPrefixDone focus tail 1)))
      (FocusedClose focus tail 4 5 ex5_shared_close ex5_shared_close_ok))
    (ExecDone 5 tail).

(** A pure conditional can preserve the focused accessor in both arms. *)
Definition ex6_test : conditional 1 1 1 1 :=
  ConditionalWitness 1 1 1 1 false.
Definition ex6_close : chunk 1 (focus :: tail) 2 tail :=
  ChunkClose 1 2 focus tail 602.
Definition ex6_close_ok : closes focus tail 1 2 ex6_close :=
  ClosesChunk 1 2 focus tail 602.
Definition ex6 : execution 0 tail 2 tail :=
  ExecAccess focus tail 0 1 2 2 ex1_open ex1_open_ok
    (FocusedPrefix focus tail 1 1 2 ex1_else_skip ex1_else_skip_ok
      (FocusedPrefix focus tail 1 1 2 ex1_else_skip ex1_else_skip_ok
        (FocusedClose focus tail 1 2 ex6_close ex6_close_ok)))
    (ExecDone 2 tail).
Definition ex6_prefix_conditional : focused_prefix focus tail 1 1 :=
  FocusedPrefixConditional focus tail 1 1 1 1 ex6_test
    (FocusedPrefixDone focus tail 1) (FocusedPrefixDone focus tail 1).

(** Both arms close [focus] and then open [nested]; the common suffix closes
    [nested].  This exercises a nonempty common branch-output stack. *)
Definition nested : marker := 20.
Definition ex7_then_close : chunk 1 (focus :: tail) 2 tail :=
  ChunkClose 1 2 focus tail 701.
Definition ex7_then_close_ok : closes focus tail 1 2 ex7_then_close :=
  ClosesChunk 1 2 focus tail 701.
Definition ex7_else_close : chunk 1 (focus :: tail) 3 tail :=
  ChunkClose 1 3 focus tail 702.
Definition ex7_else_close_ok : closes focus tail 1 3 ex7_else_close :=
  ClosesChunk 1 3 focus tail 702.
Definition ex7_then_open : chunk 2 tail 4 (nested :: tail) :=
  ChunkOpen 2 4 nested tail 703.
Definition ex7_then_open_ok : opens nested tail 2 4 ex7_then_open :=
  OpensChunk 2 4 nested tail 703.
Definition ex7_else_open : chunk 3 tail 5 (nested :: tail) :=
  ChunkOpen 3 5 nested tail 704.
Definition ex7_else_open_ok : opens nested tail 3 5 ex7_else_open :=
  OpensChunk 3 5 nested tail 704.
Definition ex7_shared_close : chunk 6 (nested :: tail) 7 tail :=
  ChunkClose 6 7 nested tail 705.
Definition ex7_shared_close_ok : closes nested tail 6 7 ex7_shared_close :=
  ClosesChunk 6 7 nested tail 705.
Definition ex7_test : conditional 1 4 5 6 :=
  ConditionalWitness 1 4 5 6 true.
Definition ex7 : execution 0 tail 7 tail :=
  ExecAccess focus tail 0 1 7 7 ex1_open ex1_open_ok
    (FocusedConditional focus tail 1 2 4 3 5 6 (nested :: tail) 7
      ex7_test
      (ClosedBranchOpened focus nested tail 1 2 2 4 4
        (FocusedClose focus tail 1 2 ex7_then_close ex7_then_close_ok)
        (ExecDone 2 tail) ex7_then_open ex7_then_open_ok
        (FocusedPrefixDone nested tail 4))
      (ClosedBranchOpened focus nested tail 1 3 3 5 5
        (FocusedClose focus tail 1 3 ex7_else_close ex7_else_close_ok)
        (ExecDone 3 tail) ex7_else_open ex7_else_open_ok
        (FocusedPrefixDone nested tail 5))
      (ExecClose nested tail 6 7 7 tail ex7_shared_close
        ex7_shared_close_ok (ExecDone 7 tail)))
    (ExecDone 7 tail).

(* These checks make the intended public types explicit and keep the file a
   useful compile-time regression test when the slice constructors evolve. *)
Check ex1.
Check ex2.
Check ex3.
Check ex4.
Check ex5.
Check ex6_prefix_conditional.
Check ex7.

(** An executable trace interpretation checks the continuation placement.
    Chunk labels are prepended to every path.  A conditional contributes 900
    on its then paths and 901 on its else paths. *)
Module TraceSemantics <: CONDITIONAL_SLICE_SEMANTICS NatConditionalPayload.
  Definition formula := list (list nat).

  Definition action_label {entry stack_in exit stack_out}
      (action : chunk entry stack_in exit stack_out) : nat :=
    match action with
    | ChunkNeutral _ _ label
    | ChunkAtomic _ _ _ label
    | ChunkNonAtomic _ _ _ label
    | ChunkOpen _ _ _ _ label
    | ChunkClose _ _ _ _ label => label
    end.

  Definition chunk_wp entry stack_in exit stack_out
      (action : chunk entry stack_in exit stack_out)
      (post : formula) : formula :=
    map (cons (action_label action)) post.

  Definition conditional_wp entry then_exit else_exit join
      (_ : conditional entry then_exit else_exit join)
      (then_paths else_paths : formula) : formula :=
    map (cons 900) then_paths ++ map (cons 901) else_paths.
End TraceSemantics.

Module TraceDenotation := ConditionalSliceDenotation
  NatConditionalPayload NatSlice TraceSemantics.

Example ex1_paths : TraceDenotation.execution_wp ex1 [[]] =
    [[100; 900; 101; 102]; [100; 901; 103; 104; 102]].
Proof. reflexivity. Qed.

Example ex2_paths : TraceDenotation.execution_wp ex2 [[999]] =
    [[200; 900; 201; 203; 999]; [200; 901; 202; 204; 999]].
Proof. reflexivity. Qed.

Example ex3_paths : TraceDenotation.execution_wp ex3 [[999]] =
    [[300; 900; 301; 302; 303; 304; 999];
     [300; 901; 301; 999]].
Proof. reflexivity. Qed.

Example ex4_paths : TraceDenotation.execution_wp ex4 [[999]] =
    [[400; 900; 401; 999];
     [400; 901; 900; 402; 403; 999];
     [400; 901; 901; 404; 405; 999]].
Proof. reflexivity. Qed.

Example ex5_paths : TraceDenotation.execution_wp ex5 [[999]] =
    [[500; 900; 501; 502; 504; 999];
     [500; 901; 503; 504; 999]].
Proof. reflexivity. Qed.

Example ex6_prefix_conditional_paths :
    TraceDenotation.focused_prefix_wp ex6_prefix_conditional [[999]] =
      [[900; 999]; [901; 999]].
Proof. reflexivity. Qed.

Example ex7_paths : TraceDenotation.execution_wp ex7 [[999]] =
    [[100; 900; 701; 703; 705; 999];
     [100; 901; 702; 704; 705; 999]].
Proof. reflexivity. Qed.
