From stdpp Require Export binders strings.
From stdpp Require Import countable.
From stdpp Require Export namespaces.
From stdpp Require Import gmap list sets.

From iris Require Import options.
From iris.algebra Require Import ofe cmra agree auth gset gmap.
From iris.bi Require Import derived_laws.
From iris.bi.lib Require Import fixpoint_mono.
From iris.base_logic Require Import upred.
From iris.base_logic.lib Require Export own.
From iris.base_logic.lib Require Import ghost_map.
From iris.base_logic.lib Require Import invariants.

From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.

From raven_iris.simp_raven_lang Require Import lang lifting ghost_state.
From raven_iris.rich_raven_lang Require Import rrl_lang.
Require Import Coq.Logic.FunctionalExtensionality.

(* "All", not "Type": with this many Let-bound cross-file names in one
   Section, "Type" mode's minimization guesses wrong far more often here
   than in rrl_lang.v, and the guess-then-fix cycle for the same handful
   of trivial early lemmas got repetitive. "All" trades that for a
   different, rarer failure mode (a lemma whose statement doesn't
   determine P/G/Gamma at its call site, needing a `@name P G Γ`-style
   explicit instantiation) -- fixed per-site as encountered, same as any
   other implicit-argument inference gap. *)
Set Default Proof Using "All".


Section MainTranslation.
    (* None of rrl_lang.v's own Section variables carry across files --
       Sigma/Gs/I/simpLangG live inside its own Section WithProgram (see
       rrl_lang.v's own header comment), same status as
       Program/GhostConfig/Gamma/invTokenG below -- redeclared here under
       the same names/projections so every bare use below works without
       qualification; cross-file calls into rrl_lang.v's own definitions
       (ProgramWF, RavenHoareTriple, trnsl_assertion, entails, ...) need
       these supplied explicitly, since Coq has no way to know trnsl.v's
       own Sigma/RProg/G/Gamma are "the same" as rrl_lang.v's without
       being told. *)
    Context {I : Type}.
    Context (Gs : I → cmra).
    Context {Σ : gFunctors}.
    Context `{!inGs Σ Gs}.
    (* gmap.gmapUR, not the bare gmapUR notation: trnsl.v's own `From stdpp
       Require Import gmap` shadows iris.algebra.gmap's own gmapUR with
       stdpp's unrelated one of the same name; qualifying avoids the
       ambiguity and matches rrl_lang.v's own inG instance exactly (needed
       so Coq recognizes this as literally the same instance, not just a
       convertible one). *)
    Context `{!inG Σ (authR (gmap.gmapUR heap_addr (agreeR gnameO)))}.
    Context `{!simpLangG Σ}.
    Context {RProg : Program}.
    Context {G : GhostConfig}.
  Definition transport {A B : Type} (H : A = B) (x : A) : B :=
    eq_rect A id x _ H.

  Lemma transport_sym : forall (A B : Type) (H : A = B) (x : B),
     (transport H (transport (eq_sym H) x)) = x.
  Proof.
    intros. unfold transport. destruct H. simpl. reflexivity.
  Qed.

  Lemma transport_cancel : forall (A B : Type) (H : A = B) (x : A),
    transport (eq_sym H) (transport H x) = x.
  Proof.
    intros. unfold transport. destruct H. simpl. reflexivity.
  Qed.

  Lemma eq_rect_transport_comp : forall (R: RA_Pack) (U : Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)) (c : U),
  eq_rect (RA_carrier R) (λ T : Type, T → T → T) (RA_inst R).(comp) U Heq_car (transport Heq_car x) c = 
  transport Heq_car ((RA_inst R).(comp) x (transport (eq_sym Heq_car) c)).
Proof.
  intros. unfold transport. destruct Heq_car. simpl. reflexivity.
Qed.


  Lemma eq_rect_transport_valid : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)),
    eq_rect (RA_carrier R) (λ T : Type, T -> Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car x) ->
    (RA_inst R).(valid) x.
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Lemma eq_rect_transport_valid_inv : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (x : (RA_carrier R)),
    (RA_inst R).(valid) x ->
    eq_rect (RA_carrier R) (λ T : Type, T -> Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car x).
    
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  Lemma eq_rect_transport_inv_comp_valid : forall (R: RA_Pack) (U: Type) (Heq_car : (RA_carrier R) = U) (y : (RA_carrier R)) (c: U),
    (RA_inst R).(valid) ((RA_inst R).(comp) y (transport (eq_sym Heq_car) c)) ->
    eq_rect (RA_carrier R) (λ T : Type, T → Prop) (RA_inst R).(valid) U Heq_car (transport Heq_car ((RA_inst R).(comp) y (transport (eq_sym Heq_car) c))).
  Proof.
    intros. unfold transport in *. destruct Heq_car. simpl in *. done.
  Qed.

  (* Γ is scoped to ra_set, not universally quantified over *every*
     RA_Pack: every actual call site only ever applies it as Γ (ra_map r)
     for some r : ra_name -- and a concrete Γ witness genuinely cannot be total
     over arbitrary RA_Pack (infinitely many possible carrier types, so
     no finite Sigma could provide a matching camera slot for every one).
     option-valued (not a r ∈ ra_set proof obligation threaded through
     every call site): a concrete Γ only needs to answer for the
     program's own, finite ra_set; every other r maps to None, mirroring
     inv_map/pred_map's own partial-lookup shape (trnsl_assertion_str's
     LGhostOwn case below matches on this the same way LInv/LPred already
     match on inv_map/pred_map !! _). *)
  Definition Γ_witness (r : ra_name) := { i : I & { U : ucmra |
      CmraDiscrete U /\
      { Heq_car : RA_carrier (ra_map r) = ucmra_car U |
          ucmra_cmraR U = Gs i /\
          ucmra_op U = eq_rect (RA_carrier (ra_map r)) (fun T => T -> T -> T) ((RA_inst (ra_map r)).(comp)) (ucmra_car U) Heq_car /\
          ucmra_valid U = eq_rect (RA_carrier (ra_map r)) (fun T => T -> Prop) ((RA_inst (ra_map r)).(valid)) (ucmra_car U) Heq_car
      }
  } } .

  (* A bespoke option, not stdlib's: Γ_witness r's own large (ucmra-valued)
     type doesn't fit stdlib option's fixed universe, triggering a
     universe inconsistency -- irrelevant to what this needs (just "found
     or not"), so a fresh, unconstrained Inductive sidesteps it. *)
  Inductive Γ_answer (r : ra_name) :=
  | Γ_found (w : Γ_witness r)
  | Γ_absent.
  Arguments Γ_found {r} w.
  Arguments Γ_absent {r}.

  Definition Γ_type := forall r : ra_name, Γ_answer r.

  Lemma RAPack_fpuValid (Γ: Γ_type) (r : ra_name) (w : Γ_witness r) :
    Γ r = Γ_found w ->
    forall x y : RA_carrier (ra_map r),
      let '(existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Hcmra (conj Hop Hvalid)))))) := w in
      (RA_inst (ra_map r)).(fpuValid) x y -> (transport Heq_car x) ~~> (transport Heq_car y).
  Proof.
    intros Heq x y.
    destruct w as [i [U [Hdisc [Heq_car [Hindx [Hcomp Hval]]]]]].
    intros Hfpu.

    intros n c Hvalid.
    destruct c as [c|].

    - simpl in *.

    (* make the dot-notation explicit so we can rewrite the op *)
    change (transport Heq_car x ⋅ c) with (ucmra_op U (transport Heq_car x) c) in Hvalid.
    rewrite Hcomp in Hvalid.
    (* bring the context back to the (ra_map r)-side by destructing the equality *)
    apply cmra_discrete_valid_iff.
    apply cmra_discrete_valid_iff in Hvalid.
    change (✓ (transport Heq_car y ⋅ c)) with (ucmra_valid U (transport Heq_car y ⋅ c)).
    rewrite Hval.
    unfold transport.

    set (cR := transport (eq_sym Heq_car) c).
    assert ((RA_inst (ra_map r)).(valid) ((RA_inst (ra_map r)).(comp) y cR)). {
      apply (fpuAxiom x y); [done | ].

      rewrite eq_rect_transport_comp in Hvalid.
      unfold cR.
      change (✓ transport Heq_car (comp x (transport (eq_sym Heq_car) c))) with ((ucmra_valid U) (transport Heq_car ((RA_inst (ra_map r)).(comp) x (transport (eq_sym Heq_car) c)))) in Hvalid.

      rewrite Hval in Hvalid.
      apply (eq_rect_transport_valid (ra_map r) (ucmra_car U) Heq_car). done.
    }

    subst cR.

    change (eq_rect (RA_carrier (ra_map r)) (λ T : Type, T → Prop) (RA_inst (ra_map r)).(valid) U Heq_car ((ucmra_op U) (eq_rect (RA_carrier (ra_map r)) id y U Heq_car) c)).

    rewrite Hcomp.
    rewrite eq_rect_transport_comp.

    apply eq_rect_transport_inv_comp_valid.
    done.

    - simpl in *. apply cmra_discrete_valid_iff. apply cmra_discrete_valid_iff in Hvalid.

    apply (fpuAxiom x y) in Hfpu.
    destruct Hfpu as [_ [HvVal _]].
    change (@cmra.valid (cmra_car (ucmra_cmraR U)) (cmra_valid (ucmra_cmraR U))) with (ucmra_valid U).
    rewrite Hval.
    apply eq_rect_transport_valid_inv. done.
  Qed.


    Context {Γ : Γ_type}.
    Context `{!invTokenG Σ}.

    (* Notation, not Let: a Let-bound alias is a genuinely new constant,
       definitionally but not syntactically equal to the projection/
       application it abbreviates -- confirmed to break `rewrite`'s
       head-symbol matching against goals produced by directly calling
       the aliased rrl_lang.v lemma/definition with explicit RProg/G/Γ
       (same root cause as the ra_map/val Section-wrapping attempt's
       "convertible but not identical" tactic friction, recurring here
       for a much smaller, local reason). Notation is pure text
       substitution, so every occurrence -- including ones reached only
       by unfolding a called lemma's own conclusion -- elaborates to the
       identical term. *)
    Local Notation proc_set := (RProg.(prog_proc_set)).
    Local Notation pred_set := (RProg.(prog_pred_set)).
    Local Notation inv_set := (RProg.(prog_inv_set)).
    Local Notation fld_set := (RProg.(prog_fld_set)).
    Local Notation proc_map := (RProg.(prog_proc_map)).
    Local Notation inv_map := (RProg.(prog_inv_map)).
    Local Notation pred_map := (RProg.(prog_pred_map)).
    Local Notation ghost_heap_name := (G.(gc_ghost_heap_name)).
    Local Notation ghost_heap_namespace := (G.(gc_ghost_heap_namespace)).
    Local Notation inv_namespace_map := (G.(gc_inv_namespace_map)).
    Local Notation ProgramWF := (@ProgramWF Σ invTokenG0 RProg G).
    Local Notation RavenHoareTriple := (@RavenHoareTriple RProg).
    Local Notation stmt_well_defined := (@stmt_well_defined RProg).
    Local Notation alloc_stmt_well_defined := (@alloc_stmt_well_defined RProg).
    Local Notation fresh_proc_entry_lvars := (@fresh_proc_entry_lvars G).
    Local Notation proc_bodies_translate := (@proc_bodies_translate RProg).
    Local Notation StackFree := (@StackFree RProg).
    Local Notation typeOf_val_has_typ := (@typeOf_val_has_typ G).



  Fixpoint trnsl_assertion_str (F : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) 
    (a: assertion) (stk_id: stack_id) (mp: symb_map) : 
     (iPropO Σ) :=      
      match a with
    | LProc p p_e => 
      match p_e with
        Proc args locals pre post body => 
          match trnsl_stmt body with
          | None' =>
            (proc_tbl_chunk p (
              lang.Proc p args locals lang.SkipS
            ))
          | Some' stmt =>
            (proc_tbl_chunk p (
              lang.Proc p args locals stmt
            ))
          | Error => 
            (False)%I
          end
      end
    | LStack σ => (stack_frame_own stk_id (symb_stk_to_stk_frm σ mp))
    | LExprA l_expr => 
      (⌜LExpr_holds l_expr mp⌝%I)
    
    | LPure p => (⌜ p ⌝%I)
    (* chunk is an LExpr, not a concrete val: existentially quantify over the
       concrete value it evaluates to, guarded by a purity fact. If chunk
       doesn't evaluate (or isn't RA-typed with the right ra_name, for
       LGhostOwn), no witness exists and the assertion is (correctly) False. *)
    | LOwn l_expr fld chunk_expr =>
      (∃ l: lang.loc, ∃ chunk : val, (
        ⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗
        ⌜interp_lexpr chunk_expr mp = Some chunk⌝ ∗
        (l#fld ↦{ 1 } (trnsl_lval chunk))
        )%I)%I

    (* Fragment of Wghost's authoritative map (see Section GhostHeapWorld,
       below), keyed by (l, fld) via heap_addr -- not a bare per-key own, so
       that HeapAllocRule can *mint* fresh ghost ownership by growing one
       standing authoritative resource, the same way LOwn's own fragments
       come from growing heap_interp. *)
    (* γ names a freshly own_alloc'd ghost cell for this (l, fld) key,
       recorded once and for all in Wghost's own standing map (see Section
       GhostHeapWorld below) -- the map only ever holds this naming
       binding, agreement-typed and never updated post-insertion; the
       actual RA ownership lives directly at γ via a bare own, exactly as
       in the original ghost_map design, so FPURule's frame-preserving
       update never has to touch the map at all. *)
    | LGhostOwn l_expr fld RAPack chunk_expr =>
      (* RAPack not in ra_set (Γ RAPack = Γ_absent) is vacuously True,
         mirroring LInv/LPred's own "name not declared" case below --
         never actually reached for a well-formed program's own LGhostOwn
         nodes, only needed for trnsl_assertion_str's own totality. *)
      match Γ RAPack with
      | Γ_absent => True%I
      | Γ_found (existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Heq_cmra (conj Hop Hvalid)))))) =>
        let HinG := inGs_inG i in
        (∃ l : lang.loc, ∃ chunk : RA_carrier (ra_map RAPack), ∃ γ : gname, (
          ⌜LExpr_holds (LBinOp EqOp l_expr (LVal (LitLoc l))) mp⌝ ∗
          ⌜interp_lexpr chunk_expr mp = Some (LitRAElem (existT RAPack chunk))⌝ ∗
          own ghost_heap_name
             (◯ {[ heap_addr_constr l fld := to_agree γ ]} : authR (gmap.gmapUR heap_addr (agreeR gnameO))) ∗
          (own γ (transport (f_equal cmra_car Heq_cmra) (transport Heq_car chunk)) (inG0 := HinG))))%I
      end
    | LForall v _t body =>
       (∀ v':lang.val, (trnsl_assertion_str F body stk_id mp))%I

    (* Restricted to witnesses matching t (the binder's declared type, per
       the LExists/LForall AST's own type annotation) -- this is what lets
       ExistsElimRule's soundness case get its witness's well-typedness for
       free from destructuring the existential, rather than needing a
       separate witness_well_typed side-condition proved per rule use. *)
    | LExists v t body =>
      (∃ v': val, ⌜typ_val_match t v'⌝ ∗
           (trnsl_assertion_str F body stk_id (λ x, if String.eqb x v then v' else mp x))
    )%I
    
    (* Generalizes LImpl's own translation (an implication is the special
       case whose else_ branch, LPure True, makes the second conjunct
       trivially provable regardless of cnd). *)
    | LIte cnd then_ else_ =>
      ((⌜LExpr_holds cnd mp⌝ -∗ (trnsl_assertion_str F then_ stk_id mp)) ∧
       (⌜¬ LExpr_holds cnd mp⌝ -∗ (trnsl_assertion_str F else_ stk_id mp)))%I

    (* Nominal, and therefore a *base case*: an invariant assertion owns a
       discrete fragment naming the invariant and its argument vector.  It
       never looks at the body, so it needs no guard and -- crucially -- is
       Timeless.  The body lives in the shared world [Winv] below. *)
    | LInv inv' args =>
        match inv_map !! inv' with
        | Some _ =>
          (∃ vs : list val,
            ⌜Forall2 (λ le v, interp_lexpr le mp = Some v) args vs⌝ ∗
            own (invtoken_names inv') (◯ ({[ vs ]} : inv_argsUR)))%I
        | None => True%I
        end

    | LPred pred args =>
        match pred_map !! pred with
        | Some pred_record =>
          let subst_map := list_to_map (zip pred_record.(pred_args) args) in

          (F (subst pred_record.(pred_body) subst_map) stk_id mp)%I
        | None => True%I
        end

    | LAnd a1 a2 => 
      ( ((trnsl_assertion_str F a1 stk_id mp) ∗ (trnsl_assertion_str F a2 stk_id mp)))%I
    end.

  Definition trnsl_assertion_pre (F : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) :
     assertion -d> stack_id -d> symb_map -d> (iPropO Σ) := λ a stk_id mp, trnsl_assertion_str F a stk_id mp.

(* --- The translation is a Knaster--Tarski least fixpoint --------------------
   Neither [LInv] (a discrete ownership fragment) nor [LPred] (a plain
   recursive call) is guarded, so [trnsl_assertion_pre] isn't
   Contractive and the step-indexed [fixpoint] is unavailable.  What survives
   -- and is all that is needed -- is monotonicity in the [⊢] order, which is
   exactly [BiMonoPred].  Raven's typing rules (resource assertions never
   appear under negation or to the left of an implication) are what guarantee
   it.  -------------------------------------------------------------------- *)

Definition trnsl_dom : Type := (assertion * stack_id * symb_map)%type.

Definition trnsl_assertion_curry (Φ : leibnizO trnsl_dom → iProp Σ) :
    assertion -d> stack_id -d> symb_map -d> (iPropO Σ) :=
  λ a stk_id mp, Φ (a, stk_id, mp).

Definition trnsl_assertion_F (Φ : leibnizO trnsl_dom → iProp Σ) :
    leibnizO trnsl_dom → iProp Σ :=
  λ x, trnsl_assertion_str (trnsl_assertion_curry Φ) x.1.1 x.1.2 x.2.

(* Every function out of a leibnizO domain is non-expansive. *)
Local Lemma leibniz_dom_ne (Φ : leibnizO trnsl_dom → iProp Σ) : NonExpansive Φ.
Proof. intros n x y Heq. change (x = y) in Heq. by subst. Qed.

(* Monotonicity of the assertion-translation functional, by structural
   induction on the assertion.  [LPred] is the only clause that consults its
   argument. *)
Local Lemma trnsl_assertion_str_mono
    (Φ Ψ : assertion -d> stack_id -d> symb_map -d> (iPropO Σ)) (a : assertion) :
  ∀ (stk : stack_id) (mp : symb_map),
  □ (∀ a' stk' mp', Φ a' stk' mp' -∗ Ψ a' stk' mp') ⊢
  trnsl_assertion_str Φ a stk mp -∗ trnsl_assertion_str Ψ a stk mp.
Proof.
  induction a; intros stk mp; simpl.
  - (* LProc *) iIntros "_ H". iExact "H".
  - (* LStack *) iIntros "_ H". iExact "H".
  - (* LExprA *) iIntros "_ H". iExact "H".
  - (* LPure *) iIntros "_ H". iExact "H".
  - (* LOwn *) iIntros "_ H". iExact "H".
  - (* LGhostOwn *)
    destruct (Γ r) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ];
      iIntros "_ H"; iExact "H".
  - (* LForall *)
    iIntros "#Hmon H" (v').
    iDestruct (IHa stk mp with "Hmon") as "IH".
    iDestruct ("H" $! v') as "H'". by iApply "IH".
  - (* LExists *)
    iIntros "#Hmon H". iDestruct "H" as (v') "[%Htyp H]". iExists v'. iSplitR; [done|].
    iDestruct (IHa stk (λ x, if String.eqb x v then v' else mp x) with "Hmon") as "IH".
    by iApply "IH".
  - (* LIte *)
    iIntros "#Hmon H". iSplit.
    + iIntros "%Hc". iDestruct (IHa1 stk mp with "Hmon") as "IH1". iApply "IH1". iDestruct "H" as "[H _]". by iApply "H".
    + iIntros "%Hc". iDestruct (IHa2 stk mp with "Hmon") as "IH2". iApply "IH2". iDestruct "H" as "[_ H]". by iApply "H".
  - (* LInv: base case, no recursive occurrence *)
    match goal with |- context [inv_map !! ?x] => destruct (inv_map !! x) end;
      iIntros "_ H"; iExact "H".
  - (* LPred: the one genuinely recursive clause *)
    match goal with |- context [pred_map !! ?x] =>
      destruct (pred_map !! x) as [pred_record|] end;
      [| iIntros "_ H"; iExact "H"].
    iIntros "#Hmon H". by iApply "Hmon".
  - (* LAnd *)
    iIntros "#Hmon [H1 H2]".
    iDestruct (IHa1 stk mp with "Hmon") as "IH1".
    iDestruct (IHa2 stk mp with "Hmon") as "IH2".
    iSplitL "H1"; [by iApply "IH1" | by iApply "IH2"].
Qed.

Global Instance trnsl_assertion_F_mono : BiMonoPred trnsl_assertion_F.
Proof.
  split; last first.
  { intros Φ _ n x y Heq. change (x = y) in Heq. by subst. }
  intros Φ Ψ HΦ HΨ. iIntros "#Hmon" ([[a stk] mp]).
  rewrite /trnsl_assertion_F /=.
  iApply (trnsl_assertion_str_mono (trnsl_assertion_curry Φ) (trnsl_assertion_curry Ψ) a stk mp).
  rewrite /trnsl_assertion_curry.
  iIntros "!>" (a' stk' mp') "H". by iApply "Hmon".
Qed.

Definition trnsl_assertion : assertion -d> stack_id -d> symb_map -d> (iPropO Σ) :=
  λ a stk mp, bi_least_fixpoint trnsl_assertion_F (a, stk, mp).

Global Arguments trnsl_assertion : simpl never.

Lemma trnsl_assertion_unfold a stk mp :
  trnsl_assertion a stk mp ≡ trnsl_assertion_pre trnsl_assertion a stk mp.
Proof. exact (least_fixpoint_unfold trnsl_assertion_F (a, stk, mp)). Qed.

(* Per-constructor unfolding lemmas: [trnsl_assertion_unfold] leaves the direct
   subterms in [trnsl_assertion_str]-applied form, which these fold back. *)
Lemma trnsl_assertion_and a1 a2 stk mp :
  trnsl_assertion (LAnd a1 a2) stk mp ⊣⊢
  trnsl_assertion a1 stk mp ∗ trnsl_assertion a2 stk mp.
Proof.
  rewrite (trnsl_assertion_unfold (LAnd a1 a2)) /trnsl_assertion_pre /=.
  apply bi.sep_proper; symmetry; apply trnsl_assertion_unfold.
Qed.

Lemma trnsl_assertion_forall v t body stk mp :
  trnsl_assertion (LForall v t body) stk mp ⊣⊢
  (∀ _ : lang.val, trnsl_assertion body stk mp).
Proof.
  rewrite (trnsl_assertion_unfold (LForall v t body)) /trnsl_assertion_pre /=.
  apply bi.forall_proper. intros _. symmetry. apply trnsl_assertion_unfold.
Qed.

Lemma trnsl_assertion_exists v t body stk mp :
  trnsl_assertion (LExists v t body) stk mp ⊣⊢
  (∃ v' : val, ⌜typ_val_match t v'⌝ ∗ trnsl_assertion body stk (λ x, if String.eqb x v then v' else mp x)).
Proof.
  rewrite (trnsl_assertion_unfold (LExists v t body)) /trnsl_assertion_pre /=.
  apply bi.exist_proper. intros v'. apply bi.sep_proper; [done|]. symmetry. apply trnsl_assertion_unfold.
Qed.

Lemma trnsl_assertion_ite cnd then_ else_ stk mp :
  trnsl_assertion (LIte cnd then_ else_) stk mp ⊣⊢
  (⌜LExpr_holds cnd mp⌝ -∗ trnsl_assertion then_ stk mp) ∧
  (⌜¬ LExpr_holds cnd mp⌝ -∗ trnsl_assertion else_ stk mp).
Proof.
  rewrite (trnsl_assertion_unfold (LIte cnd then_ else_)) /trnsl_assertion_pre /=.
  apply bi.and_proper; apply bi.wand_proper; try done; symmetry; apply trnsl_assertion_unfold.
Qed.

Lemma trnsl_assertion_impl cnd body stk mp :
  trnsl_assertion (LImpl cnd body) stk mp ⊣⊢
  (⌜LExpr_holds cnd mp⌝ -∗ trnsl_assertion body stk mp).
Proof.
  unfold LImpl. rewrite trnsl_assertion_ite.
  rewrite (trnsl_assertion_unfold (LPure True)) /trnsl_assertion_pre /=.
  iSplit.
  - iIntros "[H _] %Hc". by iApply "H".
  - iIntros "H". iSplit.
    + iIntros "%Hc". by iApply "H".
    + iIntros "%Hc". done.
Qed.

(* [LInv] denotes a discrete ownership fragment, not an Iris [inv]
   directly. The correspondence with the invariant's body isn't
   definitional; it is mediated by [Winv] and derived in
   [Winv_open]/[Winv_alloc] below. *)
Lemma trnsl_inv_validity' inv' args stk mp :
  match inv_map !! inv' with
  | Some _ =>
      trnsl_assertion (LInv inv' args) stk mp ⊣⊢
      (∃ vs : list val,
         ⌜Forall2 (λ le v, interp_lexpr le mp = Some v) args vs⌝ ∗
         own (invtoken_names inv') (◯ ({[ vs ]} : inv_argsUR)))
  | None => True
  end.
Proof.
  destruct (inv_map !! inv') eqn:HInv; try done.
  rewrite (trnsl_assertion_unfold (LInv inv' args)) /trnsl_assertion_pre /=.
  rewrite HInv. done.
Qed.

Lemma trnsl_assertion_LInv_some inv' r args stk mp :
  inv_map !! inv' = Some r →
  trnsl_assertion (LInv inv' args) stk mp ⊣⊢
  (∃ vs : list val, ⌜Forall2 (λ le v, interp_lexpr le mp = Some v) args vs⌝ ∗
                    own (invtoken_names inv') (◯ ({[ vs ]} : inv_argsUR))).
Proof.
  intros Hr. have Hv := trnsl_inv_validity' inv' args stk mp.
  rewrite Hr in Hv. exact Hv.
Qed.

(* [LInv] is a fragment of a core-id (gset) camera, hence duplicable -- which
   is what makes an invariant fact freely shareable, as it must be. *)
Global Instance trnsl_assertion_LInv_persistent inv' args stk mp :
  Persistent (trnsl_assertion (LInv inv' args) stk mp).
Proof.
  destruct (inv_map !! inv') as [r|] eqn:Hr.
  - rewrite (trnsl_assertion_LInv_some inv' r args stk mp Hr). apply _.
  - have Hv := trnsl_inv_validity' inv' args stk mp. rewrite Hr in Hv.
    rewrite (trnsl_assertion_unfold (LInv inv' args)) /trnsl_assertion_pre /=.
    rewrite Hr. apply _.
Qed.

(* [LProc]'s own proc_tbl_chunk fragment is persistent (see its definition),
   so the procedure-registration fact is freely shareable too -- needed so a
   recursive call can keep re-supplying it, the same way an invariant fact
   is freely shareable across an unbounded number of accesses. *)
Global Instance trnsl_assertion_LProc_persistent p pe stk mp :
  Persistent (trnsl_assertion (LProc p pe) stk mp).
Proof.
  rewrite (trnsl_assertion_unfold (LProc p pe)) /trnsl_assertion_pre /=.
  destruct pe. destruct (trnsl_stmt body); apply _.
Qed.

(* Overriding mp at a lvar the assertion doesn't depend on (lvar_fresh_in_assertion)
   leaves its translation unchanged, covering LStack and LForall too: it
   never manipulates the AST via subst (which would be a no-op on
   LStack's own stored map, so a subst-based approach couldn't cover it),
   just mp directly. LPred still needs excluding: its
   recursion goes through the *global* pred_map table, not a structural
   subterm of a, so a plain induction on a can't produce an induction
   hypothesis for it (the existing subst_congr_cond/least_fixpoint_ind
   machinery handles that shape of problem, but only for StackFree
   assertions -- LStack is exactly what it excludes). Neither of this
   lemma's two target use sites (an invariant body's own existential, or an
   InvAccessBlockRule-style postcondition witness) needs LPred. *)
Lemma trnsl_assertion_mp_irrelevant (v : lvar) (a : assertion) (v' : val) (stk : stack_id) (mp : symb_map) :
  lvar_fresh_in_assertion v a ->
  trnsl_assertion a stk (fun y => if (y =? v)%string then v' else mp y)
  ≡ trnsl_assertion a stk mp.
Proof.
  revert mp.
  induction a as
    [ pn pe
    | sg
    | pexp
    | pp
    | oe ofld ochunk
    | ge gfld gr gchunk
    | fv ft fbody IHf
    | ev et ebody IHe
    | icond ithen IHi1 ielse IHi2
    | ivn iargs
    | pdn pargs
    | a1 IH1 a2 IH2 ];
    intros mp Hfresh; simpl in Hfresh.
  - (* LProc *)
    rewrite (trnsl_assertion_unfold (LProc pn pe))
            (trnsl_assertion_unfold (LProc pn pe)) /trnsl_assertion_pre /=.
    destruct pe. destruct (trnsl_stmt body); done.
  - (* LStack *) simpl.
    rewrite (trnsl_assertion_unfold (LStack sg)) (trnsl_assertion_unfold (LStack sg))
            /trnsl_assertion_pre /=.
    assert (symb_stk_to_stk_frm sg (fun y => if (y =? v)%string then v' else mp y)
            = symb_stk_to_stk_frm sg mp) as Heq.
    { unfold symb_stk_to_stk_frm. f_equal.
      apply map_eq. intros v0.
      rewrite !lookup_fmap.
      destruct (sg !! v0) as [lv|] eqn:Hsg; simpl; [ | reflexivity].
      f_equal. f_equal.
      destruct (String.eqb_spec lv v) as [-> | _]; [ | reflexivity].
      exfalso. exact (Hfresh v0 Hsg). }
    rewrite Heq. done.
  - (* LExprA *) simpl.
    rewrite (trnsl_assertion_unfold (LExprA pexp))
            (trnsl_assertion_unfold (LExprA pexp)) /trnsl_assertion_pre /=.
    unfold LExpr_holds. rewrite (interp_lexpr_stable pexp mp v v' Hfresh). done.
  - (* LPure *) simpl.
    rewrite (trnsl_assertion_unfold (LPure pp)) (trnsl_assertion_unfold (LPure pp))
            /trnsl_assertion_pre /=. done.
  - (* LOwn *) simpl. destruct Hfresh as [Hfe Hfc].
    rewrite (trnsl_assertion_unfold (LOwn oe ofld ochunk))
            (trnsl_assertion_unfold (LOwn oe ofld ochunk)) /trnsl_assertion_pre /=.
    apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
    unfold LExpr_holds. simpl.
    rewrite (interp_lexpr_stable oe mp v v' Hfe) (interp_lexpr_stable ochunk mp v v' Hfc).
    done.
  - (* LGhostOwn *) simpl. destruct Hfresh as [Hfe Hfc].
    rewrite (trnsl_assertion_unfold (LGhostOwn ge gfld gr gchunk))
            (trnsl_assertion_unfold (LGhostOwn ge gfld gr gchunk)) /trnsl_assertion_pre /=.
    destruct (Γ gr) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ].
    + apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
      unfold LExpr_holds. simpl.
      rewrite (interp_lexpr_stable ge mp v v' Hfe) (interp_lexpr_stable gchunk mp v v' Hfc).
      done.
    + done.
  - (* LForall: its own binder is already a no-op in trnsl_assertion_str
       (trnsl_assertion_forall), so this is a direct recursion regardless of
       whether fv = v. *)
    rewrite (trnsl_assertion_forall fv ft fbody stk (fun y => if (y =? v)%string then v' else mp y))
            (trnsl_assertion_forall fv ft fbody stk mp).
    apply bi.forall_proper; intros _. exact (IHf mp Hfresh).
  - (* LExists *)
    rewrite (trnsl_assertion_exists ev et ebody stk (fun y => if (y =? v)%string then v' else mp y))
            (trnsl_assertion_exists ev et ebody stk mp).
    apply bi.exist_proper; intros v''. apply bi.sep_proper; [done|].
    destruct (String.eqb_spec ev v) as [-> | Hne].
    + (* shadowed: the outer update at v is immediately overwritten *)
      assert ((fun y => if (y =? v)%string then v''
                         else (fun z => if (z =? v)%string then v' else mp z) y)
              = (fun y => if (y =? v)%string then v'' else mp y)) as Heq.
      { apply functional_extensionality. intros y.
        destruct (String.eqb_spec y v); reflexivity. }
      rewrite Heq. done.
    + (* distinct binders commute *)
      destruct Hfresh as [Heqev | Hfresh]; [exfalso; exact (Hne Heqev) |].
      assert ((fun y => if (y =? ev)%string then v''
                         else (fun z => if (z =? v)%string then v' else mp z) y)
              = (fun y => if (y =? v)%string then v'
                          else (fun z => if (z =? ev)%string then v'' else mp z) y)) as Hswap.
      { apply functional_extensionality. intros y.
        destruct (String.eqb_spec y ev) as [-> | Hyev].
        - rewrite (proj2 (String.eqb_neq ev v) Hne). reflexivity.
        - reflexivity. }
      rewrite Hswap. exact (IHe (fun y => if (y =? ev)%string then v'' else mp y) Hfresh).
  - (* LIte *) destruct Hfresh as [Hfc [Hft Hfe]].
    rewrite (trnsl_assertion_ite icond ithen ielse stk (fun y => if (y =? v)%string then v' else mp y))
            (trnsl_assertion_ite icond ithen ielse stk mp).
    unfold LExpr_holds. rewrite (interp_lexpr_stable icond mp v v' Hfc).
    apply bi.and_proper; apply bi.wand_proper; try done.
    + exact (IHi1 mp Hft).
    + exact (IHi2 mp Hfe).
  - (* LInv *) simpl.
    rewrite (trnsl_assertion_unfold (LInv ivn iargs))
            (trnsl_assertion_unfold (LInv ivn iargs)) /trnsl_assertion_pre /=.
    destruct (inv_map !! ivn); [ | done].
    apply bi.exist_proper; intros vs.
    apply bi.sep_proper; [ | done].
    apply bi.pure_proper.
    revert vs Hfresh. induction iargs as [ | le0 iargs' IHl]; intros vs Hfresh.
    + split; intros H; inversion H; subst; constructor.
    + apply Forall_cons_1 in Hfresh as [Hfresh0 Hfresh'].
      destruct vs as [ | v0 vs']; simpl.
      * split; intros H; inversion H.
      * split; intros H; inversion H as [|? ? ? ? Hh Ht]; subst.
        -- constructor.
           ++ rewrite (interp_lexpr_stable le0 mp v v' Hfresh0) in Hh. exact Hh.
           ++ apply (IHl vs' Hfresh'); exact Ht.
        -- constructor.
           ++ rewrite (interp_lexpr_stable le0 mp v v' Hfresh0). exact Hh.
           ++ apply (IHl vs' Hfresh'); exact Ht.
  - (* LPred *) exfalso. exact Hfresh.
  - (* LAnd *) destruct Hfresh as [Hf1 Hf2].
    rewrite (trnsl_assertion_and a1 a2 stk (fun y => if (y =? v)%string then v' else mp y))
            (trnsl_assertion_and a1 a2 stk mp).
    apply bi.sep_proper; [exact (IH1 mp Hf1) | exact (IH2 mp Hf2)].
Qed.

Lemma trnsl_pred_validity' pred args stk_id mp :
  match pred_map !! pred with
  | Some pred_rec =>
    let subst_map := list_to_map (zip pred_rec.(pred_args) args) in

    (trnsl_assertion (subst pred_rec.(pred_body) subst_map) stk_id mp)%I ≡ trnsl_assertion (LPred pred args) stk_id mp
  | None => true
  end
.
Proof.
  destruct (pred_map !! pred) eqn:HPred; try done.
  simpl.
  rewrite (trnsl_assertion_unfold (LPred pred args)) /trnsl_assertion_pre /=.
  rewrite HPred. done.
Qed.



Definition entails (σ : lvar_typs) (P Q : assertion) :=
  forall stk_id mp, env_typ_well_defined σ mp ->
  ∃ P' Q', trnsl_assertion P stk_id mp = P' /\ trnsl_assertion Q stk_id mp = Q' /\ (P' ⊢  Q')%I.

Lemma entails_intro σ A B :
  (forall stk mp, env_typ_well_defined σ mp -> trnsl_assertion A stk mp ⊢ trnsl_assertion B stk mp) ->
  entails σ A B.
Proof.
  intros H stk mp Henv. exists (trnsl_assertion A stk mp), (trnsl_assertion B stk mp).
  split; [done | split; [done | apply H, Henv]].
Qed.

Lemma entails_refl σ A : entails σ A A.
Proof. apply entails_intro. intros stk mp Henv. done. Qed.

Lemma entails_trans σ A B C : entails σ A B -> entails σ B C -> entails σ A C.
Proof.
  intros H1 H2. apply entails_intro. intros stk mp Henv.
  destruct (H1 stk mp Henv) as [A' [B' [<- [<- H1']]]].
  destruct (H2 stk mp Henv) as [B'' [C' [Heq [<- H2']]]].
  rewrite Heq in H1'. rewrite H1'. exact H2'.
Qed.

(* Commutes a fixed-stack LAnd past a nested LExists into a single top-level
   LExists -- lets ExistsElimRule (subst-free, which only eliminates
   a top-level LExists) still reach an existential nested under
   LAnd (LStack stk) (LAnd _ p), the shape an invariant/predicate body
   naturally appears in via InvAccessBlockRule/etc. Needs v fresh for both
   stk and p, so overriding mp at v (LExists's own translation) leaves them
   untouched -- trnsl_assertion_mp_irrelevant does the rest. *)
Lemma entails_and_stack_exists_swap (σ : lvar_typs) (stk : stack) (v : lvar) (t : typ) (body p : assertion) :
  fresh_lvar stk v ->
  lvar_fresh_in_assertion v p ->
  entails σ (LAnd (LStack stk) (LAnd (LExists v t body) p))
          (LExists v t (LAnd (LStack stk) (LAnd body p))).
Proof.
  intros Hfresh_stk Hfresh_p stk_id mp Henv.
  eexists _, _. split; [reflexivity|]. split; [reflexivity|].
  rewrite trnsl_assertion_and trnsl_assertion_and trnsl_assertion_exists trnsl_assertion_exists.
  iIntros "[Hstk [[%v' [%Htyp Hbody]] Hp]]".
  iExists v'. iSplitR; [done|].
  rewrite trnsl_assertion_and trnsl_assertion_and.
  rewrite (trnsl_assertion_mp_irrelevant v (LStack stk) v' stk_id mp Hfresh_stk).
  rewrite (trnsl_assertion_mp_irrelevant v p v' stk_id mp Hfresh_p).
  iFrame.
Qed.

(* Simpler 2-way version of the above, without a fixed LStack conjunct in
   front -- lets a fresh-lvar rule's own LExists postcondition (e.g.
   VarAssignmentRule's) absorb a sibling frame fact directly. *)
Lemma entails_exists_and_swap (σ : lvar_typs) (v : lvar) (t : typ) (body p : assertion) :
  lvar_fresh_in_assertion v p ->
  entails σ (LAnd (LExists v t body) p) (LExists v t (LAnd body p)).
Proof.
  intros Hfresh_p stk_id mp Henv.
  eexists _, _. split; [reflexivity|]. split; [reflexivity|].
  rewrite trnsl_assertion_and trnsl_assertion_exists trnsl_assertion_exists.
  iIntros "[[%v' [%Htyp Hbody]] Hp]".
  iExists v'. iSplitR; [done|].
  rewrite trnsl_assertion_and.
  rewrite (trnsl_assertion_mp_irrelevant v p v' stk_id mp Hfresh_p).
  iFrame.
Qed.

(* Introduces a fresh existential over an already-known value: v' := mp v,
   justified by env_typ_well_defined + sigma v = t (Henv gives exactly the
   typ_val_match side condition LExists's own translation needs). The
   entails-unconditional-over-mp form of this is NOT provable (nothing
   constrains mp v to be well-typed without Henv) -- this is exactly why
   entails is parameterized by sigma/Henv in the first place. *)
Lemma entails_exists_intro (σ : lvar_typs) (v : lvar) (t : typ) (X : assertion) :
  σ v = t ->
  entails σ X (LExists v t X).
Proof.
  intros Hty stk_id mp Henv.
  eexists _, _. split; [reflexivity|]. split; [reflexivity|].
  rewrite trnsl_assertion_exists.
  assert ((fun y => if (y =? v)%string then mp v else mp y) = mp) as Hself.
  { apply functional_extensionality. intros y.
    destruct (String.eqb_spec y v) as [->|]; reflexivity. }
  iIntros "H".
  iExists (mp v). iSplitR.
  - iPureIntro. specialize (Henv v). rewrite Hty in Henv.
    destruct (σ v), (mp v); simpl in *; try done.
  - rewrite Hself. iExact "H".
Qed.

(* Substituting a concrete value w for lv throughout a qf_assertion, then
   translating at mp, is the same as translating unsubstituted at mp
   updated at lv -- the assertion-level generalization of
   interp_lexpr_subst_var, restricted to the fragment where it holds by
   plain structural induction (no least_fixpoint machinery needed, since
   LPred/LInv -- the only cases that would require it -- are excluded).
   Mirrors trnsl_assertion_mp_irrelevant's proof shape exactly, swapping
   "override mp at a fresh lvar" for "substitute a value for lv". *)
Lemma trnsl_assertion_subst_lv (a : assertion) (lv : lvar) (w : val) (stk : stack_id) (mp : symb_map) :
  qf_assertion a ->
  trnsl_assertion (subst a (<[lv := LVal w]> ∅)) stk mp ≡
  trnsl_assertion a stk (fun y => if (y =? lv)%string then w else mp y).
Proof.
  induction a as
    [ pn pe
    | sg
    | pexp
    | pp
    | oe ofld ochunk
    | ge gfld gr gchunk
    | fv ft fbody IHf
    | ev et ebody IHe
    | icond ithen IHi1 ielse IHi2
    | ivn iargs
    | pdn pargs
    | a1 IH1 a2 IH2 ]; intros Hqf; simpl in Hqf.
  - (* LProc *) exfalso. exact Hqf.
  - (* LStack *) exfalso. exact Hqf.
  - (* LExprA *) simpl.
    rewrite (trnsl_assertion_unfold (LExprA (lexpr_subst pexp (<[lv := LVal w]> ∅))))
            (trnsl_assertion_unfold (LExprA pexp)) /trnsl_assertion_pre /=.
    unfold LExpr_holds. rewrite (interp_lexpr_subst_var pexp lv w mp). done.
  - (* LPure *) simpl.
    rewrite (trnsl_assertion_unfold (LPure pp)) (trnsl_assertion_unfold (LPure pp))
            /trnsl_assertion_pre /=. done.
  - (* LOwn *) simpl.
    rewrite (trnsl_assertion_unfold
              (LOwn (lexpr_subst oe (<[lv := LVal w]> ∅)) ofld (lexpr_subst ochunk (<[lv := LVal w]> ∅))))
            (trnsl_assertion_unfold (LOwn oe ofld ochunk)) /trnsl_assertion_pre /=.
    apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
    unfold LExpr_holds. simpl.
    rewrite (interp_lexpr_subst_var oe lv w mp) (interp_lexpr_subst_var ochunk lv w mp).
    done.
  - (* LGhostOwn *) simpl.
    rewrite (trnsl_assertion_unfold
              (LGhostOwn (lexpr_subst ge (<[lv := LVal w]> ∅)) gfld gr (lexpr_subst gchunk (<[lv := LVal w]> ∅))))
            (trnsl_assertion_unfold (LGhostOwn ge gfld gr gchunk)) /trnsl_assertion_pre /=.
    destruct (Γ gr) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ].
    + apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
      unfold LExpr_holds. simpl.
      rewrite (interp_lexpr_subst_var ge lv w mp) (interp_lexpr_subst_var gchunk lv w mp).
      done.
    + done.
  - (* LForall *) exfalso. exact Hqf.
  - (* LExists *) exfalso. exact Hqf.
  - (* LIte *) exfalso. exact Hqf.
  - (* LInv *) simpl.
    rewrite (trnsl_assertion_unfold (LInv ivn (map (fun e => lexpr_subst e (<[lv := LVal w]> ∅)) iargs)))
            (trnsl_assertion_unfold (LInv ivn iargs)) /trnsl_assertion_pre /=.
    destruct (inv_map !! ivn); [ | done].
    apply bi.exist_proper; intros vs.
    apply bi.sep_proper; [ | done].
    apply bi.pure_proper.
    revert vs. induction iargs as [ | le0 iargs' IHl]; intros vs; simpl.
    + split; intros H; inversion H; subst; constructor.
    + destruct vs as [ | v0 vs']; simpl.
      * split; intros H; inversion H.
      * split; intros H; inversion H as [|? ? ? ? Hh Ht]; subst.
        -- constructor.
           ++ rewrite (interp_lexpr_subst_var le0 lv w mp) in Hh. exact Hh.
           ++ apply IHl; exact Ht.
        -- constructor.
           ++ rewrite (interp_lexpr_subst_var le0 lv w mp). exact Hh.
           ++ apply IHl; exact Ht.
  - (* LPred *) exfalso. exact Hqf.
  - (* LAnd *) destruct Hqf as [Hq1 Hq2]. simpl.
    rewrite (trnsl_assertion_and (subst a1 (<[lv := LVal w]> ∅)) (subst a2 (<[lv := LVal w]> ∅)) stk mp)
            (trnsl_assertion_and a1 a2 stk (fun y => if (y =? lv)%string then w else mp y)).
    apply bi.sep_proper; [exact (IH1 Hq1) | exact (IH2 Hq2)].
Qed.

(* LVar-substitution counterpart of trnsl_assertion_subst_lv (mirrors it
   case-for-case, swapping interp_lexpr_subst_var for
   interp_lexpr_subst_lvar) -- the assertion-level fact backing "swap one
   already-bound lvar for another, given they're co-asserted equal"
   (AE_LExpr_Subst_Eq_Congr). *)
Lemma trnsl_assertion_subst_lvar (a : assertion) (lv lv2 : lvar) (stk : stack_id) (mp : symb_map) :
  qf_assertion a ->
  trnsl_assertion (subst a (<[lv := LVar lv2]> ∅)) stk mp ≡
  trnsl_assertion a stk (fun y => if (y =? lv)%string then mp lv2 else mp y).
Proof.
  induction a as
    [ pn pe
    | sg
    | pexp
    | pp
    | oe ofld ochunk
    | ge gfld gr gchunk
    | fv ft fbody IHf
    | ev et ebody IHe
    | icond ithen IHi1 ielse IHi2
    | ivn iargs
    | pdn pargs
    | a1 IH1 a2 IH2 ]; intros Hqf; simpl in Hqf.
  - (* LProc *) exfalso. exact Hqf.
  - (* LStack *) exfalso. exact Hqf.
  - (* LExprA *) simpl.
    rewrite (trnsl_assertion_unfold (LExprA (lexpr_subst pexp (<[lv := LVar lv2]> ∅))))
            (trnsl_assertion_unfold (LExprA pexp)) /trnsl_assertion_pre /=.
    unfold LExpr_holds. rewrite (interp_lexpr_subst_lvar pexp lv lv2 mp). done.
  - (* LPure *) simpl.
    rewrite (trnsl_assertion_unfold (LPure pp)) (trnsl_assertion_unfold (LPure pp))
            /trnsl_assertion_pre /=. done.
  - (* LOwn *) simpl.
    rewrite (trnsl_assertion_unfold
              (LOwn (lexpr_subst oe (<[lv := LVar lv2]> ∅)) ofld (lexpr_subst ochunk (<[lv := LVar lv2]> ∅))))
            (trnsl_assertion_unfold (LOwn oe ofld ochunk)) /trnsl_assertion_pre /=.
    apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
    unfold LExpr_holds. simpl.
    rewrite (interp_lexpr_subst_lvar oe lv lv2 mp) (interp_lexpr_subst_lvar ochunk lv lv2 mp).
    done.
  - (* LGhostOwn *) simpl.
    rewrite (trnsl_assertion_unfold
              (LGhostOwn (lexpr_subst ge (<[lv := LVar lv2]> ∅)) gfld gr (lexpr_subst gchunk (<[lv := LVar lv2]> ∅))))
            (trnsl_assertion_unfold (LGhostOwn ge gfld gr gchunk)) /trnsl_assertion_pre /=.
    destruct (Γ gr) as [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ].
    + apply bi.exist_proper; intros l. apply bi.exist_proper; intros chunk0.
      unfold LExpr_holds. simpl.
      rewrite (interp_lexpr_subst_lvar ge lv lv2 mp) (interp_lexpr_subst_lvar gchunk lv lv2 mp).
      done.
    + done.
  - (* LForall *) exfalso. exact Hqf.
  - (* LExists *) exfalso. exact Hqf.
  - (* LIte *) exfalso. exact Hqf.
  - (* LInv *) simpl.
    rewrite (trnsl_assertion_unfold (LInv ivn (map (fun e => lexpr_subst e (<[lv := LVar lv2]> ∅)) iargs)))
            (trnsl_assertion_unfold (LInv ivn iargs)) /trnsl_assertion_pre /=.
    destruct (inv_map !! ivn); [ | done].
    apply bi.exist_proper; intros vs.
    apply bi.sep_proper; [ | done].
    apply bi.pure_proper.
    revert vs. induction iargs as [ | le0 iargs' IHl]; intros vs; simpl.
    + split; intros H; inversion H; subst; constructor.
    + destruct vs as [ | v0 vs']; simpl.
      * split; intros H; inversion H.
      * split; intros H; inversion H as [|? ? ? ? Hh Ht]; subst.
        -- constructor.
           ++ rewrite (interp_lexpr_subst_lvar le0 lv lv2 mp) in Hh. exact Hh.
           ++ apply IHl; exact Ht.
        -- constructor.
           ++ rewrite (interp_lexpr_subst_lvar le0 lv lv2 mp). exact Hh.
           ++ apply IHl; exact Ht.
  - (* LPred *) exfalso. exact Hqf.
  - (* LAnd *) destruct Hqf as [Hq1 Hq2]. simpl.
    rewrite (trnsl_assertion_and (subst a1 (<[lv := LVar lv2]> ∅)) (subst a2 (<[lv := LVar lv2]> ∅)) stk mp)
            (trnsl_assertion_and a1 a2 stk (fun y => if (y =? lv)%string then mp lv2 else mp y)).
    apply bi.sep_proper; [exact (IH1 Hq1) | exact (IH2 Hq2)].
Qed.
  (* assertion_entails-typed counterpart of TypeInf's entails_and_stack_exists_swap
     (that version is otherwise unused, since WeakeningRule takes
     assertion_entails, not entails), derived purely compositionally from
     the two swap primitives above: pull the
     LExists past p (AE_Exists_And_Swap_R) under the fixed LStack via
     AE_And_Mono, then past the LStack itself (AE_And_Exists_Swap_L). *)
Section AssertionsProperties.

  (* Effective value of a logical variable under substitution map M and symbolic map mp:
     either interprets the substituted expression, or returns the raw symbolic value. *)
  Definition eval_lvar (M : gmap lvar LExpr) (mp : symb_map) (x : lvar) : option val :=
    match M !! x with
    | Some e => interp_lexpr e mp
    | None => Some (mp x)
    end.

  (* Helper: push interp_lexpr inside a lookup-driven match. Needed because the kernel
     won't reduce `interp_lexpr (match M!!x with …) mp` propositionally without a case split. *)
  Lemma interp_lexpr_lookup_match (M : gmap lvar LExpr) (x : lvar) (mp : symb_map) :
    interp_lexpr (match M !! x with Some e => e | None => LVar x end) mp =
    match M !! x with Some e => interp_lexpr e mp | None => Some (mp x) end.
  Proof. destruct (M !! x); reflexivity. Qed.

  (* If two (M, mp) pairs agree on eval_lvar, lexpr_subst produces the same interp_lexpr result. *)
  Lemma interp_lexpr_lexpr_subst_eval_lvar_congr (e : LExpr) (M1 M2 : gmap lvar LExpr)
      (mp1 mp2 : symb_map) :
    (∀ x, eval_lvar M1 mp1 x = eval_lvar M2 mp2 x) →
    interp_lexpr (lexpr_subst e M1) mp1 = interp_lexpr (lexpr_subst e M2) mp2.
  Proof.
    intro Hbase. induction e; simpl.
    - (* LVar x: rewrite the interp_lexpr-over-match to the distributed form, then use Hbase. *)
      rewrite !interp_lexpr_lookup_match.
      exact (Hbase x).
    - (* LVal *) reflexivity.
    - (* LUnOp *) rewrite IHe. reflexivity.
    - (* LBinOp *) rewrite IHe1; rewrite IHe2. reflexivity.
    - (* LIfE *)
      rewrite IHe1.
      destruct (interp_lexpr (lexpr_subst e1 M2) mp2) as [[b| | | |]|]; try reflexivity.
      destruct b; [exact IHe2 | exact IHe3].
    - (* LStuck *) reflexivity.
  Qed.

  (* Updating q at v leaves eval_lvar M q x unchanged when x ∈ dom M or x ≠ v *)
  Lemma eval_lvar_update_stable (M : gmap lvar LExpr) (q : symb_map) (v : lvar) (v' : val) (x : lvar) :
    v ∉ lexpr_map_fvars M →
    (x ∈ dom M ∨ x ≠ v) →
    eval_lvar M (fun y => if (y =? v)%string then v' else q y) x = eval_lvar M q x.
  Proof.
    intros Hfresh Hcases.
    unfold eval_lvar.
    destruct (M !! x) as [le|] eqn:HMx.
    - (* x ∈ dom M: use interp_lexpr_stable *)
      apply interp_lexpr_stable.
      exact (proj1 (lexpr_map_fvars_spec M v) Hfresh x le HMx).
    - (* x ∉ dom M: x ≠ v by hypothesis *)
      destruct Hcases as [Hdom | Hne].
      + (* x ∈ dom M contradicts M !! x = None *)
        exfalso. rewrite <- not_elem_of_dom in HMx. exact (HMx Hdom).
      + destruct (String.eqb_spec x v) as [Heq | _].
        * exfalso. exact (Hne Heq).
        * reflexivity.
  Qed.

  (* Restricted version: lexpr_fvars e ⊆ dom M1 → Hbase restricted to dom M1 suffices *)
  (* Generalized via is_reserved directly, rather than a fixed gset R:
     reserved names potentially escaping dom M1's coverage (through
     assertion_lexpr_fvars's own over-approximation) aren't confined to a
     single top-level assertion's own binders --
     subst_congr_step below recurses into predicate bodies fetched fresh
     from pred_map (for recursive predicates), which are not syntactic
     subterms of whatever top-level assertion this all started from, so
     a fixed, pre-computed "safe" gset could never be threaded through
     that unfolding. is_reserved, being a uniform predicate rather than
     one assertion's own finite binder set, covers this uniformly.
     Instantiating with "fun _ _ => False" (never reserved) recovers the
     original, unconditional statement. *)
  Lemma interp_lexpr_lexpr_subst_eval_lvar_congr_dom (e : LExpr) (M1 M2 : gmap lvar LExpr)
      (mp1 mp2 : symb_map) :
    (∀ v, v ∈ lexpr_fvars e → v ∈ dom M1 ∨ is_reserved v) →
    (∀ x, x ∈ dom M1 ∨ is_reserved x → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x) →
    interp_lexpr (lexpr_subst e M1) mp1 = interp_lexpr (lexpr_subst e M2) mp2.
  Proof.
    intros Hdom Hbase. induction e; simpl.
    - rewrite !interp_lexpr_lookup_match.
      apply Hbase. apply Hdom. set_solver.
    - reflexivity.
    - simpl in Hdom. rewrite (IHe Hdom). reflexivity.
    - simpl in Hdom.
      have Hd1 : ∀ v, v ∈ lexpr_fvars e1 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      have Hd2 : ∀ v, v ∈ lexpr_fvars e2 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      rewrite (IHe1 Hd1). rewrite (IHe2 Hd2). reflexivity.
    - simpl in Hdom.
      have Hd1 : ∀ v, v ∈ lexpr_fvars e1 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      have Hd2 : ∀ v, v ∈ lexpr_fvars e2 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      have Hd3 : ∀ v, v ∈ lexpr_fvars e3 → v ∈ dom M1 ∨ is_reserved v.
      { intros v Hv. apply Hdom. set_solver. }
      rewrite (IHe1 Hd1).
      destruct (interp_lexpr (lexpr_subst e1 M2) mp2) as [[b| | | |]|]; try reflexivity.
      destruct b.
      + rewrite (IHe2 Hd2). reflexivity.
      + rewrite (IHe3 Hd3). reflexivity.
    - reflexivity.
  Qed.

  (* Restricts an "every fvar is in Z or reserved" bound from a superset Y
     of fvars down to a subset X -- the workhorse for every subterm case
     below, where X is some subterm's own fvars and Y is the whole node's. *)
  Lemma fvars_bound_mono (X Y Z : gset lvar) :
    X ⊆ Y → (∀ v, v ∈ Y → v ∈ Z ∨ is_reserved v) → (∀ v, v ∈ X → v ∈ Z ∨ is_reserved v).
  Proof. intros HXY HY v Hv. exact (HY v (HXY v Hv)). Qed.

  (* Single-map specialization of interp_lexpr_lexpr_subst_eval_lvar_congr_dom:
     agreement only needs to cover e's own fvars directly (no dom/reserved
     framing at all) -- the version used by trnsl_assertion_mp_irrelevant_reserved,
     where the whole point is to avoid needing agreement at reserved names. *)
  Lemma interp_lexpr_subst_eval_lvar_congr_true (e : LExpr) (M : gmap lvar LExpr)
      (mp1 mp2 : symb_map) :
    (∀ x, x ∈ lexpr_fvars e → eval_lvar M mp1 x = eval_lvar M mp2 x) →
    interp_lexpr (lexpr_subst e M) mp1 = interp_lexpr (lexpr_subst e M) mp2.
  Proof.
    induction e; simpl; intro Hbase.
    - rewrite !interp_lexpr_lookup_match. apply Hbase. set_solver.
    - reflexivity.
    - rewrite (IHe ltac:(intros v Hv; apply Hbase; set_solver)). reflexivity.
    - rewrite (IHe1 ltac:(intros v Hv; apply Hbase; set_solver)).
      rewrite (IHe2 ltac:(intros v Hv; apply Hbase; set_solver)). reflexivity.
    - rewrite (IHe1 ltac:(intros v Hv; apply Hbase; set_solver)).
      destruct (interp_lexpr (lexpr_subst e1 M) mp2) as [[b| | | |]|]; try reflexivity.
      destruct b.
      + exact (IHe2 ltac:(intros v Hv; apply Hbase; set_solver)).
      + exact (IHe3 ltac:(intros v Hv; apply Hbase; set_solver)).
    - reflexivity.
  Qed.

  (* Side conditions under which (M1,mp1) and (M2,mp2) assign the same meaning
     to a StackFree assertion:
     - dom M1 = dom M2
     - the assertion's LExpr fvars are covered by dom M1, up to reserved
       names (assertion_lexpr_fvars's own over-approximation through
       LExists/LForall can leak an assertion's own binder names in)
     - its own binders avoid dom/fvars of either map
     - M1/M2 were built by the ordinary framework machinery, so touch no
       reserved name themselves (subst_map_avoids_reserved) -- needed so
       a reserved name can be resolved directly, without depending on
       dom M1 membership, in the leaf/LPred cases below
     - (Hstab) restricted eval_lvar agreement survives an mp update at a binder
     - (Hbase) restricted eval_lvar agreement for mp1 and mp2 themselves,
       covering reserved names too, not just dom M1 -- necessary because
       subst_congr_step recurses into predicate bodies fetched fresh from
       pred_map, which aren't syntactic subterms of whatever top-level
       assertion this all started from, so no fixed, finite "safe" set
       could be threaded through that unfolding; is_reserved, being a
       uniform predicate, covers it regardless of which body a reserved
       name came from. *)
  Definition subst_congr_cond (a : assertion) (M1 M2 : gmap lvar LExpr)
      (mp1 mp2 : symb_map) : Prop :=
    StackFree a ∧
    assertion_exists_binders a ## (dom M1 ∪ lexpr_map_fvars M1) ∧
    assertion_exists_binders a ## (dom M2 ∪ lexpr_map_fvars M2) ∧
    (∀ v, v ∈ assertion_lexpr_fvars a → v ∈ dom M1 ∨ is_reserved v) ∧
    dom M1 = dom M2 ∧
    subst_map_avoids_reserved M1 ∧
    subst_map_avoids_reserved M2 ∧
    (∀ (q1 q2 : symb_map),
      (∀ x, x ∈ dom M1 → eval_lvar M1 q1 x = eval_lvar M2 q2 x) →
      ∀ (v : lvar), v ∉ lexpr_map_fvars M1 → v ∉ lexpr_map_fvars M2 →
      ∀ (v' : val) (x : lvar), x ∈ dom M1 →
      eval_lvar M1 (fun y => if (y =? v)%string then v' else q1 y) x =
      eval_lvar M2 (fun y => if (y =? v)%string then v' else q2 y) x) ∧
    (∀ x, x ∈ dom M1 ∨ is_reserved x → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x).

  (* The side conditions are symmetric, so one entailment direction suffices to
     get the equivalence. *)
  Lemma subst_congr_cond_sym a M1 M2 mp1 mp2 :
    subst_congr_cond a M1 M2 mp1 mp2 → subst_congr_cond a M2 M1 mp2 mp1.
  Proof.
    intros (Hsf & HbA1 & HbA2 & HfvA & HdomEq & Hmr1 & Hmr2 & Hstab & Hbase).
    split_and!; try assumption.
    - intros v Hv. rewrite <- HdomEq. exact (HfvA v Hv).
    - exact (eq_sym HdomEq).
    - intros q1 q2 Hag v Hv2 Hv1 v' x Hx.
      symmetry. apply Hstab; try assumption.
      + intros y Hy. symmetry. apply Hag. rewrite <- HdomEq. exact Hy.
      + rewrite HdomEq. exact Hx.
    - intros x Hx. symmetry. apply Hbase. set_solver.
  Qed.

  (* Transfer of the LInv clause's argument-evaluation side condition. *)
  Local Lemma Forall2_interp_subst_congr (args : list LExpr) (vs : list val)
      (M1 M2 : gmap lvar LExpr) (mp1 mp2 : symb_map) :
    (∀ le, le ∈ args →
       interp_lexpr (lexpr_subst le M1) mp1 = interp_lexpr (lexpr_subst le M2) mp2) →
    Forall2 (λ le v, interp_lexpr le mp1 = Some v)
            (map (λ e, lexpr_subst e M1) args) vs →
    Forall2 (λ le v, interp_lexpr le mp2 = Some v)
            (map (λ e, lexpr_subst e M2) args) vs.
  Proof.
    revert vs. induction args as [| le args IH]; intros vs Heq HF2; simpl in *.
    - inversion HF2. constructor.
    - inversion HF2 as [| le' v args' vs' Hhd Htl Heq1 Heq2]; subst.
      constructor.
      + rewrite <- (Heq le (elem_of_list_here _ _)). exact Hhd.
      + apply IH; [| exact Htl].
        intros le'' Hle''. exact (Heq le'' (elem_of_list_further _ _ _ Hle'')).
  Qed.

  (* Free variables of one argument are bounded by those of the whole list. *)
  Local Lemma lexpr_fvars_elem_subseteq (le : LExpr) (args : list LExpr) :
    le ∈ args → lexpr_fvars le ⊆ ⋃ (lexpr_fvars <$> args).
  Proof.
    intros Hle y Hy. apply elem_of_union_list.
    exists (lexpr_fvars le). split; [| exact Hy].
    apply elem_of_list_fmap. exists le. split; [reflexivity | exact Hle].
  Qed.

  (* The induction hypothesis carried through the least fixpoint: at every
     index, the translation under (M1, mp1) implies the one under (M2, mp2). *)
  Definition subst_congr_Phi (x : leibnizO trnsl_dom) : iProp Σ :=
    (∀ a0 M1 M2 mp2,
       ⌜x.1.1 = subst a0 M1⌝ -∗
       ⌜subst_congr_cond a0 M1 M2 x.2 mp2⌝ -∗
       trnsl_assertion (subst a0 M2) x.1.2 mp2)%I.

  Global Arguments subst_congr_Phi : simpl never.

  Local Instance subst_congr_Phi_ne : NonExpansive subst_congr_Phi.
  Proof. intros n x y Heq. change (x = y) in Heq. by subst. Qed.

  (* One unfolding step of the congruence, by structural induction on the
     assertion; the LInv clause is a leaf and the LPred clause appeals to
     [subst_congr_Phi], i.e. to the fixpoint induction hypothesis. *)
  Local Lemma subst_congr_step (Hwf : ProgramWF) (a0 : assertion) :
    ∀ (M1 M2 : gmap lvar LExpr) (stk : stack_id) (mp1 mp2 : symb_map),
      subst_congr_cond a0 M1 M2 mp1 mp2 →
      trnsl_assertion_str (trnsl_assertion_curry subst_congr_Phi) (subst a0 M1) stk mp1
      ⊢ trnsl_assertion (subst a0 M2) stk mp2.
  Proof.
    induction a0; intros M1 M2 stk mp1 mp2 Hcond;
      destruct Hcond as (Hsf & HbA1 & HbA2 & HfvA & HdomEq & Hmr1 & Hmr2 & Hstab & Hbase);
      simpl in HbA1, HbA2, HfvA;
      (etrans; [| apply bi.equiv_entails_1_2,
                  (trnsl_assertion_unfold (subst _ M2) stk mp2)]).
    - (* LProc: independent of M and mp *) iIntros "H". iExact "H".
    - (* LStack: not StackFree *) inversion Hsf.
    - (* LExprA *)
      apply bi.pure_mono. unfold LExpr_holds.
      rewrite (interp_lexpr_lexpr_subst_eval_lvar_congr_dom p M1 M2 mp1 mp2 HfvA Hbase).
      tauto.
    - (* LPure *) iIntros "H". iExact "H".
    - (* LOwn *)
      apply bi.exist_mono. intro l.
      apply bi.exist_mono. intro chunk0.
      apply bi.sep_mono.
      { apply bi.pure_mono. unfold LExpr_holds.
        have Hfv_dom : ∀ v, v ∈ lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) → v ∈ dom M1 ∨ is_reserved v.
        { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LOwn e fld chunk))); [simpl; set_solver | exact HfvA]. }
        have Hcongr := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
          (LBinOp EqOp e (LVal (LitLoc l))) M1 M2 mp1 mp2 Hfv_dom Hbase.
        simpl in Hcongr |- *. rewrite Hcongr. tauto. }
      apply bi.sep_mono; [| done].
      apply bi.pure_mono. intro Hchunk.
      have Hfv_dom2 : ∀ v, v ∈ lexpr_fvars chunk → v ∈ dom M1 ∨ is_reserved v.
      { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LOwn e fld chunk))); [simpl; set_solver | exact HfvA]. }
      have Hcongr2 := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
        chunk M1 M2 mp1 mp2 Hfv_dom2 Hbase.
      rewrite <- Hcongr2. exact Hchunk.
    - (* LGhostOwn *)
      simpl. generalize (Γ r).
      intros [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ]; [ | done].
      apply bi.exist_mono. intro l.
      apply bi.exist_mono. intro chunk0.
      apply bi.exist_mono. intro γ.
      apply bi.sep_mono.
      { apply bi.pure_mono. unfold LExpr_holds.
        have Hfv_dom : ∀ v, v ∈ lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) → v ∈ dom M1 ∨ is_reserved v.
        { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LGhostOwn e fld r chunk))); [simpl; set_solver | exact HfvA]. }
        have Hcongr := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
          (LBinOp EqOp e (LVal (LitLoc l))) M1 M2 mp1 mp2 Hfv_dom Hbase.
        simpl in Hcongr |- *. rewrite Hcongr. tauto. }
      apply bi.sep_mono; [| done].
      apply bi.pure_mono. intro Hchunk.
      have Hfv_dom2 : ∀ v, v ∈ lexpr_fvars chunk → v ∈ dom M1 ∨ is_reserved v.
      { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LGhostOwn e fld r chunk))); [simpl; set_solver | exact HfvA]. }
      have Hcongr2 := interp_lexpr_lexpr_subst_eval_lvar_congr_dom
        chunk M1 M2 mp1 mp2 Hfv_dom2 Hbase.
      rewrite <- Hcongr2. exact Hchunk.
    - (* LForall: does not update mp, so nothing about a0's own binders
         changes either -- every field carries over unchanged. *)
      inversion Hsf.
      apply bi.forall_mono. intro v'.
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold (subst a0 M2) stk mp2)].
      apply (IHa0 M1 M2 stk mp1 mp2). by split_and!.
    - (* LExists: updates mp at the binder v. Hbase' must cover
         dom M1 ∨ is_reserved: for x ∈ dom M1, Hstab unchanged; for x = v
         (reserved, since v ∈ assertion_exists_binders (LExists v t body)
         is covered by HbA1/HbA2's own bundled dom-disjointness), both
         sides reduce to v' directly, since v ∉ dom M1 ∪ dom M2; for
         x ≠ v with x reserved, the update at v doesn't touch x, so the
         outer Hbase carries over via eval_lvar_update_stable. *)
      inversion Hsf. subst.
      apply bi.exist_mono. intro v'.
      apply bi.sep_mono; [done|].
      have Hv1dom : v ∉ dom M1. { set_solver. }
      have Hv2dom : v ∉ dom M2. { set_solver. }
      have Hv1 : v ∉ lexpr_map_fvars M1. { set_solver. }
      have Hv2 : v ∉ lexpr_map_fvars M2. { set_solver. }
      have Hbase_narrow : ∀ x, x ∈ dom M1 → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x.
      { intros x Hx. apply Hbase. left. exact Hx. }
      have Hbase' : ∀ x, x ∈ dom M1 ∨ is_reserved x →
        eval_lvar M1 (fun y => if (y =? v)%string then v' else mp1 y) x =
        eval_lvar M2 (fun y => if (y =? v)%string then v' else mp2 y) x.
      { intros x Hx. destruct (decide (x ∈ dom M1)) as [HxM | HxM].
        - exact (Hstab mp1 mp2 Hbase_narrow v Hv1 Hv2 v' x HxM).
        - destruct (decide (x = v)) as [-> | Hne].
          + unfold eval_lvar.
            apply not_elem_of_dom in Hv1dom. apply not_elem_of_dom in Hv2dom.
            rewrite Hv1dom Hv2dom /=. rewrite String.eqb_refl. reflexivity.
          + rewrite (eval_lvar_update_stable M1 mp1 v v' x Hv1 (or_intror Hne)).
            rewrite (eval_lvar_update_stable M2 mp2 v v' x Hv2 (or_intror Hne)).
            apply Hbase. destruct Hx as [Hx | Hx]; [contradiction (HxM Hx) | right; exact Hx]. }
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold (subst a0 M2) stk
                    (fun y => if (y =? v)%string then v' else mp2 y))].
      apply (IHa0 M1 M2 stk
        (fun y => if (y =? v)%string then v' else mp1 y)
        (fun y => if (y =? v)%string then v' else mp2 y)).
      split_and!.
      + assumption.
      + set_solver.
      + set_solver.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + exact Hbase'.
    - (* LIte *)
      inversion Hsf. subst.
      have Hfv_cond : ∀ v, v ∈ lexpr_fvars cond → v ∈ dom M1 ∨ is_reserved v.
      { apply (fvars_bound_mono _ (assertion_lexpr_fvars (LIte cond a0_1 a0_2))); [simpl; set_solver | exact HfvA]. }
      apply bi.and_mono.
      + apply bi.wand_mono.
        * apply bi.pure_mono. unfold LExpr_holds.
          rewrite (interp_lexpr_lexpr_subst_eval_lvar_congr_dom cond M1 M2 mp1 mp2 Hfv_cond Hbase). tauto.
        * etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold (subst a0_1 M2) stk mp2)].
          apply (IHa0_1 M1 M2 stk mp1 mp2). split_and!; try assumption.
          -- set_solver.
          -- set_solver.
          -- apply (fvars_bound_mono _ (assertion_lexpr_fvars (LIte cond a0_1 a0_2))); [simpl; set_solver | exact HfvA].
      + apply bi.wand_mono.
        * apply bi.pure_mono. unfold LExpr_holds.
          rewrite (interp_lexpr_lexpr_subst_eval_lvar_congr_dom cond M1 M2 mp1 mp2 Hfv_cond Hbase). tauto.
        * etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold (subst a0_2 M2) stk mp2)].
          apply (IHa0_2 M1 M2 stk mp1 mp2). split_and!; try assumption.
          -- set_solver.
          -- set_solver.
          -- apply (fvars_bound_mono _ (assertion_lexpr_fvars (LIte cond a0_1 a0_2))); [simpl; set_solver | exact HfvA].
    - (* LInv: a leaf -- only the argument evaluations must be transferred *)
      simpl. destruct (inv_map !! inv_name) as [r|] eqn:Hr; [| done].
      apply bi.exist_mono. intro vs. apply bi.sep_mono; [| done].
      apply bi.pure_mono. apply Forall2_interp_subst_congr.
      intros le Hle.
      apply (interp_lexpr_lexpr_subst_eval_lvar_congr_dom le M1 M2 mp1 mp2);
        [| exact Hbase].
      intros v Hv. apply HfvA. exact (lexpr_fvars_elem_subseteq le args Hle v Hv).
    - (* LPred: the fixpoint induction hypothesis fires here. Unlike every
         other case, the recursive body (pred_body) is fetched fresh from
         pred_map, not a syntactic subterm of a0 -- its own binders need
         pwf_pred_binders_reserved (not HbA1/HbA2, which are about a0's
         own, unrelated, empty binder set) combined with Hmr1/Hmr2 to
         re-derive HbA1/HbA2- and HfvA-shaped facts for it. *)
      simpl. destruct (pred_map !! pred_name) as [r|] eqn:Hr; [| done].
      have Hbr1 : assertion_exists_binders r.(pred_body) ## (dom M1 ∪ lexpr_map_fvars M1).
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_pred_binders_reserved) pred_name r Hr).
        - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
            [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
      have Hbr2 : assertion_exists_binders r.(pred_body) ## (dom M2 ∪ lexpr_map_fvars M2).
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_pred_binders_reserved) pred_name r Hr).
        - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
            [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
      have HPredBodyWF := pred_body_wf_from_scoped r
        (Hwf.(pwf_pred_fvars_scoped) pred_name r Hr).
      inversion Hsf. rewrite Hr in H1. inversion H1. subst pred_record.
      rewrite (HPredBodyWF args M1 H2 ltac:(set_solver));
        rewrite (HPredBodyWF args M2 H2 ltac:(set_solver)).
      rewrite /trnsl_assertion_curry.
      iIntros "H".
      iApply ("H" $! (subst r.(pred_body) (list_to_map (zip r.(pred_args) args)))
                 M1 M2 mp2); iPureIntro; [reflexivity |].
      split_and!; try assumption.
      + rewrite assertion_exists_binders_subst. exact Hbr1.
      + rewrite assertion_exists_binders_subst. exact Hbr2.
      + intros v Hv.
        destruct (Hwf.(pwf_pred_fvars_bounded) pred_name r args Hr H2 v Hv) as [Hin | Hin].
        * exact (HfvA v Hin).
        * right. exact (Hwf.(pwf_pred_binders_reserved) pred_name r Hr v Hin).
    - (* LAnd *)
      inversion Hsf. subst.
      apply bi.sep_mono.
      + etrans; [| apply bi.equiv_entails_1_1,
                   (trnsl_assertion_unfold (subst a0_1 M2) stk mp2)].
        apply (IHa0_1 M1 M2 stk mp1 mp2). split_and!; try assumption.
        * set_solver.
        * set_solver.
        * apply (fvars_bound_mono _ (assertion_lexpr_fvars (LAnd a0_1 a0_2))); [simpl; set_solver | exact HfvA].
      + etrans; [| apply bi.equiv_entails_1_1,
                   (trnsl_assertion_unfold (subst a0_2 M2) stk mp2)].
        apply (IHa0_2 M1 M2 stk mp1 mp2). split_and!; try assumption.
        * set_solver.
        * set_solver.
        * apply (fvars_bound_mono _ (assertion_lexpr_fvars (LAnd a0_1 a0_2))); [simpl; set_solver | exact HfvA].
  Qed.

  (* One direction of the congruence. *)
  Lemma trnsl_assertion_subst_mono (Hwf : ProgramWF)
      (a : assertion) (M1 M2 : gmap lvar LExpr) stk_id (mp1 mp2 : symb_map) :
    subst_congr_cond a M1 M2 mp1 mp2 →
    trnsl_assertion (subst a M1) stk_id mp1 ⊢ trnsl_assertion (subst a M2) stk_id mp2.
  Proof.
    intros Hcond.
    iIntros "H".
    iDestruct (least_fixpoint_iter trnsl_assertion_F subst_congr_Phi with "[] H") as "H'".
    { iIntros "!>" ([[b stk'] mp']) "HF".
      rewrite /subst_congr_Phi /=.
      iIntros (a0 M1' M2' mp2') "-> %Hc".
      by iApply (subst_congr_step Hwf a0 M1' M2' stk' mp' mp2' Hc). }
    rewrite /subst_congr_Phi /=.
    iApply ("H'" $! a M1 M2 mp2); iPureIntro; [reflexivity | exact Hcond].
  Qed.

  (* Common generalization:
     If (M1, mp1) and (M2, mp2) agree on eval_lvar for x ∈ dom M1 (Hbase),
     and eval_lvar agreement is preserved under mp updates at v ∉ lexpr_map_fvars M,
     then translating the same StackFree assertion under both maps yields equivalent props. *)
  Lemma trnsl_assertion_subst_congr
    (Hwf : ProgramWF)
    (a : assertion) (M1 M2 : gmap lvar LExpr) stk_id (mp1 mp2 : symb_map) :
    StackFree a →
    assertion_exists_binders a ## (dom M1 ∪ lexpr_map_fvars M1) →
    assertion_exists_binders a ## (dom M2 ∪ lexpr_map_fvars M2) →
    (∀ v, v ∈ assertion_lexpr_fvars a → v ∈ dom M1 ∨ is_reserved v) →
    dom M1 = dom M2 →
    subst_map_avoids_reserved M1 →
    subst_map_avoids_reserved M2 →
    (∀ (q1 q2 : symb_map),
      (∀ x, x ∈ dom M1 → eval_lvar M1 q1 x = eval_lvar M2 q2 x) →
      ∀ (v : lvar), v ∉ lexpr_map_fvars M1 → v ∉ lexpr_map_fvars M2 →
      ∀ (v' : val) (x : lvar), x ∈ dom M1 →
      eval_lvar M1 (fun y => if (y =? v)%string then v' else q1 y) x =
      eval_lvar M2 (fun y => if (y =? v)%string then v' else q2 y) x) →
    (∀ x, x ∈ dom M1 ∨ is_reserved x → eval_lvar M1 mp1 x = eval_lvar M2 mp2 x) →
    trnsl_assertion (subst a M1) stk_id mp1 ≡ trnsl_assertion (subst a M2) stk_id mp2.
  Proof.
    intros HSF HbA_M1 HbA_M2 HfvA HdomEq Hmr1 Hmr2 Hstab Hbase.
    have Hcond : subst_congr_cond a M1 M2 mp1 mp2 by split_and!.
    apply bi.equiv_entails; split.
    - exact (trnsl_assertion_subst_mono Hwf a M1 M2 stk_id mp1 mp2 Hcond).
    - exact (trnsl_assertion_subst_mono Hwf a M2 M1 stk_id mp2 mp1
               (subst_congr_cond_sym _ _ _ _ _ Hcond)).
  Qed.

  (* Side conditions under which two symbolic maps mp1/mp2 assign the same
     meaning to a StackFree, once-substituted assertion, *without* needing
     any agreement at reserved names -- unlike subst_congr_cond's Hbase,
     which needs exactly that (impossible at inv_body_bridge's step 3
     below). The trick: assertion_true_fvars is scope-
     correct (unlike assertion_lexpr_fvars), so every name it reports is
     genuinely read from the ambient mp -- nothing here is a spurious
     over-approximation through a binder, and covering it directly is both
     necessary and sufficient. *)
  Definition mp_irr_cond (a : assertion) (M : gmap lvar LExpr) (mp1 mp2 : symb_map) : Prop :=
    StackFree a ∧
    assertion_exists_binders a ## (dom M ∪ lexpr_map_fvars M) ∧
    subst_map_avoids_reserved M ∧
    (∀ x, x ∈ assertion_true_fvars a → eval_lvar M mp1 x = eval_lvar M mp2 x).

  Lemma mp_irr_cond_sym a M mp1 mp2 :
    mp_irr_cond a M mp1 mp2 → mp_irr_cond a M mp2 mp1.
  Proof.
    intros (Hsf & HbA & Hmr & Hbase). split_and!; try assumption.
    intros x Hx. symmetry. exact (Hbase x Hx).
  Qed.

  Definition mp_irr_Phi (x : leibnizO trnsl_dom) : iProp Σ :=
    (∀ a0 M mp2,
       ⌜x.1.1 = subst a0 M⌝ -∗
       ⌜mp_irr_cond a0 M x.2 mp2⌝ -∗
       trnsl_assertion (subst a0 M) x.1.2 mp2)%I.

  Global Arguments mp_irr_Phi : simpl never.

  Local Instance mp_irr_Phi_ne : NonExpansive mp_irr_Phi.
  Proof. intros n x y Heq. change (x = y) in Heq. by subst. Qed.

  (* One unfolding step, structural induction on the assertion, exactly
     paralleling subst_congr_step but with a single map M throughout
     (mp1/mp2 only, no M1/M2), and using assertion_true_fvars (no reserved
     escape) instead of assertion_lexpr_fvars/is_reserved. *)
  Local Lemma mp_irr_step (Hwf : ProgramWF) (a0 : assertion) :
    ∀ (M : gmap lvar LExpr) (stk : stack_id) (mp1 mp2 : symb_map),
      mp_irr_cond a0 M mp1 mp2 →
      trnsl_assertion_str (trnsl_assertion_curry mp_irr_Phi) (subst a0 M) stk mp1
      ⊢ trnsl_assertion (subst a0 M) stk mp2.
  Proof.
    induction a0; intros M stk mp1 mp2 Hcond;
      destruct Hcond as (Hsf & HbA & Hmr & Hbase);
      simpl in HbA;
      (etrans; [| apply bi.equiv_entails_1_2,
                  (trnsl_assertion_unfold (subst _ M) stk mp2)]).
    - (* LProc *) iIntros "H". iExact "H".
    - (* LStack *) inversion Hsf.
    - (* LExprA *)
      apply bi.pure_mono. unfold LExpr_holds.
      rewrite (interp_lexpr_subst_eval_lvar_congr_true p M mp1 mp2
                 ltac:(intros x Hx; apply Hbase; simpl; exact Hx)).
      tauto.
    - (* LPure *) iIntros "H". iExact "H".
    - (* LOwn *)
      apply bi.exist_mono. intro l.
      apply bi.exist_mono. intro chunk0.
      apply bi.sep_mono.
      { apply bi.pure_mono. unfold LExpr_holds.
        have Hb1 : ∀ x, x ∈ lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) →
          eval_lvar M mp1 x = eval_lvar M mp2 x.
        { intros x Hx. apply Hbase. simpl in Hx |- *. set_solver. }
        have Hcongr := interp_lexpr_subst_eval_lvar_congr_true
          (LBinOp EqOp e (LVal (LitLoc l))) M mp1 mp2 Hb1.
        simpl in Hcongr |- *. rewrite Hcongr. tauto. }
      apply bi.sep_mono; [| done].
      apply bi.pure_mono. intro Hchunk.
      have Hb2 : ∀ x, x ∈ lexpr_fvars chunk → eval_lvar M mp1 x = eval_lvar M mp2 x.
      { intros x Hx. apply Hbase. simpl. set_solver. }
      have Hcongr2 := interp_lexpr_subst_eval_lvar_congr_true chunk M mp1 mp2 Hb2.
      rewrite <- Hcongr2. exact Hchunk.
    - (* LGhostOwn *)
      simpl. generalize (Γ r).
      intros [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ]; [ | done].
      apply bi.exist_mono. intro l.
      apply bi.exist_mono. intro chunk0.
      apply bi.exist_mono. intro γ.
      apply bi.sep_mono.
      { apply bi.pure_mono. unfold LExpr_holds.
        have Hb1 : ∀ x, x ∈ lexpr_fvars (LBinOp EqOp e (LVal (LitLoc l))) →
          eval_lvar M mp1 x = eval_lvar M mp2 x.
        { intros x Hx. apply Hbase. simpl in Hx |- *. set_solver. }
        have Hcongr := interp_lexpr_subst_eval_lvar_congr_true
          (LBinOp EqOp e (LVal (LitLoc l))) M mp1 mp2 Hb1.
        simpl in Hcongr |- *. rewrite Hcongr. tauto. }
      apply bi.sep_mono; [| done].
      apply bi.pure_mono. intro Hchunk.
      have Hb2 : ∀ x, x ∈ lexpr_fvars chunk → eval_lvar M mp1 x = eval_lvar M mp2 x.
      { intros x Hx. apply Hbase. simpl. set_solver. }
      have Hcongr2 := interp_lexpr_subst_eval_lvar_congr_true chunk M mp1 mp2 Hb2.
      rewrite <- Hcongr2. exact Hchunk.
    - (* LForall: inert binder, so a direct recursion at the same mp1/mp2 --
         matches trnsl_assertion_forall never updating mp, and
         assertion_true_fvars not subtracting v either. *)
      inversion Hsf.
      apply bi.forall_mono. intro v'.
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold (subst a0 M) stk mp2)].
      apply (IHa0 M stk mp1 mp2). by split_and!.
    - (* LExists: updates mp1/mp2 at the same fresh witness v'; assertion_true_fvars
         (LExists v t body) = assertion_true_fvars body ∖ {[v]}, so at x = v both
         sides trivially reduce to v' (v ∉ dom M, from HbA), and at x ≠ v the
         update is a no-op (eval_lvar_update_stable) and the outer Hbase carries
         over directly -- no is_reserved detour needed anywhere. *)
      inversion Hsf. subst.
      apply bi.exist_mono. intro v'.
      apply bi.sep_mono; [done|].
      have HvdomM : v ∉ dom M. { set_solver. }
      have HvlexM : v ∉ lexpr_map_fvars M. { set_solver. }
      have Hbase' : ∀ x, x ∈ assertion_true_fvars a0 →
        eval_lvar M (fun y => if (y =? v)%string then v' else mp1 y) x =
        eval_lvar M (fun y => if (y =? v)%string then v' else mp2 y) x.
      { intros x Hx. destruct (decide (x = v)) as [-> | Hne].
        - unfold eval_lvar. apply not_elem_of_dom in HvdomM. rewrite HvdomM /=.
          rewrite String.eqb_refl. reflexivity.
        - rewrite (eval_lvar_update_stable M mp1 v v' x HvlexM (or_intror Hne)).
          rewrite (eval_lvar_update_stable M mp2 v v' x HvlexM (or_intror Hne)).
          apply Hbase. simpl. set_solver. }
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold (subst a0 M) stk
                    (fun y => if (y =? v)%string then v' else mp2 y))].
      apply (IHa0 M stk
        (fun y => if (y =? v)%string then v' else mp1 y)
        (fun y => if (y =? v)%string then v' else mp2 y)).
      split_and!.
      + assumption.
      + set_solver.
      + assumption.
      + exact Hbase'.
    - (* LIte *)
      inversion Hsf. subst.
      have Hfv_cond : ∀ x, x ∈ lexpr_fvars cond → eval_lvar M mp1 x = eval_lvar M mp2 x.
      { intros x Hx. apply Hbase. simpl. set_solver. }
      apply bi.and_mono.
      + apply bi.wand_mono.
        * apply bi.pure_mono. unfold LExpr_holds.
          rewrite (interp_lexpr_subst_eval_lvar_congr_true cond M mp1 mp2 Hfv_cond). tauto.
        * etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold (subst a0_1 M) stk mp2)].
          apply (IHa0_1 M stk mp1 mp2). split_and!; try assumption.
          -- set_solver.
          -- intros x Hx. apply Hbase. simpl. set_solver.
      + apply bi.wand_mono.
        * apply bi.pure_mono. unfold LExpr_holds.
          rewrite (interp_lexpr_subst_eval_lvar_congr_true cond M mp1 mp2 Hfv_cond). tauto.
        * etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold (subst a0_2 M) stk mp2)].
          apply (IHa0_2 M stk mp1 mp2). split_and!; try assumption.
          -- set_solver.
          -- intros x Hx. apply Hbase. simpl. set_solver.
    - (* LInv: a leaf -- only the argument evaluations must be transferred *)
      simpl. destruct (inv_map !! inv_name) as [r|] eqn:Hr; [| done].
      apply bi.exist_mono. intro vs. apply bi.sep_mono; [| done].
      apply bi.pure_mono. apply (Forall2_interp_subst_congr args vs M M mp1 mp2).
      intros le Hle.
      apply (interp_lexpr_subst_eval_lvar_congr_true le M mp1 mp2).
      intros x Hx. apply Hbase. simpl. exact (lexpr_fvars_elem_subseteq le args Hle x Hx).
    - (* LPred: the fixpoint induction hypothesis fires here, exactly as in
         subst_congr_step's LPred case, but re-deriving the mp_irr_cond-shaped
         (rather than subst_congr_cond-shaped) facts for the unfolded body:
         its own binders are reserved (pwf_pred_binders_reserved) and disjoint
         from M (Hmr), and its true fvars are fully closed by its formal args
         (pwf_pred_fvars_closed), so once substituted by the call's own args
         they land inside assertion_true_fvars (LPred pred_name args) --
         exactly Hbase's domain, no reserved leftover. *)
      simpl. destruct (pred_map !! pred_name) as [r|] eqn:Hr; [| done].
      have Hbr : assertion_exists_binders r.(pred_body) ## (dom M ∪ lexpr_map_fvars M).
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_pred_binders_reserved) pred_name r Hr).
        - intros v Hv. apply elem_of_union in Hv as [Hv|Hv];
            [exact (proj1 Hmr v Hv) | exact (proj2 Hmr v Hv)]. }
      have HPredBodyWF := pred_body_wf_from_scoped r
        (Hwf.(pwf_pred_fvars_scoped) pred_name r Hr).
      inversion Hsf. rewrite Hr in H1. inversion H1. subst pred_record.
      rewrite (HPredBodyWF args M H2 ltac:(set_solver)).
      rewrite /trnsl_assertion_curry.
      iIntros "H".
      iApply ("H" $! (subst r.(pred_body) (list_to_map (zip r.(pred_args) args))) M mp2);
        iPureIntro; [reflexivity |].
      split_and!.
      + assumption.
      + rewrite assertion_exists_binders_subst. exact Hbr.
      + exact Hmr.
      + have Hclosed := Hwf.(pwf_pred_fvars_closed) pred_name r Hr.
        have Hdom : assertion_true_fvars r.(pred_body) ⊆
          dom (list_to_map (zip r.(pred_args) args) : gmap lvar LExpr).
        { rewrite (dom_list_to_map_zip r.(pred_args) args (eq_sym H2)). exact Hclosed. }
        have Hb1 := assertion_true_fvars_subst_bound r.(pred_body)
          (list_to_map (zip r.(pred_args) args)) Hdom.
        have Hb2 := lexpr_map_fvars_zip_subseteq r.(pred_args) args.
        intros x Hx. apply Hbase. simpl.
        exact (Hb2 x (Hb1 x Hx)).
    - (* LAnd *)
      inversion Hsf. subst.
      apply bi.sep_mono.
      + etrans; [| apply bi.equiv_entails_1_1,
                   (trnsl_assertion_unfold (subst a0_1 M) stk mp2)].
        apply (IHa0_1 M stk mp1 mp2). split_and!; try assumption.
        * set_solver.
        * intros x Hx. apply Hbase. simpl. set_solver.
      + etrans; [| apply bi.equiv_entails_1_1,
                   (trnsl_assertion_unfold (subst a0_2 M) stk mp2)].
        apply (IHa0_2 M stk mp1 mp2). split_and!; try assumption.
        * set_solver.
        * intros x Hx. apply Hbase. simpl. set_solver.
  Qed.

  (* One direction of the equivalence. *)
  Lemma trnsl_assertion_mp_irrelevant_reserved_mono (Hwf : ProgramWF)
      (a : assertion) (M : gmap lvar LExpr) stk_id (mp1 mp2 : symb_map) :
    mp_irr_cond a M mp1 mp2 →
    trnsl_assertion (subst a M) stk_id mp1 ⊢ trnsl_assertion (subst a M) stk_id mp2.
  Proof.
    intros Hcond.
    iIntros "H".
    iDestruct (least_fixpoint_iter trnsl_assertion_F mp_irr_Phi with "[] H") as "H'".
    { iIntros "!>" ([[b stk'] mp']) "HF".
      rewrite /mp_irr_Phi /=.
      iIntros (a0 M' mp2') "-> %Hc".
      by iApply (mp_irr_step Hwf a0 M' stk' mp' mp2' Hc). }
    rewrite /mp_irr_Phi /=.
    iApply ("H'" $! a M mp2); iPureIntro; [reflexivity | exact Hcond].
  Qed.

  (* Translating a once-substituted, StackFree assertion doesn't depend on
     the ambient mp's value anywhere -- not even at reserved names, unlike
     trnsl_assertion_subst_congr's Hbase, which needs exactly that
     agreement and is therefore unusable when mp1/mp2 (e.g. a caller's own
     mp vs the canonical WINV_MP) are genuinely unrelated. Only requires
     agreement where the assertion actually, truly (not merely
     over-approximately) reads mp -- assertion_true_fvars a, once M is
     applied, is empty of anything mp could still influence beyond that. *)
  Lemma trnsl_assertion_mp_irrelevant_reserved (Hwf : ProgramWF)
    (a : assertion) (M : gmap lvar LExpr) stk_id (mp1 mp2 : symb_map) :
    StackFree a →
    assertion_exists_binders a ## (dom M ∪ lexpr_map_fvars M) →
    subst_map_avoids_reserved M →
    (∀ x, x ∈ assertion_true_fvars a → eval_lvar M mp1 x = eval_lvar M mp2 x) →
    trnsl_assertion (subst a M) stk_id mp1 ≡ trnsl_assertion (subst a M) stk_id mp2.
  Proof.
    intros HSF HbA Hmr Hbase.
    have Hcond : mp_irr_cond a M mp1 mp2 by split_and!.
    apply bi.equiv_entails; split.
    - exact (trnsl_assertion_mp_irrelevant_reserved_mono Hwf a M stk_id mp1 mp2 Hcond).
    - exact (trnsl_assertion_mp_irrelevant_reserved_mono Hwf a M stk_id mp2 mp1
               (mp_irr_cond_sym _ _ _ _ Hcond)).
  Qed.

  (* Helper: eval_lvar agreement holds for list_to_map (zip args lexprs) vs
     list_to_map (zip args (map LVal arg_vals)) when lexprs and arg_vals are Forall2-related. *)
  Lemma eval_lvar_list_to_map_zip_forall2 (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val) (mp : symb_map) :
    Forall2 (fun le v => interp_lexpr le mp = Some (trnsl_val v)) lexprs arg_vals →
    ∀ x,
    eval_lvar (list_to_map (zip args lexprs)) mp x =
    eval_lvar (list_to_map (zip args (map (fun v : lang.val => LVal (trnsl_val v)) arg_vals))) mp x.
  Proof.
    intro HF2. unfold eval_lvar.
    revert args.
    induction HF2 as [| le v lexprs' arg_vals' Hle HF2' IH]; intro args.
    - simpl. destruct args; simpl; reflexivity.
    - destruct args as [| a args']; simpl.
      + intro x. reflexivity.
      + intro x.
        destruct (decide (x = a)) as [-> | Hne].
        * rewrite !lookup_insert. simpl. exact Hle.
        * rewrite !lookup_insert_ne; [| by intro H; apply Hne; exact (eq_sym H) | by intro H; apply Hne; exact (eq_sym H)].
          exact (IH args' x).
  Qed.

  (* Helper: every value in list_to_map (zip ks vs) is in vs. *)
  Lemma lookup_list_to_map_zip_in_snd {B : Type} (ks : list lvar) (vs : list B) (k : lvar) v :
    (list_to_map (zip ks vs) : gmap lvar B) !! k = Some v → v ∈ vs.
  Proof.
    revert vs. induction ks as [| k' ks' IH]; intros vs Hk.
    - rewrite lookup_empty in Hk. discriminate.
    - destruct vs as [| v' vs'].
      + rewrite lookup_empty in Hk. discriminate.
      + simpl in Hk.
        destruct (decide (k = k')) as [-> | Hne].
        * rewrite lookup_insert in Hk. injection Hk as <-.
          apply elem_of_cons. left. reflexivity.
        * rewrite lookup_insert_ne in Hk; [| congruence].
          apply elem_of_cons. right. exact (IH vs' Hk).
  Qed.

  (* Helper: if lv is fresh w.r.t. stk, and lexprs are translations of args via trnsl_expr_lExpr,
     then lv ∉ lexpr_map_fvars of any zip map over lexprs. *)
  Lemma fresh_lvar_not_in_lexpr_map_fvars_zip (stk : stack) (args : list lang.expr)
      (lexprs : list LExpr) (arg_names : list lvar) (lv : lvar) :
    map (fun arg => trnsl_expr_lExpr stk arg) args = map Some lexprs →
    fresh_lvar stk lv →
    lv ∉ lexpr_map_fvars (list_to_map (zip arg_names lexprs)).
  Proof.
    intros H2 Hfresh.
    apply (proj2 (lexpr_map_fvars_spec _ _)).
    intros k e Hke.
    apply lookup_list_to_map_zip_in_snd in Hke.
    apply elem_of_list_lookup_1 in Hke as [i Hi].
    have H2i : map (fun arg => trnsl_expr_lExpr stk arg) args !! i = Some (Some e).
    { rewrite H2. rewrite list_lookup_fmap. rewrite Hi. reflexivity. }
    rewrite list_lookup_fmap in H2i.
    destruct (args !! i) as [arg|] eqn:Harg.
    - simpl in H2i. injection H2i as He.
      exact (trnsl_expr_lExpr_fresh_lvar stk arg e lv He Hfresh).
    - discriminate.
  Qed.

  Lemma hstab_lexpr_subst_fwd (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val)
      (HdomEq : dom (list_to_map (zip args lexprs) : gmap lvar LExpr) =
                dom (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr)) :
    ∀ (q1 q2 : symb_map),
    (∀ x, x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr) →
           eval_lvar (list_to_map (zip args lexprs)) q1 x =
           eval_lvar (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) q2 x) →
    ∀ (v : lvar),
    v ∉ lexpr_map_fvars (list_to_map (zip args lexprs)) →
    v ∉ lexpr_map_fvars (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) →
    ∀ (v' : val) (x : lvar), x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr) →
    eval_lvar (list_to_map (zip args lexprs)) (fun y => if (y =? v)%string then v' else q1 y) x =
    eval_lvar (list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) (fun y => if (y =? v)%string then v' else q2 y) x.
  Proof.
    intros q1 q2 Hbase v Hv1 Hv2 v' x Hx.
    rewrite (eval_lvar_update_stable _ q1 v v' x Hv1 (or_introl Hx)).
    rewrite (Hbase x Hx).
    have Hx2 : x ∈ dom (list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr).
    { rewrite <- HdomEq. exact Hx. }
    exact (eq_sym (eval_lvar_update_stable _ q2 v v' x Hv2 (or_introl Hx2))).
  Qed.

  Lemma hstab_lexpr_subst_r (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val) (lvar_x : lvar) (ret_val : lang.val)
      (HdomEq : dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) =
                dom (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))) : gmap lvar LExpr)) :
    ∀ (q1 q2 : symb_map),
    (∀ x, x ∈ dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) →
           eval_lvar (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs))) q1 x =
           eval_lvar (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)))) q2 x) →
    ∀ (v : lvar),
    v ∉ lexpr_map_fvars (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs))) →
    v ∉ lexpr_map_fvars (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)))) →
    ∀ (v' : val) (x : lvar), x ∈ dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) →
    eval_lvar (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs))) (fun y => if (y =? v)%string then v' else q1 y) x =
    eval_lvar (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals)))) (fun y => if (y =? v)%string then v' else q2 y) x.
  Proof.
    intros q1 q2 Hbase v Hv1 Hv2 v' x Hx.
    rewrite (eval_lvar_update_stable _ q1 v v' x Hv1 (or_introl Hx)).
    rewrite (Hbase x Hx).
    have Hx2 : x ∈ dom (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))) : gmap lvar LExpr).
    { rewrite <- HdomEq. exact Hx. }
    exact (eq_sym (eval_lvar_update_stable _ q2 v v' x Hv2 (or_introl Hx2))).
  Qed.

  (* Extra "no key here is reserved" hypotheses (Hargs_ok, Hlvar_x_ok)
     needed for the is_reserved x disjunct: when x is reserved, none
     of "#ret_val" (never reserved, a different, "#"-prefixed convention),
     args's own formal-argument names (never reserved by the framework's
     own naming discipline), or lvar_x (ditto for
     derivation-fresh witnesses) can equal x, so both sides fall back
     directly to mp/the ret_val update, which trivially agree. *)
  Lemma hbase_lexpr_subst_r (args : list lvar) (lexprs : list LExpr)
      (arg_vals : list lang.val) (lvar_x : lvar) (ret_val : lang.val) (mp : symb_map) :
    lvar_x ∉ lexpr_map_fvars (list_to_map (zip args lexprs)) →
    ¬ is_reserved lvar_x →
    Forall (λ a, ¬ is_reserved a) args →
    Forall2 (λ expr val0, interp_lexpr expr mp = Some (trnsl_val val0)) lexprs arg_vals →
    ∀ x, x ∈ dom (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) ∨ is_reserved x →
    eval_lvar (<["#ret_val" := LVar lvar_x]>(list_to_map (zip args lexprs)))
      (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) x =
    eval_lvar (<["#ret_val" := LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ w : lang.val, LVal (trnsl_val w)) arg_vals))))
      mp x.
  Proof.
    intros Hfresh Hlvar_x_ok Hargs_ok HF2 x [Hdom | Hres].
    - destruct (decide (x = "#ret_val")) as [-> | Hne].
      + unfold eval_lvar. rewrite !lookup_insert. simpl. rewrite String.eqb_refl. reflexivity.
      + have Hne' : "#ret_val" ≠ x := fun H => Hne (eq_sym H).
        have Hdomx : x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr).
        { rewrite dom_insert in Hdom. set_solver. }
        unfold eval_lvar.
        rewrite (lookup_insert_ne _ _ _ _ Hne').
        rewrite (lookup_insert_ne _ _ _ _ Hne').
        have Hcongr : eval_lvar (list_to_map (zip args lexprs)) mp x =
                      eval_lvar (list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals))) mp x :=
          eval_lvar_list_to_map_zip_forall2 args lexprs arg_vals mp HF2 x.
        unfold eval_lvar in Hcongr.
        destruct (list_to_map (zip args lexprs) !! x) as [le|] eqn:Hle.
        * have Hle_fresh : lvar_x ∉ lexpr_fvars le :=
            proj1 (lexpr_map_fvars_spec _ _) Hfresh x le Hle.
          rewrite Hle. simpl. simpl in Hcongr.
          etransitivity.
          { exact (interp_lexpr_stable le mp lvar_x (trnsl_val ret_val) Hle_fresh). }
          exact Hcongr.
        * exfalso. rewrite elem_of_dom in Hdomx. destruct Hdomx as [le' Hle']. congruence.
    - have Hne_ret : x ≠ "#ret_val".
      { intros ->. unfold is_reserved in Hres. discriminate. }
      have Hne_lvar_x : x ≠ lvar_x.
      { intros ->. exact (Hlvar_x_ok Hres). }
      have Hnotin_args : x ∉ args.
      { intros Hin. rewrite Forall_forall in Hargs_ok. exact (Hargs_ok x Hin Hres). }
      have Hnotin1 : (list_to_map (zip args lexprs) : gmap lvar LExpr) !! x = None.
      { destruct ((list_to_map (zip args lexprs) : gmap lvar LExpr) !! x) as [e|] eqn:Heq; [| reflexivity].
        exfalso. apply elem_of_list_to_map_2 in Heq. apply elem_of_zip_l in Heq.
        exact (Hnotin_args Heq). }
      have Hnotin2 : (list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr) !! x = None.
      { destruct ((list_to_map (zip args (map (λ w, LVal (trnsl_val w)) arg_vals)) : gmap lvar LExpr) !! x)
          as [e|] eqn:Heq; [| reflexivity].
        exfalso. apply elem_of_list_to_map_2 in Heq. apply elem_of_zip_l in Heq.
        exact (Hnotin_args Heq). }
      unfold eval_lvar.
      rewrite (lookup_insert_ne _ _ _ _ (fun H => Hne_ret (eq_sym H))).
      rewrite (lookup_insert_ne _ _ _ _ (fun H => Hne_ret (eq_sym H))).
      rewrite Hnotin1 Hnotin2. simpl.
      rewrite (proj2 (String.eqb_neq x lvar_x) Hne_lvar_x).
      reflexivity.
  Qed.

  Lemma trnsl_assertion_w_lexpr_subst assertion lexprs args arg_vals stk_id mp p1 p2
      (Hwf : ProgramWF)
      (HSF : StackFree assertion)
      (HbA_M1 : assertion_exists_binders assertion ##
        (dom (list_to_map (zip args lexprs) : gmap lvar LExpr) ∪ lexpr_map_fvars (list_to_map (zip args lexprs))))
      (HbA_M2 : assertion_exists_binders assertion ##
        (dom (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr) ∪
         lexpr_map_fvars (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))))
      (HfvA : ∀ v, v ∈ assertion_lexpr_fvars assertion →
        v ∈ (dom (list_to_map (zip args lexprs) : gmap lvar LExpr)) ∨ is_reserved v)
      (HdomEq : dom (list_to_map (zip args lexprs) : gmap lvar LExpr) = dom (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)) : gmap lvar LExpr))
      (Hmr1 : subst_map_avoids_reserved (list_to_map (zip args lexprs)))
      (Hmr2 : subst_map_avoids_reserved (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))) :
    Forall2 (λ expr val0, interp_lexpr expr mp = Some (trnsl_val val0)) lexprs arg_vals →
    trnsl_assertion (subst assertion (list_to_map (zip args lexprs))) stk_id mp ≡ p1 →
    trnsl_assertion (subst assertion (list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))) stk_id mp ≡ p2 →
    p1 -∗ p2.
  Proof.
    intros HF2 Hp1 Hp2.
    have Hbase : ∀ x, x ∈ dom (list_to_map (zip args lexprs) : gmap lvar LExpr) ∨ is_reserved x →
                       eval_lvar (list_to_map (zip args lexprs)) mp x =
                       eval_lvar (list_to_map (zip args (map (λ val, LVal (trnsl_val val)) arg_vals))) mp x.
    { intros x _. exact (eval_lvar_list_to_map_zip_forall2 args lexprs arg_vals mp HF2 x). }
    have Hstab := hstab_lexpr_subst_fwd args lexprs arg_vals HdomEq.
    have Heq := trnsl_assertion_subst_congr Hwf assertion _ _ stk_id mp mp
      HSF HbA_M1 HbA_M2 HfvA HdomEq Hmr1 Hmr2 Hstab Hbase.
    rewrite <- Hp1. rewrite Heq. rewrite Hp2.
    iIntros "H". iExact "H".
  Qed.

  Lemma trnsl_assertion_w_lexpr_subst_r assertion lexprs args arg_vals lvar_x ret_val stk stk_id mp p1 p2
      (Hwf : ProgramWF)
      (HSF : StackFree assertion)
      (HbA_M1 : assertion_exists_binders assertion ##
        (dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) ∪
         lexpr_map_fvars (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)))))
      (HbA_M2 : assertion_exists_binders assertion ##
        (dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))) : gmap lvar LExpr) ∪
         lexpr_map_fvars (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))))))
      (HfvA : ∀ v, v ∈ assertion_lexpr_fvars assertion →
        v ∈ (dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr)) ∨ is_reserved v)
      (HdomEq : dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) = dom (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))) : gmap lvar LExpr))
      (Hmr1 : subst_map_avoids_reserved (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs))))
      (Hmr2 : subst_map_avoids_reserved (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals)))))
      (Hfresh_base : lvar_x ∉ lexpr_map_fvars (list_to_map (zip args lexprs)))
      (Hlvar_x_ok : ¬ is_reserved lvar_x)
      (Hargs_ok : Forall (λ a, ¬ is_reserved a) args) :
    fresh_lvar stk lvar_x →
    Forall2 (λ expr val0, interp_lexpr expr mp = Some (trnsl_val val0)) lexprs arg_vals →
    trnsl_assertion (subst assertion (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)))) stk_id
      (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) ≡ p1 →
    trnsl_assertion (subst assertion (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val : lang.val, LVal (trnsl_val val)) arg_vals))))) stk_id mp ≡ p2 →
    p2 -∗ p1.
  Proof.
    intros _Hfresh HF2 Hp1 Hp2.
    have Hstab_r := hstab_lexpr_subst_r args lexprs arg_vals lvar_x ret_val HdomEq.
    have Hbase_r : ∀ x, x ∈ dom (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)) : gmap lvar LExpr) ∨ is_reserved x →
      eval_lvar (<["#ret_val":=LVar lvar_x]>(list_to_map (zip args lexprs)))
        (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) x =
      eval_lvar (<["#ret_val":=LVal (trnsl_val ret_val)]>(list_to_map (zip args (map (λ val, LVal (trnsl_val val)) arg_vals))))
        mp x.
    { intros x Hx. exact (hbase_lexpr_subst_r args lexprs arg_vals lvar_x ret_val mp Hfresh_base Hlvar_x_ok Hargs_ok HF2 x Hx). }
    have Heq := trnsl_assertion_subst_congr Hwf assertion _ _ stk_id
      (λ x0, if (x0 =? lvar_x)%string then trnsl_val ret_val else mp x0) mp
      HSF HbA_M1 HbA_M2 HfvA HdomEq Hmr1 Hmr2 Hstab_r Hbase_r.
    rewrite <- Hp2. rewrite <- Heq. rewrite Hp1.
    iIntros "H". iExact "H".
  Qed.



  (* Fixpoint induction hypothesis for stack-independence. *)
  Definition stack_free_Phi (x : leibnizO trnsl_dom) : iProp Σ :=
    (∀ stk', ⌜StackFree x.1.1⌝ -∗ trnsl_assertion x.1.1 stk' x.2)%I.

  Global Arguments stack_free_Phi : simpl never.

  Local Instance stack_free_Phi_ne : NonExpansive stack_free_Phi.
  Proof. intros n x y Heq. change (x = y) in Heq. by subst. Qed.

  Local Lemma stack_free_step (a : assertion) :
    ∀ (stk stk' : stack_id) (mp : symb_map),
      StackFree a →
      trnsl_assertion_str (trnsl_assertion_curry stack_free_Phi) a stk mp
      ⊢ trnsl_assertion a stk' mp.
  Proof.
    induction a; intros stk stk' mp Hsf;
      (etrans; [| apply bi.equiv_entails_1_2, (trnsl_assertion_unfold _ stk' mp)]).
    - (* LProc *) iIntros "H". iExact "H".
    - (* LStack: not StackFree *) inversion Hsf.
    - (* LExprA *) iIntros "H". iExact "H".
    - (* LPure *) iIntros "H". iExact "H".
    - (* LOwn *) iIntros "H". iExact "H".
    - (* LGhostOwn *) simpl. generalize (Γ r).
      intros [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ];
        iIntros "H"; iExact "H".
    - (* LForall *)
      inversion Hsf. apply bi.forall_mono. intro v'.
      etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a stk' mp)].
      by apply (IHa stk stk' mp).
    - (* LExists *)
      inversion Hsf. apply bi.exist_mono. intro v'.
      apply bi.sep_mono; [done|].
      etrans; [| apply bi.equiv_entails_1_1,
                 (trnsl_assertion_unfold a stk' (λ x, if (x =? v)%string then v' else mp x))].
      by apply (IHa stk stk' (λ x, if (x =? v)%string then v' else mp x)).
    - (* LIte *)
      inversion Hsf. subst. apply bi.and_mono.
      + apply bi.wand_mono; [done |].
        etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a1 stk' mp)].
        by apply (IHa1 stk stk' mp).
      + apply bi.wand_mono; [done |].
        etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a2 stk' mp)].
        by apply (IHa2 stk stk' mp).
    - (* LInv: a leaf, independent of the stack *)
      simpl. destruct (inv_map !! inv_name) as [r|] eqn:Hr; [| done].
      iIntros "H". iExact "H".
    - (* LPred: the fixpoint induction hypothesis fires here *)
      simpl. destruct (pred_map !! pred_name) as [r|] eqn:Hr; [| done].
      inversion Hsf. rewrite Hr in H1. inversion H1. subst pred_record.
      rewrite /trnsl_assertion_curry.
      iIntros "H". by iApply ("H" $! stk').
    - (* LAnd *)
      inversion Hsf. subst. apply bi.sep_mono.
      + etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a1 stk' mp)].
        by apply (IHa1 stk stk' mp).
      + etrans; [| apply bi.equiv_entails_1_1, (trnsl_assertion_unfold a2 stk' mp)].
        by apply (IHa2 stk stk' mp).
  Qed.

  Lemma stack_free_assertion_trnsl_mono assertion stk_id stk_id' mp :
    StackFree assertion ->
    trnsl_assertion assertion stk_id mp ⊢ trnsl_assertion assertion stk_id' mp.
  Proof.
    intros HSF.
    iIntros "H".
    iDestruct (least_fixpoint_iter trnsl_assertion_F stack_free_Phi with "[] H") as "H'".
    { iIntros "!>" ([[b stk] mp']) "HF".
      rewrite /stack_free_Phi /=. iIntros (stk'') "%Hb".
      by iApply (stack_free_step b stk stk'' mp' Hb). }
    rewrite /stack_free_Phi /=. by iApply ("H'" $! stk_id').
  Qed.

  Lemma stack_free_assertion_trnsl assertion stk_id stk_id' mp :
    StackFree assertion ->
    trnsl_assertion assertion stk_id mp ≡ trnsl_assertion assertion stk_id' mp.
  Proof.
    intros HSF. apply bi.equiv_entails; split;
      by apply stack_free_assertion_trnsl_mono.
  Qed.

  (* Hmr: subst_map touches no reserved name -- needed to re-derive the
     "## dom subst_map" premise InvBodyWF/PredBodyWF require for whichever
     inv/pred body SF_Inv/SF_Pred happens to unfold. Whoever discharges
     this for a concrete subst_map is asserting it was built by the
     ordinary framework machinery -- see subst_map_avoids_reserved. *)
  Lemma stack_free_assertion_subst
    (Hwf : ProgramWF)
    assertion subst_map
    (Hmr : (∀ v, v ∈ dom subst_map → ¬ is_reserved v)) :
    StackFree assertion -> StackFree (subst assertion subst_map).
  Proof.
    intros HSF. induction HSF; simpl; try constructor; try assumption.
    - (* SF_Inv *)
      have Hbwf := inv_body_wf_from_scoped inv_record (Hwf.(pwf_inv_fvars_scoped) _ _ H).
      have Hbr : assertion_exists_binders inv_record.(inv_body) ## dom subst_map.
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_inv_binders_reserved) _ _ H).
        - exact Hmr. }
      eapply SF_Inv. { exact H. } { rewrite map_length. exact H0. }
      rewrite (Hbwf args subst_map H0 Hbr). exact IHHSF.
    - (* SF_Pred *)
      have Hbwf := pred_body_wf_from_scoped pred_record (Hwf.(pwf_pred_fvars_scoped) _ _ H).
      have Hbr : assertion_exists_binders pred_record.(pred_body) ## dom subst_map.
      { apply reserved_disjoint_dom.
        - exact (Hwf.(pwf_pred_binders_reserved) _ _ H).
        - exact Hmr. }
      eapply SF_Pred. { exact H. } { rewrite map_length. exact H0. }
      rewrite (Hbwf args subst_map H0 Hbr). exact IHHSF.
  Qed.
  

  (* ── Timelessness ────────────────────────────────────────────────────────
     Nothing in the translation is step-indexed any more: [LInv] is a discrete
     ownership fragment, [LPred] is a plain recursive call, and every leaf is a
     discrete resource.  Along a StackFree derivation -- which is exactly the
     discipline invariant bodies are held to -- the translation is therefore
     Timeless, and an invariant holding one can be opened for free. *)

  Local Lemma transport_cmra_discrete {A B : cmra} (p : A = B) (x : cmra_car A) :
    Discrete x → Discrete (transport (f_equal cmra_car p) x).
  Proof. intros Hx. destruct p. simpl. exact Hx. Qed.

  Lemma trnsl_assertion_timeless (a : assertion) (Hsf : StackFree a) :
    ∀ stk mp, Timeless (trnsl_assertion a stk mp).
  Proof.
    induction Hsf; intros stk mp.
    - (* LProc *)
      rewrite trnsl_assertion_unfold /trnsl_assertion_pre /=.
      destruct proc_entry. destruct (trnsl_stmt body); apply _.
    - (* LExprA *)
      rewrite trnsl_assertion_unfold. apply _.
    - (* LPure *)
      rewrite trnsl_assertion_unfold. apply _.
    - (* LOwn *)
      rewrite trnsl_assertion_unfold. apply _.
    - (* LGhostOwn *)
      rewrite trnsl_assertion_unfold /trnsl_assertion_pre /=.
      generalize (Γ RAPAck).
      intros [[i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]] | ]; [ | apply _].
      apply bi.exist_timeless. intro l.
      apply bi.exist_timeless. intro chunk0.
      apply bi.exist_timeless. intro γ.
      apply bi.sep_timeless; [apply _ |].
      apply bi.sep_timeless; [apply _ |].
      apply bi.sep_timeless; [apply _ |].
      apply own_timeless.
      have HdisGi : CmraDiscrete (Gs i). { rewrite -Heq_cmra. exact Hdis. }
      apply _.
    - (* LForall *)
      rewrite trnsl_assertion_forall. apply bi.forall_timeless. intros _. apply IHHsf.
    - (* LExists *)
      rewrite trnsl_assertion_exists. apply bi.exist_timeless. intros v'.
      apply bi.sep_timeless; [apply _ | apply IHHsf].
    - (* LIte *)
      rewrite trnsl_assertion_ite. apply bi.and_timeless.
      + apply bi.wand_timeless. apply IHHsf1.
      + apply bi.wand_timeless. apply IHHsf2.
    - (* LAnd *)
      rewrite trnsl_assertion_and. apply bi.sep_timeless; [apply IHHsf1 | apply IHHsf2].
    - (* LInv: a discrete ownership fragment *)
      have Hv := trnsl_inv_validity' inv_name args stk mp.
      rewrite H in Hv. rewrite Hv. apply _.
    - (* LPred *)
      have Hv := trnsl_pred_validity' pred_name args stk mp.
      rewrite H in Hv. simpl in Hv. rewrite <- Hv. apply IHHsf.
  Qed.

End AssertionsProperties.
Section InvariantWorld.

  (* Invariant bodies are stack-free and, once instantiated at concrete values,
     closed, so these choices are immaterial (see [Winv_body_congr]). *)
  Definition WINV_STK : stack_id := 0%Z.
  Definition WINV_MP : symb_map := λ _, LitUnit.

  Definition inv_arg_map (r : InvRecord) (vs : list val) : gmap var LExpr :=
    list_to_map (zip r.(inv_args) (map LVal vs)).

  Definition inv_body_at (inv' : inv_name) (vs : list val) : iProp Σ :=
    match inv_map !! inv' with
    | Some r =>
        if decide (length vs = length r.(inv_args))
        then trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP
        else True%I
    | None => True%I
    end.

  Definition Winv (inv' : inv_name) : iProp Σ :=
    (∃ I : gset (list val),
       own (invtoken_names inv') (● (I : inv_argsUR)) ∗
       [∗ set] vs ∈ I, inv_body_at inv' vs)%I.

  Lemma inv_body_at_timeless (Hwf : ProgramWF) inv' vs : Timeless (inv_body_at inv' vs).
  Proof.
    rewrite /inv_body_at. destruct (inv_map !! inv') as [r|] eqn:Hr; [| apply _].
    destruct (decide (length vs = length r.(inv_args))) as [Hlen |]; [| apply _].
    apply trnsl_assertion_timeless.
    apply (stack_free_assertion_subst Hwf).
    - intros v Hv. apply elem_of_dom in Hv as [e He].
      apply elem_of_list_to_map_2 in He. apply elem_of_zip_l in He.
      exact (proj1 (Forall_forall _ _) (Hwf.(pwf_inv_args_not_reserved) inv' r Hr) v He).
    - exact (Hwf.(pwf_inv_body_stack_free) inv' r Hr).
  Qed.

  Lemma Winv_timeless (Hwf : ProgramWF) inv' : Timeless (Winv inv').
  Proof.
    rewrite /Winv. apply bi.exist_timeless. intro Iopen.
    apply bi.sep_timeless; [apply _ |].
    apply big_sepS_timeless. intros vs _. by apply inv_body_at_timeless.
  Qed.

  (* [Winv] stores an invariant's body instantiated at *concrete values* and
     translated at a canonical stack/symbolic map.  A verification site sees it
     instantiated at *symbolic* LExprs under its own stack and symbolic map.
     The two agree whenever the LExprs evaluate to those values: the body is
     StackFree (so the stack is immaterial) and, once instantiated at values,
     closed (so the symbolic map is immaterial). *)
  (* Hlexprs_ok: the caller's own argument expressions -- built by
     trnsl_expr_lExpr against some ordinary symbolic stack -- touch no
     reserved lvar. Same status as subst_map_avoids_reserved elsewhere:
     an explicit premise recording that lexprs was actually built by the
     framework's own machinery, not a proof obligation dischargeable here. *)
  Lemma inv_body_bridge (Hwf : ProgramWF) (inv' : inv_name) (r : InvRecord)
      (lexprs : list LExpr) (vs : list val) (stk : stack_id) (mp : symb_map)
      (Hlexprs_ok : ∀ v, v ∈ lexpr_map_fvars (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) → ¬ is_reserved v) :
    inv_map !! inv' = Some r →
    length lexprs = length r.(inv_args) →
    Forall2 (λ le v, interp_lexpr le mp = Some v) lexprs vs →
    trnsl_assertion (subst r.(inv_body) (list_to_map (zip r.(inv_args) lexprs))) stk mp
    ≡ trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP.
  Proof.
    intros Hr Hlen HF2.
    have Hsf : StackFree r.(inv_body) := Hwf.(pwf_inv_body_stack_free) inv' r Hr.
    have Hlenvs : length vs = length r.(inv_args).
    { rewrite <- Hlen. symmetry. exact (Forall2_length _ _ _ HF2). }
    (* The value-instantiated map has no free variables at all. *)
    have Hvals : ∀ (l : list val) e, e ∈ map LVal l → ∃ w, e = LVal w.
    { intros l. induction l as [| w l' IH]; intros e He; simpl in He.
      - inversion He.
      - apply elem_of_cons in He as [-> | He]; [by exists w | exact (IH e He)]. }
    have Hnofv : lexpr_map_fvars (inv_arg_map r vs) = ∅.
    { apply elem_of_equiv_empty_L. intros y Hy.
      have Hno : y ∉ lexpr_map_fvars (inv_arg_map r vs).
      { apply (proj2 (lexpr_map_fvars_spec _ _)). intros k e Hke.
        rewrite /inv_arg_map in Hke.
        apply lookup_list_to_map_zip_in_snd in Hke.
        destruct (Hvals vs e Hke) as [w ->]. set_solver. }
      exact (Hno Hy). }
    have Hdom1 : dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr)
                 = list_to_set r.(inv_args).
    { apply dom_list_to_map_zip. by rewrite Hlen. }
    have Hdom2 : dom (inv_arg_map r vs : gmap lvar LExpr) = list_to_set r.(inv_args).
    { rewrite /inv_arg_map. apply dom_list_to_map_zip. rewrite map_length. by rewrite Hlenvs. }
    have HdomEq : dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr)
                = dom (inv_arg_map r vs : gmap lvar LExpr).
    { by rewrite Hdom1 Hdom2. }
    have Hfv : ∀ v, v ∈ assertion_lexpr_fvars r.(inv_body) →
      v ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) ∨ is_reserved v.
    { intros v Hv. destruct (Hwf.(pwf_inv_fvars_scoped) inv' r Hr v Hv) as [Hin | Hin].
      - left. rewrite Hdom1. exact Hin.
      - right. exact (Hwf.(pwf_inv_binders_reserved) inv' r Hr v Hin). }
    have Hfv2 : ∀ v, v ∈ assertion_lexpr_fvars r.(inv_body) →
      v ∈ dom (inv_arg_map r vs : gmap lvar LExpr) ∨ is_reserved v.
    { intros v Hv. destruct (Hwf.(pwf_inv_fvars_scoped) inv' r Hr v Hv) as [Hin | Hin].
      - left. rewrite Hdom2. exact Hin.
      - right. exact (Hwf.(pwf_inv_binders_reserved) inv' r Hr v Hin). }
    have Hmr1 : subst_map_avoids_reserved (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr).
    { split.
      - intros v Hv. apply elem_of_dom in Hv as [e He].
        apply elem_of_list_to_map_2 in He. apply elem_of_zip_l in He.
        exact (proj1 (Forall_forall _ _) (Hwf.(pwf_inv_args_not_reserved) inv' r Hr) v He).
      - exact Hlexprs_ok. }
    (* eval_lvar on the value-instantiated map ignores the symbolic map. *)
    have Hval_eval : ∀ (q : symb_map) x,
        x ∈ dom (inv_arg_map r vs : gmap lvar LExpr) →
        eval_lvar (inv_arg_map r vs) q x = eval_lvar (inv_arg_map r vs) WINV_MP x.
    { intros q x Hx. rewrite /eval_lvar.
      apply elem_of_dom in Hx as [e He].
      rewrite He.
      have He2 : e ∈ map LVal vs.
      { rewrite /inv_arg_map in He.
        exact (lookup_list_to_map_zip_in_snd _ _ _ _ He). }
      destruct (Hvals vs e He2) as [w ->]. done. }
    have Hmr2 : subst_map_avoids_reserved (inv_arg_map r vs : gmap lvar LExpr).
    { split.
      - intros v Hv. apply elem_of_dom in Hv as [e He]. rewrite /inv_arg_map in He.
        apply elem_of_list_to_map_2 in He. apply elem_of_zip_l in He.
        exact (proj1 (Forall_forall _ _) (Hwf.(pwf_inv_args_not_reserved) inv' r Hr) v He).
      - rewrite Hnofv. set_solver. }
    have HbA_M1 : assertion_exists_binders r.(inv_body) ##
      (dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) ∪ lexpr_map_fvars (list_to_map (zip r.(inv_args) lexprs))).
    { apply reserved_disjoint_dom.
      - exact (Hwf.(pwf_inv_binders_reserved) inv' r Hr).
      - intros v Hv. apply elem_of_union in Hv as [Hv|Hv]; [exact (proj1 Hmr1 v Hv) | exact (proj2 Hmr1 v Hv)]. }
    have HbA_M2 : assertion_exists_binders r.(inv_body) ##
      (dom (inv_arg_map r vs : gmap lvar LExpr) ∪ lexpr_map_fvars (inv_arg_map r vs)).
    { apply reserved_disjoint_dom.
      - exact (Hwf.(pwf_inv_binders_reserved) inv' r Hr).
      - intros v Hv. apply elem_of_union in Hv as [Hv|Hv]; [exact (proj1 Hmr2 v Hv) | exact (proj2 Hmr2 v Hv)]. }
    (* Step 1: replace the symbolic arguments by the values they denote. *)
    have Hbase1 : ∀ x, x ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) →
        eval_lvar (list_to_map (zip r.(inv_args) lexprs)) mp x =
        eval_lvar (inv_arg_map r vs) mp x.
    { intros x _. rewrite /inv_arg_map /eval_lvar.
      clear Hdom1 Hdom2 HdomEq Hfv Hfv2 Hval_eval Hnofv Hlen Hlenvs
        Hlexprs_ok Hmr1 Hmr2 HbA_M1 HbA_M2.
      revert lexprs vs HF2. generalize r.(inv_args) as ks. intros ks.
      induction ks as [| k ks IH]; intros lexprs vs HF2; [done |].
      inversion HF2 as [| le v lexprs' vs' Hle HF2' Heq1 Heq2]; subst; simpl; [done |].
      destruct (decide (x = k)) as [-> | Hne].
      - rewrite !lookup_insert. by rewrite Hle.
      - rewrite !lookup_insert_ne; [| congruence | congruence]. by apply IH. }
    have Hbase1' : ∀ x, x ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) ∨ is_reserved x →
        eval_lvar (list_to_map (zip r.(inv_args) lexprs)) mp x =
        eval_lvar (inv_arg_map r vs) mp x.
    { intros x [Hx | Hx]; [exact (Hbase1 x Hx) |].
      unfold eval_lvar.
      have Hn1 : (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) !! x = None.
      { apply not_elem_of_dom. intros Hin. exact (proj1 Hmr1 x Hin Hx). }
      have Hn2 : (inv_arg_map r vs : gmap lvar LExpr) !! x = None.
      { apply not_elem_of_dom. intros Hin. exact (proj1 Hmr2 x Hin Hx). }
      rewrite Hn1 Hn2. reflexivity. }
    have Hstab1 : ∀ (q1 q2 : symb_map),
        (∀ x, x ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) →
              eval_lvar (list_to_map (zip r.(inv_args) lexprs)) q1 x =
              eval_lvar (inv_arg_map r vs) q2 x) →
        ∀ v, v ∉ lexpr_map_fvars (list_to_map (zip r.(inv_args) lexprs)) →
             v ∉ lexpr_map_fvars (inv_arg_map r vs) →
        ∀ v' x, x ∈ dom (list_to_map (zip r.(inv_args) lexprs) : gmap lvar LExpr) →
        eval_lvar (list_to_map (zip r.(inv_args) lexprs))
          (fun y => if (y =? v)%string then v' else q1 y) x =
        eval_lvar (inv_arg_map r vs)
          (fun y => if (y =? v)%string then v' else q2 y) x.
    { intros q1 q2 Hag v Hv1 Hv2 v' x Hx.
      rewrite (eval_lvar_update_stable _ q1 v v' x Hv1 (or_introl Hx)).
      rewrite (Hag x Hx).
      have Hx2 : x ∈ dom (inv_arg_map r vs : gmap lvar LExpr) by rewrite <- HdomEq.
      exact (eq_sym (eval_lvar_update_stable _ q2 v v' x Hv2 (or_introl Hx2))). }
    etrans.
    { apply (trnsl_assertion_subst_congr Hwf r.(inv_body)
               (list_to_map (zip r.(inv_args) lexprs)) (inv_arg_map r vs) stk mp mp Hsf
               HbA_M1 HbA_M2 Hfv HdomEq Hmr1 Hmr2 Hstab1 Hbase1'). }
    (* Step 2: the body is StackFree, so the stack is immaterial. *)
    etrans.
    { apply stack_free_assertion_trnsl with (stk_id' := WINV_STK).
      exact (stack_free_assertion_subst Hwf _ _ (proj1 Hmr2) Hsf). }
    (* Step 3: the instantiated body is closed, so the symbolic map is too.
       trnsl_assertion_subst_congr's Hbase (agreement at reserved names too)
       is unsatisfiable here -- mp is an arbitrary caller-supplied map and
       WINV_MP a fixed global constant, genuinely unrelated at any name
       neither map's domain covers. trnsl_assertion_mp_irrelevant_reserved
       is the right tool instead: it only needs agreement where inv_body's
       *scope-correct* fvars (assertion_true_fvars, via pwf_inv_fvars_closed)
       actually land, which is exactly dom (inv_arg_map r vs) -- Hval_eval's
       own domain. *)
    have Htrue_dom : assertion_true_fvars r.(inv_body) ⊆ dom (inv_arg_map r vs : gmap lvar LExpr).
    { rewrite Hdom2. exact (Hwf.(pwf_inv_fvars_closed) inv' r Hr). }
    apply (trnsl_assertion_mp_irrelevant_reserved Hwf r.(inv_body)
             (inv_arg_map r vs) WINV_STK mp WINV_MP Hsf HbA_M2 Hmr2).
    intros x Hx. exact (Hval_eval mp x (Htrue_dom x Hx)).
  Qed.

  Lemma inv_body_at_eq (inv' : inv_name) (r : InvRecord) (vs : list val) :
    inv_map !! inv' = Some r →
    length vs = length r.(inv_args) →
    inv_body_at inv' vs =
    trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP.
  Proof. intros Hr Hlen. rewrite /inv_body_at Hr decide_True //. Qed.

  (* Owning a fragment means the argument vector really was established. *)
  Lemma Winv_frag_mem (inv' : inv_name) (Iset : gset (list val)) (vs : list val) :
    own (invtoken_names inv') (● (Iset : inv_argsUR)) -∗
    own (invtoken_names inv') (◯ ({[vs]} : inv_argsUR)) -∗
    ⌜vs ∈ Iset⌝.
  Proof.
    iIntros "Hauth Hfrag".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hval.
    apply auth_both_valid_discrete in Hval as [Hincl _].
    apply gset_included in Hincl. iPureIntro. set_solver.
  Qed.

  (* Opening an invariant: no later, no later credit.  The whole point of the
     nominal encoding is that this is available in plain Iris. *)
  Lemma Winv_open (Hwf : ProgramWF) (E : coPset) (inv' : inv_name)
      (r : InvRecord) (vs : list val) :
    inv_map !! inv' = Some r →
    length vs = length r.(inv_args) →
    ↑(inv_namespace_map inv') ⊆ E →
    inv (inv_namespace_map inv') (Winv inv') -∗
    own (invtoken_names inv') (◯ ({[vs]} : inv_argsUR)) ={E, E ∖ ↑(inv_namespace_map inv')}=∗
      trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP ∗
      (trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP
         ={E ∖ ↑(inv_namespace_map inv'), E}=∗ True).
  Proof.
    intros Hr Hlen HE.
    have Htl : Timeless (Winv inv') := Winv_timeless Hwf inv'.
    iIntros "#Hinv Hfrag".
    iMod (inv_acc_timeless with "Hinv") as "[HW Hclose]"; [exact HE |].
    iDestruct "HW" as (Iset) "[Hauth Hbig]".
    iDestruct (Winv_frag_mem with "Hauth Hfrag") as %Hmem.
    rewrite (big_sepS_delete _ Iset vs Hmem).
    iDestruct "Hbig" as "[Hbody Hrest]".
    rewrite (inv_body_at_eq inv' r vs Hr Hlen).
    iModIntro. iFrame "Hbody".
    iIntros "Hbody". iApply "Hclose".
    iExists Iset. iFrame "Hauth".
    rewrite (big_sepS_delete _ Iset vs Hmem) (inv_body_at_eq inv' r vs Hr Hlen).
    iFrame.
  Qed.

  (* Establishing an invariant: give up the body, get the nominal fragment.
     There is no inverse -- invariants are permanent, as in Iris. *)
  Lemma Winv_alloc (Hwf : ProgramWF) (E : coPset) (inv' : inv_name)
      (r : InvRecord) (vs : list val) :
    inv_map !! inv' = Some r →
    length vs = length r.(inv_args) →
    ↑(inv_namespace_map inv') ⊆ E →
    inv (inv_namespace_map inv') (Winv inv') -∗
    trnsl_assertion (subst r.(inv_body) (inv_arg_map r vs)) WINV_STK WINV_MP
    ={E}=∗ own (invtoken_names inv') (◯ ({[vs]} : inv_argsUR)).
  Proof.
    intros Hr Hlen HE.
    have Htl : Timeless (Winv inv') := Winv_timeless Hwf inv'.
    iIntros "#Hinv Hbody".
    iMod (inv_acc_timeless with "Hinv") as "[HW Hclose]"; [exact HE |].
    iDestruct "HW" as (Iset) "[Hauth Hbig]".
    iMod (own_update _ _ (● ((Iset ∪ {[vs]}) : inv_argsUR) ⋅ ◯ ({[vs]} : inv_argsUR))
      with "Hauth") as "[Hauth Hfrag]".
    { etrans.
      - apply (auth_update_auth (Iset : inv_argsUR) (Iset ∪ {[vs]}) (Iset ∪ {[vs]})).
        apply gset_local_update. set_solver.
      - apply auth_update_dfrac_alloc; [apply _ |].
        apply gset_included. set_solver. }
    iAssert (Winv inv') with "[Hauth Hbig Hbody]" as "HW".
    { iExists (Iset ∪ {[vs]}). iFrame "Hauth".
      destruct (decide (vs ∈ Iset)) as [Hin | Hnin].
      - have Heq : Iset ∪ {[vs]} = Iset by set_solver.
        rewrite Heq. iFrame "Hbig".
      - rewrite big_sepS_union; [| set_solver].
        iFrame "Hbig". rewrite big_sepS_singleton (inv_body_at_eq inv' r vs Hr Hlen).
        iExact "Hbody". }
    iMod ("Hclose" with "HW") as "_". iModIntro. iExact "Hfrag".
  Qed.

End InvariantWorld.

(* The ghost heap: one standing authoritative (loc,fld) -> gname naming
   map. HeapAllocRule mints a genuinely fresh gname (own_alloc, no chosen
   name needed) for each ghost field it allocates and grows this map to
   record the binding; FPURule never touches this map at all, since RA
   ownership lives directly at that gname via a bare own, exactly as in
   the pre-existing ghost_map design (see the comment on LGhostOwn's own
   translation above for why: updating a map fragment in place would need
   a genuine local update accounting for whatever else is framed at that
   key, which a bare RA-level ~~> doesn't in general provide -- the map's
   only job is solving the freshness/naming problem). Mirrors Winv's own
   invariant-wrapped, growable-via-iInv pattern above. *)
Section GhostHeapWorld.

  Definition Wghost : iProp Σ :=
    (∃ M : gmap heap_addr gname,
       own ghost_heap_name (● (to_agree <$> M) : authR (gmap.gmapUR heap_addr (agreeR gnameO))) ∗
       [∗ set] a ∈ dom M, ghost_dom_frag {[a]})%I.

  Global Instance Wghost_timeless : Timeless Wghost.
  Proof. rewrite /Wghost. apply _. Qed.

  (* Two reservations of the same (loc, fld) key can't coexist: ghost_dom's
     value type is exclR unitO, so the map fragment is exclusive at each
     key, exactly like heap_cellR's full fraction is for the real heap. *)
  Lemma ghost_dom_frag_excl (a : heap_addr) :
    ghost_dom_frag {[a]} -∗ ghost_dom_frag {[a]} -∗ False.
  Proof.
    rewrite /ghost_dom_frag.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %Hval.
    apply auth_frag_valid_1 in Hval.
    rewrite gset_to_gmap_singleton singleton_op singleton_valid in Hval.
    done.
  Qed.

  Lemma transport_cmra_valid {A B : cmra} (p : A = B) (x : cmra_car A) :
    ✓ x → ✓ (transport (f_equal cmra_car p) x).
  Proof. destruct p. simpl. done. Qed.

  (* Establishing a fresh ghost cell: own_alloc a genuinely fresh gname γ
     holding the initial RA chunk directly (exactly as the original
     ghost_map design would have owned it), then, given the ghost_dom_frag
     reservation wp_alloc just produced for (l, fld) (grown in lockstep
     with the real heap, at the same fresh_loc, so it's guaranteed fresh
     -- see ghost_dom_alloc_valid_sets), open Wghost, rule out (l, fld)
     already being in its domain via ghost_dom_frag_excl, and record the
     (l,fld) -> γ binding, handing the caller back both pieces in exactly
     the shape LGhostOwn's own translation expects. *)
  Lemma Wghost_alloc (E : coPset) (r : ra_name) (l : loc) (fld : fld_name)
      (chunk : RA_carrier (ra_map r)) (Hchunk_valid : (RA_inst (ra_map r)).(valid) chunk)
      (w : Γ_witness r) (HΓeq : Γ r = Γ_found w) :
    let '(existT i (exist _ U (conj Hdis (exist _ Heq_car (conj Heq_cmra (conj Hop Hvalid)))))) := w in
    ↑ghost_heap_namespace ⊆ E →
    inv ghost_heap_namespace Wghost -∗
    ghost_dom_frag {[heap_addr_constr l fld]}
    ={E}=∗
    ∃ γ : gname,
      own ghost_heap_name (◯ {[ heap_addr_constr l fld := to_agree γ ]} : authR (gmap.gmapUR heap_addr (agreeR gnameO))) ∗
      own γ (transport (f_equal cmra_car Heq_cmra) (transport Heq_car chunk)) (inG0 := inGs_inG i).
  Proof.
    destruct w as [i [U [Hdis [Heq_car [Heq_cmra [Hop Hvalid]]]]]].
    intros HE.
    iIntros "#Hinv Hwit".
    iMod (own_alloc (transport (f_equal cmra_car Heq_cmra) (transport Heq_car chunk))) as (γ) "Hγ".
    { apply transport_cmra_valid.
      change (@cmra.valid (cmra_car (ucmra_cmraR U)) (cmra_valid (ucmra_cmraR U))) with (ucmra_valid U).
      rewrite Hvalid.
      apply eq_rect_transport_valid_inv. exact Hchunk_valid. }
    iMod (inv_acc_timeless with "Hinv") as "[HW Hclose]"; [exact HE |].
    iEval (rewrite /Wghost) in "HW".
    iDestruct "HW" as (M) "[Hauth Hbig]".
    destruct (decide (heap_addr_constr l fld ∈ dom M)) as [Hin | Hnin].
    - iDestruct (big_sepS_elem_of _ _ (heap_addr_constr l fld) Hin with "Hbig") as "Hwit'".
      iDestruct (ghost_dom_frag_excl with "Hwit Hwit'") as "[]".
    - have Hfresh : M !! (heap_addr_constr l fld) = None := not_elem_of_dom_1 _ _ Hnin.
      iMod (own_update _ _
        ((● (to_agree <$> (<[ heap_addr_constr l fld := γ ]> M))
          ⋅ ◯ {[ heap_addr_constr l fld := to_agree γ ]})
         : authR (gmap.gmapUR heap_addr (agreeR gnameO)))
        with "Hauth") as "[Hauth Hfrag]".
      { rewrite fmap_insert. apply auth_update_alloc.
        apply alloc_singleton_local_update; [| done].
        rewrite lookup_fmap Hfresh. done. }
      iAssert Wghost with "[Hauth Hbig Hwit]" as "HW".
      { iEval (rewrite /Wghost).
        iExists (<[heap_addr_constr l fld := γ]> M).
        iFrame "Hauth".
        rewrite dom_insert_L.
        rewrite big_sepS_union; [| apply disjoint_singleton_l; exact Hnin].
        iFrame "Hbig". rewrite big_sepS_singleton. iExact "Hwit". }
      iMod ("Hclose" with "HW") as "_". iModIntro. iExists γ. iFrame.
  Qed.

End GhostHeapWorld.
Lemma transport_cmra_update {A B} (p : A = B) (x y : (cmra_car A)) :
  x ~~> y → transport (f_equal cmra_car p) x ~~> transport (f_equal cmra_car p) y.
Proof.
  intros Hxy. subst. done.
Qed.

    Definition inv_set_to_namespace (s : gset inv_name) : coPset :=
      set_fold (λ inv acc, acc ∪ ↑(inv_namespace_map inv)) ∅ s.

    (* The mask every trnsl_hoare_triple WP goal actually runs at: the
       user-declared Raven invariants named by msk, plus the ghost heap's
       own namespace, always -- Wghost is a built-in, like state_interp,
       not something a Raven program's own mask annotation gates (no rule
       ever puts ghost_heap_namespace into an inv_set/mask, since it isn't
       a user-declared invariant at all). *)
    Definition trnsl_mask (msk : maskAnnot) : coPset :=
      inv_set_to_namespace msk ∪ ↑ghost_heap_namespace.

    Lemma inv_set_to_namespace_subseteq_trnsl_mask msk :
      inv_set_to_namespace msk ⊆ trnsl_mask msk.
    Proof. rewrite /trnsl_mask. set_solver. Qed.

    Lemma ghost_heap_namespace_subseteq_trnsl_mask msk :
      ↑ghost_heap_namespace ⊆ trnsl_mask msk.
    Proof. rewrite /trnsl_mask. set_solver. Qed.

    Lemma inv_map_subseteq invr mask:
      invr ∈ mask -> ↑(inv_namespace_map invr) ⊆ inv_set_to_namespace mask.
    Proof.
      revert mask.
      unfold inv_set_to_namespace.
      apply (set_fold_ind (λ acc s, invr ∈ s → ↑inv_namespace_map invr ⊆ acc)).
    - solve_proper.
    - intros Hcontra. set_solver.
    - intros x s' acc Hnotin IH Hin'.
      destruct (decide (x = invr)) as [->|Hneq].
      + set_solver.
      + set_solver.
    Qed.

    (* [mask ⊆ inv_set] is genuinely needed: an invariant name outside [inv_set]
       carries no disjointness guarantee, so its namespace could overlap invr's
       and the equality would fail. *)
    Lemma inv_map_set_minus_subseteq (Hwf : ProgramWF) mask invr:
      invr ∈ mask ->
      invr ∈ inv_set ->
      mask ⊆ inv_set ->
        (inv_set_to_namespace (mask ∖ {[invr]})) = inv_set_to_namespace mask ∖ ↑inv_namespace_map invr.
    Proof.
      intros Hin Hinvset Hmask_sub.
      unfold inv_set_to_namespace.
      set (f := λ inv (acc : coPset), acc ∪ ↑inv_namespace_map inv).
      (* Every *other* invariant of the mask is in inv_set and differs from invr,
         so pwf_inv_namespace_disjoint applies to it. *)
      have Hrest_disj : set_fold f ∅ (mask ∖ {[invr]}) ## (↑inv_namespace_map invr : coPset).
      {
        have Hrest : ∀ i, i ∈ mask ∖ {[invr]} → i ∈ inv_set ∧ i ≠ invr.
        { intros i Hi. apply elem_of_difference in Hi as [Hi1 Hi2].
          split; [exact (Hmask_sub i Hi1) |].
          intros ->. apply Hi2. apply elem_of_singleton_2. reflexivity. }
        revert Hrest.
        apply (set_fold_ind
                 (λ acc s, (∀ i, i ∈ s → i ∈ inv_set ∧ i ≠ invr) →
                           acc ## (↑inv_namespace_map invr : coPset))).
        - solve_proper.
        - intros _. set_solver.
        - intros x s' acc Hnotin IH Hall.
          destruct (Hall x ltac:(set_solver)) as [Hxset Hxne].
          have Hxdisj := Hwf.(pwf_inv_namespace_disjoint) x invr Hxset Hinvset Hxne.
          have Hacc : acc ## (↑inv_namespace_map invr : coPset).
          { apply IH. intros i Hi. apply Hall. set_solver. }
          subst f. simpl. set_solver.
      }
      have Hcomm_acc : forall (S : gset inv_name) (b : coPset),
          set_fold f b S = set_fold f ∅ S ∪ b.
      {
        intros S b.
        pose proof (@set_fold_comm_acc inv_name (gset inv_name) _ _ _ _ _ _ _ _ _ coPset f (fun c => c ∪ b) ∅ S) as Hca.
        simpl in Hca.
        rewrite <- Hca.
        - f_equal. set_solver.
        - intros y c. subst f. simpl. set_solver.
      }
      have Hstep : forall (x : inv_name) (Y : gset inv_name),
          x ∉ Y ->
          set_fold f ∅ ({[x]} ∪ Y) = set_fold f ∅ Y ∪ ↑inv_namespace_map x.
      {
        intros x Y Hx.
        assert (Hdisj : ({[x]} : gset inv_name) ## Y) by set_solver.
        have H1 : set_fold f ∅ ({[x]} ∪ Y) = set_fold f (set_fold f ∅ ({[x]} : gset inv_name)) Y.
        { apply (@set_fold_disj_union_strong inv_name (gset inv_name) _ _ _ _ _ _ _ _ _ coPset eq _ f ∅ {[x]} Y).
          - intros y. solve_proper.
          - intros x1 x2 b' _ _ _. subst f. simpl. set_solver.
          - exact Hdisj.
        }
        rewrite H1.
        rewrite (@set_fold_singleton inv_name (gset inv_name) _ _ _ _ _ _ _ _ _ coPset f ∅ x).
        rewrite Hcomm_acc.
        subst f. simpl. set_solver.
      }
      pose proof (union_difference_singleton_L invr mask Hin) as Hmask_split.
      have Hmask_eq : set_fold f ∅ mask
                    = set_fold f ∅ (mask ∖ {[invr]}) ∪ ↑inv_namespace_map invr.
      {
        transitivity (set_fold f ∅ ({[invr]} ∪ (mask ∖ {[invr]}))).
        - f_equal. exact Hmask_split.
        - apply Hstep.
          intro Hc. apply elem_of_difference in Hc.
          destruct Hc as [_ Hne]. apply Hne. apply elem_of_singleton_2. reflexivity.
      }
      rewrite Hmask_eq. set_solver.
    Qed.

    Lemma trnsl_expr_interp_lexpr_compatibility stk e lexpr lv mp :
      trnsl_expr_lExpr stk e = Some (lexpr) ->
      interp_lexpr lexpr mp = Some lv ->
      expr_step e (symb_stk_to_stk_frm stk mp) (Val (trnsl_lval lv)).
    Proof.
      revert lexpr lv.
      induction e; intros lexpr lv Htrnsl Hinterp; simpl in Htrnsl.
      - (* Var x *)
        destruct (stk !! x) as [lv_name|] eqn:Hlookup; [|discriminate].
        injection Htrnsl as <-. simpl in Hinterp. injection Hinterp as <-.
        apply VarStep. unfold symb_stk_to_stk_frm. simpl.
        rewrite lookup_fmap. rewrite Hlookup. simpl. done.
      - (* Val v *)
        injection Htrnsl as <-. simpl in Hinterp. injection Hinterp as <-.
        rewrite trnsl_lval_trnsl_val_inverse. apply ExprRefl.
      - (* UnOp op e *)
        destruct (trnsl_expr_lExpr stk e) as [le1|] eqn:Hle1; [|discriminate].
        injection Htrnsl as <-.
        destruct op; simpl in Hinterp.
        + (* NotBoolOp *)
          destruct (interp_lexpr le1 mp) as [[b|n| |l|p]|] eqn:Hv1; try discriminate.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitBool b).
          * exact (IHe le1 (LitBool b) eq_refl Hv1).
          * simpl. done.
        + (* NegOp *)
          destruct (interp_lexpr le1 mp) as [[b|i| |l|p]|] eqn:Hv1; try discriminate.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitInt i).
          * exact (IHe le1 (LitInt i) eq_refl Hv1).
          * simpl. done.
        + (* RAValidOp *)
          destruct (interp_lexpr le1 mp) as [[b|n| |l|[r x]]|] eqn:Hv1; try discriminate.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitRAElem (existT r x)).
          * exact (IHe le1 (LitRAElem (existT r x)) eq_refl Hv1).
          * simpl. done.
        + (* RAOfIntOp *)
          destruct (interp_lexpr le1 mp) as [[b|z| |l|p]|] eqn:Hv1; try discriminate.
          simpl in Hinterp.
          injection Hinterp as <-.
          apply UnOpStep with (v := lang.LitInt z).
          * exact (IHe le1 (LitInt z) eq_refl Hv1).
          * simpl. reflexivity.
      - (* BinOp op e1 e2 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        injection Htrnsl as <-.
        destruct op; simpl in Hinterp;
          (* Integer arithmetic ops: AddOp, SubOp, MulOp, DivOp, ModOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|p1]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|p2]|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitInt i1) (v2 := lang.LitInt i2);
               [ exact (IHe1 le1 (LitInt i1) eq_refl Hv1)
               | exact (IHe2 le2 (LitInt i2) eq_refl Hv2)
               | simpl; done ]);
          (* Comparison ops: LtOp, GtOp, LeOp, GeOp — result is LitBool *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|p1]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|p2]|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitInt i1) (v2 := lang.LitInt i2);
               [ exact (IHe1 le1 (LitInt i1) eq_refl Hv1)
               | exact (IHe2 le2 (LitInt i2) eq_refl Hv2)
               | simpl; done ]);
          (* EqOp *)
          try (destruct (interp_lexpr le1 mp) as [v1|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [v2|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := trnsl_lval v1) (v2 := trnsl_lval v2);
               [ exact (IHe1 le1 v1 eq_refl Hv1)
               | exact (IHe2 le2 v2 eq_refl Hv2)
               | simpl; rewrite <- val_beq_bool_decide; done ]);
          (* NeOp *)
          try (destruct (interp_lexpr le1 mp) as [v1|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [v2|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := trnsl_lval v1) (v2 := trnsl_lval v2);
               [ exact (IHe1 le1 v1 eq_refl Hv1)
               | exact (IHe2 le2 v2 eq_refl Hv2)
               | simpl; rewrite bool_decide_not; rewrite <- val_beq_bool_decide; done ]);
          (* Boolean ops: AndOp, OrOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|n1| |l1|p1]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|n2| |l2|p2]|] eqn:Hv2; try discriminate;
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitBool b1) (v2 := lang.LitBool b2);
               [ exact (IHe1 le1 (LitBool b1) eq_refl Hv1)
               | exact (IHe2 le2 (LitBool b2) eq_refl Hv2)
               | simpl; done ]);
          (* RACompOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|[r1 x1]]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|[r2 x2]]|] eqn:Hv2; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate Hinterp ];
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitRAElem (existT r1 x1)) (v2 := lang.LitRAElem (existT r1 x2));
               [ exact (IHe1 le1 (LitRAElem (existT r1 x1)) eq_refl Hv1)
               | exact (IHe2 le2 (LitRAElem (existT r1 x2)) eq_refl Hv2)
               | apply bin_op_eval_ra_comp ]);
          (* RAFrameOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|[r1 x1]]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|[r2 x2]]|] eqn:Hv2; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate Hinterp ];
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitRAElem (existT r1 x1)) (v2 := lang.LitRAElem (existT r1 x2));
               [ exact (IHe1 le1 (LitRAElem (existT r1 x1)) eq_refl Hv1)
               | exact (IHe2 le2 (LitRAElem (existT r1 x2)) eq_refl Hv2)
               | apply bin_op_eval_ra_frame ]);
          (* RAFpuValidOp *)
          try (destruct (interp_lexpr le1 mp) as [[b1|i1| |l1|[r1 x1]]|] eqn:Hv1; try discriminate;
               destruct (interp_lexpr le2 mp) as [[b2|i2| |l2|[r2 x2]]|] eqn:Hv2; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate Hinterp ];
               injection Hinterp as <-;
               apply BinOpStep with (v1 := lang.LitRAElem (existT r1 x1)) (v2 := lang.LitRAElem (existT r1 x2));
               [ exact (IHe1 le1 (LitRAElem (existT r1 x1)) eq_refl Hv1)
               | exact (IHe2 le2 (LitRAElem (existT r1 x2)) eq_refl Hv2)
               | apply bin_op_eval_ra_fpuvalid ]).
      - (* IfE e1 e2 e3 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [|discriminate].
        injection Htrnsl as <-.
        simpl in Hinterp.
        destruct (interp_lexpr le1 mp) as [[b|n| |l|p]|] eqn:Hcond; try discriminate.
        (* only LitBool b remains; now case split on the boolean *)
        destruct b; simpl in Hinterp.
        + (* condition = true *)
          apply IfETrueEvalStep.
          * exact (IHe1 le1 (LitBool true) eq_refl Hcond).
          * exact (IHe2 le2 lv eq_refl Hinterp).
        + (* condition = false *)
          apply IfEFalseEvalStep.
          * exact (IHe1 le1 (LitBool false) eq_refl Hcond).
          * exact (IHe3 le3 lv eq_refl Hinterp).
      - (* StuckE *)
        injection Htrnsl as <-. simpl in Hinterp. discriminate.
    Qed.

    Lemma trnsl_expr_interp_lexpr_compatibility2 stk e lexpr lv mp :
      trnsl_expr_lExpr stk e = Some (lexpr) ->
      expr_step e (symb_stk_to_stk_frm stk mp) (Val (trnsl_lval lv)) ->
      interp_lexpr lexpr mp = Some lv.
    Proof.
      revert lexpr lv.
      induction e; intros lexpr lv Htrnsl Hstep; simpl in Htrnsl.
      - (* Var x *)
        destruct (stk !! x) as [lv_name|] eqn:Hlookup; [|discriminate].
        injection Htrnsl as <-. simpl.
        inversion Hstep; subst.
        unfold symb_stk_to_stk_frm in H2. simpl in H2.
        rewrite lookup_fmap in H2. rewrite Hlookup in H2. simpl in H2.
        injection H2 as H2. f_equal. exact (trnsl_lval_injective _ _ H2).
      - (* Val v *)
        injection Htrnsl as <-. simpl.
        inversion Hstep; subst.
        f_equal. exact (trnsl_val_trnsl_lval_inverse lv).
      - (* UnOp op e *)
        destruct (trnsl_expr_lExpr stk e) as [le1|] eqn:Hle1; [|discriminate].
        injection Htrnsl as <-.
        inversion Hstep; subst.
        destruct op; simpl.
        + (* NotBoolOp *)
          simpl in H4. destruct v; try discriminate.
          injection H4 as H4.
          pose proof (IHe le1 (LitBool b) eq_refl H3) as Hle.
          rewrite Hle. simpl. f_equal. exact (trnsl_lval_injective (LitBool (negb b)) lv H4).
        + (* NegOp *)
          simpl in H4. destruct v; try discriminate.
          injection H4 as H4.
          pose proof (IHe le1 (LitInt i) eq_refl H3) as Hle.
          rewrite Hle. simpl. f_equal. exact (trnsl_lval_injective (LitInt (-i)) lv H4).
        + (* RAValidOp *)
          simpl in H4. destruct v as [ | | | |[r x]]; try discriminate.
          injection H4 as H4.
          pose proof (IHe le1 (LitRAElem (existT r x)) eq_refl H3) as Hle.
          rewrite Hle. simpl. f_equal. exact (trnsl_lval_injective (LitBool (bool_decide (valid x))) lv H4).
        + (* RAOfIntOp *)
          simpl in H4. destruct v as [ | z | | | ]; try discriminate.
          injection H4 as H4.
          pose proof (IHe le1 (LitInt z) eq_refl H3) as Hle.
          rewrite Hle. simpl. f_equal.
          exact (trnsl_lval_injective (LitRAElem (existT r (ra_of_int z))) lv H4).
      - (* BinOp op e1 e2 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        injection Htrnsl as <-.
        inversion Hstep; subst.
        rewrite <- (trnsl_lval_trnsl_val_inverse v1) in H4.
        rewrite <- (trnsl_lval_trnsl_val_inverse v2) in H5.
        pose proof (IHe1 le1 (trnsl_val v1) eq_refl H4) as Hle1'.
        pose proof (IHe2 le2 (trnsl_val v2) eq_refl H5) as Hle2'.
        destruct op; simpl in *;
          (* Group 1: arithmetic, comparison, bool ops *)
          try (destruct v1; try discriminate; destruct v2; try discriminate;
               injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               simpl in Hle1', Hle2'; rewrite Hle1' Hle2'; simpl; done);
          (* EqOp *)
          try (injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               rewrite Hle1' Hle2'; simpl; f_equal; f_equal;
               rewrite val_beq_bool_decide;
               rewrite trnsl_lval_trnsl_val_inverse; rewrite trnsl_lval_trnsl_val_inverse;
               destruct (bool_decide (v1 = v2)); done);
          (* NeOp *)
          try (injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               rewrite Hle1' Hle2'; simpl; f_equal; f_equal;
               rewrite bool_decide_not; f_equal;
               rewrite val_beq_bool_decide;
               rewrite trnsl_lval_trnsl_val_inverse; rewrite trnsl_lval_trnsl_val_inverse;
               destruct (bool_decide (v1 = v2)); done);
          (* RACompOp *)
          try (destruct v1 as [ | | | |[r1 x1]]; try discriminate;
               destruct v2 as [ | | | |[r2 x2]]; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate H6 ];
               injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               simpl in Hle1', Hle2';
               exact (interp_lexpr_ra_comp r1 x1 x2 le1 le2 mp Hle1' Hle2'));
          (* RAFrameOp *)
          try (destruct v1 as [ | | | |[r1 x1]]; try discriminate;
               destruct v2 as [ | | | |[r2 x2]]; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate H6 ];
               injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               simpl in Hle1', Hle2';
               exact (interp_lexpr_ra_frame r1 x1 x2 le1 le2 mp Hle1' Hle2'));
          (* RAFpuValidOp *)
          try (destruct v1 as [ | | | |[r1 x1]]; try discriminate;
               destruct v2 as [ | | | |[r2 x2]]; try discriminate;
               destruct (decide (r1 = r2)) as [<-|Hne]; [ | discriminate H6 ];
               injection H6 as H6;
               symmetry in H6; apply (f_equal trnsl_val) in H6;
               rewrite trnsl_val_trnsl_lval_inverse in H6; simpl in H6; subst lv;
               simpl in Hle1', Hle2';
               exact (interp_lexpr_ra_fpuvalid r1 x1 x2 le1 le2 mp Hle1' Hle2')).
      - (* IfE e1 e2 e3 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [|discriminate].
        injection Htrnsl as <-.
        simpl.
        inversion Hstep; subst.
        + (* IfETrueStep: e1 = Val (LitBool true), true branch = Val (trnsl_lval lv) *)
          specialize (IHe1 le1 (LitBool true) eq_refl). specialize (IHe2 le2 lv eq_refl).
          simpl in IHe1, IHe2.
          pose proof (IHe1 (ExprRefl _ _)) as Hcond.
          pose proof (IHe2 (ExprRefl _ _)) as Hbranch.
          rewrite Hcond. exact Hbranch.
        + (* IfEFalseStep: e1 = Val (LitBool false), false branch = Val (trnsl_lval lv) *)
          specialize (IHe1 le1 (LitBool false) eq_refl). specialize (IHe3 le3 lv eq_refl).
          simpl in IHe1, IHe3.
          pose proof (IHe1 (ExprRefl _ _)) as Hcond.
          pose proof (IHe3 (ExprRefl _ _)) as Hbranch.
          rewrite Hcond. exact Hbranch.
        + (* IfETrueEvalStep: eval e1 → LitBool true, eval e2 → lv *)
          pose proof (IHe1 le1 (LitBool true) eq_refl H3) as Hcond.
          pose proof (IHe2 le2 lv eq_refl H5) as Hbranch.
          rewrite Hcond. exact Hbranch.
        + (* IfEFalseEvalStep: eval e1 → LitBool false, eval e3 → lv *)
          pose proof (IHe1 le1 (LitBool false) eq_refl H3) as Hcond.
          pose proof (IHe3 le3 lv eq_refl H5) as Hbranch.
          rewrite Hcond. exact Hbranch.
      - (* StuckE *)
        injection Htrnsl as <-. simpl. inversion Hstep.
    Qed.

    Definition trnsl_hoare_triple (stk_id: stack_id) (p : assertion) (msk : maskAnnot) (cmd : stmt) (q : assertion) (mp : symb_map) : iProp Σ :=
        match (trnsl_stmt cmd) with
        | Error => True
        | None' =>
          match (trnsl_assertion p stk_id mp),
                (trnsl_assertion q stk_id mp) with
          | p', q' =>
            p' ={trnsl_mask msk}=∗ q'
          end

        | Some' s =>
          match (trnsl_assertion p stk_id mp),
                (trnsl_assertion q stk_id mp) with
          | p', q' =>
            {{{ p' }}}
              to_rtstmt stk_id s @ (trnsl_mask msk)
            {{{ RET lang.LitUnit; q'}}}
          end
        end
    .

    (* The per-invariant shared worlds.  Persistent, and an explicit premise of
       [raven_soundness]: the calculus has no rule that could establish it, so
       it records how the ghost state must have been set up. *)
    Definition all_inv_worlds : iProp Σ :=
      ([∗ set] inv' ∈ inv_set, inv (inv_namespace_map inv') (Winv inv'))%I.

    Lemma all_inv_worlds_elem (inv' : inv_name) :
      inv' ∈ inv_set →
      all_inv_worlds -∗ inv (inv_namespace_map inv') (Winv inv').
    Proof.
      intros Hin. rewrite /all_inv_worlds.
      iIntros "H". by iApply (big_sepS_elem_of with "H").
    Qed.

    (* Ghost-heap world: the calculus has no rule that could establish it
       either (Wghost, like Winv, is never allocated by any rule -- see
       Wghost_alloc, the only consumer, inside HeapAllocRule's soundness
       case), so it's an explicit premise of raven_soundness, same status
       as all_inv_worlds. *)
    Definition Wghost_world : iProp Σ := inv ghost_heap_namespace Wghost.

    (* The proc-table registration for every procedure, mirroring
       all_inv_worlds's own role: the calculus has no rule that could
       establish proc_tbl_chunk (it's a persistent fact about how the ghost
       state was set up, never allocated by any rule -- see
       ProcCallRuleRet's soundness case, the only consumer), so it's an
       explicit premise of raven_soundness instead. *)
    Definition all_proc_tbl_chunks : iProp Σ :=
      ([∗ map] proc_name ↦ proc_record ∈ proc_map,
        proc_tbl_chunk proc_name
          (lang.Proc proc_name (proc_args_of proc_record) (proc_locals_of proc_record)
             match trnsl_stmt (proc_body_of proc_record) with
             | Some' s => s
             | _ => lang.SkipS
             end))%I.

    Lemma all_proc_tbl_chunks_elem (proc_name : proc_name) (proc_record : ProcRecord) :
      proc_map !! proc_name = Some proc_record ->
      all_proc_tbl_chunks -∗
      proc_tbl_chunk proc_name
        (lang.Proc proc_name (proc_args_of proc_record) (proc_locals_of proc_record)
           match trnsl_stmt (proc_body_of proc_record) with
           | Some' s => s
           | _ => lang.SkipS
           end).
    Proof.
      intros Hin. rewrite /all_proc_tbl_chunks.
      iIntros "H". by iApply (big_sepM_lookup with "H").
    Qed.

    Lemma fresh_var_trnsl_expr_invariant stk lv e lexpr mp v0:
      fresh_lvar stk lv ->
      trnsl_expr_lExpr stk e = Some lexpr ->
       interp_lexpr lexpr mp = interp_lexpr lexpr (λ x : lvar, if (x =? lv)%string then v0 else mp x).
    Proof.
      intros Hfresh Htrnsl.
      revert lexpr Htrnsl.
      induction e; intros lexpr Htrnsl; simpl in Htrnsl.
      - (* Var x: lexpr = LVar (stk !! x) *)
        destruct (stk !! x) as [lv_name|] eqn:Hlookup; [|discriminate].
        injection Htrnsl as <-. simpl.
        (* lv_name ≠ lv because fresh_lvar stk lv *)
        assert (lv_name ≠ lv) as Hneq.
        { intro Heq. subst lv_name. exact (Hfresh x Hlookup). }
        rewrite <- String.eqb_neq in Hneq. rewrite Hneq. done.
      - (* Val v: lexpr = LVal (trnsl_val v) *)
        injection Htrnsl as <-. simpl. done.
      - (* UnOp op e *)
        destruct (trnsl_expr_lExpr stk e) as [le1|] eqn:Hle1; [|discriminate].
        injection Htrnsl as <-. simpl.
        rewrite (IHe le1 eq_refl). done.
      - (* BinOp op e1 e2 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        injection Htrnsl as <-. simpl.
        rewrite (IHe1 le1 eq_refl) (IHe2 le2 eq_refl). done.
      - (* IfE e1 e2 e3 *)
        destruct (trnsl_expr_lExpr stk e1) as [le1|] eqn:Hle1; [|discriminate].
        destruct (trnsl_expr_lExpr stk e2) as [le2|] eqn:Hle2; [|discriminate].
        destruct (trnsl_expr_lExpr stk e3) as [le3|] eqn:Hle3; [|discriminate].
        injection Htrnsl as <-. simpl.
        rewrite (IHe1 le1 eq_refl) (IHe2 le2 eq_refl) (IHe3 le3 eq_refl). done.
      - (* StuckE *)
        injection Htrnsl as <-. simpl. done.
    Qed.

    Lemma lexpr_holds_interp_compat lexpr v1 mp v:
      LExpr_holds (LBinOp EqOp lexpr (LVal v1)) mp ->
      interp_lexpr lexpr mp = Some v ->
      v = v1.
    Proof.
      intros H1 H2.
      unfold LExpr_holds in H1.
      simpl in H1. rewrite H2 in H1. injection H1 as H1.
      destruct (val_beq v v1) eqn:Hvb.
      - apply internal_val_dec_bl in Hvb. done.
      - inversion H1.
    Qed.

    Lemma val_beq_refl (v : val) : val_beq v v = true.
    Proof.
      (* Straight application of the Scheme-generated "= → beq" direction. *)
      apply internal_val_dec_lb. reflexivity.
    Qed.

    Lemma val_beq_eq (v1 : val) (v2 : val) : val_beq v1 v2 = true -> v1 = v2.
    Proof.
      (* Straight application of the Scheme-generated "beq → =" direction. *)
      apply internal_val_dec_bl.
    Qed.

    Lemma val_beq_neq v1 v2 : val_beq v1 v2 = false -> v1 ≠ v2.
    Proof.
      (* Contrapositive: if v1 = v2 then val_beq v1 v2 = true (val_beq_refl),
         contradicting the hypothesis val_beq v1 v2 = false. *)
      intros Hfalse ->.
      rewrite val_beq_refl in Hfalse. discriminate.
    Qed.

    Lemma expr_interp_well_defined ρ σ stk e mp lexpr:
      stk_type_compat ρ σ stk ->
      env_typ_well_defined σ mp ->
      trnsl_expr_lExpr stk e = Some lexpr ->
      interp_lexpr lexpr mp = None ->
      not (expr_well_defined ρ e).
    Proof.
      intros Hstk Henv Htrnsl Hnone [tp Htp].
      pose proof (lexpr_expr_typ_compat ρ σ stk e lexpr tp Hstk Htrnsl Htp) as Hinf_le.
      pose proof (lexpr_typcheck_well_defined σ mp lexpr tp Henv Hinf_le) as [val Hval].
      rewrite Hnone in Hval. discriminate.
    Qed.

    (* Well-typed argument expressions all denote a value under mp, so an
       argument list has a value vector. *)
    Lemma args_interp_values ρ σ stk mp (args : list lang.expr) (lexprs : list LExpr) :
      stk_type_compat ρ σ stk →
      env_typ_well_defined σ mp →
      Forall (fun arg => expr_well_defined ρ arg) args →
      map (fun arg => trnsl_expr_lExpr stk arg) args = map (fun le => Some le) lexprs →
      ∃ vs : list val, Forall2 (λ le v, interp_lexpr le mp = Some v) lexprs vs.
    Proof.
      intros Hstk Henv Hwd. revert lexprs.
      induction args as [| a args IH]; intros lexprs Hmap.
      - destruct lexprs; [| discriminate]. exists []. constructor.
      - destruct lexprs as [| le lexprs]; [discriminate |].
        simpl in Hmap. injection Hmap as Hle Hmap'.
        inversion Hwd as [| a' args' Hwda Hwdargs]; subst.
        destruct (IH Hwdargs lexprs Hmap') as [vs Hvs].
        destruct (interp_lexpr le mp) as [v |] eqn:Hinterp.
        + exists (v :: vs). by constructor.
        + exfalso.
          exact (expr_interp_well_defined ρ σ stk a mp le Hstk Henv Hle Hinterp Hwda).
    Qed.

    Lemma fresh_mp_rewrite_LExpr_holds stk lv e lexpr mp v0 : 
      fresh_lvar stk lv -> 
      trnsl_expr_lExpr stk e = Some lexpr -> 
      interp_lexpr lexpr mp = Some v0 -> 
      LExpr_holds (LBinOp EqOp (LVar lv) lexpr)
        (λ x : lvar, if (x =? lv)%string then v0 else mp x).
    Proof. intros Hfresh Htrnsl Hinterp.
      set (mp' := (λ x : lvar, if (x =? lv)%string then v0 else mp x)).
      (* assert (interp_lexpr (LVar lv)) *)
      unfold LExpr_holds. simpl. 
      assert (mp' lv = v0). { subst mp'. simpl. rewrite String.eqb_refl. reflexivity. }
      rewrite H.
      rewrite (fresh_var_trnsl_expr_invariant _ _ _ _ _ v0 Hfresh Htrnsl) in Hinterp.
      rewrite Hinterp. 

      assert (val_beq v0 v0 = true) as Hbeq. { apply val_beq_refl. }
      rewrite Hbeq.
      reflexivity.
    Qed.

    Lemma fresh_mp_rewrite_symb_stk_to_stk_frm_compat stk lvar_x x mp val:
      fresh_lvar stk lvar_x ->
        symb_stk_to_stk_frm (<[x:=lvar_x]> stk)
          (λ x0 : lvar, if (x0 =? lvar_x)%string then val else mp x0) =

          {| locals := <[x:=trnsl_lval val]> (locals (symb_stk_to_stk_frm stk mp))|} .
    Proof. intros Hfresh.
      unfold symb_stk_to_stk_frm. apply f_equal.
      apply map_eq.
      intros i.
      destruct (stk !! i) eqn:HstkI.
      - rewrite lookup_fmap. 
        destruct (String.eqb i x) eqn:H_i_x.
        + apply String.eqb_eq in H_i_x. subst i. simpl.
        rewrite lookup_insert. rewrite lookup_insert. simpl. rewrite String.eqb_refl. done.

        + assert (not (i = x)). { apply String.eqb_neq in H_i_x. done. }

        rewrite lookup_insert_ne. 
          2 : { intro Heq; subst i; contradiction. }

        rewrite lookup_insert_ne. 
          2 : { intro Heq; subst i; contradiction. }
        simpl. rewrite HstkI. simpl. rewrite lookup_fmap. rewrite HstkI. simpl. apply f_equal. apply f_equal.
        assert ((l =? lvar_x)%string = false).
          { unfold fresh_lvar in Hfresh.
        specialize (Hfresh i). rewrite HstkI in Hfresh. apply String.eqb_neq. intro H2. subst lvar_x. contradiction. }
        rewrite H0. done.

      - destruct (String.eqb i x) eqn:H_i_x.
        + apply String.eqb_eq in H_i_x. subst i.
        rewrite lookup_fmap. rewrite lookup_insert.
        rewrite lookup_insert. simpl. rewrite String.eqb_refl. done.
        + apply String.eqb_neq in H_i_x.
          simpl.
          rewrite lookup_fmap. rewrite lookup_insert_ne.
          2 : { intro Heq; subst i; contradiction. }
          rewrite lookup_fmap. rewrite HstkI. simpl.
          rewrite lookup_insert_ne.
          2 : { intro Heq; subst i; contradiction. }
          rewrite HstkI. simpl. done.
    Qed.

    (* Native-Iris restatement of the former [proc_specs_valid] axiom: the operational
       Hoare triple for every procedure in [proc_map] holds. Persistent (□) so it can be
       freely duplicated into every nested call frame; guarded uses of this fact (behind a
       later, via Löb induction) are how [raven_soundness] below discharges it
       without assuming it outright. *)
    (* Parameterized by [σ], the same lvar-typing environment used throughout the
       whole program's verification (matching rrl_validity's own σ parameter) — not
       re-quantified internally, so every use of [all_proc_specs_valid_iris σ] and every
       rrl_validity invocation are talking about the same σ. *)
    Definition all_proc_specs_valid_iris (σ : lvar_typs) : iProp Σ :=
      □ ∀ proc proc_record stk_vals,
      ⌜proc ∈ proc_set⌝ -∗
      ⌜proc_map !! proc = Some proc_record⌝ -∗

      ∀ precond (postcond : lang.val -> iProp Σ) stk_id stk_frm mp stmt (msk : maskAnnot),

      (* mp must be well-typed against σ, mirroring the requirement rrl_validity itself needs. *)
      ⌜env_typ_well_defined σ mp⌝ -∗

      (* The mask only ever mentions invariants of the program, mirroring the
         requirement rrl_validity itself needs to reason about mask narrowing. *)
      ⌜msk ⊆ inv_set⌝ -∗

      (* The caller's own current mask must already include whatever this
         procedure itself needs to open (proc_required_mask) -- see
         ProcCallRuleRet's own copy of this comment for why an unconditional
         ∀ msk is unsatisfiable for any procedure that opens an invariant
         at all. *)
      ⌜proc_required_mask proc_record ⊆ msk⌝ -∗

      ⌜forall v, v ∈ (proc_args_of proc_record) -> is_Some (stk_frm.(locals) !! v.1)⌝ -∗

      ⌜Forall2 (λ var val, stk_frm.(locals) !! var = Some val) (proc_args_of proc_record).*1 stk_vals⌝ -∗

      (* stk_frm is exactly the frame a fresh call/spawn produces (see lang.v's
         RTCallStep/SpawnStep): every declared local (including "#ret_val")
         is present, holding a non-deterministically chosen value of its
         declared type, and nothing else. Needed so a synthesized LStack for
         the procedure's own entry scope can reconstruct stk_frm exactly. *)
      ⌜∀ v tp, (v, tp) ∈ proc_locals_of proc_record ->
          ∃ val, stk_frm.(locals) !! v = Some val ∧ typeOf val = tp⌝ -∗
      ⌜dom stk_frm.(locals) = list_to_set (proc_args_of proc_record).*1 ∪ list_to_set (proc_locals_of proc_record).*1⌝ -∗

      (* the argument values are well-typed against the procedure's own declared
         parameter types, mirroring the static proc_call_args_well_typed check. *)
      ⌜Forall2 (λ arg_decl val, typeOf val = snd arg_decl) (proc_args_of proc_record) stk_vals⌝ -∗

      let subst_map' := val_subst_map (proc_args_of proc_record).*1 stk_vals in

      ⌜trnsl_assertion (subst (proc_precond_of proc_record) subst_map') stk_id mp ≡ precond⌝ -∗
      (* The value actually placed in "#ret_val" at return matches the
         callee's own declared type for it -- the dynamic half
         ProcCallRuleRet's soundness case needs (see
         proc_call_ret_well_typed's own comment for the static half),
         bundled into this bridge (rather than as a separate conjunct of
         the WP conclusion below) so it's available to any caller-chosen
         postcond uniformly. Proven below by raven_soundness_core via
         env_typ_well_defined at the callee's own exit mp. *)
      ⌜∀ ret_val, (trnsl_assertion (subst (proc_postcond_of proc_record) (<["#ret_val" := LVal (trnsl_val (ret_val))]> subst_map')) stk_id mp ∗
                   ⌜proc_ret_typ_opt proc_record = Some (typeOf ret_val)⌝)%I ≡ postcond ret_val⌝ -∗

      ⌜(trnsl_stmt (proc_body_of proc_record) = Some' stmt) \/ (trnsl_stmt (proc_body_of proc_record) = None' /\ stmt = lang.SkipS)⌝ -∗
      {{{ stack_own[stk_id, stk_frm] ∗ precond }}} (to_rtstmt stk_id stmt) @ (trnsl_mask msk)
        {{{ RET lang.LitUnit; ∃ ret_val stk_frm'', stack_own[stk_id, stk_frm''] ∗
              ⌜ (locals stk_frm'' !! "#ret_val") = Some ret_val ⌝ ∗
              postcond ret_val }}}.

    (* Raven counterpart of all_proc_specs_valid_iris: every procedure's own
       body is provably correct against its own contract via RavenHoareTriple,
       run from a symbolic entry stack synthesized (via a fresh
       proc_entry_lvars) out of its formal args and locals. A plain Prop,
       not an iProp -- raven_soundness below is exactly the bridge from this
       Raven-level statement to the Iris-level all_proc_specs_valid_iris.

       No externally-supplied pvar_typs parameter: each procedure's own
       body is checked against proc_pvar_typs proc_record, its own
       args/locals, exactly as all_proc_specs_valid_iris already types
       "#ret_val" and every other local via proc_args_of/proc_locals_of/
       typeOf rather than a shared table. A single global pvar_typs would
       force every procedure sharing a variable name -- most unavoidably
       "#ret_val" itself, which every procedure must declare -- to agree
       on its type; see proc_call_ret_well_typed's own comment for the
       caller-side half of this same design. *)
    Definition all_proc_specs_valid_raven (σ : lvar_typs) : Prop :=
      ∀ proc_name proc_record, proc_map !! proc_name = Some proc_record →
        let ρ := proc_pvar_typs proc_record in
        stmt_well_defined ρ (proc_body_of proc_record) ∧
        ∀ msk, proc_required_mask proc_record ⊆ msk → msk ⊆ inv_set →
        ∀ (dll : proc_entry_lvars σ proc_record),
          ∃ stk0' lv_final,
            stk0' !! "#ret_val" = Some lv_final ∧
            ¬ is_reserved lv_final ∧
            proc_ret_typ_opt proc_record = Some (σ lv_final) ∧
            RavenHoareTriple ρ σ
              (LAnd (LStack (assoc_map (proc_args_of proc_record ++ proc_locals_of proc_record).*1
                                        (dll_args dll ++ dll_locals dll)))
                 (subst (proc_precond_of proc_record)
                    (lvar_subst_map (proc_args_of proc_record).*1 (dll_args dll))))
              (proc_body_of proc_record) msk
              (LAnd (LStack stk0')
                 (subst (proc_postcond_of proc_record)
                    (<["#ret_val" := LVar lv_final]>
                       (lvar_subst_map (proc_args_of proc_record).*1 (dll_args dll))))).

    (* Combines two separately-held translated assertions into one LAnd fact
       -- used by ExistsElimRule's soundness case to reassemble the pieces of
       a precondition after they've been destructured. *)
    Lemma trnsl_assertion_and_intro P1 P2 stk_id mp :
      trnsl_assertion P1 stk_id mp -∗ trnsl_assertion P2 stk_id mp -∗
      trnsl_assertion (LAnd P1 P2) stk_id mp.
    Proof. rewrite trnsl_assertion_and. iIntros "$ $". Qed.

    (* eval_lvar at any x ∈ dom M is stable under an mp-update at a var not
       mentioned by any of M's values -- the two facts InvAccessBlockRule's
       soundness case needs to bridge subst inv_body subst_map's truth
       across the mp-update the block's own postcondition existential
       (LExists lv) introduces for the wrapped stmt's fresh result lvar. *)
    Lemma eval_lvar_base_stable (M : gmap lvar LExpr) (q : symb_map) (lv : lvar) (v' : val) (x : lvar) :
      lv ∉ lexpr_map_fvars M -> x ∈ dom M ->
      eval_lvar M (fun y => if (y =? lv)%string then v' else q y) x = eval_lvar M q x.
    Proof.
      intros Hlv Hx. destruct (proj1 (elem_of_dom (D := gset lvar) M x) Hx) as [e HMx].
      unfold eval_lvar. rewrite HMx.
      apply interp_lexpr_stable. exact (proj1 (lexpr_map_fvars_spec M lv) Hlv x e HMx).
    Qed.

    (* Every lexpr InvAccessBlockRule's own call-site args translate to is
       fvar-disjoint from a stk-fresh lvar -- lifts
       trnsl_expr_lExpr_fresh_lvar (single expr) across the whole args/
       lexprs list via the rule's own Hargs map-equality premise. *)
    Lemma lexpr_list_fresh_lvar (stk : stack) (args : list lang.expr) (lexprs : list LExpr) (lv : lvar) :
      map (trnsl_expr_lExpr stk) args = map Some lexprs ->
      fresh_lvar stk lv ->
      Forall (fun le => lv ∉ lexpr_fvars le) lexprs.
    Proof.
      revert lexprs. induction args as [| a args' IH]; intros lexprs Heq Hfresh;
        destruct lexprs as [| le lexprs']; try discriminate Heq; [constructor |].
      simpl in Heq. injection Heq as Heq1 Heq2.
      constructor.
      - exact (trnsl_expr_lExpr_fresh_lvar stk a le lv Heq1 Hfresh).
      - exact (IH lexprs' Heq2 Hfresh).
    Qed.

    (* lexpr_map_fvars of a zip-built substitution map is bounded by the
       fvars of its values. *)
    Lemma lexpr_map_fvars_zip_bound (ks : list var) (vs : list LExpr) (v : lvar) :
      Forall (fun e => v ∉ lexpr_fvars e) vs ->
      v ∉ lexpr_map_fvars (list_to_map (zip ks vs) : gmap var LExpr).
    Proof.
      intros Hfa. apply (lexpr_map_fvars_spec _ v). intros k e Hke.
      apply elem_of_list_to_map_2, elem_of_zip_r in Hke.
      rewrite List.Forall_forall in Hfa. apply Hfa.
      apply elem_of_list_In. exact Hke.
    Qed.

    (* lexpr_map_fvars of a zip-built substitution map avoids the reserved
       namespace outright, given a Forall fact over the lexprs themselves
       (a local premise of whichever RavenHoareTriple rule supplies them,
       e.g. InvAccessBlockRule/InvAllocRule/ProcCallRuleRet) -- the exact
       shape inv_body_bridge's own Hlexprs_ok parameter needs, for any key
       list (inv_args, pred_args,
       ...), so every direct inv_body_bridge/PredBodyWF-style call site can
       build its own argument with this one lemma. *)
    Lemma lexpr_map_fvars_zip_no_reserved (ks : list lvar) (lexprs : list LExpr)
        (Hlexprs_ok : Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) lexprs) :
      ∀ v, v ∈ lexpr_map_fvars (list_to_map (zip ks lexprs) : gmap lvar LExpr) → ¬ is_reserved v.
    Proof.
      intros v Hv.
      have Hv' := lexpr_map_fvars_zip_subseteq ks lexprs v Hv.
      apply elem_of_union_list in Hv' as [X [HX HvX]].
      apply elem_of_list_fmap in HX as [le [-> Hle]].
      exact (proj1 (Forall_forall _ _) Hlexprs_ok le Hle v HvX).
    Qed.

    (* Builds a subst_map_avoids_reserved fact for a zip-built substitution
       map wholesale, from the two Forall facts every call site (invariant
       args, predicate args, proc-call args, ...) already establishes
       separately: formal-argument names never reserved (dom side, via
       pwf_*_args_not_reserved), and no actual argument lexpr mentions a
       reserved lvar (values side -- a local premise of whichever
       RavenHoareTriple rule supplies lexprs, e.g. InvAccessBlockRule/
       InvAllocRule/ProcCallRuleRet). *)
    Lemma subst_map_avoids_reserved_of_lexprs (ks : list lvar) (lexprs : list LExpr)
        (Hks : Forall (fun a => ¬ is_reserved a) ks)
        (Hvs : Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) lexprs) :
      subst_map_avoids_reserved (list_to_map (zip ks lexprs) : gmap lvar LExpr).
    Proof.
      split.
      - intros v Hv. apply elem_of_dom in Hv as [e He].
        apply elem_of_list_to_map_2 in He. apply elem_of_zip_l in He.
        exact (proj1 (Forall_forall _ _) Hks v He).
      - intros v Hv.
        have Hv' := lexpr_map_fvars_zip_subseteq ks lexprs v Hv.
        apply elem_of_union_list in Hv' as [X [HX HvX]].
        apply elem_of_list_fmap in HX as [le [-> Hle]].
        exact (proj1 (Forall_forall _ _) Hvs le Hle v HvX).
    Qed.

    (* "#ret_val" is never reserved -- disjoint namespaces ("#" vs "$"),
       needed wherever a subst map gets extended with a "#ret_val" slot
       (ProcCallRuleRet's postcondition side) and dom-avoids-reserved has
       to survive that extension. *)
    Lemma ret_val_not_reserved : ¬ is_reserved "#ret_val".
    Proof. unfold is_reserved. simpl. discriminate. Qed.

    (* dom-avoids-reserved survives extending a map with one more,
       itself-non-reserved key. *)
    Lemma dom_insert_not_reserved (M : gmap lvar LExpr) (k : lvar) (e : LExpr) :
      ¬ is_reserved k ->
      (∀ v, v ∈ dom M → ¬ is_reserved v) ->
      ∀ v, v ∈ dom (<[k := e]> M) → ¬ is_reserved v.
    Proof.
      intros Hk HM v Hv. apply elem_of_dom in Hv as [e' He'].
      destruct (decide (v = k)) as [-> | Hne].
      - exact Hk.
      - rewrite lookup_insert_ne in He'; [| congruence].
        apply HM. apply elem_of_dom. exists e'. exact He'.
    Qed.

    (* subst_map_avoids_reserved survives extending a map with one more
       binding, given the new key and the new value's own fvars are both
       reserved-free -- the "#ret_val" extension ProcCallRuleRet's own
       postcondition subst map needs on top of the ordinary args map. *)
    Lemma subst_map_avoids_reserved_insert (M : gmap lvar LExpr) (k : lvar) (e : LExpr) :
      ¬ is_reserved k ->
      (∀ v, v ∈ lexpr_fvars e → ¬ is_reserved v) ->
      subst_map_avoids_reserved M ->
      subst_map_avoids_reserved (<[k := e]> M).
    Proof.
      intros Hk He Hm. split.
      - exact (dom_insert_not_reserved M k e Hk (proj1 Hm)).
      - intros v Hv.
        apply lexpr_map_fvars_insert_subseteq in Hv.
        apply elem_of_union in Hv as [Hin | Hin]; [exact (He v Hin) | exact (proj2 Hm v Hin)].
    Qed.

    (* A list of bare LVal literals trivially avoids the reserved namespace
       (LVal has no free variables at all) -- the "values" side of
       subst_map_avoids_reserved for any value-instantiated substitution
       map (e.g. proc-call arg_vals, mirroring inv_body_bridge's
       inv_arg_map/Hnofv). *)
    Lemma lval_list_no_reserved {A} (l : list A) (f : A -> val) :
      Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) (map (fun w => LVal (f w)) l).
    Proof.
      induction l as [| w l' IH]; simpl; constructor; [| exact IH].
      intros v Hv. simpl in Hv. set_solver.
    Qed.

    (* Same, for a list of bare LVar-wrapped lvars, given they're
       themselves already known reserved-free (e.g. dll_args_not_reserved,
       for a proc's own entry lvars). *)
    Lemma lvar_list_no_reserved (l : list lvar) :
      Forall (fun lv => ¬ is_reserved lv) l ->
      Forall (fun le => ∀ v, v ∈ lexpr_fvars le → ¬ is_reserved v) (map LVar l).
    Proof.
      intro Hl. induction l as [| lv l' IH]; simpl; constructor.
      - intros v Hv. simpl in Hv. apply elem_of_singleton in Hv as ->. exact (Forall_inv Hl).
      - apply IH. exact (Forall_inv_tail Hl).
    Qed.

    (* Forall2's own interp_lexpr equations are stable under an mp-update at
       a var none of the lexprs mention. *)
    Lemma forall2_interp_stable (lexprs : list LExpr) (vs : list val) (mp : symb_map) (lv : lvar) (v' : val) :
      Forall (fun le => lv ∉ lexpr_fvars le) lexprs ->
      Forall2 (fun le v => interp_lexpr le mp = Some v) lexprs vs ->
      Forall2 (fun le v => interp_lexpr le (fun y => if (y =? lv)%string then v' else mp y) = Some v) lexprs vs.
    Proof.
      intros Hfa Hf2. induction Hf2 as [| le v0 lexprs' vs' Hhd Htl IH]; inversion Hfa as [| ? ? Hh Ht]; subst.
      - constructor.
      - constructor; [rewrite (interp_lexpr_stable le mp lv v' Hh); exact Hhd | exact (IH Ht)].
    Qed.

    (* subst inv_body subst_map's own translated truth doesn't change under
       an mp-update at a var lv not mentioned by subst_map's own values (see
       InvAccessBlockRule's lv-freshness premise). M1 = M2 = M throughout, so
       this is exactly trnsl_assertion_mp_irrelevant_reserved's use case --
       no Hbase over reserved names is needed. *)
    Lemma trnsl_assertion_subst_lv_stable (Hwf : ProgramWF) (a : assertion) (M : gmap lvar LExpr)
        (lv : lvar) (v' : val) stk_id mp :
      StackFree a ->
      assertion_exists_binders a ## (dom M ∪ lexpr_map_fvars M) ->
      assertion_true_fvars a ⊆ dom M ->
      subst_map_avoids_reserved M ->
      lv ∉ lexpr_map_fvars M ->
      trnsl_assertion (subst a M) stk_id (fun y => if (y =? lv)%string then v' else mp y)
      ≡ trnsl_assertion (subst a M) stk_id mp.
    Proof.
      intros Hsf Hbind Hfv Hmr Hlv.
      apply (trnsl_assertion_mp_irrelevant_reserved Hwf a M stk_id
               (fun y => if (y =? lv)%string then v' else mp y) mp Hsf Hbind Hmr).
      intros x Hx.
      exact (eval_lvar_base_stable M mp lv v' x Hlv (Hfv x Hx)).
    Qed.

  End MainTranslation.
