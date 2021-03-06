(** * Types: Type Systems *)

Require Export Smallstep.

Hint Constructors multi.  

(** Our next major topic is _type systems_ -- static program
    analyses that classify expressions according to the "shapes" of
    their results.  We'll begin with a typed version of a very simple
    language with just booleans and numbers, to introduce the basic
    ideas of types, typing rules, and the fundamental theorems about
    type systems: _type preservation_ and _progress_.  Then we'll move
    on to the _simply typed lambda-calculus_, which lives at the core
    of every modern functional programming language (including
    Coq). *)

(* ###################################################################### *)
(** * Typed Arithmetic Expressions *)

(** To motivate the discussion of type systems, let's begin as
    usual with an extremely simple toy language.  We want it to have
    the potential for programs "going wrong" because of runtime type
    errors, so we need something a tiny bit more complex than the
    language of constants and addition that we used in chapter
    [Smallstep]: a single kind of data (just numbers) is too simple,
    but just two kinds (numbers and booleans) already gives us enough
    material to tell an interesting story.

    The language definition is completely routine.  The only thing to
    notice is that we are _not_ using the [asnum]/[aslist] trick that
    we used in chapter [HoareList] to make all the operations total by
    forcibly coercing the arguments to [+] (for example) into numbers.
    Instead, we simply let terms get stuck if they try to use an
    operator with the wrong kind of operands: the [step] relation
    doesn't relate them to anything. *)

(* ###################################################################### *)
(** ** Syntax *)

(** Informally:
    t ::= true
        | false
        | if t then t else t
        | 0
        | succ t
        | pred t
        | iszero t
    Formally:
*)

Inductive tm : Type :=
  | ttrue : tm
  | tfalse : tm
  | tif : tm -> tm -> tm -> tm
  | tzero : tm
  | tsucc : tm -> tm
  | tpred : tm -> tm
  | tiszero : tm -> tm.

(** _Values_ are [true], [false], and numeric values... *)

Inductive bvalue : tm -> Prop :=
  | bv_true : bvalue ttrue
  | bv_false : bvalue tfalse.

Inductive nvalue : tm -> Prop :=
  | nv_zero : nvalue tzero
  | nv_succ : ∀ t, nvalue t -> nvalue (tsucc t).

Definition value (t:tm) := bvalue t \/ nvalue t.

Hint Constructors bvalue nvalue.
Hint Unfold value.  
(* ###################################################################### *)
(** ** Operational Semantics *)

(** Informally: *)
(**
                    ------------------------------                  (ST_IfTrue)
                    if true then t1 else t2 ==> t1

                   -------------------------------                 (ST_IfFalse)
                   if false then t1 else t2 ==> t2

                              t1 ==> t1'
                      -------------------------                         (ST_If)
                      if t1 then t2 else t3 ==>
                        if t1' then t2 else t3

                              t1 ==> t1'
                         --------------------                         (ST_Succ)
                         succ t1 ==> succ t1'

                             ------------                         (ST_PredZero)
                             pred 0 ==> 0

                           numeric value v1
                        ---------------------                     (ST_PredSucc)
                        pred (succ v1) ==> v1

                              t1 ==> t1'
                         --------------------                         (ST_Pred)
                         pred t1 ==> pred t1'

                          -----------------                     (ST_IszeroZero)
                          iszero 0 ==> true

                           numeric value v1
                      --------------------------                (ST_IszeroSucc)
                      iszero (succ v1) ==> false

                              t1 ==> t1'
                       ------------------------                     (ST_Iszero)
                       iszero t1 ==> iszero t1'
*)

(** Formally: *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : ∀ t1 t2,
      (tif ttrue t1 t2) ==> t1
  | ST_IfFalse : ∀ t1 t2,
      (tif tfalse t1 t2) ==> t2
  | ST_If : ∀ t1 t1' t2 t3,
      t1 ==> t1' ->
      (tif t1 t2 t3) ==> (tif t1' t2 t3)
  | ST_Succ : ∀ t1 t1',
      t1 ==> t1' ->
      (tsucc t1) ==> (tsucc t1')
  | ST_PredZero :
      (tpred tzero) ==> tzero
  | ST_PredSucc : ∀ t1,
      nvalue t1 ->
      (tpred (tsucc t1)) ==> t1
  | ST_Pred : ∀ t1 t1',
      t1 ==> t1' ->
      (tpred t1) ==> (tpred t1')
  | ST_IszeroZero :
      (tiszero tzero) ==> ttrue
  | ST_IszeroSucc : ∀ t1,
       nvalue t1 ->
      (tiszero (tsucc t1)) ==> tfalse
  | ST_Iszero : ∀ t1 t1',
      t1 ==> t1' ->
      (tiszero t1) ==> (tiszero t1')

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" 
  | Case_aux c "ST_Succ" | Case_aux c "ST_PredZero"
  | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred" 
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.
(** Notice that the [step] relation doesn't care about whether
    expressions make global sense -- it just checks that the operation
    in the _next_ reduction step is being applied to the right kinds
    of operands.  

    For example, the term [succ true] (i.e., [tsucc ttrue] in the
    formal syntax) cannot take a step, but the almost as obviously
    nonsensical term
       succ (if true then true else true) 
    can take a step (once, before becoming stuck). *)

(* ###################################################################### *)
(** ** Normal Forms and Values *)

(** The first interesting thing about the [step] relation in this
    language is that the strong progress theorem from the Smallstep
    chapter fails!  That is, there are terms that are normal
    forms (they can't take a step) but not values (because we have not
    included them in our definition of possible "results of
    evaluation").  Such terms are _stuck_. *)

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

(** **** Exercise: 2 stars (some_term_is_stuck) *)
Example some_term_is_stuck : exists t, stuck t.
  exists (tiszero ttrue); split; intro; solve by inversion 3.
Qed.
(** [] *)

(** However, although values and normal forms are not the same in this
    language, the former set is included in the latter.  This is
    important because it shows we did not accidentally define things
    so that some value could still take a step. *)

(** **** Exercise: 3 stars, advanced (value_is_nf) *)
(** Hint: You will reach a point in this proof where you need to
    use an induction to reason about a term that is known to be a
    numeric value.  This induction can be performed either over the
    term itself or over the evidence that it is a numeric value.  The
    proof goes through in either case, but you will find that one way
    is quite a bit shorter than the other.  For the sake of the
    exercise, try to complete the proof both ways. *)

Lemma value_is_nf : ∀ t, value t -> step_normal_form t.
  introv Hv Hnf; destruct Hnf; destruct Hv; intros;
  repeat match goal with
           | [ p : tsucc _ ==> _ |- _ ] => inverts p
           | [ IH : forall x, ?t ==> x -> False, _ : ?t ==> _ |- _ ] =>
             exfalso; eapply IH; eauto
           | [ p1 : nvalue ?t, p2 : ?t ==> ?t' |- _ ] =>
             generalize dependent t'; induction p1; intros; [solve by inversion | ]
           | _ => solve by inversion 2
         end.
Qed.

Hint Resolve value_is_nf.
(** [] *)


(** **** Exercise: 3 stars, optional (step_deterministic) *)
(** Using [value_is_nf], we can show that the [step] relation is
    also deterministic... *)

Lemma nf_s : ∀ t, step_normal_form t -> step_normal_form (tsucc t).
  unfold normal_form; destruct 2 as [k Hnfst]; inverts Hnfst; nexelim. Qed.

Hint Resolve nf_s.

Theorem step_deterministic : deterministic step.
  introv Hy1 Hy2.
  generalize dependent y2; induction Hy1; intros;
  inverts Hy2; crush; try solve by inversion;
  match goal with
    | [ p1 : nvalue ?t, p2 : tsucc ?t ==> _ |- _ ]
      => exfalso; assert (step_normal_form (tsucc t)) by crush;
         unfold normal_form in *; nexelim
    | [ IH : forall t2, ?t ==> t2 -> ?t1 = t2, p : ?t ==> ?t2 |- _]
      => apply IH in p; crush
  end.
Qed.
(** [] *)



(* ###################################################################### *)
(** ** Typing *)

(** The next critical observation about this language is that,
    although there are stuck terms, they are all "nonsensical", mixing
    booleans and numbers in a way that we don't even _want_ to have a
    meaning.  We can easily exclude such ill-typed terms by defining a
    _typing relation_ that relates terms to the types (either numeric
    or boolean) of their final results.  *)

Inductive ty : Type := 
  | TBool : ty
  | TNat : ty.

(** In informal notation, the typing relation is often written
    [|- t ∈ T], pronounced "[t] has type [T]."  The [|-] symbol is
    called a "turnstile".  (Below, we're going to see richer typing
    relations where an additional "context" argument is written to the
    left of the turnstile.  Here, the context is always empty.) *)
(** 
                           ----------------                            (T_True)
                           |- true ∈ Bool

                          -----------------                           (T_False)
                          |- false ∈ Bool

             |- t1 ∈ Bool    |- t2 ∈ T    |- t3 ∈ T
             --------------------------------------------                (T_If)
                    |- if t1 then t2 else t3 ∈ T

                             ------------                              (T_Zero)
                             |- 0 ∈ Nat
                              
                            |- t1 ∈ Nat
                          ------------------                           (T_Succ)
                          |- succ t1 ∈ Nat

                            |- t1 ∈ Nat
                          ------------------                           (T_Pred)
                          |- pred t1 ∈ Nat

                            |- t1 ∈ Nat
                        ---------------------                        (T_IsZero)
                        |- iszero t1 ∈ Bool
*)

Reserved Notation "'|-' t '∈' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue ∈ TBool
  | T_False : 
       |- tfalse ∈ TBool
  | T_If : ∀ t1 t2 t3 T,
       |- t1 ∈ TBool ->
       |- t2 ∈ T ->
       |- t3 ∈ T ->
       |- tif t1 t2 t3 ∈ T
  | T_Zero : 
       |- tzero ∈ TNat
  | T_Succ : ∀ t1,
       |- t1 ∈ TNat ->
       |- tsucc t1 ∈ TNat
  | T_Pred : ∀ t1,
       |- t1 ∈ TNat ->
       |- tpred t1 ∈ TNat
  | T_Iszero : ∀ t1,
       |- t1 ∈ TNat ->
       |- tiszero t1 ∈ TBool

where "'|-' t '∈' T" := (has_type t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Pred"
  | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

(* ###################################################################### *)
(** *** Examples *)

(** It's important to realize that the typing relation is a
    _conservative_ (or _static_) approximation: it does not calculate
    the type of the normal form of a term. *)

Example has_type_1 : 
  |- tif tfalse tzero (tsucc tzero) ∈ TNat.
Proof. auto. Qed.


(** (Since we've included all the constructors of the typing relation
    in the hint database, the [auto] tactic can actually find this
    proof automatically.) *)

Example has_type_not : 
  ~ (|- tif tfalse tzero ttrue ∈ TBool).
Proof. intro; solve by inversion 2. Qed.

(** **** Exercise: 1 star, optional (succ_hastype_nat__hastype_nat) *)
Example succ_hastype_nat__hastype_nat : ∀ t,
  |- tsucc t ∈ TNat ->
  |- t ∈ TNat.  
Proof. inversion 1; crush. Qed.
(** [] *)

(* ###################################################################### *)
(** ** Canonical forms *)

(** The following two lemmas capture the basic property that defines
    the shape of well-typed values.  They say that the definition of value
    and the typing relation agree. *)

Lemma bool_canonical : ∀ t,
  |- t ∈ TBool -> value t -> bvalue t.
Proof. repeat inversion 1; crush; solve by inversion. Qed.

Lemma nat_canonical : ∀ t,
  |- t ∈ TNat -> value t -> nvalue t.
Proof. repeat inversion 1; crush; solve by inversion. Qed.

Hint Resolve bool_canonical nat_canonical.
(* ###################################################################### *)
(** ** Progress *)

(** The typing relation enjoys two critical properties.  The first is
    that well-typed normal forms are values (i.e., not stuck). *)


Theorem progress : ∀ t T,
  |- t ∈ T ->
  value t \/ exists t', t ==> t'.

(** **** Exercise: 3 stars (finish_progress) *)
(** Complete the formal proof of the [progress] property.  (Make sure
    you understand the informal proof fragment in the following
    exercise before starting -- this will save you a lot of time.) *)
  induction 1; destr_sums; destr_prods; eauto;
  match goal with
    | [ p : value ?t, _ : |- ?t ∈ TBool |- _ ] =>
      apply bool_canonical in p; eauto
    | [ p : value ?t, _ : |- ?t ∈ TNat |- _ ] =>
      apply nat_canonical in p; eauto
  end;
  match goal with
    | [ p : bvalue _ |- _ ] => inverts p
    | [ p : nvalue _ |- _ ] => inverts p
  end; right; eauto.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_progress_informal) *)
(** Complete the corresponding informal proof: *)

(** _Theorem_: If [|- t ∈ T], then either [t] is a value or else 
    [t ==> t'] for some [t']. *)

(** _Proof_: By induction on a derivation of [|- t ∈ T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 ∈ Bool], [|- t2 ∈ T] and [|- t3
        ∈ T].  By the IH, either [t1] is a value or else [t1] can step
        to some [t1'].  

            - If [t1] is a value, then by the canonical forms lemmas
              and the fact that [|- t1 ∈ Bool] we have that [t1] 
              is a [bvalue] -- i.e., it is either [true] or [false].
              If [t1 = true], then [t] steps to [t2] by [ST_IfTrue],
              while if [t1 = false], then [t] steps to [t3] by
              [ST_IfFalse].  Either way, [t] can step, which is what
              we wanted to show.

            - If [t1] itself can take a step, then, by [ST_If], so can
              [t].
       (* Fill in here *)
     
[]
*)

(** This is more interesting than the strong progress theorem that we
    saw in the Smallstep chapter, where _all_ normal forms were
    values.  Here, a term can be stuck, but only if it is ill
    typed. *)

(** **** Exercise: 1 star (step_review) *)
(** Quick review.  Answer _true_ or _false_.  In this language...
      - Every well-typed normal form is a value.
        - true
      - Every value is a normal form.
        - false
      - The single-step evaluation relation is
        a partial function (i.e., it is deterministic).

      - The single-step evaluation relation is a _total_ function.
*)
(** [] *)

(* ###################################################################### *)
(** ** Type Preservation *)

(** The second critical property of typing is that, when a well-typed
    term takes a step, the result is also a well-typed term.

    This theorem is often called the _subject reduction_ property,
    because it tells us what happens when the "subject" of the typing
    relation is reduced.  This terminology comes from thinking of
    typing statements as sentences, where the term is the subject and
    the type is the predicate. *)

Theorem preservation : ∀ t t' T,
  |- t ∈ T ->
  t ==> t' ->
  |- t' ∈ T.

(** **** Exercise: 2 stars (finish_preservation) *)
(** Complete the formal proof of the [preservation] property.  (Again,
    make sure you understand the informal proof fragment in the
    following exercise first.) *)

Proof. introv Ht Hst;
       generalize dependent t'; induction Ht; intros; inverts Hst;
       match goal with
         | [ p : |- tsucc _ ∈ TNat |- _ ] => inverts p
         | _ => idtac
       end; crush.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (finish_preservation_informal) *)
(** Complete the following proof: *)

(** _Theorem_: If [|- t ∈ T] and [t ==> t'], then [|- t' ∈ T]. *)

(** _Proof_: By induction on a derivation of [|- t ∈ T].

      - If the last rule in the derivation is [T_If], then [t = if t1
        then t2 else t3], with [|- t1 ∈ Bool], [|- t2 ∈ T] and [|- t3
        ∈ T].  

        Inspecting the rules for the small-step reduction relation and
        remembering that [t] has the form [if ...], we see that the
        only ones that could have been used to prove [t ==> t'] are
        [ST_IfTrue], [ST_IfFalse], or [ST_If].

           - If the last rule was [ST_IfTrue], then [t' = t2].  But we
             know that [|- t2 ∈ T], so we are done.

           - If the last rule was [ST_IfFalse], then [t' = t3].  But we
             know that [|- t3 ∈ T], so we are done.

           - If the last rule was [ST_If], then [t' = if t1' then t2
             else t3], where [t1 ==> t1'].  We know [|- t1 ∈ Bool] so,
             by the IH, [|- t1' ∈ Bool].  The [T_If] rule then gives us
             [|- if t1' then t2 else t3 ∈ T], as required.

    (* FILL IN HERE *)
[]
*)

(** **** Exercise: 3 stars (preservation_alternate_proof) *)
(** Now prove the same property again by induction on the
    _evaluation_ derivation instead of on the typing derivation.
    Begin by carefully reading and thinking about the first few
    lines of the above proof to make sure you understand what
    each one is doing.  The set-up for this proof is similar, but
    not exactly the same. *)

Theorem nvalue_tnat : forall t, nvalue t -> |- t ∈ TNat.
  induction 1; crush. Qed.

Hint Resolve nvalue_tnat.

Theorem preservation' : ∀ t t' T,
  |- t ∈ T ->
  t ==> t' ->
  |- t' ∈ T.
  introv Ht Hst; generalize dependent T; induction Hst; inversion 1; crush. Qed.

Hint Resolve preservation.
(** [] *)

(* ###################################################################### *)
(** ** Type Soundness *)

(** Putting progress and preservation together, we can see that a
    well-typed term can _never_ reach a stuck state.  *)

Definition multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Ltac prog :=
  repeat match goal with
           | [ p : |- ?t ∈ ?T |- _] =>
             extend (progress t T p)
         end.

Ltac preservation :=
  repeat match goal with
           | [ p1 : |- ?t1 ∈ ?T, p2 : ?t1 ==> ?t2 |- _ ] =>
             extend (preservation t1 t2 T p1 p2)
         end.

Corollary soundness : ∀ t t' T,
  |- t ∈ T -> 
  t ==>* t' ->
  ~(stuck t').
  unfold stuck; induction 2; intros; [prog | preservation]; crush. Qed.

(* ###################################################################### *)
(** * Aside: the [normalize] Tactic *)

(** When experimenting with definitions of programming languages in
    Coq, we often want to see what a particular concrete term steps
    to -- i.e., we want to find proofs for goals of the form [t ==>*
    t'], where [t] is a completely concrete term and [t'] is unknown.
    These proofs are simple but repetitive to do by hand. Consider for
    example reducing an arithmetic expression using the small-step
    relation [astep]. *)


Definition amultistep st := multi (astep st). 
Notation " t '/' st '==>a*' t' " := (amultistep st t t')
  (at level 40, st at level 39).

Example astep_example1 : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* (ANum 15).
Proof.
  apply multi_step with (APlus (ANum 3) (ANum 12)).
    apply AS_Plus2. 
      apply av_num. 
      apply AS_Mult.
  apply multi_step with (ANum 15).
    apply AS_Plus.
  apply multi_refl.
Qed.

(** We repeatedly apply [multi_step] until we get to a normal
    form. The proofs that the intermediate steps are possible are
    simple enough that [auto], with appropriate hints, can solve
    them. *)

Hint Constructors astep aval.
Example astep_example1' : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* (ANum 15).
Proof.
  eapply multi_step. auto. simpl.
  eapply multi_step. auto. simpl.
  apply multi_refl.
Qed.


(** The following custom [Tactic Notation] definition captures this
    pattern.  In addition, before each [multi_step] we print out the
    current goal, so that the user can follow how the term is being
    evaluated. *)

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" := 
   repeat (print_goal; eapply multi_step ; 
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

Example astep_example1'' : 
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* (ANum 15).
Proof.
  normalize.
  (* At this point in the proof script, the Coq response shows 
     a trace of how the expression evaluated. 

   (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ANum 15)
   (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) (ANum 15))
   (multi (astep empty_state) (ANum 15) (ANum 15))
*)
Qed.


(** The [normalize] tactic also provides a simple way to calculate
    what the normal form of a term is, by proving a goal with an
    existential variable in it. *)

Example astep_example1''' : exists e',
  (APlus (ANum 3) (AMult (ANum 3) (ANum 4))) / empty_state 
  ==>a* e'.
Proof.
  eapply ex_intro. normalize.

(* This time, the trace will be:

    (APlus (ANum 3) (AMult (ANum 3) (ANum 4)) / empty_state ==>a* ??)
    (multi (astep empty_state) (APlus (ANum 3) (ANum 12)) ??)
    (multi (astep empty_state) (ANum 15) ??)

   where ?? is the variable ``guessed'' by eapply.
*)
Qed.


(** **** Exercise: 1 star (normalize_ex) *)
Theorem normalize_ex : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof with normalize. eexists... Qed.

(** [] *)

(** **** Exercise: 1 star, optional (normalize_ex') *)
(** For comparison, prove it using [apply] instead of [eapply]. *)

Theorem normalize_ex' : exists e',
  (AMult (ANum 3) (AMult (ANum 2) (ANum 1))) / empty_state 
  ==>a* e'.
Proof with normalize. econstructor... Qed.

(** [] *)


(* ###################################################################### *)
(** ** Additional Exercises *)

(** **** Exercise: 2 stars (subject_expansion) *)
(** Having seen the subject reduction property, it is reasonable to
    wonder whether the opposity property -- subject _expansion_ --
    also holds.  That is, is it always the case that, if [t ==> t']
    and [|- t' ∈ T], then [|- t ∈ T]?  If so, prove it.  If
    not, give a counter-example.  (You do not need to prove your
    counter-example in Coq, but feel free to do so if you like.)

    tif ttrue ttrue tzero isn't well typed, but evaluates to a well typed expression
[]
*)

(** **** Exercise: 2 stars (variation1) *)
(** Suppose, that we add this new rule to the typing relation: 
      | T_SuccBool : ∀ t,
           |- t ∈ TBool ->
           |- tsucc t ∈ TBool
   Which of the following properties remain true in the presence of
   this rule?  For each one, write either "remains true" or
   else "becomes false." If a property becomes false, give a
   counterexample.
      - Determinism of [step]
        - stays
      - Progress
        - nope
      - Preservation
        - stays
[]
*)

(** **** Exercise: 2 stars (variation2) *)
(** Suppose, instead, that we add this new rule to the [step] relation: 
      | ST_Funny1 : ∀ t2 t3,
           (tif ttrue t2 t3) ==> t3
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.
        determinism
          tif ttrue ttrue tfalse ==> ttrue /\ tif ttrue ttrue tfalse ==> tfalse
[]
*)

(** **** Exercise: 2 stars, optional (variation3) *)
(** Suppose instead that we add this rule:
      | ST_Funny2 : ∀ t1 t2 t2' t3,
           t2 ==> t2' ->
           (tif t1 t2 t3) ==> (tif t1 t2' t3)
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

(** **** Exercise: 2 stars, optional (variation4) *)
(** Suppose instead that we add this rule:
      | ST_Funny3 : 
          (tpred tfalse) ==> (tpred (tpred tfalse))
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

(** **** Exercise: 2 stars, optional (variation5) *)
(** Suppose instead that we add this rule:
   
      | T_Funny4 : 
            |- tzero ∈ TBool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

(** **** Exercise: 2 stars, optional (variation6) *)
(** Suppose instead that we add this rule:
   
      | T_Funny5 : 
            |- tpred tzero ∈ TBool
   ]]
   Which of the above properties become false in the presence of
   this rule?  For each one that does, give a counter-example.

[]
*)

(** **** Exercise: 3 stars, optional (more_variations) *)
(** Make up some exercises of your own along the same lines as
    the ones above.  Try to find ways of selectively breaking
    properties -- i.e., ways of changing the definitions that
    break just one of the properties and leave the others alone.
    [] 
*)

(** **** Exercise: 1 star (remove_predzero) *)
(** The evaluation rule [E_PredZero] is a bit counter-intuitive: we
    might feel that it makes more sense for the predecessor of zero to
    be undefined, rather than being defined to be zero.  Can we
    achieve this simply by removing the rule from the definition of
    [step]?  Would doing so create any problems elsewhere? 

    Nope, we also need to remove the T_Pred rule from has_type
    Once we do that though all properties are preserved

[] *)

Module nopredzero.

Reserved Notation "t1 ==> t2" (at level 40).
Inductive step : tm -> tm -> Prop :=
  | ST_IfTrue : Π t1 t2, tif ttrue t1 t2 ==> t1
  | ST_IfFalse : Π t1 t2, tif tfalse t1 t2 ==> t2
  | ST_If : Π t1 t1' t2 t3, t1 ==> t1' -> tif t1 t2 t3 ==> tif t1' t2 t3
  | ST_Succ : Π t1 t1', t1 ==> t1' -> tsucc t1 ==> tsucc t1'
  | ST_PredSucc : Π t, nvalue t -> tpred (tsucc t) ==> t
  | ST_Pred : Π t t', t ==> t' -> tpred t ==> tpred t'
  | ST_IszeroZero : tiszero tzero ==> ttrue
  | ST_IszeroSucc : Π t, nvalue t -> tiszero (tsucc t) ==> tfalse
  | ST_Iszero : Π t t', t ==> t' -> tiszero t ==> tiszero t'
where "t1 ==> t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" 
  | Case_aux c "ST_Succ"   | Case_aux c "ST_PredSucc" | Case_aux c "ST_Pred" 
  | Case_aux c "ST_IszeroZero" | Case_aux c "ST_IszeroSucc"
  | Case_aux c "ST_Iszero" ].

Hint Constructors step.

Reserved Notation "'|-' t '∈' T" (at level 40).

Inductive has_type : tm -> ty -> Prop :=
  | T_True : 
       |- ttrue ∈ TBool
  | T_False : 
       |- tfalse ∈ TBool
  | T_If : ∀ t1 t2 t3 T,
       |- t1 ∈ TBool ->
       |- t2 ∈ T ->
       |- t3 ∈ T ->
       |- tif t1 t2 t3 ∈ T
  | T_Zero : 
       |- tzero ∈ TNat
  | T_Succ : ∀ t1,
       |- t1 ∈ TNat ->
       |- tsucc t1 ∈ TNat
  | T_Iszero : ∀ t1,
       |- t1 ∈ TNat ->
       |- tiszero t1 ∈ TBool

where "'|-' t '∈' T" := (has_type t T).

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If"
  | Case_aux c "T_Zero" | Case_aux c "T_Succ" | Case_aux c "T_Iszero" ].

Hint Constructors has_type.

Lemma nv_sp : forall t, nvalue t <-> nvalue (tsucc t).
  split; inversion 1; crush. Qed.

Lemma bool_canonical : forall t, |- t ∈ TBool -> value t -> bvalue t.
  repeat inversion 1; crush; solve by inversion. Qed.

Lemma nat_canonical : forall t, |- t ∈ TNat -> value t -> nvalue t.
  repeat inversion 1; crush; solve by inversion. Qed.

Hint Resolve nv_sp nat_canonical bool_canonical.

Ltac bn_canonize :=
  repeat match goal with
             [ p1 : |- ?t ∈ ?T, p2 : value ?t |- _ ] =>
             match T with
               | TBool => extend (bool_canonical t p1 p2)
               | TNat => extend (nat_canonical t p1 p2)
             end
         end.

Ltac destr_bvals :=
  repeat match goal with
           | [ p : bvalue _ |- _ ] => inverts p
         end.

Lemma tif_ex : forall t1 t2 t3,
                 |- t1 ∈ TBool ->
                    (value t1 \/ exists t', t1 ==> t') ->
                    exists t', tif t1 t2 t3 ==> t'.
  destruct 2.
  - bn_canonize; destr_bvals; eauto.
  - destr_prods; eauto.
Qed.

Hint Resolve tif_ex.

Theorem progress : Π t T,
                   |- t ∈ T →
                   value t \/ ∃ t', t ==> t'.
  has_type_cases (induction 1) Case; eauto;
  destr_sums; destr_prods; bn_canonize; eauto.
  - Case "T_Iszero". right; inverts H1; eauto.
Qed.

Lemma nvalue_is_nf : forall t, nvalue t -> normal_form step t.
  unfold normal_form; induction 1; destruct 1; try solve by inversion.
  + inverts H0; nexelim.
Qed.

Theorem value_is_nf : forall t, value t → normal_form step t.
  destruct 1; [destr_bvals; intro; solve by inversion 2 | apply nvalue_is_nf; eauto].
Qed.

Theorem nf_is_value : forall t T, |- t ∈ T → normal_form step t → value t.
  unfold normal_form; introv Ht; destruct (progress t T Ht); crush. Qed.

Hint Resolve value_is_nf nf_is_value.
Hint Immediate value_is_nf nf_is_value.

Theorem value_nf : forall t T, |- t ∈ T -> (value t <-> normal_form step t).
  split; generalize dependent T; generalize dependent t; eauto. Qed.

Hint Rewrite value_nf.

Theorem tsucc_nf : forall t, nvalue t -> forall t', tsucc t ==> t' -> False.
  induction 1; crush; try solve by inversion 2.
  - match goal with [p : tsucc _ ==> _ |- _] => inverts p end; eauto.
Qed.

Hint Resolve tsucc_nf.

Theorem step_deterministic : Π t1 t2 t3,
                             t1 ==> t2 →
                             t1 ==> t3 →
                             t2 = t3.
  introv Hst2 Hst3; generalize dependent t3; induction Hst2; intros;
  inverts Hst3; eauto; try (exfalso; eauto; solve by inversion);
  match goal with
    | [ IH : forall t2, ?t ==> t2 -> ?t1 = t2,
          p : ?t ==> ?t2 |- _ ] => apply IH in p; crush
    | _ => idtac
  end.
Qed.

End nopredzero.
(** **** Exercise: 4 stars, advanced (prog_pres_bigstep) *)
(** Suppose our evaluation relation is defined in the big-step style.
    What are the appropriate analogs of the progress and preservation
    properties?

(* FILL IN HERE *)
[]
*)

(* $Date: 2014-04-08 23:31:16 -0400 (Tue, 08 Apr 2014) $ *)
