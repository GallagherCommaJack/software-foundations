(** * More Logic *)

Require Export MyProp.

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)

(** *** *)
(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** *** *)
(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note that we have to explicitly give the witness. *)

(** *** *)
(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** *** *)
(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 


(** Here is another example of how to work with existentials. *)
Lemma exists_example_3 : 
  exists (n:nat), even n /\ beautiful n.
Proof.
(* WORKED IN CLASS *)
  exists 8.
  split.
  unfold even. simpl. reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3. apply b_5.
Qed.

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* There is at least one n whose successor is a beautiful number
   More meaningfully, there is at least one beautiful number above 0 *)

(*
*)
(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. intros. intro. SearchAbout exist. inversion H0. apply H1. apply H. Qed.

(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof. intros. apply classic_ex_middle in H. unfold classic in H.
       firstorder. apply H. unfold not in *. apply H0.
Qed.       
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof. split; intros.
  Case "->". inversion H. inversion H0; [apply or_introl | apply or_intror]; 
                          exists witness; exact H1.
  Case "<-". destruct H; inversion H; exists witness.
             apply or_introl. exact H0.
             apply or_intror. exact H0.
Qed.   
(** [] *)

(* ###################################################### *)
(** * Evidence-carrying booleans. *)

(** So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 
*)

(** *** *)
(** 
It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.
Arguments left {A} {B} a.
Arguments right {A} {B} b.
(** Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 

(** *** *)

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  (* WORKED IN CLASS *)
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 
  
(** Read as a theorem, this says that equality on [nat]s is decidable:
that is, given two [nat] values, we can always produce either 
evidence that they are equal or evidence that they are not.
Read computationally, [eq_nat_dec] takes two [nat] values and returns
a [sumbool] constructed with [left] if they are equal and [right] 
if they are not; this result can be tested with a [match] or, better,
with an [if-then-else], just like a regular [boolean]. 
(Notice that we ended this proof with [Defined] rather than [Qed]. 
The only difference this makes is that the proof becomes _transparent_,
meaning that its definition is available when Coq tries to do reductions,
which is important for the computational interpretation.)
*) 

(** *** *)
(** 
Here's a simple example illustrating the advantages of the [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)

(** **** Exercise: 1 star (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof. intros. unfold override'. destruct (eq_nat_dec k1 k2); reflexivity. Qed.
  
(** [] *)

(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
| allnil : all X P []
| allcons : forall x xs, P x -> all X P xs -> all X P (x :: xs).

Arguments all {X} P xs.
Arguments allnil {X} {P}.
Arguments allcons {X} {P} {x} {xs} px pxs.

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)


Theorem forallb_all : forall X (pred : X -> Prop) 
                        (test : forall x, {pred x} + {~ (pred x)})
                        (l : list X),
         {all pred l} + {~ (all pred l)}.
Proof. intros. induction l as [|y ys]. 
       Case "l = []". left. apply allnil.
       Case "l = y :: ys". destruct IHys.
         SCase "IHxs : all test ys". destruct (test y) eqn:ty.
           SSCase "test y = true". left. apply allcons. exact p. exact a.
           SSCase "test y = false". 
             right. intro. inversion H. destruct n. exact H2.
         SCase "IHxs : ~ all test ys". right. intro. inversion H.
           apply n. apply H3.
Defined.

Arguments forallb_all {X} {pred} test l.
Eval compute in forallb_all (eq_nat_dec 10) [10; 10; 10; 10].
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

Theorem filter_spec : forall (t : nat -> bool) (l : list nat),
        all (fun x => t x = true) (filter t l) /\ subseq (filter t l) l.
Proof. split; intros. 
       Case "p1". induction l as [|y ys]; simpl.
         SCase "l = []". apply allnil.
         SCase "l = y :: ys". destruct (t y) eqn:ty.
           SSCase "t y = true". apply allcons. exact ty. apply IHys.
           SSCase "t y = false". apply IHys.
       Case "p2". induction l as [|y ys]; simpl.
         SCase "l = []". apply sub_refl.
         SCase "l = y :: ys". destruct (t y) eqn:ty.
           SSCase "t y = true". apply sub_cons2. apply IHys.
           SSCase "t y = false". apply sub_cons1. apply IHys.
Qed.
(* I'd generalize it, but subseq is specific to nats right now *)
(* on pain of really weird inversions *)
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 4 stars, advanced (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)

Lemma app_nil_r : forall X (xs : list X), xs ++ [] = xs.
Proof. induction xs. reflexivity. simpl. rewrite IHxs. reflexivity. Qed.

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof. induction xs as [|x' xs']; intros; simpl in *. 
       Case "xs = []". right. apply H.
       Case "xs = x' :: xs'". inversion H; subst.
         SCase "H : ai_here x (x :: xs ++ ys)". left. apply ai_here.
         SCase "H : ai_later x' (xs ++ ys)". apply IHxs' in H1. destruct H1.
           SSCase "H0 : right (appears_in x xs)". left. apply ai_later. apply H0.
           SSCase "H0 : appears_in x ys". right. apply H0.
Qed. 

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof. induction xs as [|x' xs']; intros.
       Case "xs = []". destruct H.
         SCase "H : appears_in x []". inversion H.
         SCase "H : appears_in x ys". apply H.
       Case "xs = x' :: xs'". destruct H; simpl.
         SCase "H : appears_in x (x' :: xs')". inversion H; subst.
           SSCase "H : appears_in x' (x' :: xs')". apply ai_here.
           SSCase "H : ai_later x' (appears_in x xs')".
             simpl. apply ai_later. apply IHxs'. left. apply H1.
         SCase "H : appears_in x ys". 
           apply ai_later. apply IHxs'. right. apply H.
Qed.
(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Definition disjoint : forall X, list X -> list X -> Prop := fun X xs ys =>
  all (fun x => ~ (appears_in x ys)) xs \/ all (fun y => ~ (appears_in y xs)) ys.

Arguments disjoint {X} xs ys.

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

Inductive no_repeats (X : Type) : list X -> Prop :=
| norepnil : no_repeats X []
| norepcons : forall (x : X) (xs : list X),
              no_repeats X xs -> ~ (appears_in x xs) -> 
              no_repeats X (x :: xs).

Arguments no_repeats {X} xs.
Arguments norepcons {X} {x} {xs} p1 p2.
Arguments norepnil {X}.

Definition Decideable1 {X : Type} (P : X -> Prop) : Type :=
  forall x,  {P x} + {~ (P x)}.

Definition Decideable2 {X Y : Type} (P : X -> Y -> Prop) : Type :=
  forall x y,  {P x y} + {~ (P x y)}.

Theorem appears_in_proc : forall X (f : forall (x y : X), {x = y} + {x <> y})
                            (x : X) (l : list X),
                            {appears_in x l} + {~ appears_in x l}.
Proof. intros. induction l as [|y ys].
       Case "l = []". right. intro. inversion H.
       Case "l = x' :: xs". destruct IHys as [IHys|IHys].
         SCase "IHys : appears_in x ys". left. apply ai_later. apply IHys.
         SCase "IHys : ~ appears_in x ys". destruct (f x y).
           SSCase "x = y". left. rewrite e. apply ai_here.
           SSCase "x <> y". right. intro. inversion H; contradiction.
Defined.

Arguments appears_in_proc {X} f x l.

Theorem dup_no_repeats : forall X (x : X) (l : list X), ~ (no_repeats (x :: x :: l)).
Proof. intros. intro. inversion H. apply H3. apply ai_here. Qed.

Theorem no_repeats_proc : forall X (f : forall (x y : X), {x = y} + {x <> y}),
                            Decideable1 (@no_repeats X).
Proof. unfold Decideable1. intros X f l. induction l as [|x xs].
       Case "l = []". left. apply norepnil.
       Case "l = x :: xs". destruct xs as [|y ys].
         SCase "xs = []". 
           left. apply norepcons. apply norepnil. intro. inversion H; subst.
         SCase "xs = y :: ys". destruct IHxs as [IHxs | IHxs].
           SSCase "IHxs : no_repeats (y :: ys)". destruct (f x y).
             SSSCase "x = y". right. rewrite e. apply dup_no_repeats.
             SSSCase "x <> y". destruct (appears_in_proc f x ys).
               SSSSCase "appears_in x ys". right. intro. inversion H; subst.
                 apply H3. apply ai_later. apply a.
               SSSSCase "~ appears_in x ys". left.
                 apply norepcons. apply IHxs. intro. inversion H. contradiction n.
                 apply n0. apply H1.
           SSCase "IHxs : ~ no_repeats (y :: ys)". right. intro. destruct (f x y).
             SSSCase "x = y". inversion H; subst. apply H3. apply ai_here.
             SSSCase "x <> y". inversion H; subst. destruct (appears_in_proc f x ys).
               apply H3. apply ai_later. apply a.
               apply IHxs. apply H2.
Defined. 

Arguments no_repeats_proc {X} f x.

(** [] *)


(** **** Exercise: 3 stars (nostutter) *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
| nostutnil : nostutter []
| nostutcons : forall n xs, Some n <> hd_opt xs -> nostutter xs -> nostutter (n :: xs).

Arguments nostutcons {n} {xs} p1 p2.
(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
Proof. repeat constructor; simplify_eq. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
Proof. repeat constructor; simplify_eq. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof. repeat constructor; simplify_eq. Qed.
(* 
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof. intro.
       repeat match goal with 
         h: nostutter _ |- _ => inversion h; clear h; subst 
       end.
       contradiction H1; auto. 
Qed.

(* 
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
*)
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. induction l1; simpl in *; intros.
       reflexivity. rewrite IHl1. reflexivity.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof. intros X x l; generalize dependent x; induction l as [|y ys]; 
       intros; inversion H; subst.
       exists []. exists ys. reflexivity.
       apply IHys in H1. inversion H1. inversion H0.
       exists (y :: witness). exists witness0. simpl. rewrite H2. reflexivity.
Qed.

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| rephere : forall x xs, appears_in x xs -> repeats (x :: xs)
| replater : forall x xs, repeats xs -> repeats (x :: xs).

(** Now here's a way to formalize the pigeonhole principle. List [l2]
    represents a list of pigeonhole labels, and list [l1] represents
    the labels assigned to a list of items: if there are more items
    than labels, at least two items must have the same label.  This
    proof is much easier if you use the [excluded_middle] hypothesis
    to show that [appears_in] is decidable, i.e. [forall x
    l, (appears_in x l) \/ ~ (appears_in x l)].  However, it is also
    possible to make the proof go through _without_ assuming that
    [appears_in] is decidable; if you can manage to do this, you will
    not need the [excluded_middle] hypothesis. *)

Lemma len0_nil {X : Type} : forall (l : list X), length l = 0 <-> l = [].
Proof. split; intros; destruct l; inversion H; firstorder. Qed.

Definition dec_eq (X : Type) : Type := forall x y : X, {x = y} + {x <> y}.

Lemma apr_uncons : forall X (a b : X) l, appears_in a (b :: l) ->
                                    a <> b -> appears_in a l.
Proof. intros. induction l; inversion H; subst.
       contradiction H0. contradiction H0. reflexivity. inversion H2.
       apply ai_later. apply IHl. apply ai_here. apply H2.
Qed.
Lemma appear_remove_redundant : forall X (a b : X) l1 l2,
                                  dec_eq X -> 
                                  a <> b ->
                                  appears_in a (l1 ++ b :: l2) ->
                                  appears_in a (l1 ++ l2).
Proof. induction l1; intros; simpl in *.
       apply apr_uncons in H0. apply H0. apply H.
       destruct (X0 a x); subst. apply ai_here.
       apply ai_later. apply IHl1. apply X0. apply H.
       apply apr_uncons with (b := x). apply H0. apply n.
Qed.

Theorem Pigeonhole_Principle: forall (X : Type) (l1 l2 : list X)
                              (f : dec_eq X),
        (forall x, appears_in x l1 -> appears_in x l2) -> 
        length l2 < length l1 -> 
        repeats l1.  
Proof. unfold excluded_middle, lt, dec_eq. 
       induction l1 as [|y ys].
       Case "l1 = []". intros l2 f H Hlen. inversion Hlen.
       Case "l1 = y :: ys". intros l2 f H Hlen.
         assert (Decideable2 (@appears_in X)). unfold Decideable2.
           apply appears_in_proc. apply f.
         unfold Decideable2 in *.
         destruct (X0 y ys).
           apply rephere. apply a.
           apply replater. assert (Hl2: exists pre, exists post, l2 = pre ++ y :: post).
             apply appears_in_app_split. apply H. apply ai_here.
             inversion Hl2. inversion H0.
             apply (IHys (witness ++ witness0)).
               apply f. intros. destruct (f x y).
               apply ex_falso_quodlibet. apply n. subst. apply H2.
               subst. firstorder. clear H1. 
               apply appear_remove_redundant with (b := y).
                 unfold dec_eq. apply f. 
                 apply n0. apply H. apply ai_later. apply H2. 
                 rewrite <- app_length_cons with (x := y); subst.
                 inversion Hlen; firstorder; subst.
Qed.
(** [] *)

(* $Date: 2014-02-22 09:43:41 -0500 (Sat, 22 Feb 2014) $ *)
