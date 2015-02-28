Require Import List.
Export ListNotations.
Require Import SfLib.
Require Import CpdtTactics.
Require Import LibTactics.

Set Implicit Arguments.

Inductive pal {X} : list X -> Prop :=
| palnil : pal []
| palsing : forall x, pal [x]
| palcons : forall x l, pal l -> pal (x :: l ++ [x]).

Hint Constructors pal.

(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

Inductive init_and_last {X : Type} : list X -> list X -> X -> Prop :=
| ising : forall x, init_and_last [x] [] x
| icons : forall x y ixs xs, init_and_last xs ixs x ->
                             init_and_last (y :: xs) (y :: ixs) x.

Hint Constructors init_and_last.

Theorem idec {X} (l : list X) : {l = []} + {exists xs x, init_and_last l xs x}.
  induction l; [left; reflexivity|right].
  - destruct IHl; [subst|destr_prods]; eauto.
Qed.

Lemma init_and_list : forall X xs ys (y : X),
                        init_and_last xs ys y ->
                        xs = ys ++ [y].
  induction 1; crush. Qed.

Definition lengthOrder {X : Type} (ls1 ls2 : list X) := length ls1 < length ls2.

Hint Unfold lengthOrder.
Hint Unfold well_founded.
Hint Constructors Acc.

Lemma lengthOrder_wf' : forall X len (ls : list X), 
                          length ls <= len -> Acc lengthOrder ls.
  unfold lengthOrder; induction len; crush. Qed.

Local Hint Resolve lengthOrder_wf'.

Theorem lengthOrder_wf : forall X, well_founded (@lengthOrder X).
  red; eauto. Qed.

Hint Resolve lengthOrder_wf.

Hint Rewrite app_length.

Lemma init_and_last_length_ordered X xs ys : forall y : X,
                                               init_and_last xs ys y ->
                                               length ys <= length xs.
  induction 1; crush. Qed.

Hint Resolve init_and_last_length_ordered.

Theorem deq_induction : forall X (P : list X -> Prop),
                          P []
                       -> (forall x, P [x]) 
                       -> (forall x xs y, P xs -> P (x :: xs ++ [y]))
                       -> forall l, P l.
  introv Pnil Psi PCons;
  apply well_founded_induction with (R := lengthOrder); [auto|intros xs IHlo].
  - destruct xs as [|x xs']; [assumption|].
    + destruct (idec xs') as [|H]; [crush|destr_prods].
      * rewrite (init_and_list H) in *; apply PCons; apply IHlo; red; crush.
Defined.

Theorem pal__rev : forall X (l : list X), pal l -> rev l = l.
  induction 1; eauto; simpl; rewrite rev_app_distr.
  - apply (f_equal (fun l => x :: l ++ [x])); apply IHpal.
Qed.

Hint Resolve app_inv_tail.
Hint Rewrite rev_unit.

Theorem rev__pal : forall X (l : list X), rev l = l -> pal l.
  intro; eapply (deq_induction (fun xs => rev xs = xs -> pal xs)); ecrush.
Qed.
