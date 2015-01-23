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

Theorem pal_l_plus_rev_l : forall X (l : list X), pal (l ++ rev l).
Proof. induction l; crush.
       - Case "a :: l". rewrite app_assoc; constructor; assumption.
Qed.
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

Hint Resolve f_equal.

Hint Rewrite app_inv_tail.
Hint Rewrite app_inj_tail.

Fixpoint init_and_last {X : Type} (l : list X) : option (list X * X) :=
  match l with
    | [] => None
    | x :: xs => match init_and_last xs with
                  | None => Some ([], x)
                  | Some (xs', x') => Some (x :: xs', x')
                end
  end.

Hint Resolve f_equal.

Theorem init_and_list : forall X xs ys (y : X), init_and_last xs = Some (ys, y) ->
                                           xs = ys ++ [y].
Proof with crush.
  induction xs as [|x xs'].
  - inversion 1.
  - intros. simpl in *. destruct (init_and_last xs') as [p|] eqn:ilxs'.
    + Case "Some p". destruct p; invert H...
    + Case "None". inverts H; destruct xs'; trivial.
      simpl in *; destruct (init_and_last xs'); try destruct p; inverts ilxs'.
Qed.

Hint Rewrite init_and_list.

Definition lengthOrder {X : Type} (ls1 ls2 : list X) :=
  length ls1 < length ls2.

Hint Unfold lengthOrder.
Hint Constructors Acc.

Lemma lengthOrder_wf' : forall X len (ls : list X), 
                          length ls <= len -> Acc lengthOrder ls.
Proof. unfold lengthOrder; induction len; crush. Qed.

Theorem lengthOrder_wf : forall X, well_founded (@lengthOrder X).
Proof. red. intros. eapply lengthOrder_wf'. eauto. Qed.

Hint Resolve lengthOrder_wf.

Lemma le_S : forall n m, n <= m -> S n <= S m.
  induction 1; crush. Qed.

Lemma le_Sn_m : forall n m, S n <= m -> n <= m.
  induction 1; crush. Qed.

Hint Rewrite app_length.

Theorem init_and_last_length_ordered : forall X xs ys (x y : X),
           init_and_last (x :: xs) = Some (ys, y) ->
           length ys <= length (x :: xs).                              
Proof. induction xs; intros; [crush|].
       - simpl in *. destruct (init_and_last xs) eqn:ilxs.
         + destruct p; apply init_and_list in ilxs; inverts H; crush.
         + inverts H; crush.
Qed.

Hint Resolve init_and_last_length_ordered.

Theorem deq_induction X (P : list X -> Prop)
        (Pi : P [])
        (Psi : forall x, P [x])
        (Psnoc : forall x xs y, P xs -> P (x :: xs ++ [y])) :
  (forall l, P l).
Proof. apply well_founded_induction with (R := lengthOrder); eauto.
       - introv IHlo. destruct x as [|x xs']; eauto.
         + destruct (init_and_last xs') as [p|] eqn:ilxs; [destruct p|]; eauto.
           * apply init_and_list in ilxs. subst. apply Psnoc. apply IHlo.
             unfold lengthOrder; crush.
           * destruct xs'; crush. destruct (init_and_last xs'); [destruct p|]; crush.
Defined.

Hint Rewrite rev_unit.

Theorem pal__rev : forall X (l : list X), pal l -> l = rev l.
Proof. induction 1; eauto. simpl; rewrite rev_unit. crush. Qed.

Hint Resolve pal__rev.
Hint Resolve app_inv_tail.

Theorem rev__pal : forall X (l : list X), l = rev l -> pal l.
Proof with crush. intro X.
  refine (deq_induction (fun xs => xs = rev xs -> pal xs)
                        (fun _ => palnil)
                        (fun x _ => palsing x)
                        _)...
  - Case "x :: xs ++ [y]". replace (rev xs) with xs in *. intuition.
    + SCase "assertion". eapply app_inv_tail; eassumption.
Qed.
