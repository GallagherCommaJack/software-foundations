Require Import SfLib.
Require Import CpdtTactics.

Inductive pal : forall X, list X -> Prop :=
| palnil : forall X, pal X []
| palsing : forall X (x : X), pal X [x]
| palcons : forall X (l : list X) (x : X), pal X l -> pal X (x :: l ++ [x]).

Arguments pal {X} l.
Arguments palnil {X}.
Arguments palsing {X} {x}.
Arguments palcons {X} {l} {x} p.

Theorem pal_l_plus_rev_l : forall X (l : list X), pal (l ++ rev l).
Proof. intros. induction l as [|x xs].
       Case "l = []". simpl. exact palnil.
       Case "l = x :: xs". simpl. rewrite <- snoc_with_append.
         apply palcons. exact IHxs.
Qed.
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

Theorem snoc_neq_nil : forall X (x : X) (l1 : list X), l1 ++ [x] <> [].
Proof. induction l1; intro; inversion H. Qed.

Lemma snoc_eq : forall X (x : X) (l1 l2 : list X), l1 ++ [x] = l2 ++ [x] -> l1 = l2.
Proof. induction l1 as [|y ys]; [Case "l1 = []" | Case "l1 = x :: xs"]; intros;
       destruct l2 as [|b bs]; try reflexivity; inversion H.
       Case "l1 = []". SCase "l2 = b :: bs". 
           exfalso. apply (snoc_neq_nil _ b bs). symmetry. apply H2.
       Case "l1 = x :: xs". 
         SCase "l2 = []". exfalso. apply (snoc_neq_nil _ x ys). apply H2.
         SCase "l2 = b :: bs". apply IHys in H2. subst. reflexivity.
Qed.

Fixpoint init_and_last {X : Type} (l : list X) : option (list X * X) :=
  match l with
    | [] => None
    | x :: xs => match init_and_last xs with
                  | None => Some ([], x)
                  | Some (xs', x') => Some (x :: xs', x')
                end
  end.

Theorem init_and_last_cons : forall X xs ys (x y : X),
                               init_and_last xs = Some (ys, y) <->
                               init_and_last (x :: xs) = Some (x :: ys, y).
Proof. split. 
       Case "->". generalize dependent ys. induction xs as [|x' xs']; intros.
         SCase "xs = []". simpl in H. inversion H.
         SCase "xs = x :: xs". simpl. 
           destruct xs'; inversion H; subst; [|simpl in *; rewrite H1];
                                               reflexivity.
       Case "<-". generalize dependent ys. induction xs as [|x' xs']; intros.
         SCase "xs = []". inversion H. 
         SCase "xs = x' :: xs'". simpl in *. 
           destruct (init_and_last xs'); try destruct p;
           inversion H; subst; reflexivity.
Qed.

Definition cons_eq {X : Type} (xs ys : list X) x : xs = ys -> x :: xs = x :: ys :=
  @f_equal (list X) (list X) (cons x) xs ys.

Theorem init_and_list : forall X xs ys (y : X), init_and_last xs = Some (ys, y) <->
                                           xs = ys ++ [y].
Proof. split.
       Case "->". generalize dependent ys. induction xs as [|a xs']; 
                                          intros; inversion H.
         SCase "xs = a :: xs'". 
           destruct (init_and_last xs') eqn:ilxs'; try destruct p.
           SSCase "init_and_last xs' = Some (ys, y)". 
             inversion H1. subst. simpl. 
             apply cons_eq. apply IHxs'. reflexivity.
           SSCase "init_and_last xs' = None".
             destruct xs'; inversion H1; subst; try reflexivity.
             simpl in ilxs'; destruct (init_and_last xs');
             try destruct p; inversion ilxs'.
       Case "<-". generalize dependent xs. 
         induction ys as [|b ys']; intros; 
         [SCase "ys = []" | SCase "ys = b :: ys'"];
         destruct xs; inversion H; subst.
         SCase "ys = []". reflexivity.
         SCase "ys = b :: ys'". 
           apply init_and_last_cons. apply IHys'. reflexivity.
Qed.

Definition lengthOrder {X : Type} (ls1 ls2 : list X) :=
  length ls1 < length ls2.
Hint Constructors Acc.

Lemma lengthOrder_wf' : forall X len (ls : list X), 
                          length ls <= len -> Acc lengthOrder ls.
Proof. unfold lengthOrder; induction len; crush. Qed.

Theorem lengthOrder_wf : forall X, well_founded (@lengthOrder X).
Proof. red. intros. eapply lengthOrder_wf'. eauto. Qed.

Definition opt_extract {X} (m : option X) (p : exists x, m = Some x) : X.
Proof. destruct m; firstorder; exfalso; firstorder; inversion H. Qed.

Definition init_and_last_ordered : forall X xs (x : X),
           match init_and_last (x :: xs) with
             | Some (xs', x) => length xs' <= length (x :: xs)
             | None => 0 <= length (x :: xs)
           end.
Proof. intros. induction xs as [|y ys].
       Case "xs = []". simpl. auto.
       Case "xs = y :: ys". simpl in *.
         destruct (init_and_last ys) eqn:ilys; 
         try destruct p; simpl in *; apply le_n_S.
         SCase "init_and_last ys = Some (l, x0)". apply IHys.
         SCase "init_and_last ys = None". apply le_0_n.
Qed.

Theorem deq_induction X (P : list X -> Prop)
        (Pi : P [])
        (Psi : forall x, P [x])
        (Psnoc : forall x xs y, P xs -> P (x :: xs ++ [y])) :
  (forall l, P l).
Proof. apply well_founded_induction with (R := lengthOrder).
       Case "well-founded". apply lengthOrder_wf.
       Case "proof of induction". 
         intros xs H. destruct xs as [|x xs'].
         SCase "xs = []". apply Pi.
         SCase "xs = x :: xs'". destruct (init_and_last xs') as [p|] eqn:ilxs'.
           SSCase "init_and_last xs' = Some (ys, y)". destruct p as [ys y]. 
             inversion ilxs'. apply init_and_list in ilxs'. rewrite ilxs'.
             apply Psnoc. apply H. unfold lengthOrder. unfold lt.
             remember (init_and_last_ordered X xs' x) as H0. simpl in *.
             subst. rewrite app_length. simpl. 
             rewrite <- plus_n_Sm. rewrite plus_0_r. auto.
           SSCase "init_and_last xs' = None".
             destruct xs'; try apply Psi. simpl in ilxs'. 
             destruct (init_and_last xs'); try destruct p; inversion ilxs'.
Defined.

Theorem pal__rev : forall X (l : list X), pal l -> l = rev l.
Proof. intros. induction H; simpl; try reflexivity. 
       rewrite rev_snoc. rewrite <- IHpal. reflexivity.
Qed.

Theorem rev_iff_pal : forall X (l : list X),
                        l = rev l <-> pal l.
Proof. 
  intro X. apply (deq_induction X); 
           [Case "l = []" | Case "l = [x]" | Case "l = x :: xs ++ [y]"];
           split; try apply pal__rev; intros; try constructor; simpl in *.
  Case "l = x :: xs ++ [y]".
    SCase "->". 
      rewrite rev_snoc in H0. simpl in H0. inversion H0; subst.
      apply palcons. apply snoc_eq in H3. apply H. apply H3.
Qed.

Theorem rev__pal : forall X (l : list X), l = rev l -> pal l.
Proof. apply rev_iff_pal. Qed.
