(** * MoreStlc: A Typechecker for STLC *)

(* $Date: 2011-04-12 22:39:07 -0400 (Tue, 12 Apr 2011) $ *)

Require Export Stlc_J.
Require Import Relations.

(** The [has_type] relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, tell us how to _check_ whether or not a term is well
    typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- they exactly follow the shape of the term.  This makes it
    straightforward to translate the typing rules into clauses of a
    typechecking _function_ that takes a term and a context and either
    returns the term's type or else signals that the term is not
    typable. *)

Module STLCChecker.
Import STLC.

(* ###################################################################### *)
(** ** Comparing Types *)

(** First, we need a function to compare two types for equality... *)

Fixpoint beq_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | ty_Bool, ty_Bool =>
      true
  | ty_arrow T11 T12, ty_arrow T21 T22 =>
      andb (beq_ty T11 T21) (beq_ty T12 T22)
  | _,_ =>
      false
  end.

(** ... and we need to establish the usual two-way connection between
    the boolean result returned by [beq_ty] and the logical
    proposition that its inputs are equal. *)

Lemma beq_ty_refl : forall T1,
  beq_ty T1 T1 = true.
Proof.
  intros T1. induction T1; simpl.
    reflexivity.
    rewrite IHT1_1. rewrite IHT1_2. reflexivity.  Qed.

Lemma beq_ty__eq : forall T1 T2,
  beq_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  Case "T1=ty_Bool".
    reflexivity.
  Case "T1=ty_arrow T1_1 T1_2".
    apply andb_true in H0. destruct H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.

(* ###################################################################### *)
(** ** The Typechecker *)

(** Now here's the typechecker.  It works by walking over the
    structure of the given term, returning either [Some T] or [None].
    Each time we make a recursive call to find out the types of the
    subterms, we need to pattern-match on the results to make sure
    that they are not [None].  Also, in the [tm_app] case, we use
    pattern matching to extract the left- and right-hand sides of the
    function's arrow type (and fail if the type of the function is not
    [ty_arrow T11 T12] for some [T1] and [T2]). *)

Fixpoint type_check (Gamma:context) (t:tm) : option ty :=
  match t with
  | tm_var x => Gamma x
  | tm_abs x T11 t12 => match type_check (extend Gamma x T11) t12 with
                          | Some T12 => Some (ty_arrow T11 T12)
                          | _ => None
                        end
  | tm_app t1 t2 => match type_check Gamma t1, type_check Gamma t2 with
                      | Some (ty_arrow T11 T12),Some T2 =>
                        if beq_ty T11 T2 then Some T12 else None
                      | _,_ => None
                    end
  | tm_true => Some ty_Bool
  | tm_false => Some ty_Bool
  | tm_if x t f => match type_check Gamma x with
                     | Some ty_Bool =>
                       match type_check Gamma t, type_check Gamma f with
                         | Some T1, Some T2 =>
                           if beq_ty T1 T2 then Some T1 else None
                         | _,_ => None
                       end
                     | _ => None
                   end
  end.

(* ###################################################################### *)
(** ** Properties *)

(** To verify that this typechecking algorithm is the correct one, we
    show that it is _sound_ and _complete_ for the original [has_type]
    relation -- that is, [type_check] and [has_type] define the same
    partial function. *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  tm_cases (induction t) Case; intros Gamma T Htc; inversion Htc.
  Case "tm_var"...
  Case "tm_app".
    remember (type_check Gamma t1) as TO1.
    remember (type_check Gamma t2) as TO2.
    destruct TO1 as [T1|]; try solve by inversion;
    destruct T1 as [|T11 T12]; try solve by inversion.
    destruct TO2 as [T2|]; try solve by inversion.
    remember (beq_ty T11 T2) as b.
    destruct b; try solve by inversion.
    symmetry in Heqb. apply beq_ty__eq in Heqb.
    inversion H0; subst...
  Case "tm_abs".
    rename i into y. rename t into T1.
    remember (extend Gamma y T1) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve by inversion.
    inversion H0; subst...
  Case "tm_true"...
  Case "tm_false"...
  Case "tm_if".
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve by inversion.
    destruct Tc; try solve by inversion.
    destruct TO1 as [T1|]; try solve by inversion.
    destruct TO2 as [T2|]; try solve by inversion.
    remember (beq_ty T1 T2) as b.
    destruct b; try solve by inversion.
    symmetry in Heqb. apply beq_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  has_type_cases (induction Hty) Case; simpl.
  Case "T_Var"...
  Case "T_Abs". rewrite IHHty...
  Case "T_App".
    rewrite IHHty1. rewrite IHHty2.
    rewrite (beq_ty_refl T11)...
  Case "T_True"...
  Case "T_False"...
  Case "T_If". rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (beq_ty_refl T)...
Qed.

End STLCChecker.

