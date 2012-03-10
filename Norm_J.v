(** * Norm_J: STLCの正規化 *)
(* * Norm: Normalization of STLC *)

(* $Date: 2011-04-13 14:34:47 -0400 (Wed, 13 Apr 2011) $ *)
(* Chapter maintained by Andrew Tolmach *)

(* (Based on TAPL Ch. 12.) *)

Require Import Stlc_J.
Require Import Relations.

(*
(This chapter is optional.)

In this chapter, we consider another fundamental theoretical property
of the simply typed lambda-calculus: the fact that the evaluation of a
well-typed program is guaranteed to halt in a finite number of
steps---i.e., every well-typed term is _normalizable_.

Unlike the type-safety properties we have considered so far, the
normalization property does not extend to full-blown programming
languages, because these languages nearly always extend the simply
typed lambda-calculus with constructs, such as general recursion
(as we discussed in the MoreStlc chapter) or recursive types, that can
be used to write nonterminating programs.  However, the issue of
normalization reappears at the level of _types_ when we consider the
metatheory of polymorphic versions of the lambda calculus such as
F_omega: in this system, the language of types effectively contains a
copy of the simply typed lambda-calculus, and the termination of the
typechecking algorithm will hinge on the fact that a ``normalization''
operation on type expressions is guaranteed to terminate.

Another reason for studying normalization proofs is that they are some
of the most beautiful---and mind-blowing---mathematics to be found in
the type theory literature, often (as here) involving the fundamental
proof technique of _logical relations_.

The calculus we shall consider here is the simply typed
lambda-calculus over a single base type [bool] and with pairs. We'll
give full details of the development for the basic lambda-calculus
terms treating [bool] as an uninterpreted base type, and leave the
extension to the boolean operators and pairs to the reader.  Even for
the base calculus, normalization is not entirely trivial to prove,
since each reduction of a term can duplicate redexes in subterms. *)
(**
(この章はオプションです。)

この章では、単純型付きラムダ計算の別の基本的な理論的性質を検討します。
型付けされるプログラムは有限回のステップで停止することが保証されるという事実です。
つまり、すべての型付けされた項は正規化可能(_normalizable_)です。

ここまで考えてきた型安全性とは異なり、
正規化性は本格的なプログラミング言語には拡張されません。
なぜなら、本格的な言語ではほとんどの場合、単純型付きラムダ計算に、
(MoreStlc_J章で議論したような)一般再帰や再帰型が拡張され、
停止しないプログラムが書けるようになっているからです。
しかし、正規化性の問題は「型のレベル」で再度現れます。
それが現れるのは、F_omegaのようなラムダ計算の多相バージョンの、メタ理論を考えるときです。
F_omegaでは、型の言語は単純型付きラムダ計算のコピーを効果的に包括しており、
型チェックアルゴリズムの停止性は、
型の式の「正規化」操作が停止することが保証されていることに依拠しています。

正規化の証明を学習する別の理由は、それが、
(ここでやっているように)論理的関係の基本的証明テクニックを含むような型理論の文献において、
見るべき一番美しい---そして刺激的な---数学だからです。

ここで考える計算は、基本型[bool]と対を持つ単純型付きラムダ計算です。
ここでは[bool]を未解釈基本型として扱う基本ラムダ計算項の処理を細部まで示します。
ブール演算と対の拡張は読者に残しておきます。
基本計算においてさえ、正規化は証明が完全に自明ということはありません。
なぜなら、項の各簡約は部分項のリデックスを複製することがあるからです。 *)

(* **** Exercise: 1 star *)
(** **** 練習問題: ★ *)
(* Where do we fail if we attempt to prove normalization by a
straightforward induction on the size of a well-typed term? *)
(** 型付けされた項のサイズについての素直な帰納法で正規化性を証明しようとしたとき、
    どこで失敗するでしょうか？ *)

(* FILL IN HERE *)
(** [] *)

(* ###################################################################### *)
(* * Language *)
(** * 言語 *)

(* We begin by repeating the relevant language definition, which is
similar to those in the MoreStlc chapter, and supporting results
including type preservation and step determinism.  (We won't need
progress.)  You may just wish to skip down to the Normalization
section... *)
(** 関係する言語の定義から始めます。MoreStlc_J章のものと同様です。
そして、型の保存とステップの決定性を含む結果も成立します。
(進行は使いません。)
正規化の節まで飛ばしても構いません... *)

(* ###################################################################### *)
(* *** Syntax and Operational Semantics *)
(** *** 構文と操作的意味 *)

Inductive ty : Type :=
  | ty_Bool : ty
  | ty_arrow : ty -> ty -> ty
  | ty_prod  : ty -> ty -> ty
.

Tactic Notation "ty_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ty_Bool" | Case_aux c "ty_arrow" | Case_aux c "ty_prod" ].

Inductive tm : Type :=
    (* pure STLC *)
  | tm_var : id -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : id -> ty -> tm -> tm
    (* pairs *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm
    (* booleans *)
  | tm_true : tm
  | tm_false : tm
  | tm_if : tm -> tm -> tm -> tm.
          (* i.e., [if t0 then t1 else t2] *)

Tactic Notation "tm_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tm_var" | Case_aux c "tm_app" | Case_aux c "tm_abs"
  | Case_aux c "tm_pair" | Case_aux c "tm_fst" | Case_aux c "tm_snd"
  | Case_aux c "tm_true" | Case_aux c "tm_false" | Case_aux c "tm_if" ].


(* ###################################################################### *)
(* *** Substitution *)
(** *** 置換 *)

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tm_var y => if beq_id x y then s else t
  | tm_abs y T t1 =>  tm_abs y T (if beq_id x y then t1 else (subst x s t1))
  | tm_app t1 t2 => tm_app (subst x s t1) (subst x s t2)
  | tm_pair t1 t2 => tm_pair (subst x s t1) (subst x s t2)
  | tm_fst t1 => tm_fst (subst x s t1)
  | tm_snd t1 => tm_snd (subst x s t1)
  | tm_true => tm_true
  | tm_false => tm_false
  | tm_if t0 t1 t2 => tm_if (subst x s t0) (subst x s t1) (subst x s t2)
  end.

(* ###################################################################### *)
(* *** Reduction *)
(** *** 簡約 *)

Inductive value : tm -> Prop :=
  | v_abs : forall x T11 t12,
      value (tm_abs x T11 t12)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value (tm_pair v1 v2)
  | v_true : value tm_true
  | v_false : value tm_false
.

Hint Constructors value.

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
  | ST_AppAbs : forall x T11 t12 v2,
         value v2 ->
         (tm_app (tm_abs x T11 t12) v2) ==> (subst x v2 t12)
  | ST_App1 : forall t1 t1' t2,
         t1 ==> t1' ->
         (tm_app t1 t2) ==> (tm_app t1' t2)
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 ==> t2' ->
         (tm_app v1 t2) ==> (tm_app v1 t2')
  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2,
        t1 ==> t1' ->
        (tm_pair t1 t2) ==> (tm_pair t1' t2)
  | ST_Pair2 : forall v1 t2 t2',
        value v1 ->
        t2 ==> t2' ->
        (tm_pair v1 t2) ==> (tm_pair v1 t2')
  | ST_Fst : forall t1 t1',
        t1 ==> t1' ->
        (tm_fst t1) ==> (tm_fst t1')
  | ST_FstPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (tm_fst (tm_pair v1 v2)) ==> v1
  | ST_Snd : forall t1 t1',
        t1 ==> t1' ->
        (tm_snd t1) ==> (tm_snd t1')
  | ST_SndPair : forall v1 v2,
        value v1 ->
        value v2 ->
        (tm_snd (tm_pair v1 v2)) ==> v2
  (* booleans *)
  | ST_IfTrue : forall t1 t2,
        (tm_if tm_true t1 t2) ==> t1
  | ST_IfFalse : forall t1 t2,
        (tm_if tm_false t1 t2) ==> t2
  | ST_If : forall t0 t0' t1 t2,
        t0 ==> t0' ->
        (tm_if t0 t1 t2) ==> (tm_if t0' t1 t2)

where "t1 '==>' t2" := (step t1 t2).

Tactic Notation "step_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ST_AppAbs" | Case_aux c "ST_App1" | Case_aux c "ST_App2"
  | Case_aux c "ST_Pair1" | Case_aux c "ST_Pair2"
    | Case_aux c "ST_Fst" | Case_aux c "ST_FstPair"
    | Case_aux c "ST_Snd" | Case_aux c "ST_SndPair"
  | Case_aux c "ST_IfTrue" | Case_aux c "ST_IfFalse" | Case_aux c "ST_If" ].

Notation stepmany := (refl_step_closure step).
Notation "t1 '==>*' t2" := (stepmany t1 t2) (at level 40).

Hint Constructors step.

Notation step_normal_form := (normal_form step).

Lemma value__normal : forall t, value t -> step_normal_form t.
Proof with eauto.
  intros t H; induction H; intros [t' ST]; inversion ST...
Qed.


(* ###################################################################### *)
(* *** Typing *)
(** *** 型付け *)

Definition context := partial_map ty.

Inductive has_type : context -> tm -> ty -> Prop :=
  (* Typing rules for proper terms *)
  | T_Var : forall Gamma x T,
      Gamma x = Some T ->
      has_type Gamma (tm_var x) T
  | T_Abs : forall Gamma x T11 T12 t12,
      has_type (extend Gamma x T11) t12 T12 ->
      has_type Gamma (tm_abs x T11 t12) (ty_arrow T11 T12)
  | T_App : forall T1 T2 Gamma t1 t2,
      has_type Gamma t1 (ty_arrow T1 T2) ->
      has_type Gamma t2 T1 ->
      has_type Gamma (tm_app t1 t2) T2
  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      has_type Gamma t1 T1 ->
      has_type Gamma t2 T2 ->
      has_type Gamma (tm_pair t1 t2) (ty_prod T1 T2)
  | T_Fst : forall Gamma t T1 T2,
      has_type Gamma t (ty_prod T1 T2) ->
      has_type Gamma (tm_fst t) T1
  | T_Snd : forall Gamma t T1 T2,
      has_type Gamma t (ty_prod T1 T2) ->
      has_type Gamma (tm_snd t) T2
  (* booleans *)
  | T_True : forall Gamma,
      has_type Gamma tm_true ty_Bool
  | T_False : forall Gamma,
      has_type Gamma tm_false ty_Bool
  | T_If : forall Gamma t0 t1 t2 T,
      has_type Gamma t0 ty_Bool ->
      has_type Gamma t1 T ->
      has_type Gamma t2 T ->
      has_type Gamma (tm_if t0 t1 t2) T
.

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var" | Case_aux c "T_Abs" | Case_aux c "T_App"
  | Case_aux c "T_Pair" | Case_aux c "T_Fst" | Case_aux c "T_Snd"
  | Case_aux c "T_True" | Case_aux c "T_False" | Case_aux c "T_If" ].

Hint Extern 2 (has_type _ (tm_app _ _) _) => eapply T_App; auto.
Hint Extern 2 (_ = _) => compute; reflexivity.

(* ###################################################################### *)
(* *** Context Invariance *)
(** *** コンテキスト不変性 *)

Inductive appears_free_in : id -> tm -> Prop :=
  | afi_var : forall x,
      appears_free_in x (tm_var x)
  | afi_app1 : forall x t1 t2,
      appears_free_in x t1 -> appears_free_in x (tm_app t1 t2)
  | afi_app2 : forall x t1 t2,
      appears_free_in x t2 -> appears_free_in x (tm_app t1 t2)
  | afi_abs : forall x y T11 t12,
        y <> x  ->
        appears_free_in x t12 ->
        appears_free_in x (tm_abs y T11 t12)
  (* pairs *)
  | afi_pair1 : forall x t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tm_pair t1 t2)
  | afi_pair2 : forall x t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tm_pair t1 t2)
  | afi_fst : forall x t,
      appears_free_in x t ->
      appears_free_in x (tm_fst t)
  | afi_snd : forall x t,
      appears_free_in x t ->
      appears_free_in x (tm_snd t)
  (* booleans *)
  | afi_if0 : forall x t0 t1 t2,
      appears_free_in x t0 ->
      appears_free_in x (tm_if t0 t1 t2)
  | afi_if1 : forall x t0 t1 t2,
      appears_free_in x t1 ->
      appears_free_in x (tm_if t0 t1 t2)
  | afi_if2 : forall x t0 t1 t2,
      appears_free_in x t2 ->
      appears_free_in x (tm_if t0 t1 t2)
.

Hint Constructors appears_free_in.

Definition closed (t:tm) :=
  forall x, ~ appears_free_in x t.

Lemma context_invariance : forall Gamma Gamma' t S,
     has_type Gamma t S  ->
     (forall x, appears_free_in x t -> Gamma x = Gamma' x)  ->
     has_type Gamma' t S.
Proof with eauto.
  intros. generalize dependent Gamma'.
  has_type_cases (induction H) Case;
    intros Gamma' Heqv...
  Case "T_Var".
    apply T_Var... rewrite <- Heqv...
  Case "T_Abs".
    apply T_Abs... apply IHhas_type. intros y Hafi.
    unfold extend. remember (beq_id x y) as e.
    destruct e...
  Case "T_Pair".
    apply T_Pair...
  Case "T_If".
    eapply T_If...
Qed.

Lemma free_in_context : forall x t T Gamma,
   appears_free_in x t ->
   has_type Gamma t T ->
   exists T', Gamma x = Some T'.
Proof with eauto.
  intros x t T Gamma Hafi Htyp.
  has_type_cases (induction Htyp) Case; inversion Hafi; subst...
  Case "T_Abs".
    destruct IHHtyp as [T' Hctx]... exists T'.
    unfold extend in Hctx.
    apply not_eq_beq_id_false in H2. rewrite H2 in Hctx...
Qed.

Corollary typable_empty__closed : forall t T,
    has_type empty t T  ->
    closed t.
Proof.
  intros. unfold closed. intros x H1.
  destruct (free_in_context _ _ _ _ H1 H) as [T' C].
  inversion C.  Qed.

(* ###################################################################### *)
(* *** Preservation *)
(** *** 保存 *)

Lemma substitution_preserves_typing : forall Gamma x U v t S,
     has_type (extend Gamma x U) t S  ->
     has_type empty v U   ->
     has_type Gamma (subst x v t) S.
Proof with eauto.
  (* Theorem: If Gamma,x:U |- t : S and empty |- v : U, then
     Gamma |- (subst x v t) S. *)
  intros Gamma x U v t S Htypt Htypv.
  generalize dependent Gamma. generalize dependent S.
  (* Proof: By induction on the term t.  Most cases follow directly
     from the IH, with the exception of tm_var and tm_abs.
     The former aren't automatic because we must reason about how the
     variables interact. *)
  tm_cases (induction t) Case;
    intros S Gamma Htypt; simpl; inversion Htypt; subst...
  Case "tm_var".
    simpl. rename i into y.
    (* If t = y, we know that
         [empty |- v : U] and
         [Gamma,x:U |- y : S]
       and, by inversion, [extend Gamma x U y = Some S].  We want to
       show that [Gamma |- subst x v y : S].

       There are two cases to consider: either [x=y] or [x<>y]. *)
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
    (* If [x = y], then we know that [U = S], and that [subst x v y = v].
       So what we really must show is that if [empty |- v : U] then
       [Gamma |- v : U].  We have already proven a more general version
       of this theorem, called context invariance. *)
      apply beq_id_eq in Heqe. subst.
      unfold extend in H1. rewrite <- beq_id_refl in H1.
      inversion H1; subst. clear H1.
      eapply context_invariance...
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
    (* If [x <> y], then [Gamma y = Some S] and the substitution has no
       effect.  We can show that [Gamma |- y : S] by [T_Var]. *)
      apply T_Var... unfold extend in H1. rewrite <- Heqe in H1...
  Case "tm_abs".
    rename i into y. rename t into T11.
    (* If [t = tm_abs y T11 t0], then we know that
         [Gamma,x:U |- tm_abs y T11 t0 : T11->T12]
         [Gamma,x:U,y:T11 |- t0 : T12]
         [empty |- v : U]
       As our IH, we know that forall S Gamma,
         [Gamma,x:U |- t0 : S -> Gamma |- subst x v t0 S].

       We can calculate that
         subst x v t = tm_abs y T11 (if beq_id x y
                                      then t0
                                      else subst x v t0)
       And we must show that [Gamma |- subst x v t : T11->T12].  We know
       we will do so using [T_Abs], so it remains to be shown that:
         [Gamma,y:T11 |- if beq_id x y then t0 else subst x v t0 : T12]
       We consider two cases: [x = y] and [x <> y].
    *)
    apply T_Abs...
    remember (beq_id x y) as e. destruct e.
    SCase "x=y".
    (* If [x = y], then the substitution has no effect.  Context
       invariance shows that [Gamma,y:U,y:T11] and [Gamma,y:T11] are
       equivalent.  Since the former context shows that [t0 : T12], so
       does the latter. *)
      eapply context_invariance...
      apply beq_id_eq in Heqe. subst.
      intros x Hafi. unfold extend.
      destruct (beq_id y x)...
    SCase "x<>y".
    (* If [x <> y], then the IH and context invariance allow us to show that
         [Gamma,x:U,y:T11 |- t0 : T12]       =>
         [Gamma,y:T11,x:U |- t0 : T12]       =>
         [Gamma,y:T11 |- subst x v t0 : T12] *)
      apply IHt. eapply context_invariance...
      intros z Hafi. unfold extend.
      remember (beq_id y z) as e0. destruct e0...
      apply beq_id_eq in Heqe0. subst.
      rewrite <- Heqe...
Qed.

Theorem preservation : forall t t' T,
     has_type empty t T  ->
     t ==> t'  ->
     has_type empty t' T.
Proof with eauto.
  intros t t' T HT.
  (* Theorem: If [empty |- t : T] and [t ==> t'], then [empty |- t' : T]. *)
  remember (@empty ty) as Gamma. generalize dependent HeqGamma.
  generalize dependent t'.
  (* Proof: By induction on the given typing derivation.  Many cases are
     contradictory ([T_Var], [T_Abs]).  We show just the interesting ones. *)
  has_type_cases (induction HT) Case;
    intros t' HeqGamma HE; subst; inversion HE; subst...
  Case "T_App".
    (* If the last rule used was [T_App], then [t = t1 t2], and three rules
       could have been used to show [t ==> t']: [ST_App1], [ST_App2], and
       [ST_AppAbs]. In the first two cases, the result follows directly from
       the IH. *)
    inversion HE; subst...
    SCase "ST_AppAbs".
      (* For the third case, suppose
           [t1 = tm_abs x T11 t12]
         and
           [t2 = v2].
         We must show that [empty |- subst x v2 t12 : T2].
         We know by assumption that
             [empty |- tm_abs x T11 t12 : T1->T2]
         and by inversion
             [x:T1 |- t12 : T2]
         We have already proven that substitution_preserves_typing and
             [empty |- v2 : T1]
         by assumption, so we are done. *)
      apply substitution_preserves_typing with T1...
      inversion HT1...
  Case "T_Fst".
    inversion HT...
  Case "T_Snd".
    inversion HT...
Qed.
(** [] *)


(* ###################################################################### *)
(* *** Determinism *)
(** *** 決定性 *)

Lemma step_deterministic :
   partial_function step.
Proof with eauto.
   unfold partial_function.
   (* FILL IN HERE *) 
   (** ここを埋めなさい *) Admitted.

(* ###################################################################### *)
(* * Normalization *)
(** * 正規化 *)

(* Now for the actual normalization proof.

    Our goal is to prove that every well-typed term evaluates to a
    normal form.  In fact, it turns out to be convenient to prove
    something slightly stronger, namely that every well-typed term
    evaluates to a _value_.  This follows from the weaker property
    anyway via the Progress lemma (why?) but otherwise we don't need
    Progress, and we didn't bother re-proving it above.

    Here's the key definition: *)
(** ここからが本当の正規化の証明です。

    ゴールはすべての型付けされた項が正規形になることを証明することです。
    実際のところ、もうちょっと強いことを証明した方が便利です。
    つまり、すべての型付けされた項が値になるということです。
    この強い方は、いずれにしろ弱い方から進行補題を使って得ることができますが(なぜでしょう？)、
    最初から強い方を証明すれば進行性は必要ありません。
    そして、進行性を再び証明することは上では行いませんでした。

    これがキーとなる定義です: *)

Definition halts  (t:tm) : Prop :=  exists t', t ==>* t' /\  value t'.

(* A trivial fact: *)
(** あたりまえの事実: *)

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  apply rsc_refl.
  assumption.
Qed.

(* The key issue in the normalization proof (as in many proofs by
induction) is finding a strong enough induction hypothesis.  To this
end, we begin by defining, for each type [T], a set [R_T] of closed
terms of type [T].  We will specify these sets using a relation [R]
and write [R T t] when [t] is in [R_T]. (The sets [R_T] are sometimes
called _saturated sets_ or _reducibility candidates_.)

Here is the definition of [R] for the base language:

- [R bool t] iff [t] is a closed term of type [bool] and [t] halts in a value

- [R (T1 -> T2) t] iff [t] is a closed term of type [T1 -> T2] and [t] halts
  in a value _and_ for any term [s] such that [R T1 s], we have [R
  T2 (t s)]. *)
(** 正規化の証明のキーとなる問題は、
(多くの帰納法による証明と同様に)十分な強さの帰納法の仮定を見つけることです。
このために、それぞれの型[T]に対して型[T]の閉じた項の集合[R_T]を定義することから始めます。
これらの集合を関係[R]を使って定め、[t]が[R_T]の要素であることを [R T t] と書きます。
(集合[R_T]はしばしば飽和集合(_saturated sets_)あるいは簡約可能性候補
(_reducibility candidates_)と呼ばれます。)

基本言語に対する[R]の定義は以下の通りです:

- [R bool t] とは、[t]が型[bool]の閉じた項で[t]が値になることである

- [R (T1 -> T2) t] とは、[t]が型 [T1 -> T2] の閉じた項で、[t]が値になり、かつ、
  [R T1 s] となる任意の項[s]について、[R T2 (t s)] となることである。 *)

(* This definition gives us the strengthened induction hypothesis that we
need.  Our primary goal is to show that all _programs_ ---i.e., all
closed terms of base type---halt.  But closed terms of base type can
contain subterms of functional type, so we need to know something
about these as well.  Moreover, it is not enough to know that these
subterms halt, because the application of a normalized function to a
normalized argument involves a substitution, which may enable more
evaluation steps.  So we need a stronger condition for terms of
functional type: not only should they halt themselves, but, when
applied to halting arguments, they should yield halting results.

The form of [R] is characteristic of the _logical relations_ proof
technique.  (Since we are just dealing with unary relations here, we
could perhaps more properly say _logical predicates_.)  If we want to
prove some property [P] of all closed terms of type [A], we proceed by
proving, by induction on types, that all terms of type [A] _possess_
property [P], all terms of type [A->A] _preserve_ property [P], all
terms of type [(A->A)->(A->A)] _preserve the property of preserving_
property [P], and so on.  We do this by defining a family of
predicates, indexed by types.  For the base type [A], the predicate is
just [P].  For functional types, it says that the function should map
values satisfying the predicate at the input type to values satisfying
the predicate at the output type.

When we come to formalize the definition of [R] in Coq, we hit a
problem.  The most obvious formulation would be as a parameterized
Inductive proposition like this:

[[
Inductive R : ty -> tm -> Prop :=
| R_bool : forall b t, has_type empty t ty_Bool ->
                halts t ->
                R ty_Bool t
| R_arrow : forall T1 T2 t, has_type empty t (ty_arrow T1 T2) ->
                halts t ->
                (forall s, R T1 s -> R T2 (tm_app t s)) ->
                R (ty_arrow T1 T2) t.
]]

Unfortunately, Coq rejects this definition because it violates the
_strict positivity requirement_ for inductive definitions, which says
that the type being defined must not occur to the left of an arrow in
the type of a constructor argument. Here, it is the third argument to
[R_arrow], namely [(forall s, R T1 s -> R TS (tm_app t s))], and
specifically the [R T1 s] part, that violates this rule.  (The
outermost arrows separating the constructor arguments don't count when
applying this rule; otherwise we could never have genuinely inductive
predicates at all!)  The reason for the rule is that types defined
with non-positive recursion can be used to build non-terminating
functions, which as we know would be a disaster for Coq's logical
soundness. Even though the relation we want in this case might be
perfectly innocent, Coq still rejects it because it fails the
positivity test.

Fortunately, it turns out that we _can_ define [R] using a
[Fixpoint]: *)
(** この定義は必要な強化された帰納法の仮定を与えます。
最初のゴールはすべてのプログラム(つまり、基本型のすべての閉じた項)が停止することを示すことです。
しかし、基本型の閉じた項は関数型の部分項を含むこともできるので、
これらについても性質を知ることが必要です。
さらに、これらの部分項が停止することを知るだけでは不十分です。なぜなら、
正規化された関数を正規化された引数へ適用すると置換が行われるため、
さらに評価ステップが発生する可能性があるからです。
これから関数型の項についてより強い条件が必要です。つまり、
自分自身が停止するだけでなく、停止する引数に適用されると停止する結果にならなければならないという条件です。

[R]の形は論理的関係(_logical relations_)証明テクニックの特徴です。
(ここで扱うのは単項関係のみなので、おそらく論理的述語(_logical predicates_)
という方がより適切でしょう。)
型[A]のすべての閉じた項についてある性質[P]を証明したい場合、
型についての帰納法により、型[A]のすべての項が性質[P]を「持ち」、型[A->A]
のすべての項が性質[P]を「保存し」、型[(A->A)->(A->A)]のすべての項が性質[P]を
「保存することを保存し」、...ということを証明していきます。
このために型をインデックスとする述語の族を定義します。
基本型[A]に対しては、述語は単に[P]です。関数型に対しては、述語は、
その関数が入力の型の述語を満たす値を出力の型の述語を満たす値に写像することを言うものです。

Coqで[R]の定義を形式化しようとするとき、問題が生じます。
一番自明な形式化は、次のようなパラメータ化された Inductive による命題でしょう：

[[
Inductive R : ty -> tm -> Prop :=
| R_bool : forall b t, has_type empty t ty_Bool ->
                halts t ->
                R ty_Bool t
| R_arrow : forall T1 T2 t, has_type empty t (ty_arrow T1 T2) ->
                halts t ->
                (forall s, R T1 s -> R T2 (tm_app t s)) ->
                R (ty_arrow T1 T2) t.
]]

残念ながらCoqはこの定義を受け付けません。なぜなら帰納的定義の
_strict positivity requirement_を満たさないからです。
_strict positivity requirement_とは、
定義される型がコンストラクタ引数の型の矢印の左に現れてはいけないというものです。
ここで、この規則を破っているのは、[R_arrow]の第3引数、すなわち、
[(forall s, R T1 s -> R TS (tm_app t s))] の、特に [R T1 s] の部分です。
(一番外側のコンストラクタ引数を分離している矢印は規則の対象外です。
そうでなければ、純粋な帰納的述語はまったく定義できません!)
この規則がある理由は、正ではない再帰(non-positive recursion)
を使って定義された型は停止しない関数を作るのに使うことができ、
それがCoqの論理的健全性を脅かすからです。
ここで定義しようとしている関係が完全に問題ないものであるにもかかわらず、
_strict positivity requirement_のテストを通らないので、Coqはこれを拒否します。

幸い、[Fixpoint]を使うと[R]が定義できます: *)

Fixpoint R (T:ty) (t:tm) {struct T} : Prop :=
  has_type empty t T /\ halts t /\
  (match T with
   | ty_Bool  => True
   | ty_arrow T1 T2 => (forall s, R T1 s -> R T2 (tm_app t s))
(* FILL IN HERE *)
(** ここを埋めなさい *)
   | ty_prod T1 T2 => False (* ... and delete this line *)
   end).

(* As immediate consequences of this definition, we have that every
element of every set [R_T] halts in a value and is closed with type
[t] :*)
(** この定義からすぐに導かれることとして、
すべての集合[R_T]について、
そのすべての要素は停止して値となり、また型[T]について閉じていることが言えます: *)

Lemma R_halts : forall {T} {t}, R T t -> halts t.
Proof.
  intros. destruct T; unfold R in H; inversion H; inversion H1;  assumption.
Qed.


Lemma R_typable_empty : forall {T} {t}, R T t -> has_type empty t T.
Proof.
  intros. destruct T; unfold R in H; inversion H; inversion H1; assumption.
Qed.

(* Now we proceed to show the main result, which is that every
well-typed term of type [T] is an element of [R_T].  Together with
[R_halts], that will show that every well-typed term halts in a
value.  *)
(** さて、メインの結果に進みます。
すべての型[T]の項が[R_T]の要素であることを示すことです。
[R_halts]と組み合わせると、すべての型付けされる項は停止して値になることが示されます。 *)


(* ###################################################################### *)
(* **  Membership in [R_T] is invariant under evaluation *)
(** **  [R_T] の要素であるか否かは評価によって変化しない *)

(* We start with a preliminary lemma that shows a kind of strong
preservation property, namely that membership in [R_T] is _invariant_
under evaluation. We will need this property in both directions,
i.e. both to show that a term in [R_T] stays in [R_T] when it takes a
forward step, and to show that any term that ends up in [R_T] after a
step must have been in [R_T] to begin with.

First of all, an easy preliminary lemma. Note that in the forward
direction the proof depends on the fact that our language is
determinstic. This lemma might still be true for non-deterministic
languages, but the proof would be harder! *)
(** 一種の強保存性を示す予備的補題から始めます。[R_T]の要素であるか否かは
評価によって「不変」(_invariant_)であるという補題です。
この性質は両方向が必要です。つまり、[R_T]の項がステップを進めても[R_T]にあることを示すことと、
ステップ後[R_T]の要素になる任意の項が最初から[R_T]であることを示すことです。

一番最初に、簡単な予備的補題です。
前向き方法については、言語が決定性を持つという事実に証明が依存していることに注意します。
この補題は非決定的な言語でも成立するかもしれませんが、証明はより難しくなるでしょう! *)

Lemma step_preserves_halting : forall t t', (t ==> t') -> (halts t <-> halts t').
Proof.
 intros t t' ST.  unfold halts.
 split.
 Case "->".
  intros [t'' [STM V]].
  inversion STM; subst.
   apply ex_falso_quodlibet.  apply value__normal in V. unfold normal_form in V. apply V. exists t'. auto.
   rewrite (step_deterministic _ _ _ ST H). exists t''. split; assumption.
 Case "<-".
  intros [t'0 [STM V]].
  exists t'0. split; eauto.
Qed.

(* Now the main lemma, which comes in two parts, one for each
   direction.  Each proceeds by induction on the structure of the type
   [T].  In fact, this is where we make fundamental use of the
   finiteness of types.

   One requirement for staying in [R_T] is to stay in type [T]. In the
   forward direction, we get this from ordinary type Preservation. *)
(** さてメインの補題ですが、2つの方向に対応する2つの部分から成ります。
   それぞれは型[T]の構造についての帰納法で進みます。
   事実、ここでは型の有限性を本質的な部分で使っています。

   ステップを進んだ結果が[R_T]の要素であるためには型[T]を持つことが必要です。
   このことは、前向き方向については、もともとの型保存から得られます。 *)

Lemma step_preserves_R : forall T t t', (t ==> t') -> R T t -> R T t'.
Proof.
 induction T;  intros t t' E Rt; unfold R; fold R; unfold R in Rt; fold R in Rt;
               destruct Rt as [typable_empty_t [halts_t RRt]].
  (* ty_Bool *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  auto.
  (* ty_arrow *)
  split. eapply preservation; eauto.
  split. apply (step_preserves_halting _ _ E); eauto.
  intros.
  eapply IHT2.
  apply  ST_App1. apply E.
  apply RRt; auto.
  (* FILL IN HERE *)(** ここを埋めなさい *) Admitted.


(* The generalization to multiple steps is trivial: *)
(** 複数ステップへの一般化については自明です: *)

Lemma stepmany_preserves_R : forall T t t',
  (t ==>* t') -> R T t -> R T t'.
Proof.
  intros T t t' STM; induction STM; intros.
  assumption.
  apply IHSTM. eapply step_preserves_R. apply H. assumption.
Qed.

(* In the reverse direction, we must add the fact that [t] has type
   [T] before stepping as an additional hypothesis. *)
(** 逆向き方向については、
   [t]がステップ前に型[T]を持つという事実を追加の仮定として加える必要があります。 *)

Lemma step_preserves_R' : forall T t t',
  has_type empty t T -> (t ==> t') -> R T t' -> R T t.
Proof.
  (* FILL IN HERE *)(** ここを埋めなさい *) Admitted.

Lemma stepmany_preserves_R' : forall T t t',
  has_type empty t T -> (t ==>* t') -> R T t' -> R T t.
Proof.
  intros T t t' HT STM.
  induction STM; intros.
    assumption.
    eapply step_preserves_R'.  assumption. apply H. apply IHSTM.
    eapply preservation;  eauto. auto.
Qed.

(* ###################################################################### *)
(* ** Closed instances of terms of type [T] belong to [R_T] *)
(** ** [R_T]に含まれる型[T]の項の閉じたインスタンス *)

(* Now we proceed to show that every term of type [T] belongs to
[R_T].  Here, the induction will be on typing derivations (it would be
surprising to see a proof about well-typed terms that did not
somewhere involve induction on typing derivations!).  The only
technical difficulty here is in dealing with the abstraction case.
Since we are arguing by induction, the demonstration that a term
[tm_abs x T1 t2] belongs to [R_(T1->T2)] should involve applying the
induction hypothesis to show that [t2] belongs to [R_(T2)].  But
[R_(T2)] is defined to be a set of _closed_ terms, while [t2] may
contain [x] free, so this does not make sense.

This problem is resolved by using a standard trick to suitably
generalize the induction hypothesis: instead of proving a statement
involving a closed term, we generalize it to cover all closed
_instances_ of an open term [t].  Informally, the statement of the
lemma will look like this:

If [x1:T1,..xn:Tn |- t : T] and [v1,...,vn] are values such that
[R T1 v1], [R T2 v2], ..., [R Tn vn], then [R T ([v1/x1][v2/x2]...[vn/xn]t)].

The proof will proceed by induction on the typing derivation
[x1:T1,..xn:Tn |- t : T]; the most interesting case will be the one
for abstraction. *)
(** これから、型[T]のすべての項が[R_T]に含まれることを示すことに取りかかります。
ここで使う帰納法は型付け導出についてのものです
(もし、型付け導出の帰納法と全く関係がない型付けされた項についての証明があったら、
驚くでしょう!)。
ここで技術的に難しいのは、関数抽象の場合だけです。
帰納法で議論していることから、項 [tm_abs x T1 t2] が[R_(T1->T2)]に属していることを示すことには
[t2]が[R_(T2)]に属するという帰納法の仮定を含みます。
しかし[R_(T2)]は「閉じた」項の集合である一方、[t2]は[x]を自由変数として含む可能性があるので、
これは筋が通りません。

この問題は帰納法の仮定を適度に一般化するという標準的なトリックを使うことで解決されます。
閉じた項を含む主張を証明する代わりに、開いた項[t]のすべての閉じたインスタンス(_instances_)
をカバーするように一般化します。非形式的には、補題の主張は次のようになります:

もし [x1:T1,..xn:Tn |- t : T] かつ、 [v1,...,vn] が
[R T1 v1], [R T2 v2], ..., [R Tn vn] となる値ならば、
[R T ([v1/x1][v2/x2]...[vn/xn]t)] である。

証明は、型付け [x1:T1,..xn:Tn |- t : T] の導出についての帰納法で進みます。
一番興味深いのは、関数抽象の場合です。 *)

(* ###################################################################### *)
(* *** Multisubstitutions, multi-extensions, and instantiations *)
(** *** 多重置換、多重拡張、インスタンス化 *)

(* However, before we can proceed to formalize the statement and
proof of the lemma, we'll need to build some (rather tedious)
machinery to deal with the fact that we are performing _multiple_
substitutions on term [t] and _multiple_ extensions of the typing
context.  In particular, we must be precise about the order in which
the substitutions occur and how they act on each other.  Often these
details are simply elided in informal paper proofs, but of course Coq
won't let us do that. Since here we are substituting closed terms, we
don't need to worry about how one substitution might affect the term
put in place by another.  But we still do need to worry about the
_order_ of substitutions, because it is quite possible for the same
identifier to appear multiple times among the [x1,...xn] with
different associated [vi] and [Ti].

To make everything precise, we will assume that environments are
extended from left to right, and multiple substitutions are performed
from right to left.  To see that this is consistent, suppose we have
an environment written as [...,y:bool,...,y:nat,...]  and a
corresponding term substitution written as [...[(tm_bool
true)/y]...[(tm_nat 3)/y]...t].  Since environments are extended from
left to right, the binding [y:nat] hides the binding [y:bool]; since
substitutions are performed right to left, we do the substitution
[(tm_nat 3)/y] first, so that the substitution [(tm_bool true)/y] has
no effect. Substitution thus correctly preserves the type of the term.

With these points in mind, the following definitions should make sense.

A _multisubstitution_ is the result of applying a list of
substitutions, which we call an _environment_. *)
(** しかしながら、主張と補題の証明の形式化に進む前に、項[t]の多重置換(_multiple_
substitutions)と型付けコンテキストの多重拡張(_multiple_ extensions)
についての事実を扱う、ある(かなり退屈な)機構を構築する必要があります。
特に、置換が現れる順序とそれらの相互関係を正確にする必要があります。
これらの詳細は非形式的な紙の証明では単に省略されるのが通常です。
しかしもちろん、Coqはそうはしません。ここでは閉じた項を置換していることから、
1つの置換が他の置換によってできた項に影響するかどうかを心配する必要はありません。
しかしそれでも置換の順序については考慮する必要があります。
なぜなら、[x1,...xn]に同じ識別子が複数回出現しそれらが違う[vi]や[Ti]
と関連付けされている可能性があるからです。

すべてを正確にするために、環境は左から右へ拡張されることとし、
多重置換は右から左へ実行されることとします。
これが整合的であることを見るために、[...,y:bool,...,y:nat,...] と書かれる環境と、
対応する [...[(tm_bool true)/y]...[(tm_nat 3)/y]...t] 
と書かれる項の置換があるとします。
環境は左から右に拡張されることから、[y:nat]は[y:bool]を隠します。
置換は右から左に実行されることから、[(tm_nat 3)/y] が最初に実行され、
[(tm_bool true)/y] は何の作用もしません。
これから置換は項の型を正しく保存します。

このポイントを覚えておくと、次の定義が理解できます。

多重置換(_multisubstitution_)は置換のリストの適用結果です。
置換のリストは環境と呼ばれます(_environment_)。 *)

Definition env := list (id * tm).

Fixpoint msubst (ss:env) (t:tm) {struct ss} : tm :=
match ss with
| nil => t
| ((x,s)::ss') => msubst ss' (subst x s t)
end.

(* We need similar machinery to talk about repeated extension of a
    typing context using a list of (identifier, type) pairs, which we
    call a _type assignment_. *)
(** (識別子、型)の対のリストを使った型付けコンテキストの継続的拡張についても同様の機構が必要です。
    この型付けコンテキストを「型割当て」(_type assignment_)と呼びます。 *)

Definition tass := list (id * ty).

Fixpoint mextend (Gamma : context) (xts : tass) :=
  match xts with
  | nil => Gamma
  | ((x,v)::xts') => extend (mextend Gamma xts') x v
  end.

(* We will need some simple operations that work uniformly on
environments and type assigments *)
(** 環境と型割当てに同様にはたらくいくつかの簡単な操作が必要です。 *)

Fixpoint lookup {X:Set} (k : id) (l : list (id * X)) {struct l} : option X :=
  match l with
    | nil => None
    | (j,x) :: l' =>
      if beq_id j k then Some x else lookup k l'
  end.

Fixpoint drop {X:Set} (n:id) (nxs:list (id * X)) {struct nxs} : list (id * X) :=
  match nxs with
    | nil => nil
    | ((n',x)::nxs') => if beq_id n' n then drop n nxs' else (n',x)::(drop n nxs')
  end.

(* An _instantiation_ combines a type assignment and a value
   environment with the same domains, where corresponding elements are
   in R *)
(** インスタンス化(_instantiation_)は型割当てと値環境を同じ定義域で結合します。
   この定義域の要素はRに含まれます。 *)

Inductive instantiation :  tass -> env -> Prop :=
| V_nil : instantiation nil nil
| V_cons : forall x T v c e, value v -> R T v -> instantiation c e -> instantiation ((x,T)::c) ((x,v)::e).


(* We now proceed to prove various properties of these definitions. *)
(** これから、これらの定義についてのいろいろな性質を証明します。 *)

(* ###################################################################### *)
(* *** More Substitution Facts *)
(** *** 置換についてのさらなる事実 *)

(* First we need some additional lemmas on (ordinary) substitution. *)
(** 最初に(もともとの)置換について、ある追加の補題が必要です。 *)

Lemma vacuous_substitution : forall  t x,
     ~ appears_free_in x t  ->
     forall t', subst x t' t = t.
Proof with eauto.
  (* FILL IN HERE *)(** ここを埋めなさい *) Admitted.

Lemma subst_closed: forall t,
     closed t  ->
     forall x t', subst x t' t = t.
Proof.
  intros. apply vacuous_substitution. apply H.  Qed.


Lemma subst_not_afi : forall t x v, closed v ->  ~ appears_free_in x (subst x v t).
Proof with eauto.  (* rather slow this way *)
  unfold closed, not.
  tm_cases (induction t) Case; intros x v P A; simpl in A.
    Case "tm_var".
     remember (beq_id x i) as e; destruct e...
       inversion A; subst. rewrite <- beq_id_refl in Heqe; inversion Heqe.
    Case "tm_app".
     inversion A; subst...
    Case "tm_abs".
     remember (beq_id x i) as e; destruct e...
       apply beq_id_eq in Heqe; subst. inversion A; subst...
       inversion A; subst...
    Case "tm_pair".
     inversion A; subst...
    Case "tm_fst".
     inversion A; subst...
    Case "tm_snd".
     inversion A; subst...
    Case "tm_true".
     inversion A.
    Case "tm_false".
     inversion A.
    Case "tm_if".
     inversion A; subst...
Qed.


Lemma duplicate_subst : forall t' x t v,
  closed v -> subst x t (subst x v t') = subst x v t'.
Proof.
  intros. eapply vacuous_substitution. apply subst_not_afi.  auto.
Qed.

Lemma swap_subst : forall t x x1 v v1, x <> x1 -> closed v -> closed v1 ->
                   subst x1 v1 (subst x v t) = subst x v (subst x1 v1 t).
Proof with eauto.
 tm_cases (induction t) Case; intros; simpl.
  Case "tm_var".
   remember (beq_id x i) as e; destruct e; remember (beq_id x1 i) as e; destruct e.
      apply  beq_id_eq in Heqe. apply beq_id_eq in Heqe0. subst.
         apply ex_falso_quodlibet...
      apply beq_id_eq in Heqe; subst.  simpl.
         rewrite <- beq_id_refl.  apply subst_closed...
      apply beq_id_eq in Heqe0; subst.  simpl.
         rewrite <- beq_id_refl. rewrite subst_closed...
      simpl. rewrite <- Heqe. rewrite <- Heqe0...
  (* FILL IN HERE *)(** ここを埋めなさい *) Admitted.

(* ###################################################################### *)
(* *** Properties of multi-substitutions *)
(** *** 多重置換の性質 *)

Lemma msubst_closed: forall t, closed t -> forall ss, msubst ss t = t.
Proof.
  induction ss.
    reflexivity.
    destruct a. simpl. rewrite subst_closed; assumption.
Qed.

(* Closed environments are those that contain only closed terms. *)
(** 閉じた環境とは、閉じた項のみを含む環境です。 *)

Fixpoint closed_env (env:env) {struct env} :=
match env with
| nil => True
| (x,t)::env' => closed t /\ closed_env env'
end.

(* Next come a series of lemmas charcterizing how [msubst] of closed terms
    distributes over [subst] and over each term form *)
(** 次は、閉じた項についての[msubst]がどのように[subst]
    や各項の形に分配されるかを特徴づける一連の補題です。 *)

Lemma subst_msubst: forall env x v t, closed v -> closed_env env ->
  msubst env (subst x v t) = subst x v (msubst (drop x env) t).
Proof.
  induction env0; intros.
    auto.
    destruct a. simpl.
    inversion H0. fold closed_env in H2.
    remember (beq_id i x) as e; destruct e.
      apply  beq_id_eq in Heqe; subst.
        rewrite duplicate_subst; auto.
      symmetry in Heqe. apply beq_id_false_not_eq in Heqe.
      simpl. rewrite swap_subst; eauto.
Qed.


Lemma msubst_var:  forall ss x, closed_env ss ->
   msubst ss (tm_var x) =
   match lookup x ss with
   | Some t => t
   | None => tm_var x
  end.
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
     simpl. destruct (beq_id i x).
      apply msubst_closed. inversion H; auto.
      apply IHss. inversion H; auto.
Qed.

Lemma msubst_abs: forall ss x T t,
  msubst ss (tm_abs x T t) = tm_abs x T (msubst (drop x ss) t).
Proof.
  induction ss; intros.
    reflexivity.
    destruct a.
      simpl. destruct (beq_id i x); simpl; auto.
Qed.

Lemma msubst_app : forall ss t1 t2, msubst ss (tm_app t1 t2) = tm_app (msubst ss t1) (msubst ss t2).
Proof.
 induction ss; intros.
   reflexivity.
   destruct a.
    simpl. rewrite <- IHss. auto.
Qed.

(* You'll need similar functions for the other term constructors. *)
(** 他の項コンストラクタに対しても同様の関数が必要になるでしょう。 *)

(* FILL IN HERE *)
(** ここを埋めなさい *)

(* ###################################################################### *)
(* *** Properties of multi-extensions *)
(** *** 多重拡張の性質 *)

(* We need to connect the behavior of type assignments with that of their
   corresponding contexts. *)
(** 型割当てのふるまいを、対応するコンテキストのふるまいと結合する必要があります。 *)

Lemma mextend_lookup : forall (c : tass) (x:id), lookup x c = (mextend empty c) x.
Proof.
  induction c; intros.
    auto.
    destruct a. unfold lookup, mextend, extend. destruct (beq_id i x); auto.
Qed.

Lemma mextend_drop : forall (c: tass) Gamma x x',
       mextend Gamma (drop x c) x' = if beq_id x x' then Gamma x' else mextend Gamma c x'.
   induction c; intros.
      destruct (beq_id x x'); auto.
      destruct a. simpl.
      remember (beq_id i x) as e; destruct e.
        apply beq_id_eq in Heqe; subst. rewrite IHc.
            remember (beq_id x x') as e; destruct e.  auto. unfold extend. rewrite <- Heqe. auto.
        simpl.  unfold extend.  remember (beq_id i x') as e; destruct e.
            apply beq_id_eq in Heqe0; subst.
                              remember (beq_id x x') as e; destruct e.
                  apply beq_id_eq in Heqe0; subst.  rewrite <- beq_id_refl in Heqe.  inversion Heqe.
                  auto.
            auto.
Qed.


(* ###################################################################### *)
(* *** Properties of Instantiations *)
(** *** インスタンス化の性質 *)

(* These are strightforward. *)
(** 以下は簡単です。 *)

Lemma instantiation_domains_match: forall {c} {e},
  instantiation c e -> forall {x} {T}, lookup x c = Some T -> exists t, lookup x e = Some t.
Proof.
  intros c e V. induction V; intros x0 T0 C.
    solve by inversion .
    simpl in *.
    destruct (beq_id x x0); eauto.
Qed.

Lemma instantiation_env_closed : forall c e,  instantiation c e -> closed_env e.
Proof.
  intros c e V; induction V; intros.
    econstructor.
    unfold closed_env. fold closed_env.
    split.  eapply typable_empty__closed. eapply R_typable_empty. eauto.
        auto.
Qed.

Lemma instantiation_R : forall c e, instantiation c e ->
                        forall x t T, lookup x c = Some T ->
                                      lookup x e = Some t -> R T t.
Proof.
  intros c e V. induction V; intros x' t' T' G E.
    solve by inversion.
    unfold lookup in *.  destruct (beq_id x x').
      inversion G; inversion E; subst.  auto.
      eauto.
Qed.

Lemma instantiation_drop : forall c env,
  instantiation c env -> forall x, instantiation (drop x c) (drop x env).
Proof.
  intros c e V. induction V.
    intros.  simpl.  constructor.
    intros. unfold drop. destruct (beq_id x x0); auto. constructor; eauto.
Qed.


(* ###################################################################### *)
(* *** Congruence lemmas on stepmany *)
(** *** stepmany([==>*])についての合同補題 *)

(* We'll need just a few of these; add them as the demand arises. *)
(** これらのいくつかだけが必要になります。必要が生じた時点で追加しなさい。 *)

Lemma stepmany_App2 : forall v t t',
  value v -> (t ==>* t') -> (tm_app v t) ==>* (tm_app v t').
Proof.
  intros v t t' V STM. induction STM.
   apply rsc_refl.
   eapply rsc_step.
     apply ST_App2; eauto.  auto.
Qed.

(* FILL IN HERE *)
(** ここを埋めなさい *)

(* ###################################################################### *)
(* *** The R Lemma. *)
(** *** R補題 *)

(* We finally put everything together.

    The key lemma about preservation of typing under substitution can
    be lifted to multi-substitutions: *)
(** 最後にすべてをまとめます。

    置換についての型付けの保存についてのキーとなる補題は、
    多重置換に対応する形にすることができます: *)

Lemma msubst_preserves_typing : forall c e,
     instantiation c e ->
     forall Gamma t S, has_type (mextend Gamma c) t S ->
     has_type Gamma (msubst e t) S.
Proof.
  induction 1; intros.
    simpl in H. simpl. auto.
    simpl in H2.  simpl.
    apply IHinstantiation.
    eapply substitution_preserves_typing; eauto.
    apply (R_typable_empty H0).
Qed.

(* And at long last, the main lemma. *)
(** そして一番最後に、メインの補題です。 *)

Lemma msubst_R : forall c env t T,
  has_type (mextend empty c) t T -> instantiation c env -> R T (msubst env t).
Proof.
  intros c env0 t T HT V.
  generalize dependent env0.
  (* We need to generalize the hypothesis a bit before setting up the induction. *)
  remember (mextend empty c) as Gamma.
  assert (forall x, Gamma x = lookup x c).
    intros. rewrite HeqGamma. rewrite mextend_lookup. auto.
  clear HeqGamma.
  generalize dependent c.
  has_type_cases (induction HT) Case; intros.

  Case "T_Var".
   rewrite H0 in H. destruct (instantiation_domains_match V H) as [t P].
   eapply instantiation_R; eauto.
   rewrite msubst_var.  rewrite P. auto. eapply instantiation_env_closed; eauto.

  Case "T_Abs".
    rewrite msubst_abs.
    (* We'll need variants of the following fact several times, so its simplest to
       establish it just once. *)
    assert (WT: has_type empty (tm_abs x T11 (msubst (drop x env0) t12)) (ty_arrow T11 T12)).
     eapply T_Abs. eapply msubst_preserves_typing.  eapply instantiation_drop; eauto.
      eapply context_invariance.  apply HT.
      intros.
      unfold extend. rewrite mextend_drop. remember (beq_id x x0) as e; destruct e.  auto.
        rewrite H.
          clear - c Heqe. induction c.
              simpl.  rewrite <- Heqe.  auto.
              simpl. destruct a.  unfold extend. destruct (beq_id i x0); auto.
    unfold R. fold R. split.
       auto.
     split. apply value_halts. apply v_abs.
     intros.
     destruct (R_halts H0) as [v [P Q]].
     pose proof (stepmany_preserves_R _ _ _ P H0).
     apply stepmany_preserves_R' with (msubst ((x,v)::env0) t12).
       eapply T_App. eauto.
       apply R_typable_empty; auto.
       eapply rsc_trans.  eapply stepmany_App2; eauto.
       eapply rsc_R.
       simpl.  rewrite subst_msubst.
       eapply ST_AppAbs; eauto.
       eapply typable_empty__closed.
       apply (R_typable_empty H1).
       eapply instantiation_env_closed; eauto.
       eapply (IHHT ((x,T11)::c)).
          intros. unfold extend, lookup. destruct (beq_id x x0); auto.
       constructor; auto.

  Case "T_App".
    rewrite msubst_app.
    destruct (IHHT1 c H env0 V) as [_ [_ P1]].
    pose proof (IHHT2 c H env0 V) as P2.  fold R in P1.  auto.

  (* FILL IN HERE *)(** ここを埋めなさい *) Admitted.

(* ###################################################################### *)
(* *** Normalization Theorem *)
(** *** 正規化定理 *)

Theorem normalization : forall t T, has_type empty t T -> halts t.
Proof.
  intros.
  replace t with (msubst nil t).
  eapply R_halts.
  eapply msubst_R; eauto. instantiate (2:= nil). eauto.
  eapply V_nil.
  auto.
Qed.

