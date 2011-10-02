(** * Rel:関係の性質 *)
   
   
(* $Date: 2011-03-21 10:44:46 -0400 (Mon, 21 Mar 2011) $ *)


(** この短い章では、いくつかの基本的な定義を行います。それらは後に[Smallstep_J.v]における
    小ステップ操作的意味論で必要となるものです。[Smallstep_J.v]の直前まで手を
    つけないでおくこともできますが、Coqの基本的推論機構を使う良い練習問題ともなるので、
    [Logic_J.v]の直後で見ておくのがよいかもしれません。 *)

Require Export Logic_J.

(** 関係(_relation_)はパラメータを持った命題にほかなりません。
    大学の離散数学の講義で習っているように、関係を`一般的に'議論し記述する方法がいくつもあります。
    -- 関係を分類する方法(反射的か、推移的か、などなど)、関係のクラスについて一般的に証明できる定理、
    関係からの別の関係の構成、などなどです。ここでちょっと立ち止まって、後で有用になる
    いくつかをふりかえってみましょう。 *)

(** 集合[X]の`上の'関係は、[X]2つをパラメータとする関係です。-- つまり、集合[X]の2つの要素に
    関する論理的主張です。*)

Definition relation (X: Type) := X->X->Prop.

(** 若干まぎらわしいことに、Coqの標準ライブラリでは、一般的な用語"関係(relation)"を
    この特定の場合(つまり1つの集合上の二項関係)を指すためだけに使っています。
    ライブラリとの整合性を保つために、ここでもそれに従います。
    したがって、Coq の識別子[relation]は常に、集合上の二項関係を指すために使います。
    一方、日本語の"関係"は、Coq の relation を指す場合もあれば、より一般の
    任意の数の(それぞれ別のものかもしれない)集合の間の関係を指す場合もあります。
    どちらを指しているかは常に議論の文脈から明らかになるようにします。 *)

(* ######################################################### *)
(** * 関係の基本性質 *)

(** 集合[X]上の関係[R]は、次の条件を満たすとき、部分関数(_partial function_)です。
    条件とは、すべての[x]に対して、[R x y]となる[y]は高々1つであるということです。
    -- つまり、[R x y1]かつ[R x y2]ならば [y1 = y2] となることです。*)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(** 例えば、Logic_J.vで定義されている[next_nat]関係は部分関数です。*)

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 P Q.
  inversion P. inversion Q.
  reflexivity.  Qed.

(** しかし、数値上の[<=]関係は部分関数ではありません。

    これは矛盾を導くことで示すことができます。簡単にいうと: [<=]が部分関数であると仮定します。
    すると、[0<=0]かつ[0<=1]から、[0=1]となります。これはおかしなことです。したがって、
    [<=]が部分関数だという仮定は矛盾するということになります。*)

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros H.
  assert (0 = 1) as Nonsense.
   Case "Proof of assertion".
   apply H with 0.
     apply le_n.
     apply le_S. apply le_n.
  inversion Nonsense.   Qed.

(** **** 練習問題:★★, optional *)
(** Logic_J.v に定義された [total_relation] が部分関数ではないことを示しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(** **** 練習問題:★★, optional *)
(** Logic_J.v に定義された [empty_relation] が部分関数ではないことを示しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(** 集合[X]上の反射的(_reflexive_)関係とは、[X]のすべての要素について、成立する関係です。
    (訳注: 集合[X]上の関係[R]が反射的とは、[X]の任意の要素 [x]について [R x x]が成立
     することです。)    *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.

(** 関係[R]が推移的(_transitive_)であるとは、[R a b]かつ[R b c]ならば常に[R a c]
    となることです。*)

Definition transitive {X: Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo.  Qed.

Theorem lt_trans:
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo. Qed.

(** **** 練習問題:★★, optional *)
(** [lt_trans] は、帰納法を使って手間をかければ、le_trans を使わずに証明することができます。
    これをやってみなさい。*)


Theorem lt_trans' :
  transitive lt.
Proof.
  (* [m]が[o]より小さい、というエビデンスについての帰納法で証明する *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題:★★, optional *)
(** 同じことを、[o]についての帰納法で証明しなさい。*)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** [le]の推移性は、同様に、後に(つまり以下の反対称性の証明において)
    有用な事実を証明するのに使うことができます... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H.  Qed.

(** **** 練習問題:★, optional *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題:★★, optional(le_Sn_n_inf) *)
(** 以下の定理のインフォーマルな証明を示しなさい。

    定理: すべての[n]について、[~(S n <= n)]

    フォーマルな証明は後のoptionalな練習問題ですが、
    ここでは、フォーマルな証明を行わずに、まずインフォーマルな証明を示しなさい。 

    証明:
    (* FILL IN HERE *)
    []
  *)

(** **** 練習問題:★, optional *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 反射性と推移性は後の章で必要となる主要概念ですが、Coq で関係を扱う練習をもう少ししましょう。
    次のいくつかの概念もよく知られたものです。

    関係[R]が対象的(_symmetric_)であるとは、[R a b]ならば[R b a]となることです。 *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** **** 練習問題:★★, optional *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 関係[R]が反対称的(_antisymmetric_)であるとは、[R a b]かつ[R b a]ならば
    [a = b] となることです。 -- つまり、[R]における「閉路」は自明なものしかないということです。
    (訳注:この「つまり」以降は、[R]は反射的かつ推移的でもあるという前提の場合。)
    *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** 練習問題:★★, optional *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題:★★, optional *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** 関係が同値関係(_equivalence_)であるとは、その関係が、
    反射的、対称的、かつ推移的であることです。 *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(** 関係が半順序(_partial order_)であるとは、その関係が、
    推移的、反対称的、かつ推移的であることです。
    Coq 標準ライブラリでは、半順序のことを単に"順序(order)"と呼びます。*)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** 前順序(preorder)とは、半順序の条件から反対称性を除いたものです。*)

Definition preorder {X:Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
    Case "refl". apply le_reflexive.
    split.
      Case "antisym". apply le_antisymmetric.
      Case "transitive.". apply le_trans.  Qed.

(* ########################################################### *)
(** * 反射推移閉包 *)

(** 関係[R]の反射推移閉包とは、[R]を含み反射性と推移性の両者を満たす
    最小の関係のことです。フォーマルには、Coq標準ライブラリのRelationモジュールで、
    以下のように定義されます。*)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.

(** 例えば、[next_nat]関係の反射推移閉包は[le]関係となります。*)

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m. split.
    Case "->".
      intro H. induction H.
         apply rt_refl.
         apply rt_trans with m. apply IHle. apply rt_step. apply nn.
    Case "<-".
      intro H. induction H.
        SCase "rt_step".  inversion H. apply le_S.  apply le_n.
        SCase "rt_refl". apply le_n.
        SCase "rt_trans".
           apply le_trans with y.
           apply IHclos_refl_trans1.
           apply IHclos_refl_trans2.  Qed.

(** 上の反射推移閉包の定義は自然です。--定義は[R]の反射推移閉包が
    [R]を含み反射律と推移律について閉じている最小の関係であることを明示的に
    述べています。しかし、この定義は、証明をする際にはあまり便利ではないのです。
    -- rt_trans ルールの"非決定性"によって、しばしばわかりにくい帰納法になって
    しまいます。

    以下は、より使いやすい定義です... *)

Inductive refl_step_closure {X:Type} (R: relation X)
                            : X -> X -> Prop :=
  | rsc_refl  : forall (x : X),
                 refl_step_closure R x x
  | rsc_step : forall (x y z : X),
                    R x y ->
                    refl_step_closure R y z ->
                    refl_step_closure R x z.

(** (以下の[Tactic Notation]の定義は Imp_J.v で説明されます。
    その章をまだ読んでいないならば、ここではそれを無視して構いません。) *)

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rt_step" | Case_aux c "rt_refl"
  | Case_aux c "rt_trans" ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

(** 新しい反射推移閉包の定義は、[rtc_R]ルールと[rtc_trans]ルールを
    「まとめ」て、1ステップのルールにします。
    このステップの左側は[R]を1回だけ使います。このことが帰納法をはるかに簡単なものにします。

    次に進む前に、二つの定義が同じものを定義していることを確認しなければなりません...

    最初に、[rsc]が「失われた」2つの[rtc]構成子の働きを代替することを示す
    二つの補題を証明します。*)

Theorem rsc_R : forall (X:Type) (R:relation X) (x y : X),
       R x y -> refl_step_closure R x y.
Proof.
  intros X R x y r.
  apply rsc_step with y. apply r. apply rsc_refl.   Qed.

(** **** 練習問題:★★, optional(rsc_trans) *)
Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y  ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** そして、反射推移閉包の2つの定義が同じ関係を定義していることを証明するために、
    上記の事実を使います。*)

(** **** 練習問題:★★★, optional (rtc_rsc_coincide) *)
Theorem rtc_rsc_coincide :
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)
