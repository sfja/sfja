(** * Rel: Properties of Relations *)

(* $Date: 2011-03-21 10:44:46 -0400 (Mon, 21 Mar 2011) $ *)


(** This short chapter develops some basic definitions that will be
    needed when we come to working with small-step operational
    semantics in [Smallstep.v].  It can be postponed until just before
    [Smallstep.v], but it is also a good source of good exercises for
    developing facility with Coq's basic reasoning facilities, so it
    may be useful to look at it just after [Logic.v]. *)
(** この小さな章では、いくつかの基本的な定義を行います。それらは後に[Smallstep_J.v]における
    小ステップ操作的意味論で必要となるものです。[Smallstep_J.v]の直前まで手を
    つけないでおくこともできますが、Coqの基本的推論機構を使う良い練習問題ともなるので、
    [Logic_J.v]の直後で見ておくのがよいかもしれません。 *)

Require Export Logic_J.

(** A _relation_ is just a parameterized proposition.  As you know
    from your undergraduate discrete math course, there are a lot of
    ways of discussing and describing relations _in general_ -- ways
    of classifying relations (are they reflexive, transitive, etc.),
    theorems that can be proved generically about classes of
    relations, constructions that build one relation from another,
    etc.  Let us pause here to review a few that will be useful in
    what follows. *)
(** 関係(_relation_)はパラメータを持った命題にほかなりません。
    大学の離散数学の講義で習っているように、関係を`一般的に'議論し記述する方法がいくつもあります。
    -- 関係を分類する方法(反射的か、推移的か、などなど)、関係のクラスについて一般的に証明できる定理、
    関係からの別の関係の構成、などなどです。ここでちょっと立ち止まって、後で有用になる
    いくつかをふりかえってみましょう。 *)

(** A relation _on_ a set [X] is a proposition parameterized by two
    [X]s -- i.e., it is a logical assertion involving two values from
    the set [X].  *)
(** 集合[X]の`上の'関係は、[X]2つをパラメータとする関係です。-- つまり、集合[X]の2つの要素に
    関する論理的主張です。*)

Definition relation (X: Type) := X->X->Prop.

(** Somewhat confusingly, the Coq standard library hijacks the generic
    term "relation" for this specific instance. To maintain
    consistency with the library, we will do the same.  So, henceforth
    the Coq identifier [relation] will always refer to a binary
    relation between some set and itself, while the English word
    "relation" can refer either to the specific Coq concept or the
    more general concept of a relation between any number of possibly
    different sets.  The context of the discussion should always make
    clear which is meant. *)
(** 若干まぎらわしいことに、Coqの標準ライブラリでは、一般的な用語"関係(relation)"を
    この特定の場合(つまり1つの集合上の二項関係)を指すためだけに使っています。
    ライブラリとの整合性を保つために、ここでもそれに従います。
    したがって、Coq の識別子[relation]は常に、集合上の二項関係を指すために使います。
    一方、日本語の"関係"は、Coq の relation を指す場合もあれば、より一般の
    任意の数の(それぞれ別のものかもしれない)集合の間の関係を指す場合もあります。
    どちらを指しているかは常に議論の文脈から明らかになるようにします。 *)

(* ######################################################### *)
(** * Basic Properties of Relations *)
(** * 関係の基本性質 *)

(** A relation [R] on a set [X] is a _partial function_ if, for every
    [x], there is at most one [y] such that [R x y] -- i.e., if [R x
    y1] and [R x y2] together imply [y1 = y2]. *)
(** 集合[X]上の関係[R]は、次の条件を満たすとき、部分関数(_partial function_)です。
    条件とは、すべての[x]に対して、[R x y]となる[y]は高々1つであるということです。
    -- つまり、[R x y1]かつ[R x y2]ならば [y1 = y2] となることです。*)

Definition partial_function {X: Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

(** For example, the [next_nat] relation defined in Logic.v is a
    partial function. *)
(** 例えば、Logic.vで定義されている[next_nat]関係は部分関数です。*)

Theorem next_nat_partial_function :
   partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 P Q.
  inversion P. inversion Q.
  reflexivity.  Qed.

(** However, the [<=] relation on numbers is not a partial function.

    This can be shown by contradiction.  In short: Assume, for a
    contradiction, that [<=] is a partial function.  But then, since
    [0 <= 0] and [0 <= 1], it follows that [0 = 1].  This is nonsense,
    so our assumption was contradictory. *)
(** しかし、数値上の[<=]関係は部分関数ではありません。

    これは背理法で示すことができます。簡単にいうと: [<=]が部分関数であると仮定します。
    すると、[0<=0]かつ[0<=1]から、[0=1]となります。これはおかしなことです。したがって、
    [<=]が部分関数だという仮定は間違いということになります。*)

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

(** **** Exercise: 2 stars, optional *)
(** Show that the [total_relation] defined in Logic.v is not a partial
    function. *)
(** **** 練習問題:星二つ, オプショナル *)
(** Logic.v に定義された [total_relation] が部分関数ではないことを示しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** Show that the [empty_relation] defined in Logic.v is a partial
    function. *)
(** **** 練習問題:星二つ, オプショナル *)
(** Logic_J.v に定義された [empty_relation] が部分関数ではないことを示しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(** A _reflexive_ relation on a set [X] is one that holds for every
    element of [X]. *)
(** 集合[X]上の反射的(_reflexive_)関係とは、[X]のすべての要素について、成立する関係です。
    (訳注: 集合[X]上の関係[R]が反射的とは、[X]の任意の要素 [x]について [R x x]が成立
     することです。)    *)

Definition reflexive {X: Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.  Qed.

(** A relation [R] is _transitive_ if [R a c] holds whenever [R a b]
    and [R b c] do. *)
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

(** **** Exercise: 2 stars, optional *)
(** We can also prove [lt_trans] more laboriously by induction,
    without using le_trans.  Do this.*)
(** **** 練習問題:星二つ, オプショナル *)
(** [lt_trans] は、帰納法を使うと、(手間はかかるが)le_trans を使わずに証明することができる。
    これをやってみなさい。*)

Theorem lt_trans' :
  transitive lt.
Proof.
  (* Prove this by induction on evidence that [m] is less than [o]. *)
  (* [m]が[o]より小さい、というエビデンスについての帰納法で証明する *)
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
    (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** Prove the same thing again by induction on [o]. *)
(** **** 練習問題:星二つ, オプショナル *)
(** 同じことを、[o]についての帰納法で証明しなさい。*)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [| o'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** The transitivity of [le], in turn, can be used to prove some facts
    that will be useful later (e.g., for the proof of antisymmetry
    below)... *)
(** [le]の推移性は、同様に、後に(つまり以下の反対称性の証明において)
    有用な事実を証明するのに使うことができる... *)

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
    apply le_S. apply le_n.
    apply H.  Qed.

(** **** Exercise: 1 star, optional *)
(** **** 練習問題:星一つ, オプショナル *)
Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional (le_Sn_n_inf) *)
(** Provide an informal proof of the following theorem:

    Theorem: For every [n], [~(S n <= n)]

    A formal proof of this is an optional exercise below, but try
    the informal proof without doing the formal proof first.

    Proof:
    (* FILL IN HERE *)
    []
 *)
(** **** 練習問題:星二つ, オプショナル(le_Sn_n_inf) *)
(** 以下の定理のインフォーマルな証明を示しなさい。

    定理: すべての[n]について、[~(S n <= n)]

    フォーマルな証明は後のオプショナルな練習問題だが、
    ここでは、フォーマルな証明を行わずにまずインフォーマルな証明を示しなさい。 

    証明:
    (* FILL IN HERE *)
    []
  *)

(** **** Exercise: 1 star, optional *)
(** **** 練習問題:星一つ, オプショナル *)
Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Reflexivity and transitivity are the main concepts we'll need for
    later chapters, but, for a bit of additional practice working with
    relations in Coq, here are a few more common ones.

   A relation [R] is _symmetric_ if [R a b] implies [R b a]. *)
(** 反射性と推移性は後の章で必要となる主要概念ですが、Coq で関係を扱う練習をもう少ししましょう。
    次のいくつかの概念もよく知られたものです。

    関係[R]が対象的(_symmetric_)であるとは、[R a b]ならば[R b a]となることです。 *)

Definition symmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(** **** Exercise: 2 stars, optional *)
(** **** 練習問題:星二つ, オプショナル *)
Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** A relation [R] is _antisymmetric_ if [R a b] and [R b a] together
    imply [a = b] -- that is, if the only "cycles" in [R] are trivial
    ones. *)
(** 関係[R]が反対称的(_antisymmetric_)であるとは、[R a b]かつ[R b a]ならば
    [a = b] となることです。 -- つまり、[R]における「閉路」は自明なものしかないということです。
    (訳注:この「つまり」以降は、[R]は反射的かつ推移的でもあるという前提の場合。)
    *)

Definition antisymmetric {X: Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(** **** Exercise: 2 stars, optional *)
(** **** 練習問題:星二つ, オプショナル *)
Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, optional *)
(** **** 練習問題:星二つ, オプショナル *)
Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** A relation is an _equivalence_ if it's reflexive, symmetric, and
    transitive.  *)
(* 関係が同値関係(_equivalence_)であるとは、その関係が、
   反射的、対称的、かつ推移的であることです。 *)

Definition equivalence {X:Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

(** A relation is a _partial order_ when it's reflexive,
    _anti_-symmetric, and transitive.  In the Coq standard library
    it's called just "order" for short. *)
(** 関係が半順序(_partial order_)であるとは、その関係が、
    推移的、反対称的、かつ推移的であることです。
    Coq 標準ライブラリでは、半順序のことを単に"順序(order)"と呼びます。*)

Definition order {X:Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

(** A preorder is almost like a partial order, but doesn't have to be
    antisymmetric. *)
(* 前順序(preorder)とは、半順序の条件から反対称性を除いたものです。*)

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
(** * Reflexive, Transitive Closure *)
(** * 反射推移閉包 *)

(** The _reflexive, transitive closure_ of a relation [R] is the
    smallest relation that contains [R] and that is both reflexive and
    transitive.  Formally, it is defined like this in the Relations
    module of the Coq standard library: *)
(** * 関係[R]の反射推移閉包とは、[R]を含み反射性と推移性の両者を満たす
      最小の関係のことです。フォーマルには、Coq標準ライブラリのRelationモジュール
      で、以下のように定義されます。*)

Inductive clos_refl_trans {A: Type} (R: relation A) : relation A :=
    | rt_step : forall x y, R x y -> clos_refl_trans R x y
    | rt_refl : forall x, clos_refl_trans R x x
    | rt_trans : forall x y z,
          clos_refl_trans R x y -> clos_refl_trans R y z -> clos_refl_trans R x z.

(** For example, the reflexive and transitive closure of the
    [next_nat] relation coincides with the [le] relation. *)
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

(** The above definition of reflexive, transitive closure is
    natural -- it says, explicitly, that the reflexive and transitive
    closure of [R] is the least relation that includes [R] and that is
    closed under rules of reflexivity and transitivity.  But it turns
    out that this definition is not very convenient for doing
    proofs -- the "nondeterminism" of the rt_trans rule can sometimes
    lead to tricky inductions.

    Here is a more useful definition... *)
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

(** (The following [Tactic Notation] definitions are explained in
    Imp.v.  You can ignore them if you haven't read that chapter
    yet.) *)
(** (以下の[Tactic Notation]の定義は Imp_J.v で説明されます。
    その章をまだ読んでいないならば、ここではそれを無視して構いません。) *)

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rt_step" | Case_aux c "rt_refl"
  | Case_aux c "rt_trans" ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

(** Our new definition of reflexive, transitive closure "bundles"
    the [rtc_R] and [rtc_trans] rules into the single rule step.
    The left-hand premise of this step is a single use of [R],
    leading to a much simpler induction principle.

    Before we go on, we should check that the two definitions do
    indeed define the same relation...

    First, we prove two lemmas showing that [rsc] mimics the behavior
    of the two "missing" [rtc] constructors.  *)
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

(** **** Exercise: 2 stars, optional (rsc_trans) *)
(** **** 練習問題:星二つ, オプショナル(rsc_trans) *)
Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y  ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Then we use these facts to prove that the two definitions of
    reflexive, transitive closure do indeed define the same
    relation. *)
(** 次に、反射推移閉包の2つの定義が同じ関係を定義していることを証明するために、
    上記の事実を使います。*)

(** **** Exercise: 3 stars, optional (rtc_rsc_coincide) *)
Theorem rtc_rsc_coincide :
         forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

