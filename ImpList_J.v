(** * ImpList_J: Imp のリスト拡張 *)
(* * ImpList: Imp Extended with Lists *)

Require Export SfLib_J.

(* ####################################################### *)
(* * Imp Programs with Lists *)
(** * リストを持つ Imp プログラム *)

(* There are only so many numeric functions with interesting
    properties that have simple proofs.  (Of course, there are lots of
    interesting functions on numbers and they have many interesting
    properties -- this is the whole field of number theory! -- but
    proving these properties often requires developing a lot of
    supporting lemmas.)  In order to able to write a few more programs
    to reason about, we introduce here an extended version of Imp
    where variables can range over both numbers and lists of numbers.
    The basic operations are extended to also include taking the head
    and tail of lists, and testing lists for nonemptyness.

    To do this, we only need to change the definitions of [state],
    [aexp], [aeval], [bexp], and [beval]. The definitions of [com] and
    [ceval] can be reused verbatim, although we need to copy-and-paste
    them in the context of the new definitions.

    We start by repeating some material from [Imp.v]. *)
(** 興味深い性質とその簡単な証明を併せ持つ数値関数はそんなにたくさんはありません。
    (もちろん、興味深い数値関数はたくさんあり、
    それらはいろいろなおもしろい性質を持っています。
    なんといっても数論全体なのです!
    しかし大抵の場合、その性質の証明には、たくさんの補題が必要となるのです。)
    推論対象として、あといくつかのプログラムを書くことができるようにするために、
    Impの拡張版を導入します。拡張版では、変数は数値だけでなく数値のリストも変域とします。
    基本操作には、リストの先頭(head)と後部(tail)を取る操作、
    リストが空か否かを判定する操作が拡張されます。

    このためには、[state]、[aexp]、[aeval]、[bexp]、[beval]
    の定義を変えるだけで良いのです。
    [com]と[ceval]は字面上の変更なく再利用できます。
    ただ、新しい定義の中にコピー&ペーストしてやる必要はありますが。

    [Imp_J.v]の素材を繰り返すことから始めましょう。 *)

(* ** Repeated Definitions *)
(** ** 定義の繰り返し *)

Inductive id : Type :=
  Id : nat -> id.

Definition beq_id id1 id2 :=
  match (id1, id2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Theorem beq_id_refl : forall i,
  true = beq_id i i.
Proof.
  intros. destruct i.
  apply beq_nat_refl.  Qed.

Theorem beq_id_eq : forall i1 i2,
  true = beq_id i1 i2 -> i1 = i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_eq in H. subst.
  reflexivity.  Qed.

Theorem beq_id_false_not_eq : forall i1 i2,
  beq_id i1 i2 = false -> i1 <> i2.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  apply beq_nat_false in H.
  intros C. apply H. inversion C. reflexivity.  Qed.

Theorem not_eq_beq_id_false : forall i1 i2,
  i1 <> i2 -> beq_id i1 i2 = false.
Proof.
  intros i1 i2 H.
  destruct i1. destruct i2.
  assert (n <> n0).
    intros C. subst. apply H. reflexivity.
  apply not_eq_beq_false. assumption.  Qed.

Definition X : id := Id 0.
Definition Y : id := Id 1.
Definition Z : id := Id 2.

(* ** Extensions *)
(** ** 拡張 *)

(* Now we come to the key changes.

    Rather than evaluating to a [nat], an [aexp] in our new language
    will evaluate to a _value_ -- an element of type [val] -- which
    can be either a [nat] or a list of [nat]s.

    Similarly, [state]s will now map identifiers to [val]s rather than
    [nat]s, so that we can store lists in mutable variables. *)
(** 一番の変更点にかかります。

    新しい言語では、[aexp]の評価は[nat]になるのではなく、値(_value_、型[val]の要素)
    になります。値は、[nat]か、または[nat]のリストです。    

    同様に、[state]は識別子を[nat]ではなく[val]にマッピングします。
    それによって、リストを数値と同じ変数に格納できるのです。*)

Inductive val : Type :=
| VNat : nat -> val
| VList : list nat -> val.

Definition state := id -> val.

Definition empty_state : state := fun _ => VNat 0.
Definition update (st : state) (V:id) (n : val) : state :=
  fun V' => if beq_id V V' then n else st V'.

(* Imp does not have a static type system, so nothing prevents the
    programmer from e.g. adding two lists or taking the head of a
    number. We have to decide what to do in such nonsensical
    situations.

    We adopt a simple solution: if an arithmetic function is given a
    list as an argument we treat the list as if it was the number
    [0]. Similarly, if a list function is given a number as an
    argument we treat the number as if it was [nil].  (Cf. Javascript,
    where adding [3] to the empty list evaluates to [3]...)

    The two functions [asnat] and [aslist] interpret [val]s in a
    numeric or a list context; [aeval] calls these whenever it
    evaluates an arithmetic or a list operation.*)
(** Impには静的型システムがありません。
    そのため、プログラマが2つのリストを足したり、
    数値の先頭をとったりすることを防ぐことはできません。
    そういう不条理な状況をどうするかを決めなければなりません。

    これに対しては次のようなシンプルなやり方を採用します。
    もし算術関数が引数としてリストを受けとったときには、
    そのリストを数値[0]として扱います。
    同様に、もしリスト関数が数値を引数として受けとったときには、
    その数値を[nil]として扱います。
    (Javascript参照。Javascriptでは[3]を空リストに足すと[3]になる...)

    2つの関数[asnat]と[aslist]は、[val]をそれぞれ数値およびリストのコンテキストで解釈します。
    [aeval]は、数値操作またはリスト操作を評価するときには常に、
    [asnat]や[aslist]を呼びます。*)

Definition asnat (v : val) : nat :=
  match v with
  | VNat n => n
  | VList _ => 0
  end.

Definition aslist (v : val) : list nat :=
  match v with
  | VNat n => []
  | VList xs => xs
  end.

(* Now we fill in the definitions of abstract syntax and
    evaluation functions for arithmetic and boolean expressions. *)
(** ここで、算術式とブール式について、
    抽象構文と評価関数の定義の足りないところを埋めます。*)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | AId : id -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp
  (* Four new cases: *)
  | AHead : aexp -> aexp
  | ATail : aexp -> aexp
  | ACons : aexp -> aexp -> aexp
  | ANil  : aexp.

Tactic Notation "aexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "ANum" | Case_aux c "AId" | Case_aux c "APlus"
  | Case_aux c "AMinus" | Case_aux c "AMult"
  | Case_aux c "AHead" | Case_aux c "ATail"
  | Case_aux c "ACons" | Case_aux c "ANil" ].

Definition tail (l : list nat) :=
  match l with
  | x::xs => xs
  | [] => []
  end.

Definition head (l : list nat) :=
  match l with
  | x::xs => x
  | [] => 0
  end.

Fixpoint aeval (st : state) (e : aexp) : val :=
  match e with
  | ANum n => VNat n
  | AId i => st i
  | APlus a1 a2   => VNat (asnat (aeval st a1) + asnat (aeval st a2))
  | AMinus a1 a2  => VNat (asnat (aeval st a1) - asnat (aeval st a2))
  | AMult a1 a2   => VNat (asnat (aeval st a1) * asnat (aeval st a2))
  (* Four new cases: *)
  | ATail a => VList (tail (aslist (aeval st a)))
  | AHead a => VNat (head (aslist (aeval st a)))
  | ACons a1 a2 => VList (asnat (aeval st a1) :: aslist (aeval st a2))
  | ANil => VList []
  end.

(* We extend [bexp]s with an operation to test if a list is nonempty
    and adapt [beval] acordingly. *)
(** [bexp]を拡張して、リストが空かどうかをテストする操作を追加します。
    また、[beval]をそれに合わせて変更します。*)

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp
  (* New case: *)
  | BIsCons : aexp -> bexp.

Tactic Notation "bexp_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "BTrue" | Case_aux c "BFalse" | Case_aux c "BEq"
  | Case_aux c "BLe" | Case_aux c "BNot" | Case_aux c "BAnd"
  | Case_aux c "BIsCons" ].

Fixpoint beval (st : state) (e : bexp) : bool :=
  match e with
  | BTrue       => true
  | BFalse      => false
  | BEq a1 a2   => beq_nat (asnat (aeval st a1)) (asnat (aeval st a2))
  | BLe a1 a2   => ble_nat (asnat (aeval st a1)) (asnat (aeval st a2))
  | BNot b1     => negb (beval st b1)
  | BAnd b1 b2  => andb (beval st b1) (beval st b2)
  (* New case: *)
  | BIsCons a    => match aslist (aeval st a) with
                     | _::_ => true
                     | [] => false
                   end
  end.

(* ** Repeated Definitions *)
(** ** 定義の繰り返し *)

(* Now we need to repeat a little bit of low-level work from Imp.v,
    plus the definitions of [com] and [ceval].  There are no
    interesting changes -- it's just a matter of repeating the same
    definitions, lemmas, and proofs in the context of the new
    definitions of arithmetic and boolean expressions.

    (Is all this cutting and pasting really necessary?  No: Coq
    includes a powerful module system that we could use to abstract
    the repeated definitions with respect to the varying parts.  But
    explaining how it works would distract us from the topic at hand.)
 *)
(** ここで、Imp_J.vから低レベルの仕事を少々と、
    [com]と[ceval]の定義を繰り返さなければなりません。
    おもしろみのある変化は何もありません。
    算術式とブール式の新しい定義のコンテキストで、同じ定義、同じ補題、
    同じ証明を繰り返すだけです。

    (このカット&ペーストは本当に必要なのでしょうか？ 
     答えはNoです。Coq には強力なモジュールシステムがあって、
     変化する部分に関する同じ定義を抽象化することもできます。
     ただ、その説明をここですると、主題から逸れていってしまいます。)
 *)

Theorem update_eq : forall n V st,
  (update st V n) V = n.
Proof.
  intros n V st.
  unfold update.
  rewrite <- beq_id_refl.
  reflexivity.
Qed.

Theorem update_neq : forall V2 V1 n st,
  beq_id V2 V1 = false ->
  (update st V2 n) V1 = (st V1).
Proof.
  intros V2 V1 n st Hneq.
  unfold update.
  rewrite -> Hneq.
  reflexivity. Qed.

Theorem update_shadow : forall x1 x2 k1 k2 (f : state),
   (update  (update f k2 x1) k2 x2) k1 = (update f k2 x2) k1.
Proof.
  intros x1 x2 k1 k2 f.
  unfold update.
  destruct (beq_id k2 k1); reflexivity.  Qed.

Theorem update_same : forall x1 k1 k2 (f : state),
  f k1 = x1 ->
  (update f k1 x1) k2 = f k2.
Proof.
  intros x1 k1 k2 f Heq.
  unfold update. subst.
  remember (beq_id k1 k2) as b.
  destruct b.
  Case "true".
    apply beq_id_eq in Heqb. subst. reflexivity.
  Case "false".
    reflexivity.  Qed.

Theorem update_permute : forall x1 x2 k1 k2 k3 f,
  beq_id k2 k1 = false ->
  (update (update f k2 x1) k1 x2) k3 = (update (update f k1 x2) k2 x1) k3.
Proof.
  intros x1 x2 k1 k2 k3 f H.
  unfold update.
  remember (beq_id k1 k3) as b13.
  remember (beq_id k2 k3) as b23.
  apply beq_id_false_not_eq in H.
  destruct b13; try reflexivity.
  Case "true".
    destruct b23; try reflexivity.
    SCase "true".
      apply beq_id_eq in Heqb13.
      apply beq_id_eq in Heqb23.
      subst. apply ex_falso_quodlibet. apply H. reflexivity.  Qed.

(* We can keep exactly the same old definitions of [com] and
    [ceval]. *)
(** [com]と[ceval]の定義は、前とまったく同じで済みます。*)

Inductive com : Type :=
  | CSkip : com
  | CAss : id -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Tactic Notation "com_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "SKIP" | Case_aux c "::=" | Case_aux c ";"
  | Case_aux c "IFB" | Case_aux c "WHILE" ].

Notation "'SKIP'" :=
  CSkip.
Notation "l '::=' a" :=
  (CAss l a) (at level 60).
Notation "c1 ; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' e1 'THEN' e2 'ELSE' e3 'FI'" :=
  (CIf e1 e2 e3) (at level 80, right associativity).

Reserved Notation "c1 '/' st '||' st'" (at level 40, st at level 39).

Inductive ceval : state -> com -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st || st
  | E_Asgn  : forall st a1 n l,
      aeval st a1 = n ->
      (l ::= a1) / st || (update st l n)
  | E_Seq : forall c1 c2 st st' st'',
      c1 / st  || st' ->
      c2 / st' || st'' ->
      (c1 ; c2) / st || st''
  | E_IfTrue : forall st st' b1 c1 c2,
      beval st b1 = true ->
      c1 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_IfFalse : forall st st' b1 c1 c2,
      beval st b1 = false ->
      c2 / st || st' ->
      (IFB b1 THEN c1 ELSE c2 FI) / st || st'
  | E_WhileEnd : forall b1 st c1,
      beval st b1 = false ->
      (WHILE b1 DO c1 END) / st || st
  | E_WhileLoop : forall st st' st'' b1 c1,
      beval st b1 = true ->
      c1 / st || st' ->
      (WHILE b1 DO c1 END) / st' || st'' ->
      (WHILE b1 DO c1 END) / st || st''

  where "c1 '/' st '||' st'" := (ceval st c1 st').

Tactic Notation "ceval_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "E_Skip" | Case_aux c "E_Asgn" | Case_aux c "E_Seq"
  | Case_aux c "E_IfTrue" | Case_aux c "E_IfFalse"
  | Case_aux c "E_WhileEnd" | Case_aux c "E_WhileLoop" ].

Definition loop : com :=
  WHILE BTrue DO
    SKIP
  END.

Theorem loop_never_stops : forall st st',
  ~(loop / st || st').
Proof.
  intros st st' contra. unfold loop in contra.
  remember (WHILE BTrue DO SKIP END) as loopdef.
  ceval_cases (induction contra) Case; try (inversion Heqloopdef).
    Case "E_WhileEnd".
      rewrite -> H1 in H. inversion H.
    Case "E_WhileLoop".
      apply IHcontra2. subst. reflexivity.  Qed.
