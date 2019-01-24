(** * Lists_J: 直積、リスト、オプション *)
(* * Lists: Products, Lists and Options *)

(* $Date: 2011-06-22 10:06:32 -0400 (Wed, 22 Jun 2011) $ *)

(* The next line imports all of our definitions from the
    previous chapter. *)
(** 次の行を実行すると、前章の定義を一度にインポートすることができます。 *)

Require Export Basics_J.

(* For it to work, you need to use [coqc] to compile [Basics.v]
    into [Basics.vo].  (This is like making a .class file from a .java
    file, or a .o file from a .c file.)
  
    Here are two ways to compile your code:
  
     - CoqIDE:
   
         Open Basics.v.
         In the "Compile" menu, click on "Compile Buffer".
   
     - Command line:
   
         Run [coqc Basics.v]

    In this file, we again use the [Module] feature to wrap all of the
    definitions for pairs and lists of numbers in a module so that,
    later, we can reuse the same names for improved (generic) versions
    of the same operations. *)
(** ただしこれを使うには、 [coqc] を使って [Basics_J.v] をコンパイルし、 [Basics_J.vo] を作成しておく必要があります。（これは、 .java ファイルから .class ファイルを作ったり、 .c ファイルから .o ファイルを作ったりするのと同じことです。）

    コードをコンパイルする方法はふたつあります。

     - CoqIDE:

         Basics_J.v を開き、 "Compile" メニューの "Compile Buffer" をクリックする。

     - コマンドライン:

         [coqc Basics_J.v] を実行する。

    このファイルでも [Module] 機能を使って数のリストやペアの定義を囲んでおきます。こうしておくことで、同じ操作を改良した（一般化した）ものに同じ名前をつけることができます。
*)

Module NatList.


(* * Pairs of Numbers *)
(** * 数のペア *)

(* In an [Inductive] type definition, each constructor can take
    any number of parameters -- none (as with [true] and [O]), one (as
    with [S]), or more than one, as in this definition: *)
(**
   [Inductive] による型定義では、各構成子は任意の個数の引数を取ることができました。
   [true] や [O] のように引数のないもの、 [S] のようにひとつのもの、また、ふたつ以上の取るものも以下のように定義することができます。
   *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

(* This declaration can be read: "There is just one way to
    construct a pair of numbers: by applying the constructor [pair] to
    two arguments of type [nat]."

    Here are some simple function definitions illustrating pattern
    matching on two-argument constructors: *)
(**
   この定義は以下のように読めます。すなわち、「数のペアを構成する方法がただひとつある。それは、構成子 [pair] を [nat] 型のふたつの引数に適用することである」。

   次に示すのは二引数の構成子に対してパターンマッチをする簡単な関数の定義です。
   *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

(* Since pairs are used quite a bit, it is nice to be able to
    write them with the standard mathematical notation [(x,y)] instead
    of [pair x y].  We can tell Coq to allow this with a [Notation]
    declaration. *)
(**
   ペアはよく使うものなので、 [pair x y] ではなく、数学の標準的な記法で [(x, y)] と書けるとよいでしょう。このような記法を使うためには [Notation] 宣言を使います。
   *)

Notation "( x , y )" := (pair x y).

(* The new notation can be used both in expressions and in
    pattern matches (indeed, we've seen it already in the previous
    chapter -- this notation is provided as part of the standard
    library): *)
(** こうして定義した新しい記法（notation）は、式だけでなくパターンマッチに使うこともできます。（実際には、前章でも見たように、この記法は標準ライブラリの一部として提供されています。） *)

Eval simpl in (fst (3,4)).

Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.

(* Let's try and prove a few simple facts about pairs.  If we
    state the lemmas in a particular (and slightly peculiar) way, we
    can prove them with just reflexivity (and its built-in
    simplification): *)
(**
   それでは、数のペアに関する簡単な事実をいくつか証明してみましょう。補題を一定の（一種独特な）形式で書いておけば、単に reflexivity（と組み込みの簡約）だけで証明することができます。
   *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(* But reflexivity is not enough if we state the lemma in a more
    natural way: *)
(** しかし、補題を以下のようにより自然な書き方をした場合は、反射律では足りません。 *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* なにも変わらない！ *)
Admitted.

(* We have to expose the structure of [p] so that [simpl] can
    perform the pattern match in [fst] and [snd].  We can do this with
    [destruct].

    Notice that, unlike for [nat]s, [destruct] doesn't generate an
    extra subgoal here.  That's because [natprod]s can only be
    constructed in one way.  *)
(** [simpl] で [fst] や [snd] の中のパターンマッチを実行できるよう、 [p] の構造を明らかにする必要があります。これには [destruct] を使います。

   [nat] の場合と異なり、 [destruct] でサブゴールが増えることはありません。これは、 [natprod] の構成法がひとつしかないからです。
   *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as (n,m).  simpl.  reflexivity.  Qed.

(* Notice that Coq allows us to use the notation we introduced
    for pairs in the "[as]..." pattern telling it what variables to
    bind. *)
(**
   先ほど宣言した記法を "[as] ..." パターンで束縛する変数を指定するために使っています。
   *)

(* **** Exercise: 1 star (snd_fst_is_swap) *)
(** **** 練習問題: ★ (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* * Lists of Numbers *)
(** * 数のリスト *)

(* Generalizing the definition of pairs a little, we can
    describe the type of _lists_ of numbers like this: "A list is
    either the empty list or else a pair of a number and another
    list." *)
(**
   ペアの定義を少し一般化すると、数のリストは次のように表すことができます。すなわち、「リストは、空のリストであるか、または数と他のリストをペアにしたものである」。
   *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(* For example, here is a three-element list: *)
(** たとえば、次の定義は要素が三つのリストです *)

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

(* As with pairs, it is more convenient to write lists in
    familiar programming notation.  The following two declarations
    allow us to use [::] as an infix [cons] operator and square
    brackets as an "outfix" notation for constructing lists. *)
(**
   ペアの場合と同じく、リストをプログラミング言語で馴染んだ記法で書くことができると便利でしょう。次のふたつの宣言では [::] を中置の [cons] 演算子として使えるようにし、角括弧をリストを構成するための外置（outfix）記法として使えるようにしています。
   *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(* It is not necessary to fully understand these declarations,
    but in case you are interested, here is roughly what's going on.

    The [right associativity] annotation tells Coq how to parenthesize
    expressions involving several uses of [::] so that, for example,
    the next three declarations mean exactly the same thing: *)
(**
   この宣言を完全に理解する必要はありませんが、興味のある読者のために簡単に説明しておきます。

   [right associativity] アノテーションは複数の [::] を使った式にどのように括弧を付けるか指示するものです。例えば、次のみっつの宣言はすべて同じ意味に解釈されます。
   *)

Definition l_123'   := 1 :: (2 :: (3 :: nil)).
Definition l_123''  := 1 :: 2 :: 3 :: nil.
Definition l_123''' := [1,2,3].

(* The [at level 60] part tells Coq how to parenthesize
    expressions that involve both [::] and some other infix operator.
    For example, since we defined [+] as infix notation for the [plus]
    function at level 50,
[[
Notation "x + y" := (plus x y)  
                    (at level 50, left associativity).
]]
   The [+] operator will bind tighter than [::], so [1 + 2 :: [3]]
   will be parsed, as we'd expect, as [(1 + 2) :: [3]] rather than [1
   + (2 :: [3])].

   (By the way, it's worth noting in passing that expressions like "[1
   + 2 :: [3]]" can be a little confusing when you read them in a .v
   file.  The inner brackets, around 3, indicate a list, but the outer
   brackets are there to instruct the "coqdoc" tool that the bracketed
   part should be displayed as Coq code rather than running text.
   These brackets don't appear in the generated HTML.)

   The second and third [Notation] declarations above introduce the
   standard square-bracket notation for lists; the right-hand side of
   the third one illustrates Coq's syntax for declaring n-ary
   notations and translating them to nested sequences of binary
   constructors. *)
(**
   [at level 60] の部分は [::] を他の中置演算子といっしょに使っている式にどのように括弧を付けるかを指示するものです。例えば、 [+] を [plus] に対する level 50 の中置記法として定義したので、
[[
Notation "x + y" := (plus x y)
                    (at level 50, left associativity).
]]
   [+] は [::] よりも強く結合し、 [1 + 2 :: [3]] は期待通り、 [1 + (2 :: [3])] ではなく [(1 + 2) :: [3]] と構文解析されます。

   （ところで、 .v ファイルを読んでいるときには "[1 + 2 :: [3]]" のような書き方は少し読みにくいように感じるでしょう。内側の 3 の左右の角括弧はリストを表すものですが、外側の括弧は coqdoc 用の命令で、角括弧内の部分をそのままのテキストではなく Coq のコードとして表示するよう指示するものです。この角括弧は生成された HTML には現れません。）

   上の二番目と三番目の [Notation] 宣言は標準的なリストの記法を導入するためのものです。三番目の [Notation] の右辺は、 n 引数の記法を二項構成子の入れ子に変換する記法を定義するための Coq の構文の例です。
   *)

(* A number of functions are useful for manipulating lists.
    For example, the [repeat] function takes a number [n] and a
    [count] and returns a list of length [count] where every element
    is [n]. *)
(** リストを操作するために便利な関数がいくつかあります。例えば、 [repeat] 関数は数 [n] と [count] を取り、各要素が [n] で長さ [count] のリストを返します。 *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(* The [length] function calculates the length of a list. *)
(** [length] 関数はリストの長さを計算します。 *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(* The [app] ("append") function concatenates two lists. *)
(** [app] （"append"）関数はふたつのリストを連結します。 *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(* Actually, [app] will be used a lot in some parts of what
    follows, so it is convenient to have an infix operator for it. *)
(** [app] はこの後でよく使うので、中置演算子を用意しておくと便利でしょう。 *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4,5] = [4,5].
Proof. reflexivity.  Qed.
Example test_app3:             [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity.  Qed.

(* Here are two more small examples of programming with lists.
    The [hd] function returns the first element (the "head") of the
    list, while [tail] returns everything but the first
    element.  Of course, the empty list has no first element, so we
    must pass a default value to be returned in that case.  *)
(** もうふたつリストを使った例を見てみましょう。 [hd] 関数はリストの最初の要素（先頭—— head）を返し、 [tail] は最初の要素を除いたものを返します。空のリストには最初の要素はありませんから、その場合に返す値を引数として渡しておかなければなりません。 *)

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | nil => default
  | h :: t => h
  end.

Definition tail (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => t
  end.

Example test_hd1:             hd 0 [1,2,3] = 1.
Proof. reflexivity.  Qed.
Example test_hd2:             hd 0 [] = 0.
Proof. reflexivity.  Qed.
Example test_tail:            tail [1,2,3] = [2,3].
Proof. reflexivity.  Qed.

(* **** Exercise: 2 stars, recommended (list_funs) *)
(** **** 練習問題: ★★, recommended (list_funs) *)
(* Complete the definitions of [nonzeros], [oddmembers] and
    [countoddmembers] below.  *)
(** 以下の [nonzeros]、 [oddmembers]、 [countoddmembers] の定義を完成させなさい。  *)

Fixpoint nonzeros (l:natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_nonzeros:            nonzeros [0,1,0,2,3,0,0] = [1,2,3].
 (* FILL IN HERE *) Admitted.

Fixpoint oddmembers (l:natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_oddmembers:            oddmembers [0,1,0,2,3,0,0] = [1,3].
 (* FILL IN HERE *) Admitted.

Fixpoint countoddmembers (l:natlist) : nat :=
  (* FILL IN HERE *) admit.

Example test_countoddmembers1:    countoddmembers [1,0,3,1,4,5] = 4.
 (* FILL IN HERE *) Admitted.
Example test_countoddmembers2:    countoddmembers [0,2,4] = 0.
 (* FILL IN HERE *) Admitted.
Example test_countoddmembers3:    countoddmembers nil = 0.
 (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars (alternate) *)
(** **** 練習問題: ★★ (alternate) *)
(* Complete the definition of [alternate], which "zips up" two lists
    into one, alternating between elements taken from the first list
    and elements from the second.  See the tests below for more
    specific examples.

    Note: one natural way of writing [alternate] will fail to satisfy
    Coq's requirement that all [Fixpoint] definitions be "obviously
    terminating."  If you find yourself in this rut, look for a
    slightly more verbose solution that considers elements of both
    lists at the same time. *)
(**
   [alternate] の定義を完成させなさい。この関数は、ふたつのリストから交互に要素を取り出しひとつに「綴じ合わせる」関数です。具体的な例は下のテストを見てください。

   注意: [alternate] の自然な定義のひとつは、 「[Fixpoint] による定義は『明らかに停止する』ものでなければならない」という Coq の要求を満たすことができません。このパターンにはまってしまったようであれば、両方のリストの要素を同時に見ていくような少し冗長な方法を探してみてください。
   *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  (* FILL IN HERE *) admit.

Example test_alternate1:        alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
 (* FILL IN HERE *) Admitted.
Example test_alternate2:        alternate [1] [4,5,6] = [1,4,5,6].
 (* FILL IN HERE *) Admitted.
Example test_alternate3:        alternate [1,2,3] [4] = [1,4,2,3].
 (* FILL IN HERE *) Admitted.
Example test_alternate4:        alternate [] [20,30] = [20,30].
 (* FILL IN HERE *) Admitted.
(** [] *)


(* ** Bags via Lists *)
(** ** リストを使ったバッグ *)

(* A [bag] (or [multiset]) is like a set, but each element can appear
    multiple times instead of just once.  One reasonable
    implementation of bags is to represent a bag of numbers as a
    list. *)
(**
   バッグ（[bag]。または多重集合—— [multiset]）は集合のようなものですが、それぞれの要素が一度ではなく複数回現れることのできるようなものを言います。バッグの実装としてありうるのは数のバッグをリストで表現するというものでしょう。
   *)

Definition bag := natlist.

(* **** Exercise: 3 stars (bag_functions) *)
(** **** 練習問題: ★★★ (bag_functions) *)
(* Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)
(**
   バッグに対する [count]、 [sum]、 [add]、 [member] 関数の定義を完成させなさい。
   *)

Fixpoint count (v:nat) (s:bag) : nat :=
  (* FILL IN HERE *) admit.

(* All these proofs can be done just by [reflexivity]. *)
(** 下の証明はすべて [reflexivity] だけでできます。 *)

Example test_count1:              count 1 [1,2,3,1,4,1] = 3.
 (* FILL IN HERE *) Admitted.
Example test_count2:              count 6 [1,2,3,1,4,1] = 0.
 (* FILL IN HERE *) Admitted.

(* Multiset [sum] is similar to set [union]: [sum a b] contains
    all the elements of [a] and of [b].  (Mathematicians usually
    define [union] on multisets a little bit differently, which
    is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)
(**
   多重集合の [sum] （直和。または非交和）は集合の [union] （和）と同じようなものです。 [sum a b] は [a] と [b] の両方の要素を持つ多重集合です。（数学者は通常、多重集合の [union] にもう少し異なる定義を与えます。それが、この関数の名前を [union] にしなかった理由です。） [sum] のヘッダには引数の名前を与えませんでした。さらに、 [Fixpoint] ではなく [Definition] を使っています。ですから、引数に名前がついていたとしても再帰的な処理はできません。問題をこのように設定したのは、 [sum] を（定義済みの関数を使うといった）別の方法で定義できないか考えさせるためです。
   *)

Definition sum : bag -> bag -> bag :=
  (* FILL IN HERE *) admit.

Example test_sum1:              count 1 (sum [1,2,3] [1,4,1]) = 3.
 (* FILL IN HERE *) Admitted.

Definition add (v:nat) (s:bag) : bag :=
  (* FILL IN HERE *) admit.

Example test_add1:                count 1 (add 1 [1,4,1]) = 3.
 (* FILL IN HERE *) Admitted.
Example test_add2:                count 5 (add 1 [1,4,1]) = 0.
 (* FILL IN HERE *) Admitted.

Definition member (v:nat) (s:bag) : bool :=
  (* FILL IN HERE *) admit.

Example test_member1:             member 1 [1,4,1] = true.
 (* FILL IN HERE *) Admitted.
Example test_member2:             member 2 [1,4,1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars, optional (bag_more_functions) *)
(** **** 練習問題: ★★★, optional (bag_more_functions) *)
(* Here are some more bag functions for you to practice with. *)
(** 練習として、さらにいくつかの関数を作成してください。 *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* When remove_one is applied to a bag without the number to remove,
     it should return the same bag unchanged. *)
  (* [remove_one] を削除すべき数のないバッグに適用した場合は、同じバッグを変更せずに返す *)
  (* FILL IN HERE *) admit.

Example test_remove_one1:         count 5 (remove_one 5 [2,1,5,4,1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_one2:         count 5 (remove_one 5 [2,1,4,1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_one3:         count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_one4:
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
 (* FILL IN HERE *) Admitted.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  (* FILL IN HERE *) admit.

Example test_remove_all1:          count 5 (remove_all 5 [2,1,5,4,1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all2:          count 5 (remove_all 5 [2,1,4,1]) = 0.
 (* FILL IN HERE *) Admitted.
Example test_remove_all3:          count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
 (* FILL IN HERE *) Admitted.
Example test_remove_all4:          count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
 (* FILL IN HERE *) Admitted.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  (* FILL IN HERE *) admit.

Example test_subset1:              subset [1,2] [2,1,4,1] = true.
 (* FILL IN HERE *) Admitted.
Example test_subset2:              subset [1,2,2] [2,1,4,1] = false.
 (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars, recommended (bag_theorem) *)
(** **** 練習問題: ★★★, recommended (bag_theorem) *)
(* Write down an interesting theorem about bags involving the
    functions [count] and [add], and prove it.  Note that, since this
    problem is somewhat open-ended, it's possible that you may come up
    with a theorem which is true, but whose proof requires techniques
    you haven't learned yet.  Feel free to ask for help if you get
    stuck!
 *)
(**
   [count] や [add] を使ったバッグに関する面白い定理を書き、それを証明しなさい。この問題はいわゆる自由課題で、真になることがわかっていても、証明にはまだ習っていない技を使わなければならない定理を思いついてしまうこともあります。証明に行き詰まってしまったら気軽に質問してください。
 *)

(** FILL IN HERE *)
(** [] *)


(* * Reasoning About Lists *)
(** * リストに関する推論 *)

(* Just as with numbers, simple facts about list-processing
    functions can sometimes be proved entirely by simplification. For
    example, the simplification performed by [reflexivity] is enough
    for this theorem... *)
(**
   数の場合と同じく、リスト処理関数についての簡単な事実はもっぱら簡約のみで証明できることがあります。たとえば、次の定理は [reflexivity] で行われる簡約だけで証明できます。
   *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof.
   reflexivity.  Qed.

(* ... because the [[]] is substituted into the match position
    in the definition of [app], allowing the match itself to be
    simplified. *)
(**
   これは、 [[]] が [app] の定義のパターンマッチ部分に代入され、パターンマッチ自体が簡約できるようになるからです。
   *)

(* Also, as with numbers, it is sometimes helpful to perform case
    analysis on the possible shapes (empty or non-empty) of an unknown
    list. *)
(**
   またこれも数の場合と同じように、未知のリストの形（空であるかどうか）に応じた場合分けも有効です。
   *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tail l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity.  Qed.

(* Here, the [nil] case works because we've chosen to define
    [tl nil = nil]. Notice that the [as] annotation on the [destruct]
    tactic here introduces two names, [n] and [l'], corresponding to
    the fact that the [cons] constructor for lists takes two
    arguments (the head and tail of the list it is constructing). *)
(**
   ここで、 [nil] の場合がうまく行くのは、 [tl nil = nil] と定義したからです。ここでは、 [destruct] タクティックの [as] で [n] と [l'] のふたつの名前を導入しました。これは、リストの [cons] 構成子が引数をふたつ（構成するリストの頭部と尾部）取ることに対応しています。
   *)

(* Usually, though, interesting theorems about lists require
    induction for their proofs. *)
(** ただし、リストに関する興味深い定理の証明には、帰納法が必要になるのが普通です。
   *)


(* ** Micro-Sermon *)
(** ** お小言 *)

(* Simply reading example proofs will not get you very far!  It is
    very important to work through the details of each one, using Coq
    and thinking about what each step of the proof achieves.
    Otherwise it is more or less guaranteed that the exercises will
    make no sense. *)
(** 単に例題の証明を読んでいるだけでは大きな進歩は望めません！ 各証明を実際に Coq で動かし、各ステップがその証明にどのようにかかわっているか考え、道筋をていねいになぞっていくことがとても大切です。そうしなければ、演習には何の意味もありません。 *)


(* ** Induction on Lists *)
(** ** リスト上の帰納法 *)

(* Proofs by induction over datatypes like [natlist] are
    perhaps a little less familiar than standard natural number
    induction, but the basic idea is equally simple.  Each [Inductive]
    declaration defines a set of data values that can be built up from
    the declared constructors: a boolean can be either [true] or
    [false]; a number can be either [O] or [S] applied to a number; a
    list can be either [nil] or [cons] applied to a number and a list.

    Moreover, applications of the declared constructors to one another
    are the _only_ possible shapes that elements of an inductively
    defined set can have, and this fact directly gives rise to a way
    of reasoning about inductively defined sets: a number is either
    [O] or else it is [S] applied to some _smaller_ number; a list is
    either [nil] or else it is [cons] applied to some number and some
    _smaller_ list; etc. So, if we have in mind some proposition [P]
    that mentions a list [l] and we want to argue that [P] holds for
    _all_ lists, we can reason as follows:

      - First, show that [P] is true of [l] when [l] is [nil].

      - Then show that [P] is true of [l] when [l] is [cons n l'] for
        some number [n] and some smaller list [l'], asssuming that [P]
        is true for [l'].

    Since larger lists can only be built up from smaller ones,
    eventually reaching [nil], these two things together establish the
    truth of [P] for all lists [l].  Here's a concrete example: *)
(**
   [natlist] のようなデータ型に対して帰納法で証明をするのは、普通の自然数に対する帰納法よりも馴染みにくさを感じたことでしょう。しかし、基本的な考え方は同じくらい簡単です。 [Inductive] 宣言では、宣言した構成子から構築できるデータ型の集合を定義しています。例えば、ブール値では [true] と [false] のいずれかであり、数では [O] か数に対する [S] のいずれか、リストであれば [nil] か数とリストに対する [cons] のいずれかです。

   さらに言えば、帰納的に定義された集合の要素になるのは、宣言した構成子を互いに適用したものだけです。このことがそのまま帰納的に定義された集合に関する推論の方法になります。すなわち、数は [O] であるか、より小さい数に [S] を適用したものであるかのいずれかです。リストは [nil] であるか、何らかの数とより小さいリストに [cons] を適用したものです。他のものも同様です。ですから、あるリスト [l] に関する命題 [P] があり、 [P] がすべてのリストに対して成り立つことを示したい場合には、次のように推論します。

      - まず、 [l] が [nil] のとき [P] が [l] について成り立つことを示す。

      - それから、 [l] が [cons n l'] であるとき、ある数 [n] とより小さいリスト [l'] に対して、 [P] が [l'] について成り立つと仮定すれば [P] が [l] についても成り立つことを示す。

     大きなリストはそれより小さなリストから作り出され、少しずつ [nil] に近付いて行きます。よって、このふたつのことからすべてのリスト [l] に関して [P] が真であることが言えます。具体的な例で説明しましょう。
     *)

Theorem app_ass : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(* Again, this Coq proof is not especially illuminating as a
    static written document -- it is easy to see what's going on if
    you are reading the proof in an interactive Coq session and you
    can see the current goal and context at each point, but this state
    is not visible in the written-down parts of the Coq proof.  So a
    natural-language proof -- one written for human readers -- will
    need to include more explicit signposts; in particular, it will
    help the reader stay oriented if we remind them exactly what the
    induction hypothesis is in the second case.  *)
(** 蒸し返すようですが、この Coq の証明はこうして単に静的なテキストとして読んでいる限り、さほど明白で分かりやすいものではありません。 Coq の証明は、 Coq を対話的に動かしながらポイントごとに「現在のゴールは何か」「コンテキストに何が出ているか」を見て、証明が今どうなっているかを読み下していくことで理解されるようになっています。しかし、このような証明の途中経過は、全てが証明結果として書き出されるわけではありません。だからこそ、人間向けの自然言語での証明には証明の筋道がわかるように証明の指針を書いておく必要があるのです。特に、読者が流れを見失わないよう、ふたつめの場合分けで使う帰納法の仮定が何だったのかわかるようにしておくのは有益なはずです。
   *)

(* _Theorem_: For all lists [l1], [l2], and [l3], 
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)].

   _Proof_: By induction on [l1].

   - First, suppose [l1 = []].  We must show
[[
       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),
]]
     which follows directly from the definition of [++].

   - Next, suppose [l1 = n::l1'], with
[[
       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
]]
     (the induction hypothesis). We must show
[[
       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).
]]  
     By the definition of [++], this follows from
[[
       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
]]
     which is immediate from the induction hypothesis.  []

  Here is an exercise to be worked together in class: *)
(**
   定理: 任意のリスト [l1]、 [l2]、 [l3] について、
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)]
     が成り立つ。

   証明: [l1] についての帰納法で証明する

   - まず、 [l1 = []] と仮定して
[[
       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3)
]]
     を示す。これは [++] の定義から自明である。

   - 次に [l1 = n::l1'] かつ
[[
       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
]]
     （帰納法の仮定）と仮定して
[[
       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3)
]]
     を示す。 [++] の定義から、この式は以下のように変形できる。
[[
       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3))
]]
     これは帰納法の仮定から直接導かれる。  []

  下の練習問題は授業中に解きましょう。 *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(* For a slightly more involved example of an inductive proof
    over lists, suppose we define a "cons on the right" function
    [snoc] like this... *)
(** リストに対する帰納的証明のもう少し入り組んだ例を見てみましょう。リストの右側に [cons] する関数 [snoc] を定義したとしましょう。 *)

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

(* ... and use it to define a list-reversing function [rev]
    like this: *)
(** この関数を使ってリストの反転関数 [rev] を定義します。 *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1:            rev [1,2,3] = [3,2,1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(* Now let's prove some more list theorems using our newly
    defined [snoc] and [rev].  For something a little more challenging
    than the inductive proofs we've seen so far, let's prove that
    reversing a list does not change its length.  Our first attempt at
    this proof gets stuck in the successor case... *)
(**
   新しく定義した [snoc] と [rev] に関する定理を証明してみましょう。ここまでの帰納的証明よりも難易度の高いものですが、リストを反転しても長さの変わらないことを証明します。下の方法では、ふたつめの場合分けで行き詰まってしまいます。
   *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl. (* Here we are stuck: the goal is an equality involving
              [snoc], but we don't have any equations in either the
              immediate context or the global environment that have
              anything to do with [snoc]! *)
           (* ここで行き詰まる。ゴールは [snoc] に関する等式だが、
              コンテキスト中にも大域環境中にも [snoc] に関する等式はない。 *)
Admitted.

(* So let's take the equation about [snoc] that would have
    enabled us to make progress and prove it as a separate lemma. *)
(** この [snoc] に関する等式が成り立つことを示せれば証明が先に進むはずです。この式を取り出して別個の補題として証明してみましょう。 *)

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity.  Qed.

(* Now we can complete the original proof. *)
(** これで、元々の証明ができるようになりました。 *)

Theorem rev_length : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons".
    simpl. rewrite -> length_snoc.
    rewrite -> IHl'. reflexivity.  Qed.

(* For comparison, here are _informal_ proofs of these two theorems: 

    _Theorem_: For all numbers [n] and lists [l],
       [length (snoc l n) = S (length l)].
 
    _Proof_: By induction on [l].

    - First, suppose [l = []].  We must show
[[
        length (snoc [] n) = S (length []),
]]
      which follows directly from the definitions of
      [length] and [snoc].

    - Next, suppose [l = n'::l'], with
[[
        length (snoc l' n) = S (length l').
]]
      We must show
[[
        length (snoc (n' :: l') n) = S (length (n' :: l')).
]]
      By the definitions of [length] and [snoc], this
      follows from
[[
        S (length (snoc l' n)) = S (S (length l')),
]] 
      which is immediate from the induction hypothesis. [] *)
(** 対比として、この二つの定理の非形式的な証明を見てみましょう

    定理: 任意の数 [n] とリスト [l] について
       [length (snoc l n) = S (length l)] が成り立つ。

    証明: [l] についての帰納法で証明する。

    - まず、 [l = []] と仮定して
[[
        length (snoc [] n) = S (length [])
]]
      を示す。これは [length] と [snoc] の定義から直接導かれる。

    - 次に、 [l = n'::l'] かつ
[[
        length (snoc l' n) = S (length l')
]]
      と仮定して、
[[
        length (snoc (n' :: l') n) = S (length (n' :: l'))
]]
      を示す。 [length] と [snoc] の定義から次のように変形できる。
[[
        S (length (snoc l' n)) = S (S (length l'))
]]
      これは帰納法の仮定から明らかである。 [] *)

(* _Theorem_: For all lists [l], [length (rev l) = length l].
    
    _Proof_: By induction on [l].  

      - First, suppose [l = []].  We must show
[[
          length (rev []) = length [],
]]
        which follows directly from the definitions of [length] 
        and [rev].
    
      - Next, suppose [l = n::l'], with
[[
          length (rev l') = length l'.
]]
        We must show
[[
          length (rev (n :: l')) = length (n :: l').
]]
        By the definition of [rev], this follows from
[[
          length (snoc (rev l') n) = S (length l')
]]
        which, by the previous lemma, is the same as
[[
          S (length (rev l')) = S (length l').
]]
        This is immediate from the induction hypothesis. [] *)
(** 定理: 任意のリスト [l] について [length (rev l) = length l] が成り立つ。

    証明: [l] についての帰納法で証明する。

      - まず、 [l = []] と仮定して
[[
          length (rev []) = length []
]]
        を示す。これは [length] と [rev] の定義から直接導かれる

      - 次に、 [l = n::l'] かつ
[[
          length (rev l') = length l'
]]
        と仮定して、
[[
          length (rev (n :: l')) = length (n :: l')
]]
        を示す。 [rev] の定義から次のように変形できる。
[[
          length (snoc (rev l') n) = S (length l')
]]
        これは、先程の補題から、次のものと同じである。
[[
          S (length (rev l')) = S (length l')
]]
        これは、帰納法の仮定から明らかである。 [] *)

(* Obviously, the style of these proofs is rather longwinded
    and pedantic.  After the first few, we might find it easier to
    follow proofs that give a little less detail overall (since we can
    easily work them out in our own minds or on scratch paper if
    necessary) and just highlight the non-obvious steps.  In this more
    compressed style, the above proof might look more like this: *)
(** こういった証明のスタイルは、どう見ても長ったらしく杓子定規な感じがします。最初の何回かは別にして、それ以後は、細かいところは省略してしまって（必要であれば、頭の中や紙の上で追うのは簡単です）、自明でないところにだけ注目した方がわかりやすいでしょう。そのように省略がちに書けば、上の証明は次のようになります。
   *)

(* _Theorem_:
     For all lists [l], [length (rev l) = length l].

    _Proof_: First, observe that
[[
       length (snoc l n) = S (length l)
]]
     for any [l].  This follows by a straightforward induction on [l].
     The main property now follows by another straightforward
     induction on [l], using the observation together with the
     induction hypothesis in the case where [l = n'::l']. [] *)
(** 定理:
     任意のリスト [l] について [length (rev l) = length l] が成り立つ。

    証明: まず、任意の [l] について
[[
       length (snoc l n) = S (length l)
]]
     であることに注目する。これは [l] についての帰納法から自明である。このとき、もとの性質についても [l] についての帰納法から自明である。 [l = n'::l'] の場合については、上の性質と帰納法の仮定から導かれる。 [] *)

(* Which style is preferable in a given situation depends on
    the sophistication of the expected audience and on how similar the
    proof at hand is to ones that the audience will already be
    familiar with.  The more pedantic style is a good default for
    present purposes. *)
(** どちらのスタイルの方が好ましいかは、読み手の証明への馴れや、彼らが今まで触れてきた証明がどちらに近いかに依ります。本書の目的としては冗長なスタイルの方が無難でしょう。
   *)


(* ###################################################### *)
(* ** [SearchAbout] *)
(** ** [SearchAbout] *)

(* We've seen that proofs can make use of other theorems we've
    already proved, using [rewrite], and later we will see other ways
    of reusing previous theorems.  But in order to refer to a theorem,
    we need to know its name, and remembering the names of all the
    theorems we might ever want to use can become quite difficult!  It
    is often hard even to remember what theorems have been proven,
    much less what they are named.

    Coq's [SearchAbout] command is quite helpful with this.  Typing
    [SearchAbout foo] will cause Coq to display a list of all theorems
    involving [foo].  For example, try uncommenting the following to
    see a list of theorems that we have proved about [rev]: *)
(**
   これまで見てきたように、定理を証明するには既に証明した定理を使うことができます。以降では [rewrite] 以外にも、証明済みの定理を使う方法があることを紹介します。ところで、定理を使うためにはその名前を知らなければなりませんが、使えそうな定理の名前をすべて覚えておくのはとても大変です。今まで証明した定理を覚えておくだけでも大変なのに、その名前となったら尚更です。

   Coq の [SearchAbout] コマンドはこのような場合にとても便利です。 [SearchAbout foo] とすると、 [foo] に関する証明がすべて表示されます。例えば、次の部分のコメントを外せば、これまで [rev] に関して証明した定理が表示されます。
   *)

(* SearchAbout rev. *)

(* Keep [SearchAbout] in mind as you do the following exercises and
    throughout the rest of the course; it can save you a lot of time! *)
(** 続く練習問題やコースに取り組む際には、常に [SearchAbout] コマンドのことを頭の隅に置いておくといいでしょう。そうすることでずいぶん時間の節約ができるはずです。 *)

(* Also, if you are using ProofGeneral, you can run [SearchAbout]
    with [C-c C-f]. Pasting its response into your buffer can be
    accomplished with [C-c C-;]. *)
(** もし ProofGeneral を使っているのなら、 [C-c C-f] とキー入力をすることで [SearchAbout] コマンドを使うことができます。その結果をエディタに貼り付けるには [C-c C-;] を使うことができます。 *)


(* ###################################################### *)
(* ** List Exercises, Part 1 *)
(** ** リストについての練習問題 (1) *)

(* **** Exercise: 3 stars, recommended (list_exercises) *)
(* More practice with lists. *)
(** **** 練習問題: ★★★, recommended (list_exercises) *)
(** リストについてさらに練習しましょう。 *)

Theorem app_nil_end : forall l : natlist,
  l ++ [] = l.
Proof.
  (* FILL IN HERE *) Admitted.


Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *) Admitted.


Theorem distr_rev : forall l1 l2 : natlist,
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  (* FILL IN HERE *) Admitted.

(* There is a short solution to the next exercise.  If you find
    yourself getting tangled up, step back and try to look for a
    simpler way. *)
(**
   次の問題には簡単な解法があります。こんがらがってしまったようであれば、少し戻って単純な方法を探してみましょう。
   *)

Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  (* FILL IN HERE *) Admitted.

(* An exercise about your implementation of [nonzeros]: *)
(** 前に書いた [nonzeros] 関数に関する練習問題です。 *)

Lemma nonzeros_length : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(* ** List Exercises, Part 2 *)

(* **** Exercise: 2 stars, recommended (list_design) *)
(* Design exercise:
     - Write down a non-trivial theorem involving [cons]
       ([::]), [snoc], and [append] ([++]).
     - Prove it.
*)
(** ** リストについての練習問題 (2) *)

(** **** 練習問題: ★★, recommended (list_design) *)
(** 自分で問題を考えましょう。
     - [cons] （[::]）、 [snoc]、 [append] （[++]） に関する、自明でない定理を考えて書きなさい。
     - それを証明しなさい。
*)

(* FILL IN HERE *)
(** [] *)

(* **** Exercise: 2 stars, optional (bag_proofs) *)
(* If you did the optional exercise about bags above, here are a
    couple of little theorems to prove about your definitions. *)
(** **** 練習問題: ★★, optional (bag_proofs) *)
(**
   前のバッグについての optional な練習問題に挑戦したのであれば、その定義について、以下の定理を証明しなさい。
   *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(* The following lemma about [ble_nat] might help you in the next proof. *)
(** 以下の [ble_nat] に関する補題は、この次の証明に使えるかもしれません。 *)

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n. induction n as [| n'].
  Case "0".
    simpl.  reflexivity.
  Case "S n'".
    simpl.  rewrite IHn'.  reflexivity.  Qed.

Theorem remove_decreases_count: forall (s : bag),
  ble_nat (count 0 (remove_one 0 s)) (count 0 s) = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars, optional (bag_count_sum) *)
(* Write down an interesting theorem about bags involving the
    functions [count] and [sum], and prove it.
(** **** 練習問題: ★★★, optional (bag_count_sum) *)
(**
   バッグについて [count] と [sum] を使った定理を考え、それを証明しなさい。
   *)

(* FILL IN HERE *)
[]
 *)

(* **** Exercise: 4 stars, optional (rev_injective) *)
(* Prove that the [rev] function is injective, that is,

[[
    forall X (l1 l2 : list X), rev l1 = rev l2 -> l1 = l2.
]]

There is a hard way and an easy way to solve this exercise.
*)
(** **** 練習問題: ★★★★, optional (rev_injective) *)
(** [rev] 関数が単射である、すなわち
[[
    forall X (l1 l2 : list X), rev l1 = rev l2 -> l1 = l2
]]
であることを証明しなさい。

この練習問題には簡単な解法と難しい解法があります。
*)

(* FILL IN HERE *)
(** [] *)



(* ###################################################### *)
(* * Options *)
(** * オプション *)

(* Here is another type definition that is often useful in
    day-to-day programming: *)
(**
   次に、日々のプログラミングでも役に立つような型の定義を見てみましょう。
   *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(* One use of [natoption] is as a way of returning "error
    codes" from functions.  For example, suppose we want to write a
    function that returns the [n]th element of some list.  If we give
    it type [nat -> natlist -> nat], then we'll have to return some
    number when the list is too short! *)
(** [natoption] 型の使い途のひとつは、関数からエラーコードを返すことです。例えば、リストの [n] 番目の要素を返す関数を書きたいとしましょう。型を [nat -> natlist -> nat] としてしまったら、リストが短かすぎた場合でも何か適当な数を返さなければなりません！
   *)

Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => index_bad (pred n) l'
               end
  end.

(* On the other hand, if we give it type [nat -> natlist ->
    natoption], then we can return [None] when the list is too short
    and [Some a] when the list has enough members and [a] appears at
    position [n]. *)
(** これに対して、型を [nat -> natlist -> natoption] とすれば、リストが短かすぎた場合には [None] を返し、リストが十分に長く、 [n] 番目の要素が [a] であった場合には [Some a] を返すことができます。
   *)

Fixpoint index (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => match beq_nat n O with
               | true => Some a
               | false => index (pred n) l'
               end
  end.

Example test_index1 :    index 0 [4,5,6,7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index 3 [4,5,6,7]  = Some 7.
Proof. reflexivity.  Qed.
Example test_index3 :    index 10 [4,5,6,7] = None.
Proof. reflexivity.  Qed.

(* This example is also an opportunity to introduce one more
    small feature of Coq's programming language: conditional
    expressions... *)
(** この機会に、 Coq のプログラミング言語としての機能として、条件式を紹介しておきましょう。
   *)

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a else index' (pred n) l'
  end.

(* Coq's conditionals are exactly like those found in any other
    language, with one small generalization.  Since the boolean type
    is not built in, Coq actually allows conditional expressions over
    _any_ inductively defined type with exactly two constructors.  The
    guard is considered true if it evaluates to the first constructor
    in the [Inductive] definition and false if it evaluates to the
    second. *)
(** Coq の条件式(if式)は他の言語に見られるものとほとんど同じですが、少しだけ一般化されています。 Coq には 組み込みのブーリアン型がないため、 Coq の条件式では、実際には、構成子のふたつある任意の帰納型に対して分岐をすることができます。条件部の式が [Inductive] の定義の最初の構成子に評価された場合には真、ふたつめの構成子に評価された場合には偽と見做されます。
   *)

(* The function below pulls the [nat] out of a [natoption], returning
    a supplied default in the [None] case. *)
(** 次の関数は、 [natoption] 型から [nat] の値を取り出し、 [None] の場合には与えられたデフォルト値を返します。
   *)

Definition option_elim (o : natoption) (d : nat) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(* **** Exercise: 2 stars (hd_opt) *)
(* Using the same idea, fix the [hd] function from earlier so we don't
   have to pass a default element for the [nil] case.  *)
(** **** 練習問題: ★★ (hd_opt) *)
(** 同じ考え方を使って、以前定義した [hd] 関数を修正し、 [nil] の場合に返す値を渡さなくて済むようにしなさい。
   *)

Definition hd_opt (l : natlist) : natoption :=
  (* FILL IN HERE *) admit.

Example test_hd_opt1 : hd_opt [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt2 : hd_opt [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt3 : hd_opt [5,6] = Some 5.
 (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, optional (option_elim_hd) *)
(* This exercise relates your new [hd_opt] to the old [hd]. *)
(** **** 練習問題: ★★, optional (option_elim_hd) *)
(** 新しい [hd_opt] と古い [hd] の関係についての練習問題です。 *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim (hd_opt l) default.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 2 stars, recommended (beq_natlist) *)
(* Fill in the definition of [beq_natlist], which compares
    lists of numbers for equality.  Prove that [beq_natlist l l]
    yields [true] for every list [l]. *)
(** **** 練習問題: ★★, recommended (beq_natlist) *)
(** 数のリストふたつを比較し等価性を判定する関数 [beq_natlist] の定義を完成させなさい。そして、 [beq_natlist l l] が任意のリスト [l] で [true] となることを証明しなさい。 *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  (* FILL IN HERE *) admit.

Example test_beq_natlist1 :   (beq_natlist nil nil = true).
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist2 :   beq_natlist [1,2,3] [1,2,3] = true.
 (* FILL IN HERE *) Admitted.
Example test_beq_natlist3 :   beq_natlist [1,2,3] [1,2,4] = false.
 (* FILL IN HERE *) Admitted.

Theorem beq_natlist_refl : forall l:natlist,
  true = beq_natlist l l.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(* ###################################################### *)
(* * The [apply] Tactic *)
(** * [apply] タクティック *)

(* We often encounter situations where the goal to be proved is
    exactly the same as some hypothesis in the context or some
    previously proved lemma. *)
(** 証明をしていると、証明すべきゴールがコンテキスト中の仮定と同じであったり以前証明した補題と同じであることがしばしばあります。
   *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with 
     "[rewrite -> eq2. reflexivity.]"
     as we have done several times above.  
     But we can achieve the same effect in 
     a single step by using the [apply] tactic 
     instead: *)
  (* このような場合は、
     "[rewrite -> eq2. reflexivity.]"
     として証明を終えてきましたが、 [apply] タクティックを使えば一回で同じ結果が得られます。
     *)
  apply eq2.  Qed.

(* The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)
(**
   また、 [apply] タクティックは、条件付きの仮定や補題にも使うことができます。適用するものに含意が含まれていれば、含意の前提部分が証明すべきサブゴールに加えられます。
   *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(* You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply]. *)
(** この証明で、 [apply] の代わりに [rewrite] を使って証明を終えられるか試してみると有益でしょう。
   *)

(* Typically, when we use [apply H], the statement [H] will
    begin with a [forall] binding some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)
(** [apply H] を使う典型的な例は、 [H] が [forall] で始まり、何らかの全称限量された変数を束縛している場合です。現在のゴールが [H] の帰結部と一致した場合には、変数に対応する適当な値を見つけてくれます。例えば、次の証明で [apply eq2] すると、 [eq2] 内の変数 [q] は [n] に、 [r] は [m] に具体化されます。
   *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(* **** Exercise: 2 stars, optional (silly_ex) *)
(* Complete the following proof without using [simpl]. *)
(** **** 練習問題: ★★, optional (silly_ex) *)
(** 次の証明を [simpl] を使わずに完成させなさい。 *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal _exactly_ -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)
(** [apply] タクティックを使う場合には、適用する事実（の帰結部）が、ゴールと完全に一致していなければなりません。例えは、等式の左辺と右辺が入れ替わっているだけでも [apply] タクティックは使えません。
   *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* here we cannot use [apply] directly *)
  (* ここで [apply] を使えない *)
Admitted.

(* In this case we can use the [symmetry] tactic, which
    switches the left and right sides of an equality in the goal. *)
(** そのような場合には [symmetry] タクティックを使って、ゴールの等式の左辺と右辺を入れ替えることができます。 *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since 
            [apply] will do a [simpl] step first. *)  
  (* この [simpl] は必須ではありません。 [apply] は最初に [simpl] をします。 *)
  apply H.  Qed.


(* **** Exercise: 3 stars, recommended (apply_exercise1) *)
(** **** 練習問題: ★★★, recommended (apply_exercise1) *)
Theorem rev_exercise1 : forall (l l' : natlist),
     l = rev l' ->
     l' = rev l.
Proof.
  (* Hint: you can use [apply] with previously defined lemmas, not
     just hypotheses in the context.  Remember that [SearchAbout] is
     your friend. *)
  (* ヒント: コンテスキト中の補題以外にも、以前に定義した補題を [apply] することができます。こんなときには [SearchAbout] を使うのでしたね。
     *)
  (* FILL IN HERE *) Admitted.
(** [] *)


(* **** Exercise: 1 star (apply_rewrite) *)
(* Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied?
  *)
(** **** 練習問題: ★ (apply_rewrite) *)
(** [apply] と [rewrite] の違いを簡単に説明しなさい。どちらもうまく使えるような場面はありますか？

  (* FILL IN HERE *)
*)
(** [] *)


(* ###################################################### *)
(* * Varying the Induction Hypothesis *)
(** * 帰納法の仮定を変更する *)

(* One subtlety in these inductive proofs is worth noticing here.
    For example, look back at the proof of the [app_ass] theorem.  The
    induction hypothesis (in the second subgoal generated by the
    [induction] tactic) is

      [ (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3 ].

    (Note that, because we've defined [++] to be right associative,
    the expression on the right of the [=] is the same as writing [l1'
    ++ (l2 ++ l3)].)

    This hypothesis makes a statement about [l1'] together with the
    _particular_ lists [l2] and [l3].  The lists [l2] and [l3], which
    were introduced into the context by the [intros] at the top of the
    proof, are "held constant" in the induction hypothesis.  If we set
    up the proof slightly differently by introducing just [n] into the
    context at the top, then we get an induction hypothesis that makes
    a stronger claim:

     [ forall l2 l3,  (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3 ]

    Use Coq to see the difference for yourself.

    In the present case, the difference between the two proofs is
    minor, since the definition of the [++] function just examines its
    first argument and doesn't do anything interesting with its second
    argument.  But we'll soon come to situations where setting up the
    induction hypothesis one way or the other can make the difference
    between a proof working and failing. *)
(** 帰納法による証明の微妙さについては説明しておく価値があるでしょう。例えば、以前証明した [app_ass] を見てみましょう。帰納法の仮定（[induction] タクティックで生成されたふたつめのサブゴール）は以下のようなものでした。

      [(l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3]

    （[++] を右結合と定義したので、 [=] の右辺は [l1' ++ (l2 ++ l3)] と同じです。）

    この仮定は、 [l1'] と、特定のリスト [l2]、 [l3] に関するものです。 [l2] と [l3] はこの証明の初めに [intros] タクティックで導入したもので、この仮定中で「一定」です。証明の方法を少し変えて、最初に [n] だけをコンテキストに [intros] するようにしたら、帰納法の仮定は次のようにもっと強いものになります。

     [ forall l2 l3,  (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3 ]

    Coq を使って実際に違いを確認してください。

    今回の場合では、ふたつの証明の違いはささいなものです。これは、 [++] 関数の定義が最初の引数だけを見て、ふたつめの引数には特に何もしないからです。しかし、遠からずわかることですが、帰納法の仮定をどちらにするかで証明の成否が分かれることもあるのです。
   *)

(* **** Exercise: 2 stars, optional (app_ass') *)
(* Give an alternate proof of the associativity of [++] with a more
    general induction hypothesis.  Complete the following (leaving the
    first line unchanged). *)
(** **** 練習問題: ★★, optional (app_ass') *)
(** [++] の結合則をより一般的な仮定のもとで証明しなさい。（最初の行を変更せずに）次の証明を完成させること。 *)

Theorem app_ass' : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1. induction l1 as [ | n l1'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars (apply_exercise2) *)
(* Notice that we don't introduce [m] before performing induction.
    This leaves it general, so that the IH doesn't specify a
    particular [m], but lets us pick. *)
(** **** 練習問題: ★★★ (apply_exercise2) *)
(** [induction] の前に [m] を [intros] していないことに注意してください。これによって仮定が一般化され、帰納法の仮定が特定の [m] に縛られることがなくなり、より使いやすくなりました。 *)

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [| n'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 3 stars, recommended (beq_nat_sym_informal) *)
(* Provide an informal proof of this lemma that corresponds
    to your formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof: *)
(** **** 練習問題: ★★★, recommended (beq_nat_sym_informal) *)
(** 以下の補題について上の証明と対応する非形式的な証明を書きなさい。

   定理: 任意の [nat] [n] [m] について、 [beq_nat n m = beq_nat m n]。

   証明: *)
   (** FILL IN HERE *)
(** [] *)

End NatList.


(* ###################################################### *)
(* * Exercise: Dictionaries *)
(** * 練習問題: 辞書 *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty  : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

(* This declaration can be read: "There are two ways to construct a
    [dictionary]: either using the constructor [empty] to represent an
    empty dictionary, or by applying the constructor [record] to
    a key, a value, and an existing [dictionary] to construct a
    [dictionary] with an additional key to value mapping." *)
(** この宣言は次のように読めます。「[dictionary] を構成する方法はふたつある。構成子 [empty] で空の辞書を表現するか、構成子 [record] をキーと値と既存の [dictionary] に適用してキーと値の対応を追加した [dictionary] を構成するかのいずれかである」。 *)

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

(* Below is a function [find] that searches a [dictionary] for a
    given key.  It evaluates evaluates to [None] if the key was not
    found and [Some val] if the key was mapped to [val] in the
    dictionary. If the same key is mapped to multiple values, [find]
    will return the first one it finds. *)
(** 下の [find] 関数は、 [dictionary] から与えられたキーに対応する値を探し出すものです。 キーが見つからなかった場合には [None] に評価され、キーが [val] に結び付けられていた場合には [Some val] に評価されます。同じキーが複数の値に結び付けられている場合には、最初に見つかったほうの値を返します。 *)

Fixpoint find (key : nat) (d : dictionary) : option nat :=
  match d with
  | empty         => None
  | record k v d' => if (beq_nat key k) then (Some v) else (find key d')
  end.

(* **** Exercise: 1 star (dictionary_invariant1) *)
(* Complete the following proof. *)
(** **** 練習問題: ★ (dictionary_invariant1) *)
(* 次の証明を完成させなさい。 *)
Theorem dictionary_invariant1 : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(* **** Exercise: 1 star (dictionary_invariant2) *)
(* Complete the following proof. *)
(** **** 練習問題: ★ (dictionary_invariant2) *)
(* 次の証明を完成させなさい。 *)
Theorem dictionary_invariant2 : forall (d : dictionary) (m n o: nat),
  (beq_nat m n) = false -> (find m d) = (find m (insert n o d)).
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

End Dictionary.

(* The following declaration puts [beq_nat_sym] into the
    top-level namespace, so that we can use it later without having to
    write [NatList.beq_nat_sym]. *)
(**
   次の宣言で、 [beq_nat_sym] の定義をトップレベルの名前空間に置いておきます。こうすることで、後で [beq_nat_sym] を使うのに [NatList.beq_nat_sym] と書かずに済みます。 *)

Definition beq_nat_sym := NatList.beq_nat_sym.

