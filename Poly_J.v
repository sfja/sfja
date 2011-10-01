(** * ポリモルフィズム（多相性）と高階関数 *)

(* $Date: 2011-06-22 10:06:32 -0400 (Wed, 22 Jun 2011) $ *)

Require Export Lists_J.



(** * ポリモルフィズム（多相性） *)


(** ** ポリモルフィック（多相性を持った）リスト *)

(** ここまでは、数値のリストについて学んできました。もちろん、数値以外の、文字列、ブール値、リストといったものを要素として持つリストを扱えるプログラムは、より興味深いものとなるでしょう。これまで学んできたことだけでも、実は新しい機能的なデータ型を作ることはできるのです。例えば次のように... *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

(** ... しかし、こんなことをやっていると、すぐに嫌になってしまうでしょう。その理由の一つは、データ型ごとに違ったコンストラクタの名前をつけなければならないことですが、もっと大変なのは、こういったリストを扱う関数（[length]、[rev]など）を、新しく対応した型ごとに作る必要が出てくることです。 *)

(** この無駄な繰り返し作業を無くすため、Coqはポリモルフィックな帰納的データ型の定義をサポートしています。これを使うと、ポリモルフィックなリストは以下のように書くことができます。 *)

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

(** これは、前の章にある[natlist]の定義とほとんどそっくりですが、コンストラクタ[cons]の引数の型が[nat]であったのに対し、任意の型を表す[X]がそれに変わっています。この[X]はヘッダに加えられた[X]と結びつけられ、さらに[natlis]tであったものが[list X]に置き換わっています（ここで、コンストラクタに[nil]や[con]sといった名前を付けられるのは、最初に定義した[natlist]が[Module]の中で定義されていて、ここからはスコープの外になっているからです）。 *)

(** それでは、[list]とはいったい何なのか、ということを正確に考えて見ましょう。これを考える一つの手がかりは、リストが「型を引数にとり、帰納的な定義を返す関数である」と考えることです。あるいは「型を引数にとり、型を返す関数」と考えてもいいかもしれません。任意の型[X]について、[list X]という型は、帰納的に定義されたリストの集合で、その要素が型[X]となっているものと考えることもできます。
 *)

(** この定義の下で、コンストラクタ[nil]や[cons]を使う際には、今作ろうとしているリストの要素の型を指定してやる必要があります。なぜなら、今や[nil]も[cons]もポリモルフィックなコンストラクタとなっているからです。 *)

Check nil.
(* ===> nil : forall X : Type, list X *)
Check cons.
(* ===> cons : forall X : Type, X -> list X -> list X *)

(** ここで出てきた"[forall X]"というのは、コンストラクタに追加された引数で、後に続く引数で型を特定させるものです。[nil]や[cons]が使われる際、例えば[2]と[1]を要素に持つリストは、以下のように表されます。  *)

Check (cons nat 2 (cons nat 1 (nil nat))).

(** （ここでは[nil]や[cons]を明示的に記述していますが、それは我々がまだ[[]]や[::]の表記法（Notation）をまだ記述していないからです。この後でやります） *)

(** それでは少し話を戻して、以前書いたリスト処理関数をポリモルフィック版（汎用版）に作り直していきましょう。[length]関数は以下のようになります。 *)

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.

(** ここで、[match]に使われている[nil]や[cons]に型修飾がついていないことに注意してください。我々はすでにリスト[l]が型[X]の要素を持っていることを知っていますが、それはパターンマッチに[X]を含める理由になりません。さらに形式的には、[X]はリスト定義全体での型であって、個々のコンストラクタの型ではないのです。

    [nil]や[cons]と同様に、[length]も与えるリストと同じ型を最初に適用すれば使えます。 *)

Example test_length1 :
    length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity.  Qed.

(** この[length]を別の型のリストに使いたい場合は、適切な型を与えるだけで済みます。 *)

Example test_length2 :
    length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity.  Qed.

(** では、このサブセクションの終わりに、他の標準的なリスト処理関数をポリモルフィックに書き直しましょう。 *)

Fixpoint app (X : Type) (l1 l2 : list X)
                : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity.  Qed.

Example test_rev2:
  rev bool (nil bool) = nil bool.
Proof. reflexivity.  Qed.


(** *** 型推論 *)

(** それでは、[app]関数の定義をもう一度書いてみましょう。ただし今回は、引数の型を指定しないでおきます。Coqはこれを受け入れてくれるでしょうか？ *)

Fixpoint app' X l1 l2 : list X :=
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app' X t l2)
  end.

(** うまくいったようです。Coqが[app']にどのような型を設定したのか確認してみましょう。 *)

Check app'.
Check app.

(** 両者は全く同じであることが分かります。Coqは型推論という機構を持っていて、これを使い、[l1]、[l2]の[X]が何であるかを、その使われ方から導き出します。例えば、[X]が[cons]の引数として使われたことがあれば、それは型に違いなく、さらに[cons]の最初に引数で型が指定されていて、[l1]が[nil]や[cons]とマッチされているなら、それは[list]に違いなかろう、といった具合です。

    このパワフルな機構の存在は、型情報を常にそこら中に書かなければならないわけではない、ということを意味します。とはいえ、型を明示的に書くことは、ドキュメント作成やプログラムの健全性をチェックする際に大いに意味はあるのですが。とにかく、これからは自分の書くコードで、型指定を書くところ、書かないところのバランスを考えていく必要があります（多すぎれば、コードが目障りな型指定で読みにくくなりますし、少なすぎると、プログラムを読む人に型推論の結果をいちいち推測させなければならなくなります）。
*)


(** *** 引数の同化（Synthesys） *)

(** ポリモルフィックな関数を使うときはいつも、通常の引数に加えて型を一つ以上渡さなければなりません。例えば、[length]関数で自分を再帰している部分には、型[X]として渡されたものをそのまま渡すことになります。しかしこのように、そこらじゅうに明示的に型を書かなければならないとなると、これはとても面倒で冗長な作業です。[length]の二つ目の引数が[X]型のリストなら、最初の引数は[X]以外になり得ないのは明らかなのではないか・・・・ならなぜわざわざそれを書く必要があるのでしょう。

    幸いなことに、Coqではこの種の冗長性を避けることができます。型を引数に渡すところではどこでも同化した引数"[_]"を書くことができるのです。これは「ここをあるべき型に解釈してください」という意味です。もう少し正確に言うと、Coqが[_]を見つけると、手近に集められる情報を集めます。それは、適用されている関数の型や、その適用が現れている文脈から予想される型などですが、それを使って[_]と置き換えるべき具体的な型を決定するのです。

    これを聞くと、型推論と同じじゃないかと思われるかもしれません。実際、この二つの機能は水面下にあるメカニズムではつながっています。次のように単に引数の型を省略する代わりに
[[
      app' X l1 l2 : list X :=
]]
    このように、型を[_]で書くことができるということです。
[[
      app' (X : _) (l1 l2 : _) : list X :=
]]
    いずれも、Coqに、欠落している情報を推論させるもので、これを引数の同化といいます。

    引数の同化を使うと、[length]関数は以下のように書けます。 *)

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

(** この例では、[X]を[_]に省略することをあまりしていません。しかし多くの場合、この違いは重要です。例えば、[1],[2],[3]といった数値を保持するリストを書きたい場合、以下のように書く代わりに... *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ...引数同化を使って以下のように書くこともできます。 *)

Definition list123' := cons _ 1 (cons _ 2 (cons _ 3 (nil _))).


(** *** 暗黙の引数 *)

(** さらに先に進みましょう。プログラム全体が[_]まみれになることを避けるため、特定の関数の引数については常に型推論するよう指定できます。 *)

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

(* 注）もはや引数に_は必要ありません... *)
Definition list123'' := cons 1 (cons 2 (cons 3 nil)).
Check (length list123'').

(** また、関数定義の中で、引数を暗黙のものにすることもできます。その際は、次のように引数を中カッコで囲みます。 *)

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
  | nil      => 0
  | cons h t => S (length'' t)
  end.

(** （ここで注意してほしいのは、再帰呼び出しの[length'']ではもうすでに型を引数で指定していない、ということです）これからは、この書き方をできるだけ使っていくことにします。ただし、[Inductive]宣言のコンストラクタでは[Implicit Arguments]を明示的に書くようにします。 *)

(** 引数を暗黙的に宣言することには、小さな問題が一つあります。時折、Coqが型を特定するために必要な情報を十分に集められない時があるのです。そういう場合には、その時だけ明示してやります。たとえそれがグローバルには[Implicit]と宣言されていたとしてもです。例えば、もし次のように書きたかったとします。 *)

(* Definition mynil := nil. *)

(** この定義のコメントをはずすと、Coqはエラーを出します。[nil]が何の型の[nil]なのか分からないからです。このようなときは、型宣言を明示的に行うことができます（これによって[nil]を何に適用できるか、という情報が与えられます）。 *)

Definition mynil : list nat := nil.

(** それとは別に、関数名の前に[@]を付けることで暗黙的に宣言された関数に対して型を明示的に与えることができます。 *)

Check @nil.

Definition mynil' := @nil nat.

(** 引数同化と暗黙的な引数をつかうことで、リストのノーテーヨン（表記法）をより便利に記述できます。コンストラクタの型引数を暗黙的に記述すれば、Coqはその表記法を使ったときに型を自動的に推論してくれます。 *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** これで、我々の望む書き方ができるようになりました。 *)

Definition list123''' := [1, 2, 3].


(** *** 練習問題:ポリモルフィックなリスト *)

(** **** 練習問題: ★★, optional (poly_exercises) *)
(** っここにあるいくつかの練習問題は、List.vにあったものと同じですが、ポリモルフィズムの練習になります。以下の定義を行い、証明を完成させなさい。 *)

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X :=
  (* FILL IN HERE *) admit.

Example test_repeat1:
  repeat bool true 2 = cons true (cons true nil).
 (* FILL IN HERE *) Admitted.

Theorem nil_app : forall X:Type, forall l:list X,
  app [] l = l.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem rev_snoc : forall X : Type,
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem snoc_with_append : forall X : Type,
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** ** ポリモルフィックなペア *)

(** 次も同様に、前の章で作った数値のペアをポリモルフィックにすることを考えます。 *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

(** リストと同様、型引数を暗黙にし、その表記法を定義します。 *)

Notation "( x , y )" := (pair x y).

(** また、「ペア型」の、より標準的な表記法も登録しておきます。 *)

Notation "X * Y" := (prod X Y) : type_scope.

(** （[type_scope]というアノテーションは、この省略形が、型を解析する際に使われるものであることを示しています。これによって、[*]が乗算の演算子と衝突することを避けています。*)

(** 注意：最初のうちは、[(x,y)]と[X*Y]の違いに混乱するかもしれません。覚えてほしいのは、[(x,y)]が値のペアを構成するもので、[X*Y]は型のペアを構成するものだということです。値[x]が[X]型で、値[y]が[Y]型なら、値[(x,y)]は[X*Y]型となります。 *)

(** ペアの最初の要素、２番目の要素を返す射影関数は他のプログラミング言語で書いたものと比べると若干長くなります。 *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x,y) => y end.

(** 次の関数は二つのリストを引数にとり、一つの"ペアのリスト"を作成します。多くの関数型言語で[zip]関数と呼ばれているものです。Coqの標準ライブラリとぶつからないよう、ここでは[combine]と呼ぶことにします。 *)
(** ペアの表記法は、式だけではなくパターンマッチにも使えることに注目してください。 *)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

(** また、あいまいさがない場合は、matchを囲む括弧を取る事もできます。 *)

Fixpoint combine' {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx,ly with
  | [],_ => []
  | _,[] => []
  | x::tx, y::ty => (x,y) :: (combine' tx ty)
  end.

(** **** 練習問題: ★ (combine_checks) *)
(** 次の質問の答えを紙に書いた後で、Coqの出した答えと同じかチェックしなさい。
    - 関数[combine]の型は何でしょう ([Check @combine]の出力結果は？
    - それでは
[[
        Eval simpl in (combine [1,2] [false,false,true,true]).
]]
      は何を出力する？   []
*)

(** **** 練習問題: ★★, recommended (split) *)
(** [split]関数は[combine]と全く逆で、ペアのリストを引数に受け取り、リストのペアを返します。多くの関数型言語とで[unzip]と呼ばれているものです。次の段落のコメントをはずし、[split]関数の定義を完成させなさい。続くテストを通過することも確認しなさい。 *)

(*
Fixpoint split
  (* FILL IN HERE *)

Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity.  Qed.
*)
(** [] *)


(** ** ポリモルフィックなオプション *)

(** 最後に、ポリモルフィックなオプションに取り組みます。この型は、前の章の[natoption]を多相化して定義することにします。 *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

(** また、[index]関数も、色々な型のリストで使えるように定義し直しましょう。 *)

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 :    index 0 [4,5,6,7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index  1 [[1],[2]]  = Some [2].
Proof. reflexivity.  Qed.
Example test_index3 :    index  2 [true]  = None.
Proof. reflexivity.  Qed.

(** **** 練習問題: ★, optional (hd_opt_poly) *)
(** 前の章に出てきた[hd_opt]関数のポリモルフィック版を定義しなさい。。次の単体テストでの確認も忘れずに。 *)

Definition hd_opt {X : Type} (l : list X)  : option X :=
  (* FILL IN HERE *) admit.

(** 再び、暗黙的に定義された引数を明示的に指定してみましょう。関数名の前に[@]をつければいいのでしたね。 *)

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1,2] = Some 1.
 (* FILL IN HERE *) Admitted.
Example test_hd_opt2 :   hd_opt  [[1],[2]]  = Some [1].
 (* FILL IN HERE *) Admitted.
(** [] *)


(** * データとしての関数 *)


(** ** 高階関数 *)

(** 他の多くの近代的なプログラミング言語（全ての関数型言語を含む）同様、Coqは関数をファーストクラスに属するものとして取り扱います。つまりそれは、関数を他の関数の引数として渡したり、結果として関数を返したり、データ構造の中に関数を含めたりすることができるということです。

    関数を操作する関数を、一般に「高階関数」と呼びます。例えば次のようなものです。 *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** ここで引数[f]は関数です。[doit3times]の内容は、値[n]に対して関数[f]を3回適用するものです。 *)

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.


(** ** 部分適用 *)

(** 実は、我々がすでに見た、複数の引数を持つ関数は、関数を引数に渡すサンプルになっているのです。どういうことかは、[plus]関数の型を思い出せば分かります。それは[nat -> nat -> nat]でした。 *)

Check plus.

(** [->]は、型同士の二項演算子ですが、このことはCoqが基本的に引数一つの関数しかサポートしていないことを意味します。さらに、この演算子は右結合であるため、[plus]関数の型は[nat -> (nat -> nat)]の省略であると言えます。これをよく読むと"[plus]は[nat]型の引数を一つ取り、引数が[nat]型一つで[nat]型を返す関数を返す"と読むことができます。以前の例では[plus]に二つの引数を一緒に与えていましたが、もし望むなら最初の一つだけを与えることもできます。これを部分適用といいます。 *)

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.


(** ** 余談： カリー化 *)

(** **** 練習問題: ★★, optional (currying) *)
(** Coqでは、[f : A -> B -> C]という型の関数は[A -> (B -> C)]型と同じです。このことは、もし上の関数[f]に値[A]を与えると、[f' : B -> C]という型の関数が戻り値として返ってくるということです。これは部分適用の[plus3]でやりましたが、このように、複数の引数から戻り値の型のリストを、関数を返す関数として捉えなおすことを、論理学者ハスケル・カリーにちなんでカリー化、と呼んでいます。

    逆に、[A -> B -> C]型の関数を[(A * B) -> C]型の関数に変換することもできます。これをアンカリー化（非カリー化）といいます。アンカリー化された二項演算は、二つの引数を同時にペアの形で与える必要があり、部分適用はできません。 *)

(** カリー化は以下のように定義できます。 *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** 練習問題として、その逆の[prod_uncurry]を定義し、二つの関数が互いに逆関数であることを証明しなさい。 *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  (* FILL IN HERE *) admit.

(** (考える練習: 次のコマンドを実行する前に、[prod_curry]と[prod_uncurry]の型を考えなさい。) *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem curry_uncurry : forall (X Y Z : Type)
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** ** フィルター (Filter)関数 *)

(** 次に紹介するのは、とても有用な高階関数です。これは、[X]型のリストと、[X]についての述語（[X]を引数にとり、boolを返す関数）を引数にとり、リストの要素にフィルターをかけて、述語として与えられた関数の結果が[true]となった要素だけのリストを返す関数です。 *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** 例えば、この[filter]関数に述語として[evenb]と数値のリスト[l]を与えると、リスト[l]の要素の中で偶数の要素だけがリストとなって帰ります。 *)

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity.  Qed.

(** この[filter]を使うことで、 [Lists.v]にある[countoddmembers]関数をもっと簡潔に書くことができます。 *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0,2,4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.


(** ** 無名（匿名）関数 *)

(** [filter]関数に渡すためだけに、二度と使われない[length_is_1]といった関数を定義して、それにわざわざ名前を付けるというのは、少しわずらわしく感じます。このようなことは、この例だけの問題ではありません。高階関数を使うときは、引数として"一度しか使わない関数"を渡すことがよくあります。こういう関数にいちいち名前を考えるのは、退屈以外の何物でもありません。

    幸いなことに、いい方法があります。一時的な関数を、名前を付けることも、トップレベルで宣言することもなく作成することができるのです。これは定数のリストや、数値定数と同じようなものだと考えられます。 *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

(** 次は無名関数を使った書き換えのもう少しいい例です。 *)

Example test_filter2':
    filter (fun l => beq_nat (length l) 1)
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity.  Qed.

(** **** 練習問題: ★★, optional (filter_even_gt7) *)

(** [filter]関数を使い、数値のリストを入力すると、そのうち偶数でなおかつ7より大きい要素だけを取り出す[filter_even_gt7]関数を書きなさい。 *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  (* FILL IN HERE *) admit.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
 (* FILL IN HERE *) Admitted.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
 (* FILL IN HERE *) Admitted.

(** [] *)

(** **** 練習問題: ★★★, optional (partition) *)
(** [filter]関数を使って、[partition]関数を書きなさい。:
[[
  partition : forall X : Type,
              (X -> bool) -> list X -> list X * list X
]]
   型[X]について、[X]型の値がある条件を満たすかを調べる述語[X -> bool]と[X]のリスト[list X]を引数に与えると、[partition]関数はリストのペアを返します。ペアの最初の要素は、与えられたリストのうち、条件を満たす要素だけの理宇土で、二番目の要素は、条件を満たさないもののリストです。二つのリストの要素の順番は、元のリストの順と同じでなければなりません。*)

Definition partition {X : Type} (test : X -> bool) (l : list X)
                     : list X * list X :=
(* FILL IN HERE *) admit.

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
(* FILL IN HERE *) Admitted.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
(* FILL IN HERE *) Admitted.
(** [] *)


(** ** マップ（Map）関数 *)

(** もう一つ、便利な高階関数として[map]を挙げます。 *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** これは、関数[f]とリスト[ l = [n1, n2, n3, ...] ]を引数にとり、関数[f]を[l]の各要素に適用した[ [f n1, f n2, f n3,...] ]というリストを返します。例えばこのようなものです。 *)

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity.  Qed.

(** 入力されるリストの要素の型と、出力されるリストの要素の型は同じである必要はありません（[map]は、[X]と[Y]二種類の型変数を取ります）。次の例は、数値のリストと、数値を受け取り[bool]値を返す関数から、bool型のリストを返します。 *)

Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity.  Qed.

(** 同じ関数が、数値のリストと、「数値から[bool]型のリストへの関数」を引数にとり、「[bool]型のリストのリスト」を返すような関数にも使えます。 *)

Example test_map3:
    map (fun n => [evenb n,oddb n]) [2,1,2,5]
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity.  Qed.


(** **** 練習問題: ★★★, optional (map_rev) *)
(** [map]と[rev]が可換であることを示しなさい。証明には補題をたてて証明する必要があるでしょう。 *)

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, recommended (flat_map) *)
(** [map]関数は、[list X]から[list Y]へのマップを、型[X -> Y]の関数を使って実現しています。同じような関数[flat_map]を定義しましょう。これは[list X]から[list Y]へのマップですが、[X -> list Y]となる関数[f]を使用できます。このため、次のように要素ごとの関数[f]の結果を平坦化してやる必要があります。
[[
        flat_map (fun n => [n,n+1,n+2]) [1,5,10]
      = [1, 2, 3, 5, 6, 7, 10, 11, 12].
]]
*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X)
                   : (list Y) :=
  (* FILL IN HERE *) admit.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
 (* FILL IN HERE *) Admitted.
(** [] *)

(** リストは、[map]関数のような関数意渡すことができる、帰納的に定義された唯一の型、というわけではありません。次の定義は、[option]型のために[map]関数を定義したものです。 *)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** 練習問題: ★★, optional (implicit_args) *)
(** [filter]や[map]関数を定義したり使ったりするケースでは、多くの場合暗黙的な型引数が使われます。暗黙の型引数定義に使われている中括弧を普通の括弧に置き換え、必要なところに型引数を明示的に書くようにして、それが正しいかどうかをCoqでチェックしなさい。 [] *)


(** ** 畳み込み（Fold）関数 *)

(** さらにパワフルな高階関数[fold]に話を移します。この関数はGoogleの分散フレームワーク"map/reduce"でいうところの"reduce"オペレーションに根ざしています。 *)

Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** 直感的に[fold]は、与えられたリストの各要素の間に、与えられた二項演算子[f]を挟み込むように挿入していくような操作です。 例えば、[ fold plus [1,2,3,4] ]は、直感的に[1+2+3+4]と同じ意味です。ただし正確には、二番めの引数に、[f]に最初に与える"初期値"が必要になります。例えば
[[
   fold plus [1,2,3,4] 0
]]
    は、次のように解釈されます。
[[
   1 + (2 + (3 + (4 + 0))).
]]
    もう少しサンプルを見てください。
*)

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app  [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

(** **** 練習問題: ★, optional (fold_types_different) *)
(** [fold]関数が[X]と[Y]二つの型引数をとっていて、関数[f]が型[X]を引数にとり型[Y]を返すようになっていることに注目してください。[X]と[Y]が別々の型となっていることで、どのような場合に便利であるかを考えてください。 *)


(** ** 関数を作成する関数 *)

(** これまで見てきた高階関数は、ほとんどが関数を引数にとるものでした。ここでは、関数が別の関数の戻り値になるような例を見ていきましょう。

    まず、値[x]（型[X]）を引数としてとり、「[nat]型の引数から[X]型の戻り値を返す関数」を返す関数を考えます。戻る関数は、引数に関係なく、生成時に与えられた値｢x｣を常に返すものです。 *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** もう少し面白い例を挙げます。次の関数は、数値から型[X]を戻す関数[f]と、数値[k]、型[X]の値[x]を引数にとり、[f]に[k]と同じ引数が与えられた場合だけ値[x]を返し、それ以外のときは[f]に[k]を渡した戻り値を返します。 *)

Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.

(** たとえば、この[override]関数を数値から[bool]型への関数に以下のように２回適用すると、値が[1]と[3]のときだけ[false]を返し、それ以外はtrueを返すようにすることができます。 *)

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(** **** 練習問題: ★ (override_example) *)
(** 次の証明にとりかかる前に、あなたがこの証明の意味することを理解しているか確認するため、証明内容を別の言葉で言い換えてください。証明自体は単純なものです。 *)

Theorem override_example : forall (b:bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** このコースでこれ以降、、関数のオーバーライド（上書き）はよく登場しますが、この性質について多くを知る必要はありません。しかし、これらの性質を証明するには、さらにいくつかのCoqのタクティクを知らなければなりません。それが、この章の残りの部分の主なトピックになります。 *)


(** * さらにCoqについて *)


(* ###################################################### *)
(** ** [unfold]タクティク *)

(** 時折、Coqが関数を自動的に展開してくれないために証明が行き詰まってしまうことがあります（これは仕様であって、バグではありません。Coqがもし可能な展開を全て自動でやってしまったら、証明のゴールはたちまち巨大化して、読むこともCoqで操作することもできなくなってしまいます）。 *)

Theorem unfold_example_bad : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  (* ここでは[rewrite -> H]としたいところです。なぜなら、[plus3 n]はと同じ定義と言えるからです。しかしCoqは[plus3 n]をその定義に従って自動的に展開してくれません。 *)
  Admitted.

(** [unfold]タクティクは、定義された名前を、その定義の右側の記述に置き換えてくれるものです。  *)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.  Qed.

(** 今我々は、[override]の最初の性質を証明することができるようになりました。もしある関数の引数のある値[k]をオーバーライドしてから引数[k]を与えると、オーバーライドされた値が帰る、というものです。 *)

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.  Qed.

(** この証明はストレートなものですが、[override]関数の展開に[unfold]を必要としている点だけ注意してください。 *)

(** **** 練習問題: ★★ (override_neq) *)
Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** [unfold]の逆の機能として、Coqには[fold]というタクティクも用意されています。これは、展開された定義を元に戻してくれますが、あまり使われることはありません。 *)


(** ** 反転（Inversion） *)

(** 自然数の定義を思い出してください。
[[
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
]]
    この定義から、全ての数は二つの形式、コンストラクタ[O]で作られたか、今ストら歌[S]に他の数値を与えて作られたかのどちらかであることは明白です。しかし両目を見開いてよく見ると、この定義（と、他のプログラミング言語で、データ型の定義がどのように働くか、という非形式的な理解）から、二つの暗黙的な事実が見つかります。
    - コンストラクタ[S]が単射であること。つまり、[S n = S m]となるためのただ一つの方法は[n = m]であること。

    - コンストラクタ[O]とコンストラクタ[S]は、互いに素であること。つまり、[O]はどんな[n]についても[S n]と等しくないということ。 *)

(** 同じ原理が、全ての機能的に定義された型にあてはまります。全てのコンストラクタは単射で、コンストラクタが違えば同じ値は生まれません。リストについて言えば[cons]コンストラクタは単射で、[nil]全ての空でないリストと異なっています。[bool]型では、[true]と[false]は異なるものです（ただ、[true]も[false]も引数を取らないため、単射かどうか、という議論には意味がありません）。 *)

(** Coqには、この性質を証明に利用する[inversion]というタクティクが用意されています。

    [inversion]タクティクは、次のような場合に使います。コンテキストに以下のような形の仮定[H]（や過去に定義された補助定理）がある場合、
[[
      c a1 a2 ... an = d b1 b2 ... bm
]]
    これが、あるコンストラクタ[c]と[d]と、その引数[a1 ... an]と[b1 ... bm]について成り立つというものです。.

    このような時、[inversion H]とすることで、この等式を"反転"し、そこに含まれている情報を以下のようなやり方で引き出します。

    - もし[c]と[d]が同じコンストラクタの場合、すでに分かっているように、コンストラクタの単射性から、[a1 = b1], [a2 = b2]をが導かれます。
      また、[inversion H]はこの事実をコンテキストに追加し、ゴールの置き換えに使えないかを試します。

    - もし[c]と[d]が違うコンストラクタの場合、仮定[H]は矛盾していることになります。つまり、偽である前提がコンテキストに紛れ込んでいるということになり、これはどんなゴールも証明できてしまうことを意味します。このような場合、[inversion H]は現在のゴールが解決されたものとして、ゴールの一覧から取り除きます。 *)

(** [inversion]タクティクは、このような一般的な説明を読むより、その動きを実際に見てもらったほうが簡単に理解できるでしょう。以下は[inversion]の使い方を見てもらい、理解するための練習を兼ねた定理の例です。 *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

(** 便利なように、[inversion]タクティクは、等式でつながった複合値を展開して、それぞれを対応する相手に結び付けてくれます。 *)

Theorem silly5 : forall (n m o : nat),
     [n,m] = [o,o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** 練習問題: ★ (sillyex1) *)
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** 練習問題: ★ (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** コンストラクタの単射性が、[forall (n m : nat), S n = S m -> n = m]を示している一方で、これを逆に適用することで、普通の等式の証明をすることができれば、これまで出てきたいくつかのケースにも使えるでしょう。 *)

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof. intros n m eq. rewrite -> eq. reflexivity. Qed.

(** これはinversionの、もっと現実的な使い方です。ここで示された性質は、この後でもよく使うことになります。 *)

Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0".
    intros m. destruct m as [| m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. intros contra. inversion contra.
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m'". simpl. intros H.
      apply eq_remove_S. apply IHn'. apply H. Qed.

(** **** 練習問題: ★★ (beq_nat_eq_informal) *)
(** [beq_nat_eq]の、非形式的な証明を示しなさい。 *)

(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★★ (beq_nat_eq') *)
(** [beq_nat_eq]は、[m]について帰納法をつかうことで証明することができました。しかし我々は、もう少し編集を導入する順序に注意を払うべきです。なぜなら、我々は一般に、十分な帰納法の仮定を得ているからです。このことを次に示します。次の証明を完成させなさい。この練習問題の効果を最大にするため、とりあえずは先にやった証明を見ないで取り組んでください。 *)

Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** [inversion]のもう一つの側面を見てみましょう。以前にすでに証明済みのものですが、少し遠回りな書き方になっています。新しく追加され等号のせいで、少し等式に関する証明を追加する必要がありますし、これまでに出てきたタクティクを使う練習にもなります。 *)

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply eq_remove_S. apply IHl'. inversion eq. reflexivity. Qed.


(** *** 練習問題 *)


(** **** 練習問題: ★★, optional (practice) *)
(** 同じところに分類され、相互に関連するような、自明でもないが複雑というほどでもない証明をいくつか練習問題としましょう。このうち、いくつかは過去のレクチャーや練習問題に出てきた補題を使用します。 *)


Theorem beq_nat_0_l : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem beq_nat_0_r : forall n,
  true = beq_nat n 0 -> 0 = n.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  (* WORKED IN CLASS *)
    Case "n = 0". simpl. intros m eq. destruct m as [| m'].
      SCase "m = 0". reflexivity.
      SCase "m = S m'". inversion eq.
    Case "n = S n'". intros m eq. destruct m as [| m'].
      SCase "m = 0". inversion eq.
      SCase "m = S m'".
        apply eq_remove_S. apply IHn'. inversion eq. reflexivity. Qed.


(** ** タクティクを仮定に使用する *)

(** デフォルトでは、ほとんどのタクティクはゴールの式に作用するだけで、コンテキストの内容には手を付けません。しかしながら、ほとんどのタクティクは変数を付けることで同じ操作をコンテキストの式に行うことができます。

    例えば、[simpl in H]というタクティクは、コンテキストの中の[H]と名前のついた仮定に対して簡約をします。 *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** 同様に、[apply L in H]というタクティクは、ある条件式[L] ([L1 -> L2]といった形の)を、コンテキストにある過程[H]に適用します。しかし普通のあ[apply]と異なるのは、[apply L in H]が、[H]が[L1]とマッチすることを調べ、それに成功したらそれを[L2]に書き換えることです。

    言い換えると、[apply L in H]は、"前向きの証明"の形をとっているといえます。それは、[L1 -> L2]が与えられ、仮定と[L1]がマッチしたら、仮定は[L2]と同じと考えてよい、ということです。逆に、[apply L]は"逆向きの証明"であると言えます。それは、[L1->L2]であることが分かっていて、今証明しようとしているものが[L2]なら、[L1]を証明すればよいとすることです。

    以前やった証明の変種を挙げておきます。逆向きの証明ではなく、前向きの証明を進めましょう。 *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H.
  apply H.  Qed.

(** 前向きの証明は、与えられたもの（前提や、すでに証明された定理）からスタートして、そのゴールを次々につなげていき、ゴールに達するまでそれを続けます。逆向きの証明は、ゴールからスタートし、そのゴールが結論となる前提を調べ、それを前提や証明済みの定理にたどりつくまで繰り返します。皆さんがこれまで（数学やコンピュータサイエンスの分野で）見てきた非形式的な証明は、おそらく前向きの証明であったのではないかと思います。一般にCoqでの証明は逆向きの証明となる傾向があります。しかし、状況によっては前向きの証明のほうが簡単で考えやすい、ということもあります。  *)

(** **** 練習問題: ★★★, recommended (plus_n_n_injective) *)
(** 先に述べて"in"を使って次の証明をしなさい。 *)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    (* ヒント: 補題plus_n_Smを使用します *)
    (* FILL IN HERE *) Admitted.
(** [] *)


(** ** [destruct]を複合式で使う *)


(** ここまで[destruct]タクティクがいくつかの変数の値についてケース分析を行う例をたくさん見てきました。しかし時には、ある式の結果についてケース分析をすることで証明を行う必要があります。このような場合にも[destruct]タクティクが使えます。.

    例を見てください。 *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun.
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

(** 上の証明で[sillyfun]を展開すると、[if (beq_nat n 3) then ... else ...]で行き詰まることがわかります。そこで、[n]が[3]である場合とそうでない場合とに[destruct (beq_nat n 3)]を使って二つのケースに分け、証明を行います。 *)

(** **** 練習問題: ★ (override_shadow) *)
Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, recommended (combine_split) *)
(*
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].
  (* FILL IN HERE *) Admitted.
*)
(** [] *)

(** **** 練習問題: ★★★, optional (split_combine) *)
(** 思考練習: 我々はすでに、全ての型のリストのペアで[combine]が[split]の逆関数であることを証明しました。ではその逆の「[split]は[combine]の逆関数である」を示すことはできるでしょうか？

    ヒント: [split combine l1 l2 = (l1,l2)]が[true]となる[l1]、[l2]の条件は何でしょう？

    この定理をCoqで証明しなさい（なるべく[intros]を使うタイミングを送らせ、帰納法の仮定を一般化させておくといいでしょう。 *)

(* FILL IN HERE *)
(** [] *)


(** ** [remember]タクティク *)

(** (注: [remember]タクティクは、今必ず読んでおかないといけないほどのものではありません。必要になるまでこの項はとばしておいて、必要になってから読んでもいいでしょう。 ) *)

(** 前の項では、[destruct]を使えば任意の演算対象の評価結果についてケース分析できることを見てきました。 [e]が何らかの帰納的な型[T]であれば、[destruct e]は型[T]のコンストラクタそれぞれにサブゴールを作成し、起こりえる全ての（ゴールやコンテキストにある）[e]の状態をコンストラクタ[c]で網羅的に置き換えます。

    しかし時折、この置き換えのプロセスで、証明に必要な情報が失われてしまうことがあります。例えば、関数[sillyfun1]を次のように定義したとします。 *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** そしてCoqを使いよく観察することで、[sillyfun1 n]が、[n]が奇数のときだけ[true]となることを示したいとします。先ほど[sillyfun]でやった証明を参考に類推すると、証明はこんな風に始まるのが自然に思えます。 *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* 手詰まり・・・・ *)
Admitted.

(** しかし証明はここで手詰まりになってしまいます。なぜなら、コンテキストからゴールまでたどりつくのに必要な情報がなくなってしまったからです。この問題は[destruct]による置き換えが厳格すぎることから起こります。[destruct]は[beq_nat n 3]の結果起こる事象を全て投げ捨ててしまいますが、我々はそのうち少なくとも一つは残してもらわないと証明が進みません。このケースで必要なのは[beq_nat n 3 = true]で、ここから[n = 3]は明らかで、ここから[n]が奇数であることが導かれます。

    実際のところやりたいことは[destruct]を[beq_nat n 3]に直接使ってこの式の結果起こることを全て置き換えてしまうことではなく、[destruct]を[beq_nat n 3]と同じような何か別のものに適用することです。例えば[beq_nat n 3]と同じ値になる変数が分かっているなら、代わりにその値に対して[destruct]する、といったことです。

    [remember]タクティクは、そういう変数を導きたいときに使えます。 *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
   remember (beq_nat n 3) as e3.
   (* ここで、コンテキストに新しい変数[e3]と、[e3 = beq_nat n 3]という仮定が追加されます。こうしてから[destruct e3]とすると... *)
   destruct e3.
   (* ... 変数[e3]は置換され（完全に見えなくなり）ゴールは先ほど行き詰まったときと同じになってしまいますが、コンテキストには等式を持つ仮定 --[e3]が[true]に置き換わっています--  が増えており、この仮定があればこの先の証明を進めていけるようになります。 *)
     Case "e3 = true". apply beq_nat_eq in Heqe3.
       rewrite -> Heqe3. reflexivity.
     Case "e3 = false".
      (* 証明中の関数の二番目の等式をテストすることになりました。[remember]を同じように使用して、証明を終わらせましょう。 *)
       remember (beq_nat n 5) as e5. destruct e5.
         SCase "e5 = true".
           apply beq_nat_eq in Heqe5.
           rewrite -> Heqe5. reflexivity.
         SCase "e5 = false". inversion eq.  Qed.

(** **** 練習問題: ★★ (override_same) *)
Theorem override_same : forall {X:Type} x1 k1 k2 (f : nat->X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, optional (filter_exercise) *)
(** この問題はやや難しいかもしれません。最初に[intros]を使うと、帰納法を適用するための変数まで上に上げてしまうので気をつけてください。 *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** ** [apply ... with ...]タクティク *)

(** 次の例は、[[a,b]]から[[e,f]]を得るためにrewriteを二回も使っており、少し要領が悪く思われます。 *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** このようなことがよくあるため、これを補題として定義し、全ての等式が遷移性をもっていることを示します。 *)

Theorem trans_eq : forall {X:Type} (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2.
  reflexivity.  Qed.

(** そして、[trans_eq]をさきほどの証明に使ってみます。しかし、実際にやってみると[apply]タクティクに多少細工が必要なことがわかります。 *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  (* ここで単純に[apply trans_eq]とすると（その補題の結論をゴールにマッチすることで）[X]を[[nat]]に、[n]を[[a,b]]に、[o]を[[e,f]]にあてはめようとします。しかしこのマッチングでは、[m]に何をあてはめるかを決めることができません。そこで、[with (m:=[c,d])]を明示的に情報として追加することで[apply]を動かします。 *)
  apply trans_eq with (m:=[c,d]). apply eq1. apply eq2.   Qed.

(**  実際には、このように名前[m]を[with]に与えるということはそれほど多くありません。Coqは多くの場合賢く振舞って、我々の要求を実現してくれます。ちなみにこの上の[apply]はapply trans_eq with [c,d]と書くこともできます。 *)

(** **** 練習問題: ★★★, recommended (apply_exercises) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  (* FILL IN HERE *) Admitted.

Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem override_permute : forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* ################################################################## *)
(** * まとめ *)

(** ここまでに、たくさんの基本的なタクティクを見てきました。これだけあればしばらくの間は困らずに済むはずです。この先数回のレクチャーで2～3新しいものが出てきますが、その先ではさらに強力な「自動化されたタクティク」を紹介していきます。それを使うと、多くの低レベルな作業をCoqに処理してもらうことができます。しかし基本的に、皆さんはもう必要なことを知っていると考えていいでしょう。


    ここまでに出てきたタクティクの一覧です

      - [intros]:
        仮定や変数をゴールからコンテキストに移す

      - [reflexivity]:
        証明を完了させる（ゴールが[e = e]という形になっている場合）

      - [apply]:
        仮定、補助定理、コンストラクタを使ってゴールを証明する

      - [apply... in H]:
        仮定、補助定理、コンストラクタを使ってゴールを証明する（前向きの証明）

      - [apply... with...]:
        パターンマッチだけで決定できなかった変数を、特定の値に明示的に結びつける

      - [simpl]:
        ゴールの式を簡約する

      - [simpl in H]:
        ゴール、もしくは仮定Hの式を簡約する

      - [rewrite]:
        等式の形をした仮定（もしくは定理）を使い、ゴールを書き換える

      - [rewrite ... in H]:
        等式の形をした仮定（もしくは定理）を使い、ゴールや仮定を書き換える

      - [unfold]:
        定義された定数を、ゴールの右側の式で置き換える

      - [unfold... in H]:
        定義された定数を、ゴールや仮定の右側の式で置き換える

      - [destruct... as...]:
        帰納的に定義された型の値について、ケースごとに解析する

      - [induction... as...]:
        機能的に定義された型の値に帰納法を適用する

      - [inversion]:
        コンストラクタの単射性と独立性を利用して証明を行う

      - [remember (e) as x]:
        destruct [x]とすることで式を失わないようにするため、式([e])に名前([x])を与える

      - [assert (e) as H]:
        定義した補助定理(e)をHという名前でコンテキストに導入する
*)


(** * さらなる練習問題 *)

(** **** 練習問題: ★★, optional (fold_length) *)
(** リストに関する多くの一般的な関数は[fold]を使って書きなおすることができます。例えば、次に示すのは[length]の別な実装です。 *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

(** [fold_length]が正しいことを証明しなさい。 *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, recommended (fold_map) *)
(** [map]関数も[fold]を使って書くことができます。以下の[fold_map]を完成させなさい。 *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
(* FILL IN HERE *) admit.

(** [fold_map]の正しさを示す定理をCoqで書き、証明しなさい *)

(* FILL IN HERE *)
(** [] *)

Module MumbleBaz.
(** **** 練習問題: ★★, optional (mumble_grumble) *)
(** つぎの、機能的に定義された二つの型をよく観察してください。 *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** 次の式のうち、ある型[X]について[grumble X]の要素として正しく定義されているものはどれでしょうか。
      - [d (b a 5)]
      - [d mumble (b a 5)]
      - [d bool (b a 5)]
      - [e bool true]
      - [e mumble (b c 0)]
      - [e bool (b c 0)]
      - [c]
(* FILL IN HERE *)
[] *)

(** **** 練習問題: ★★, optional (baz_num_elts) *)
(** 次の、機能的に定義された型をよく観察してください。 *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(** 型[baz]はいくつの要素を持つことができるでしょうか？
(* FILL IN HERE *)
[] *)

End MumbleBaz.

(** **** 練習問題: ★★★★, recommended (forall_exists_challenge) *)
(** チャレンジ問題: 二つの再帰関数[forallb]、[existsb]を定義しなさい。[forallb]は、リストの全ての要素が与えられた条件を満たしているかどうかを返します。
[[
      forallb oddb [1,3,5,7,9] = true

      forallb negb [false,false] = true

      forallb evenb [0,2,4,5] = false

      forallb (beq_nat 5) [] = true
]]
    [existsb]は、リストの中に、与えられた条件を満たす要素が一つ以上あるかを返します。
[[
      existsb (beq_nat 5) [0,2,3,6] = false

      existsb (andb true) [true,true,false] = true

      existsb oddb [1,0,0,0,0,3] = true

      existsb evenb [] = false
]]
    次に[existsb']を再帰関数としてではなく、[forallb]と[negb]を使って定義しなさい。.

    そして、[existsb']と[existsb]が同じ振る舞いをすることを証明しなさい。
*)

(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★, optional (index_informal) *)
(** [index]関数の定義を思い出してください。
[[
   Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else index (pred n) l'
     end.
]]
   次の定理の、非形式的な証明を書きなさい。
[[
   forall X n l, length l = n -> @index X (S n) l = None.
]]
(* FILL IN HERE *)
*)
(** [] *)

