(** * Lists_J: ペア, リスト，オプション *)

(* $Date: 2011-06-22 10:06:32 -0400 (Wed, 22 Jun 2011) $ *)

(** 次の行を実行すると、前の章で定義したものを一度にインポートすることができます。 *)

Require Export Basics_J.

(** ただしこれを使うには、[coqc]を使って[Basics.v]をコンパイルし、[Basics.vo]を作成しておく必要があります。（これは、.javaファイルから.classファイルを作ったり、.cファイルから.oファイルを作ったりするのと同じことです。）

    あなたの環境でコードをコンパイルするには、以下の二つの方法があります。

     - CoqIDEで行う

         CoqIDEの"Compile"メニューから"Basics.v"を開き、"Compile" メニューの "Compile Buffer"をクリックする。

     - コマンドラインから

         [coqc Basics.v]を実行する。

このファイルには、[Module]機能でラップされた数値のペアやリストに関する多くの定義が収録されています。そのためこれ以降、同じ名前の機能が、よりすぐれたバージョンで、同じ操作により利用できるようになります。 *)

Module NatList.


(** * 数値のペア *)

(** 帰納的な型定義では、各コンストラクタは好きな数の引数を取ることができました。引数がないもの（[true]や[O]）、ひとつのもの（[S]）、さらにそれ以上のものも以下のようにできます。 *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

(** この定義は以下のように読めます：”以下は、数値のペアを作成するためのひとつの方法である。それは、二つの自然数型[nat]を引数にして、コンストラクタ[pair]に適用することである。”

次に示すのは、二つの引数を持つコンストラクタでパターンマッチングを行う簡単な定義です。 *)

Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y => y
  end.

(** この数値のペアをよく使う場合は、[pair x y].と書くかわりに数学で普通に使われる[(x,y)]のような表記ができるといいですね。そんなときは[Notation]の定義をすると、Coq上でそのような書き方が許されるようになります。 *)

Notation "( x , y )" := (pair x y).

(** こうして定義した新しい表記法（Notation）は、式だけでなくパターンマッチに使うこともできます。（実際には、この前の章でも書いたように、この表記は標準ライブラリに定義されています。） *)

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

(** それでは、数値のペアに関するいくつかの簡単な事実を証明してみましょう。もし我々が証明すべき命題を、以下のような特殊な（そしてちょっとかわった）やり方で定義していれば、証明はreflexivity（と普通の簡約）だけで得ることができます。 *)

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  reflexivity.  Qed.

(** しかし、reflexivityは、命題を以下のように普通に定義するとうまく使えません *)

Theorem surjective_pairing_stuck : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  simpl. (* なにも変わりません！ *)
Admitted.

(** 我々は、[p]の構造を明らかにし、[simpl]が[fst]や[snd]の中のパターンマッチに作業できるようにする必要があります。これは[destruct]でできるでしょう。

自然数と異なり、[destruct]は特別なサブゴールを作らないことに注意してください。これは、[natprod]が一つのの方法でしか構築されないからです。  *)

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.  destruct p as (n,m).  simpl.  reflexivity.  Qed.

(**  "[as]..."パターンで変数をどのような名前にするか、ということを指定するために、先ほど紹介した表記法が使えることにも注目してください。 *)

(** **** 練習問題: ★ (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** * 数値のリスト *)

(** ペアの定義より一般化させると、数値のリスト型を以下のように表すことができます。”リストは、空のリストであるか、数値とリストのペアである” *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

(** たとえば、次の定義は要素が三つのリストです *)

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

(** ペアと同様、リストをより親しみやすい記法で書くことができると便利です。次の二つの定義は、[cons]演算子を中置で記述できる([::])と、リストを外からくくることで表記ができる大括弧のの定義です。 *)

Notation "x :: l" := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

(** これらの定義を完全に理解する必要はありませんが、興味があるなら、次を読めばだいたい何がどうなっているか分かるはずです。

    [right associativity]アノテーションは、[::]を連続して使った場合に式をどのような順で展開すればよいかを指定します。例えば、次の三つの例は全て同じ意味に解釈されます。  *)

Definition l_123'   := 1 :: (2 :: (3 :: nil)).
Definition l_123''  := 1 :: 2 :: 3 :: nil.
Definition l_123''' := [1,2,3].

(** [at level 60]は、[::]が他の演算子と一緒使われた際、どのような優先順で展開、評価するかを指定します。例えば、"[+]"という中置演算子をレベル50で定義するには以下のようにします。
[[
Notation "x + y" := (plus x y)
                    (at level 50, left associativity).
]]
   このように定義された[+]演算子は、::よりも強い結びつきを持つことになります。このため [1 + 2 :: [3]]という式は[1 + (2 :: [3])]ではなく[(1 + 2) :: [3]]と解釈されるでしょう。

    (ところで、あなたがもし拡張子[.v]のファイルを直接読んでいるなら、"[1 + 2 :: [3]]" といういささか冗長な表現に少し戸惑っているかもしれません。3を囲んでいる内側の大括弧は、それがリストであることを示しています。しかし、外側の大括弧はcoqdocというツールに対して、「これは文章ではなく、プログラムの一部である」ということを示すために付けられているものです。この外側の大括弧は、HTML版に変換される際に消し去られます。)

上に挙げた[Notation]定義の2番目と3番目のものは、リストの標準的な書き方を示しています。3行目の右側はnまでの配列をCoqの文法で表しており、これは引数二つのコンストラクタ[cons]のネストした列に変換されます。 *)

(** リストを操作するための関数がいくつか用意されています。例えば、[repeat]関数は数[n]と[count]を引数に取り、[n]が[count]個並んだリストを返します。 *)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => nil
  | S count' => n :: (repeat n count')
  end.

(** [length]関数はリストの要素数を返します。 *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil => O
  | h :: t => S (length t)
  end.

(** [app] ("append")関数は二つのリストを結合します。 *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil    => l2
  | h :: t => h :: (app t l2)
  end.

(** [app]の使用頻度は高いため、中置演算子が用意されています。 *)

Notation "x ++ y" := (app x y)
                     (right associativity, at level 60).

Example test_app1:             [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. reflexivity.  Qed.
Example test_app2:             nil ++ [4,5] = [4,5].
Proof. reflexivity.  Qed.
Example test_app3:             [1,2,3] ++ nil = [1,2,3].
Proof. reflexivity.  Qed.

(** リストを使ったサンプルをもう二つほど見てみましょう。[hd]関数はリストの先頭（"head")要素を取得します。一方、[tail]関数は最初の要素以外の全ての要素をリストで返します。もちろん、空のリストには最初の要素がありませんから、そのような場合に何を返すか、先に引数として与えておく必要があります  *)

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

(** **** 練習問題: ★★, recommended (list_funs) *)
(** 以下の三つの関数[nonzeros], [oddmembers], [countoddmembers]の定義を完成させなさい。  *)

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

(** **** 練習問題: ★★ (alternate) *)
(** 二つのリストを交互に混ぜながら一つのリストを作り上げる[alternate]関数の定義を完成させなさい。下のテスト内容を見れば、どのようなものかは分かると思います。

注） [alternate]を普通に書いてしまうと、Coqの"[Fixpoint]で定義される関数は、明らかに停止するものでなければならない"という制限にひっかかってしまう場合があります。もしこれにはまってしまったら、両方のリストの要素を一緒に見ていくような、少々冗長な方法を探してみてください。
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


(** ** バッグとリスト *)

(** バッグ（[bag]）もしくはマルチセット ([multiset])と呼ばれるものは、いわゆる"集合"のようなものですが、それぞれの要素が「ただ一度しか現れない」のではなく「同じものが何回現れてもよい」ようなもののことをいいます。 *)

Definition bag := natlist.

(** **** 練習問題: ★★★ (bag_functions) *)
(** バッグを操作する、[count], [sum], [add], [member]関数の定義を完成させなさい *)

Fixpoint count (v:nat) (s:bag) : nat :=
  (* FILL IN HERE *) admit.

(** これらすべての証明は、[reflexivity]だけでできるはずです。 *)

Example test_count1:              count 1 [1,2,3,1,4,1] = 3.
 (* FILL IN HERE *) Admitted.
Example test_count2:              count 6 [1,2,3,1,4,1] = 0.
 (* FILL IN HERE *) Admitted.

(** マルチセットの[sum]は、集合の[union]（和集合）と同じようなものです。[sum a b]は、[a]と[b]の要素を全て併せ持つ集合です（数学者は普通マルチセットの[union]という言葉を少し違うものの意味で使っています。それが、この関数の名前を"union"としなかった理由です）。sum関数のために、引数に名前をつけていないヘッダーを用意しました。さらにそのヘッダーは[Fixpoint]ではなく[Definition]で定義されています。こうしておけば、もし引数に名前を与えていたとしても再帰的な処理はできないからです。このような制限を課すことで、あなたは何とか他の方法で（たぶん、これまでに定義してきた関数を使用するといった方法）で[sum]を実現しようとがんばるでしょう。  *)

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

(** **** 練習問題: ★★★, optional (bag_more_functions) *)
(** 練習として、さらにいくつかの関数を作成してください。 *)

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* [remove_one]が[bag]に適用された際、削除すべき数値が無かった場合は、同じbagを変更しないでそのまま返す。 *)
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

(** **** 練習問題: ★★★, recommended (bag_theorem) *)
(** bagについての、[count]や[add]がからむような面白い定理を自分で考え、証明しなさい。この問題はいわゆる自由課題で、常に真となるような定理を自分で決めてかまわないのですが、その定理がこれまで習ったテクニックだけで証明できるとは限りません。もし証明に行き詰まってしまったら気軽に質問してください。

(* FILL IN HERE *)
[]
 *)


(** * リストにかかわる証明 *)

(** 数でもそうだったように、リスト処理の関数についての簡単な事実は簡約（Simplification）だけで証明することができます。例えば、[reflexivity]を使った簡約だけで、以下の定理は証明できます。 *)

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof.
   reflexivity.  Qed.

(** なぜなら、空リスト[[]]は（Notationによってnilに展開されたのち）[app]関数のmatchで最初の行が選択され、それだけで簡約できる式になるからです。  *)

(** さらに数と同様に、未知のリストを特定の形（空である場合とそうでない場合に分かれた定義）で定義した関数については、case分析がしばしば有効です。 *)

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tail l).
Proof.
  intros l. destruct l as [| n l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n l'".
    reflexivity.  Qed.

(** ここで、[nil]のcaseがうまくいく理由は、tlを定義した際、[tl nil = nil]としたからです。[destruct]タクティックの[as]句についている注釈[[| n l']]は、展開の際に[n]と[l']を名前として使いますが、これはlistのコンストラクタ[cons]の二つの引数に対応しています。（この際の二つの引数は、作成されるリストのそれぞれ[head]と[tail]にあたります *)

(** 通常、リストに関する定理の多くは証明に帰納法を必要とします。 *)


(** ** ちょっとだけお説教 *)

(** 単に例題の証明をよんでいるだけでは、大きな進歩は望めません！！各証明を実際にCoqで動かし、その証明の一行一行がどのように証明にかかわっているかを細かく見て、その道筋をていねいになぞっていくことがとても大切です。そうしなければ、これらの演習は何の意味もありません。 *)


(** ** リストでの帰納法 *)

(** [natlist]のような型に帰納法を適用するのは、おそらく普通の自然数に帰納法を使用するよりもなじみにくく感じたかもしれません。しかし基本的な考え方は同じくらいシンプルです。帰納的な宣言は、宣言されたコンストラクタが生成する値の組として定義されます。bool型では[true]か[false]ですし、数値は[O]か数値を与えた[S]ですし、リストは[nil]か、数値とリストを引数にとる[cons]の組です。

さらに言うなら、帰納的に定義された集合の要素は、あるコンストラクタの要素と、その結果を別のコンストラクタに渡したものだけです。そしてこの事実は、帰納的にに定義された集合に関する証明に直接道を開いてくれるのです。数値は[O]であるか、そうでなければ[S]により小さい数値を適用したものです。リストは[nil]であるか、そうでなければ[cons]に、数値とより要素の少ないリストを適用したものです。他のものも同様です。ですので、もし私たちがリスト[l]を参照しているいくつかの命題[P]を考え、[P]が全てのリストで成り立つことを論じたい場合は、以下のように推論すればよいのです。

      - まず、[l]が[nil]の時に[P]が[l]についてtrueであることを示す。

      - そして、[l]がある数値[n]と、より小さいリスト[l']について[cons n l']とあらわせる場合、[P]がtrueであることを示す。

大きいリストは小さいリストからのみ作成されるのですから、いつかは[nil]に達します。これら二つで、全てのリスト[l]について[P]がtrueであることが立証されるのです。以下は具体的な例です。 *)

Theorem app_ass : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons n l1'".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** 蒸し返すようですが、このCoqの証明はこうして単に静的なテキストとして読んでいる限り、さほど明白で分かりやすいものではありません。Coqの証明は、インタクラティブな環境でポイントごとに「現在のゴールは何か」「コンテキストに何が出ているか」を見て、証明が今どうなっているかを読み下していくことで理解されるようになっています。しかし、こうして画面に表示される証明の途中経過は、全てが証明結果として書き出されるわけではありません。それだけに、自然言語で人間が読むために人間が書いた証明には、このことがわかる道筋を持たせることが常に期待されています。特に、読み手が二つ目のCaseを読む中で、帰納法の仮定が何であったかをちゃんと頭に浮かべられるような書き方になっていなければなりません。  *)

(** 定理: 全てのリスト[l1], [l2], [l3]について、
   [(l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3)]。

   証明: [l1]について帰納法を適用する。

   - まず、[l1 = []]と仮定すると、[++]の定義より
[[
       ([] ++ l2) ++ l3 = [] ++ (l2 ++ l3),
]]
     が導かれる。

   - 次に[l1 = n::l1']と仮定すると
[[
       (l1' ++ l2) ++ l3 = l1' ++ (l2 ++ l3)
]]
     帰納法の仮定より、以下が示される。さらに[++]の定義より
[[
       ((n :: l1') ++ l2) ++ l3 = (n :: l1') ++ (l2 ++ l3).
]]
     が導かれる。
[[
       n :: ((l1' ++ l2) ++ l3) = n :: (l1' ++ (l2 ++ l3)),
]]
     これは、帰納法の仮定より直接導かれる  []

  次は、同じ系統の練習問題です。 *)

Theorem app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  (* WORKED IN CLASS *)
  intros l1 l2. induction l1 as [| n l1'].
  Case "l1 = nil".
    reflexivity.
  Case "l1 = cons".
    simpl. rewrite -> IHl1'. reflexivity.  Qed.

(** リストでの帰納的証明のもう少し高度な例を見てみましょう。リストの右側に数値を追加する[snoc]関数です。 *)

Fixpoint snoc (l:natlist) (v:nat) : natlist :=
  match l with
  | nil    => [v]
  | h :: t => h :: (snoc t v)
  end.

(** そしてこの関数を、リストを反転する関数[rev]の定義に使ってみましょう。 *)

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil    => nil
  | h :: t => snoc (rev t) h
  end.

Example test_rev1:            rev [1,2,3] = [3,2,1].
Proof. reflexivity.  Qed.
Example test_rev2:            rev nil = nil.
Proof. reflexivity.  Qed.

(** 新しく定義した[snoc]と[rev]を使ったいくつかの定理を証明してみましょう。これまで見てきた帰納的証明より、もう少しチャレンジングな課題として「リストを反転しても要素数は変わらない」ことを証明してみます。早速以下のようなことを試してみましたが、二つ目（successor）のケースで行き詰まってしまいました。 *)

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
  intros l. induction l as [| n l'].
  Case "l = []".
    reflexivity.
  Case "l = n :: l'".
    simpl. (* ここで行き詰まってしまいます。ゴールは[snoc]を含む等式ですが、コンテキストの中にも[snoc]が扱える対象の中にも等式は見あたりません *)
Admitted.

(** ならば、この証明を複数の補題に分割することで[snoc]にからむ等式を引き出し、証明を進める方法を検討しましょう。 *)

Theorem length_snoc : forall n : nat, forall l : natlist,
  length (snoc l n) = S (length l).
Proof.
  intros n l. induction l as [| n' l'].
  Case "l = nil".
    reflexivity.
  Case "l = cons n' l'".
    simpl. rewrite -> IHl'. reflexivity.  Qed.

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

(** 対比として、この二つの定理の非形式的な証明を見てみましょう

    定理: 任意の数[n]とリスト[l]について
       [length (snoc l n) = S (length l)].
    が成り立つ。

    証明: [l]について帰納法を適用する。

    - まず、[l = []]と仮定すると、以下の式が立つ。
[[
        length (snoc [] n) = S (length []),
]]
      これは[length]と[snoc]の定義より、直接導かれる。

    - 次に、[l = n'::l']と仮定すると、以下により
[[
        length (snoc l' n) = S (length l').
]]
      次のものが導かれる
[[
        length (snoc (n' :: l') n) = S (length (n' :: l')).
]]
      これは[length]と[snoc]の定義より、次のように変形できる。
[[
        S (length (snoc l' n)) = S (S (length l')),
]]
      これは帰納法の仮定より明らかである。 [] *)

(** 定理: 任意のリスト[l]について[length (rev l) = length l].

    証明: [l]について帰納法を適用する。

      - まず、[l = []]と仮定すると、[length]と[rev]の定義より、以下が導かれる。
[[
          length (rev []) = length [],
]]

      - 次に、[l = n::l']と仮定すると、以下により
[[
          length (rev l') = length l'.
]]
        次のものが導かれる。
[[
          length (rev (n :: l')) = length (n :: l').
]]
        [rev]の定義より、次のように変形できる。
[[
          length (snoc (rev l') n) = S (length l')
]]
        これは、以前の補題より、次のものと同じである。
[[
          S (length (rev l')) = S (length l').
]]
        これは、帰納法の仮定より明らかである。 [] *)

(** 明らかに、こういった証明のスタイルは長たらしく、杓子定規に感じられます。最初の何行かを過ぎると、こんなに瑣末なことまで細かく書かないほうが分かりやすいのではないかと思うでしょう。（頭の中で考えたり、紙に書いたりすればわかるので）もっと縮めて書くと、こんな風に書くこともできます。 *)

(** 定理:
     任煮のリスト[l]について、 [length (rev l) = length l].


    証明: まず、
[[
       length (snoc l n) = S (length l)
]]
     が任意のリスト[l]について正しいことを観察によって確認しましょう。これは[l]についての帰納法から導かれます。この性質と帰納法の仮定を[l = n'::l']という二つ目のcaseと共に観察することで、[l]について次の詞値でも成り立つことが導かれます。 [] *)

(** どちらのスタイルがより好ましいかは、それを読む人の理解度や、彼らがこれまで触れてきた証明がどちらに近いか、に依存します。多くの場合、冗長な書き方を選択したほうがよい結果となるようです。 *)


(** ** [SearchAbout] *)

(** 我々がこれまで触れてきた証明には、それ以前に証明した定理を使用することができました。[rewrite]でやったように、これからも他のやり方で以前証明した定理を使用していくことになります。しかしそれらの定理を使用するためには、その名前をまず覚えて、必要な時にそれを思い出せるようにしておかなければなりませんが、それはとても大変なことです。どんな定理が証明されていたかを思い出せても、それがどんな名前であったかが出てこないこともしばしばです。

    Coqの[SearchAbout]コマンドは、このような場合にとても便利です。[SearchAbout foo]と入力することで、Coqは[foo]にまつわる定理を一覧してくれます。例えば、次の分のコメントをはずすと、[rev]について照明された定理がリストアップされます。 *)

(* SearchAbout rev. *)

(** 続く練習問題やコースに取り組む際には、常に[SearchAbout]コマンドのことを頭のすみに置いておくといいでしょう。そうすることでずいぶん時間の節約ができるはずです。 *)

(** もしProofGeneralを使用しているなら、[C-c C-f]とキー入力することで[SearchAbout]コマンドを使うことができます。その結果をエディタに貼り付けるためには[C-c C-;]を使うこともできます。 *)


(** ** リストについての練習問題　パート１ *)

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

(** これらは、続く練習で使うことができる部品になっています。もしこれらの証明にこんがらがってしまうようなら、一度証明を戻して、もっとシンプルな方法を探してみましょう。 *)

Theorem app_ass4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  (* FILL IN HERE *) Admitted.

Theorem snoc_append : forall (l:natlist) (n:nat),
  snoc l n = l ++ [n].
Proof.
  (* FILL IN HERE *) Admitted.

(** あなたの書いた[nonzeros]関数について練習してみましょう。: *)

Lemma nonzeros_length : forall l1 l2 : natlist,
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)


(** ** リストについての練習問題　パート２ *)

(** **** 練習問題: ★★, recommended (list_design) *)
(** デザインについての練習:
     - [cons]([::]), [snoc], and [append] ([++])にかかわる、自明でない定理を考えて書きなさい。
     - それを証明しなさい。
*)

(* FILL IN HERE *)
(** [] *)

(** **** 練習問題: ★★, optional (bag_proofs) *)
(** もし、以前あったbagについてのオプション問題をやっているなら、その定義をつかって以下の定理の証明をしなさい。 *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** 次の[ble_nat]についての補題は、それに続く証明に使用できます。 *)

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

(** **** 練習問題: ★★★, optional (bag_count_sum) *)
(** bagについての、[count]と[sum]関数に関する面白そうな定理を書き、証明をしなさい。

(* FILL IN HERE *)
[]
 *)

(** **** 練習問題: ★★★★, optional (rev_injective) *)
(** [rev]関数が単射（[f(a1) = f(a2)]が成り立つならば必ず[a1 = a2]が成り立つ）であることを証明しなさい。

[[
    forall X (l1 l2 : list X), rev l1 = rev l2 -> l1 = l2.
]]

この証明には、大変な方法と楽な方法があります。
*)

(* FILL IN HERE *)
(** [] *)



(** * オプション *)

(** 日々のプログラミングで有用な、これまでなかったタイプの定義を見てみましょう。 *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

(** この[natoption]型の使い道の一つは、関数からエラーをコードを返すような場合です。例えば、リストの[n]番目の要素をあらわす関数を書くとします。そこでその関数の型を[nat -> natlist -> nat]とした場合、最初の引数に対しリストが短すぎた場合に何を返せばいいのでしょうか。 *)

Fixpoint index_bad (n:nat) (l:natlist) : nat :=
  match l with
  | nil => 42  (* arbitrary! *)
  | a :: l' => match beq_nat n O with
               | true => a
               | false => index_bad (pred n) l'
               end
  end.

(** 発想を変えて、関数の型を[nat -> natlist -> natoption]とすると、リストが短すぎた場合に[None]を返し、リストが十分に長かった場合には[Some a]という型で[n]番目に表れた値[a]を返すことができます。 *)

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

(** この例は、Coqに用意された、小さな機能「条件式」を紹介するいいサンプルになっています。 *)

Fixpoint index' (n:nat) (l:natlist) : natoption :=
  match l with
  | nil => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

(** Coqのこの機能は、他の言語で見られるものとほとんど同じですが、少しだけ一般化されています。Coqにはbool型がビルトインされていないため、二つのコンストラクタを持つ、帰納的に定義された型の全てで、この条件付の式を使用することが許されています。これにより、[Inductive]で定義された型では、一つ目のコンストラクタが評価された場合にtrue、二つ目のコンストラクタで評価された場合にfalseとみなされます。 *)

(** 次の関数は[natoption]から[nat]の値を取り出しますが、値が[None]の場合は与えられたデフォルト値を返します。 *)

Definition option_elim (o : natoption) (d : nat) : nat :=
  match o with
  | Some n' => n'
  | None => d
  end.

(** **** 練習問題: ★★ (hd_opt) *)
(** 同じ考え方を使って、以前定義した[hd]関数を、引数の値が[nil]だった場合にデフォルト値を返さなくて済むように修正しなさい。  *)

Definition hd_opt (l : natlist) : natoption :=
  (* FILL IN HERE *) admit.

Example test_hd_opt1 : hd_opt [] = None.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt2 : hd_opt [1] = Some 1.
 (* FILL IN HERE *) Admitted.

Example test_hd_opt3 : hd_opt [5,6] = Some 5.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, optional (option_elim_hd) *)
(** この練習問題は、新しい[hd_opt]と古い[hd]の関係に関するものです。 *)

Theorem option_elim_hd : forall (l:natlist) (default:nat),
  hd default l = option_elim (hd_opt l) default.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★, recommended (beq_natlist) *)
(** 二つの数値のリストを比較する関数[beq_natlist]の定義を完成させなさい。そして、[beq_natlist l l]が、任意のリスト[l]で[true]となることを証明しなさい。 *)

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


(** * [apply]タクティック *)

(** 証明を行っている際に、証明すべきゴールが、仮定や以前出てきた補題と全く同じになっている場合があります。 *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* このような場合に、これまでは"[rewrite -> eq2. reflexivity.]"とすることで証明を進めてきましたが、[apply]タクティックを代わりに使えば、たった1行で同じ結果を得ることができます。 *)
  apply eq2.  Qed.

(** また[apply]タクティックは、前提付きの仮定や補題にも使うことができます。もし適用しようとしている仮定や補題が前提付きの命題（→を含む命題）ならば、その前提部分が、証明されるべきサブゴールのリストに追加されるでしょう。 *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** この証明を実際にCoqで動かし、[rewrite]の代わりに[apply]を使った場合に何がどうなっていくのかを見極めることは、とても有意義であることが分かるでしょう。 *)

(** [apply H]を使用する典型的な例は、仮定[H]が[forall]で始まり、束縛変数を持つ式となっているような場合です。その際、現在のゴールと仮定[H]の結論がマッチできると、仮定で使われているをゴールの変数名と照らし合わせ、対応する名前を求めてくれます。例えば、次の証明で、[apply eq2]とした場合、[eq2]で使われている変数[q]は[n]に置き換えられ、[r]は[m]に置き換えられます。 *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** 練習問題: ★★, optional (silly_ex) *)
(** 次の証明を、[simpl]を使わずに完成させなさい。 *)

Theorem silly_ex :
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** [apply]タクティックを使うには、適用する仮定、定理の結論が正確にゴールと一致している必要があります。例えば、等式の左右が入れ替わっているだけでも[apply]は適用できなくなります。 *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* ここで[apply]を使いたいが使えない *)
Admitted.

(** このような場合は[symmetry]タクティックを使用して、ゴールとなっている等式の左右を入れ替えることができます。 *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* この[simpl]は必ず必要というわけではありません。[apply]は、適用する前に[simpl]を先に行ってから適用を行います。 *)
  apply H.  Qed.


(** **** 練習問題: ★★★, recommended (apply_exercise1) *)
Theorem rev_exercise1 : forall (l l' : natlist),
     l = rev l' ->
     l' = rev l.
Proof.
  (* ヒント: ここで、コンテキストに表示されている仮定以外に、以前定義した補題を[apply]に使うことができます。こんなときに[SearchAbout]が使えましたね。 *)
  (* FILL IN HERE *) Admitted.
(** [] *)


(** **** 練習問題: ★ (apply_rewrite) *)
(** [apply]と[rewrite]の違いを簡単に説明しなさい。それぞれ便利に使えるシチュエーションはどんなものでしたか？

  (* FILL IN HERE *)
*)
(** [] *)


(** * 帰納法の仮定の一般化 *)

(** ここで、機能的な証明に見られる、注目すべき点を見てみましょう。例として、以前やった[app_ass]という定理の証明をもう一度追ってみます。[induction]タクティックで作られた二つ目のサブゴールの、帰納法の仮定は以下のようなものです。

      [ (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3 ].

    ([++]が右結合で定義されていることに注意してください。上の式の右辺は[l1' ++ (l2 ++ l3)]と同じ意味になります。)

    この仮定では、[l1']が特定のリスト[l2]、[l3]とともに式を作っています。この[l2]、[l3]というリストは、証明の冒頭に、[intros]タクティックによってコンテキストに導入されたものですが、これは帰納法の仮定が「保持している定数」です。もし証明を少し違う方法で行うなら、まず最初に[n]だけをコンテキストに導入して帰納法の仮定を得ると、仮定は[forall]を含むもっと強い主張になります。

     [ forall l2 l3,  (l1' ++ l2) ++ l3 = l1' ++ l2 ++ l3 ]

    Coqで実際にその違いを確認してください。

    前のケースでは、二つの証明の違いはささいなものでした。これは[++]関数の定義が最初の引数の内容を見るだけで、二つ目の引数については何もしていないことからきています。しかし今後、どちらの方法をとるかで証明の成否が分かれてしまう場合もあることに注意してください。 *)

(** **** 練習問題: ★★, optional (app_ass') *)
(** [++]の結合則を、より一般化された仮定を用いた方法で証明しなさい。（次の証明を完成させることが課題ですが、証明の最初の行は変更しないで、その続きを書きなさい。） *)

Theorem app_ass' : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1. induction l1 as [ | n l1'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★ (apply_exercise2) *)
(** 帰納法を使う前に[m]を[intro]していないことに注意してください。これによって仮定が[forall]を使った、より一般化した式に保たれ、仮定[IH]が特定の[m]に縛られることがなくなり、使いやすくなります。 *)

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [| n'].
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★★★, recommended (beq_nat_sym_informal) *)
(** 以下の補題について、以前やった形式的な証明に対応するような非形式的証明を作成しなさい。

   定理: 任意の [nat] [n] [m]について, [beq_nat n m = beq_nat m n].

   証明:
   (* FILL IN HERE *)
[]
 *)

End NatList.


(** * 練習問題: ディクショナリ *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty  : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

(** この宣言は次のように読めます。：「[dictionary]を作成するには二つの方法がある。emptyコンストラクタを使って空の[dictionary]を表すか、[record]コンストラクタにキー、値、既存の[dictionary]を与えて、キー→値のマッピングが追加された[dictionary]を返すかのどちらかである」 *)

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

(** 以下の[find]関数は、[dictionary]から、与えられたキーに対応する値を探し出すものです。 これは、キーが見つからなかった場合に[None]を、そのキーが[val]に結び付けられていた場合に [Some val]を返します。もし同じキーが複数の値に結び付けられていれば、[find]は最初に見つかったほうの値を返します。 *)

Fixpoint find (key : nat) (d : dictionary) : option nat :=
  match d with
  | empty         => None
  | record k v d' => if (beq_nat key k) then (Some v) else (find key d')
  end.

(** **** 練習問題: ★ (dictionary_invariant1) *)
(* 次の証明を完成させなさい。 *)
Theorem dictionary_invariant1 : forall (d : dictionary) (k v: nat),
  (find k (insert k v d)) = Some v.
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

(** **** 練習問題: ★ (dictionary_invariant2) *)
(* 次の証明を完成させなさい。 *)
Theorem dictionary_invariant2 : forall (d : dictionary) (m n o: nat),
  (beq_nat m n) = false -> (find m d) = (find m (insert n o d)).
Proof.
 (* FILL IN HERE *) Admitted.
(** [] *)

End Dictionary.

(** 次の定義は[beq_nat_sym]をトップレベルの名前空間に置くものです。こうすうる理由は、今後我々がこの関数を使う際に[NatList.beq_nat_sym]と書かなくてもいいようにするためです。 *)

Definition beq_nat_sym := NatList.beq_nat_sym.

