Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Local Open Scope Z.
Local Open Scope string.

(** * 用Coq归纳类型定义二叉树 *)

Inductive tree: Type :=
| Leaf: tree
| Node (l: tree) (v: Z) (r: tree): tree.

(** 这个定义说的是，一棵二叉树要么是一棵空树_[Leaf]_，要么有一棵左子树、有一棵右
    子树外加有一个根节点整数标号。我们可以在Coq中写出一些具体的二叉树的例子。*)

Definition tree_example0: tree :=
  Node Leaf 1 Leaf.

Definition tree_example1: tree :=
  Node (Node Leaf 0 Leaf) 2 Leaf.

Definition tree_example2a: tree :=
  Node (Node Leaf 8 Leaf) 100 (Node Leaf 9 Leaf).

Definition tree_example2b: tree :=
  Node (Node Leaf 9 Leaf) 100 (Node Leaf 8 Leaf).

Definition tree_example3a: tree :=
  Node (Node Leaf 3 Leaf) 5 tree_example2a.

Definition tree_example3b: tree :=
  Node tree_example2b 5 (Node Leaf 3 Leaf).


(** Coq中，我们往往可以使用递归函数定义归纳类型元素的性质。Coq中定义递归函数时使
    用的关键字是_[Fixpoint]_。下面两个定义通过递归定义了二叉树的高度和节点个数。*)

Fixpoint tree_height (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => Z.max (tree_height l) (tree_height r) + 1
  end.

Fixpoint tree_size (t: tree): Z :=
  match t with
  | Leaf => 0
  | Node l v r => tree_size l + tree_size r + 1
  end.

(** Coq系统“知道”每一棵特定树的高度和节点个数是多少。下面是一些Coq代码的例子。*)

Example Leaf_height:
  tree_height Leaf = 0.
Proof. reflexivity. Qed.

Example tree_example2a_height:
  tree_height tree_example2a = 2.
Proof. reflexivity. Qed.

Example treeexample3b_size:
  tree_size tree_example3b = 5.
Proof. reflexivity. Qed.

(** Coq中也可以定义树到树的函数。下面的_[tree_reverse]_函数把二叉树进行了左右翻转。 *)

Fixpoint tree_reverse (t: tree): tree :=
  match t with
  | Leaf => Leaf
  | Node l v r => Node (tree_reverse r) v (tree_reverse l)
  end.

(** 下面是三个二叉树左右翻转的例子：*)

Example Leaf_tree_reverse:
  tree_reverse Leaf = Leaf.
Proof. reflexivity. Qed.

Example tree_example0_tree_reverse:
  tree_reverse tree_example0 = tree_example0.
Proof. reflexivity. Qed.

Example tree_example3_tree_reverse:
  tree_reverse tree_example3a = tree_example3b.
Proof. reflexivity. Qed.

(** 归纳类型有几条基本性质。(1) 归纳定义规定了一种分类方法，以_[tree]_类型为例，
    一棵二叉树_[t]_要么是_[Leaf]_，要么具有形式_[Node l v r]_；(2) 以上的分类之
    间是互斥的，即无论_[l]_、_[v]_与_[r]_取什么值，_[Leaf]_与_[Node l v r]_都不
    会相等；(3) _[Node]_这样的构造子是函数也是单射。这三条性质对应了Coq中的三条
    证明指令：_[destruct]_、_[discriminate]_与_[injection]_。利用它们就可以证明
    几条最简单的性质：*)

Lemma Node_inj_left: forall l1 v1 r1 l2 v2 r2,
  Node l1 v1 r1 = Node l2 v2 r2 ->
  l1 = l2.
Proof.
  intros.
  injection H as H_l H_v H_r.
  (** 上面的_[injection]_指令使用了_[Node]_是单射这一性质。*)
  rewrite H_l.
  reflexivity.
Qed.

(** 有时，手动为_[injection]_生成的命题进行命名显得很啰嗦，Coq允许用户使用问号占
    位，从而让Coq进行自动命名。*)

Lemma Node_inj_right: forall l1 v1 r1 l2 v2 r2,
  Node l1 v1 r1 = Node l2 v2 r2 ->
  r1 = r2.
Proof.
  intros.
  injection H as ? ? ?.
  (** 这里，Coq自动命名的结果是使用了_[H]_、_[H0]_与_[H1]_。下面也使用_[apply]_
      指令取代_[rewrite]_简化后续证明。*)
  apply H1.
Qed.

(** 如果不需要用到_[injection]_生成的左右命题，可以将不需要用到的部分用下划线占
    位。*)

Lemma Node_inj_value: forall l1 v1 r1 l2 v2 r2,
  Node l1 v1 r1 = Node l2 v2 r2 ->
  v1 = v2.
Proof.
  intros.
  injection H as _ ? _.
  apply H.
Qed.

(** 下面引理说：若_[Leaf]_与_[Node l v r]_相等，那么_[1 = 2]_。换言之，_[Leaf]_
    与_[Node l v r]_始终不相等，否则就形成了一个矛盾的前提。*)

Lemma Leaf_Node_conflict: forall l v r,
  Leaf = Node l v r -> 1 = 2.
Proof.
  intros.
  discriminate.
Qed.

(** 下面这个简单性质与_[tree_reverse]_有关。*)

Lemma reverse_result_Leaf: forall t,
  tree_reverse t = Leaf ->
  t = Leaf.
Proof.
  intros.
  (** 下面的_[destruct]_指令根据_[t]_是否为空树进行分类讨论。*)
  destruct t.
  (** 执行这一条指令之后，Coq中待证明的证明目标由一条变成了两条，对应两种情况。
      为了增加Coq证明的可读性，我们推荐大家使用bullet记号把各个子证明过程分割开
      来，就像一个一个抽屉或者一个一个文件夹一样。Coq中可以使用的bullet标记有：
      _[+ - * ++ -- **]_等等*)
  + reflexivity.
    (** 第一种情况是_[t]_是空树的情况。这时，待证明的结论是显然的。*)
  + discriminate H.
    (** 第二种情况下，其实前提_[H]_就可以推出矛盾。可以看出，_[discriminate]_指
        令也会先根据定义化简，再试图推出矛盾。*)
Qed.

(** * 结构归纳法 *)


(** 我们接下去将证明一些关于_[tree_height]_，_[tree_size]_与_[tree_reverse]_的基
    本性质。我们在证明中将会使用的主要方法是归纳法。  

    相信大家都很熟悉自然数集上的数学归纳法。数学归纳法说的是：如果我们要证明某性
    质_[P]_对于任意自然数_[n]_都成立，那么我可以将证明分为如下两步：  
    奠基步骤：证明_[P 0]_成立；  
    归纳步骤：证明对于任意自然数_[n]_，如果_[P n]_成立，那么_[P (n + 1)]_也成
    立。  


    对二叉树的归纳证明与上面的数学归纳法稍有不同。具体而言，如果我们要证明某性质
    _[P]_对于一切二叉树_[t]_都成立，那么我们只需要证明以下两个结论：  

    奠基步骤：证明_[P Leaf]_成立；  
    归纳步骤：证明对于任意二叉树_[l]_ _[r]_以及任意整数标签_[n]_，如果_[P l]_与
    _[P r]_都成立，那么_[P (Node l n r)]_也成立。  

    这样的证明方法就成为结构归纳法。在Coq中，_[induction]_指令表示：使用结构归纳
    法。下面是几个证明的例子。  


    第一个例子是证明_[tree_size]_与_[tree_reverse]_之间的关系。*)

Lemma reverse_size: forall t,
  tree_size (tree_reverse t) = tree_size t.
Proof.
  intros.
  induction t.
  (** 上面这个指令说的是：对_[t]_结构归纳。Coq会自动将原命题规约为两个证明目标，
      即奠基步骤和归纳步骤。*)
  + simpl.
    (** 第一个分支是奠基步骤。这个_[simpl]_指令表示将结论中用到的递归函数根据定
        义化简。*)
    reflexivity.
  + simpl.
    (** 第二个分支是归纳步骤。我们看到证明目标中有两个前提_[IHt1]_以及_[IHt2]_。
        在英文中_[IH]_表示induction hypothesis的缩写，也就是归纳假设。在这个证明
        中_[IHt1]_与_[IHt2]_分别是左子树_[t1]_与右子树_[t2]_的归纳假设。 *)

    rewrite IHt1.
    rewrite IHt2.
    lia.
Qed.


(** 第二个例子很类似，是证明_[tree_height]_与_[tree_reverse]_之间的关系。*)

Lemma reverse_height: forall t,
  tree_height (tree_reverse t) = tree_height t.
Proof.
  intros.
  induction t.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHt1.
    rewrite IHt2.
    lia.
    (** 注意：_[lia]_指令也是能够处理_[Z.max]_与_[Z.min]_的。*)
Qed.

(** 下面我们将通过重写上面这一段证明，介绍Coq证明语言的一些其他功能。*)

Lemma reverse_height_attempt2: forall t,
  tree_height (tree_reverse t) = tree_height t.
Proof.
  intros.
  induction t; simpl.
  (** 在Coq证明语言中可以用分号将小的证明指令连接起来形成大的证明指令，其中
      _[tac1 ; tac2]_这个证明指令表示先执行指令_[tac1]_，再对于_[tac1]_生成的每
      一个证明目标执行_[tac2]_。分号是右结合的。*)
  + reflexivity.
  + simpl.
    lia.
Qed.

(************)
(** 习题：  *)
(************)

Lemma reverse_involutive: forall t,
  tree_reverse (tree_reverse t) = t.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Lemma size_nonneg: forall t,
  0 <= tree_size t.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Lemma reverse_result_Node: forall t t1 k t2,
  tree_reverse t = Node t1 k t2 ->
  t = Node (tree_reverse t2) k (tree_reverse t1).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** * 加强归纳 *)


(** 下面证明_[tree_reverse]_是一个单射。*)

Lemma tree_reverse_inj: forall t1 t2,
  tree_reverse t1 = tree_reverse t2 ->
  t1 = t2.
Proof.
  (** 这个引理的Coq证明需要我们特别关注：真正需要归纳证明的结论是什么？如果选择
      对_[t1]_做结构归纳，那么究竟是归纳证明对于任意_[t2]_上述性质成立，还是归纳
      证明对于某“特定”的_[t2]_上述性质成立？如果我们按照之前的Coq证明习惯，用
      _[intros]_与_[induction t1]_两条指令开始证明，那就表示用归纳法证明一条关于
      “特定”_[t2]_的性质。*)
  intros.
  induction t1.
  + destruct t2.
    (** 奠基步骤的证明可以通过对_[t2]_的分类讨论完成。*)
    - reflexivity.
      (** 如果_[t2]_是空树，那么结论是显然的。*)
    - simpl in H.
      discriminate H.
      (** 如果_[t2]_是非空树，那么前提_[H]_就能导出矛盾。如上面指令展示的那样，
          _[simpl]_指令也可以对前提中的递归定义化简。当然，在这个证明中，由于之
          后的_[discriminate]_指令也会完成自动化简，这条_[simpl]_指令其实是可以
          省略的。*)
  +
Abort.

(** 进入归纳步骤的证明时，不难发现，证明已经无法继续进行。因为需要使用的归纳假设
    并非关于原_[t2]_值的性质。正确的证明方法是用归纳法证明一条对于一切_[t2]_的结
    论。*)

Lemma tree_reverse_inj: forall t1 t2,
  tree_reverse t1 = tree_reverse t2 ->
  t1 = t2.
Proof.
  intros t1.
  (** 上面这条_[intros 1t]_指令可以精确地将_[t1]_放到证明目标的前提中，同时却将
      _[t2]_保留在待证明目标的结论中。*)
  induction t1; simpl; intros.
  + destruct t2.
    - reflexivity.
    - discriminate H.
  + destruct t2.
    - discriminate H.
    - injection H as ? ? ?.
      rewrite (IHt1_1 _ H1).
      rewrite (IHt1_2 _ H).
      rewrite H0.
      reflexivity.
Qed.

(** 当然，上面这条引理其实可以不用归纳法证明。下面的证明中使用了前面证明的结论：
    _[reverse_involutive]_。*)

Lemma tree_reverse_inj_again: forall t1 t2,
  tree_reverse t1 = tree_reverse t2 ->
  t1 = t2.
Proof.
  intros.
  rewrite <- (reverse_involutive t1), <- (reverse_involutive t2).
  rewrite H.
  reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 下面的_[left_most]_函数与_[right_most]_函数计算了二叉树中最左侧的节点信息与
    最右侧的节点信息。如果树为空，则返回_[default]_。*)

Fixpoint left_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => left_most l n
  end.

Fixpoint right_most (t: tree) (default: Z): Z :=
  match t with
  | Leaf => default
  | Node l n r => right_most r n
  end.

(** 很显然，这两个函数应当满足：任意一棵二叉树的最右侧节点，就是将其左右翻转之后
    最左侧节点。这个性质可以在Coq中如下描述：*)

Lemma left_most_reverse: forall t default,
  left_most (tree_reverse t) default = right_most t default.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** * 用递归函数定义性质 *)

(** 我们同样可以利用递归函数定义二叉树的一些性质。 *)

Fixpoint tree_le (ub: Z) (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => tree_le ub l /\ k <= ub /\ tree_le ub r
  end.

Fixpoint tree_ge (lb: Z) (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => tree_ge lb l /\ k >= lb /\ tree_ge lb r
  end.

(** 这里，_[tree_le n t]_表示树中每个节点标号的值都小于等于_[n]_，类似的，
    _[tree_ge n t]_表示树中每个节点标号的值都大于等于_[n]_。下面用_[<<=]_与_[>>=]_
    两个符号表示上面定义的_[tree_le]_和_[tree_ge]_. *)

Declare Scope tree_scope.
Local Open Scope tree_scope.
Notation "t <<= n" := (tree_le n t)
  (at level 49, no associativity): tree_scope.
Notation "t >>= n" := (tree_ge n t)
  (at level 49, no associativity): tree_scope.

(** 进一步，我们还可以定义，树中元素根据中序遍历是从小到大排列的_[low2high]_，或
    从大到小排列的_[high2low]_这两条性质。*)

Fixpoint low2high (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => low2high l /\ l <<= k /\ r >>= k /\ low2high r
  end.

Fixpoint high2low (t: tree): Prop :=
  match t with
  | Leaf => True
  | Node l k r => high2low l /\ l >>= k /\ r <<= k /\ high2low r
  end.

(** 下面证明一些关于它们的有趣性质。我们先试着证明：如果_[t]_中元素中序遍历是从
    小到大的，那么将其左右翻转后，其中元素的中序遍历是从大到小的。*)

Lemma reverse_low2high: forall t,
  low2high t ->
  high2low (tree_reverse t).
Proof.
  intros.
  induction t.
  + simpl.
    exact I.
  + simpl in H.
    simpl.
    (** 看来，我们需要一些关于_[<<=]_与_[>>=]_的辅助引理。*)
Abort.

(** 首先证明关于_[<<=]_的引理。*)

Lemma reverse_le: forall n t,
  t <<= n ->
  tree_reverse t <<= n.
Proof.
  intros.
  induction t; simpl.
  + exact I.
  + simpl in H.
    destruct H as [Ht1 [? Ht2]].
    split; [| split].
    (** 这里，_[tac; [ tac1 | tac2 | ... | tacn]]_表示先运行_[tac]_指令，该指
        令会产生n个证明目标，之后对这n个证明目标分别执行_[tac1]_、_[tac2]_ ...
        _[tacn]_这n个指令。
        除此之外，有时可能第一个指令生成的证明目标太多了，这时可以用双点号简写，
        例如_[tac; [ tac1 | tac2 | tac3 .. ]]_表示先运行_[tac]_指令，之后在其
        生成的第一第二个证明子目标中分别执行_[tac1]_与_[tac2]_，并在其余所有证明
        目标中执行_[tac3]_。 *)
    - apply IHt2.
      exact Ht2.
    - exact H.
    - apply IHt1.
      exact Ht1.
Qed.

(** 其次证明关于_[>>=]_的引理。*)

Lemma reverse_ge: forall n t,
  t >>= n ->
  tree_reverse t >>= n.
Proof.
  intros.
  induction t; simpl.
  + exact I.
  + simpl in H.
    tauto.
    (** 这个指令_[tauto]_表示使用命题逻辑完成证明，它能够自动完成关于_[/\]_、
         _[\/]_、_[~]_、_[->]_、_[True]_与_[False]_的证明。 *)
Qed.

(** 现在，准备工作已经就绪，可以开始证明_[reverse_low2high]_了，这一个证明留作习
    题。*)

(************)
(** 习题：  *)
(************)

Lemma reverse_low2high: forall t,
  low2high t ->
  high2low (tree_reverse t).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 最后，我们再定义一个关于两棵树的性质，并证明几个基本结论。*)

Fixpoint same_structure (t1 t2: tree): Prop :=
  match t1, t2 with
  | Leaf, Leaf =>
      True
  | Leaf, Node _ _ _ =>
      False
  | Node _ _ _, Leaf =>
      False
  | Node l1 _ r1, Node l2 _ r2 =>
      same_structure l1 l2 /\ same_structure r1 r2
  end.

(** 这个定义说的是：两棵二叉树结构相同，但是每个节点上标号的值未必相同。从这一定
    义的语法也不难看出，Coq中允许同时对多个对象使用_[match]_并且可以用下划线省去
    用不到的_[match]_信息。  

    下面证明，如果两棵树结构相同，那么它们的高度也相同。*)

Lemma same_structure_same_height: forall t1 t2,
  same_structure t1 t2 ->
  tree_height t1 = tree_height t2.
Proof.
  intros.
  (** 要证明这一结论，很自然的思路是要对_[t1]_做结构归纳证明。这样一来，当_[t1]_
      为非空树时，归纳假设大致是：_[t1]_的左右子树分别与_[t2]_的左右子树结构相
      同，显然，这样的归纳假设可以理解推出最终的结论。*)
  induction t1.
  (** 下面先进行奠基步骤的证明。*)
  + destruct t2.
    - reflexivity.
    - simpl in H.
      contradiction.
  +
  (** 下面进入归纳步骤。然而，通过观察此时的证明目标，我们会发现，当前证明目标与
      我们先前的设想并不一致！我们设想的证明步骤中，归纳假设应当是归于_[t2]_的子
      树的，而非归于_[t2]_本身的。这里的问题在于，当我们执行_[induction t1]_证明
      指令时，_[t2]_已经在证明目标的前提中了，这意味着，我们告诉Coq，要对某个特
      定的_[t2]_完成后续证明。这并不是我们先前拟定的证明思路。*)
Abort.

(** 解决这一问题的办法是像我们先前介绍的那样采用加强归纳法。*)

Lemma same_structure_same_height: forall t1 t2,
  same_structure t1 t2 ->
  tree_height t1 = tree_height t2.
Proof.
  intros t1.
  induction t1 as [| l1 IHl v1 r1 IHr]; intros.
  (** 奠基步骤与原先类似。 *)
  + destruct t2.
    - reflexivity.
    - simpl in H.
      contradiction.
  (** 归纳步骤中，归纳假设现在不同了 *)
  + destruct t2 as [| l2 v2 r2]; simpl in H.
    - contradiction.
    - destruct H.
      (** 现在我们可以将归纳假设作用在_[t2]_的子树上了。 *)
      apply IHl in H.
      apply IHr in H0.
      simpl.
      lia.
Qed.

(************)
(** 习题：  *)
(************)


(** 下面的证明留作习题。*)

Theorem same_structure_trans: forall t1 t2 t3,
  same_structure t1 t2 ->
  same_structure t2 t3 ->
  same_structure t1 t3.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** * Coq标准库中的list *)

Module ListDemo.

(** 在Coq中，_[list X]_表示一列_[X]_类型的元素，在标准库中，这一类型是通过Coq归
    纳类型定义的。下面介绍它的定义方式，重要函数与性质。此处为了演示这些函数的定
    义方式以及从定义出发构建各个性质的具体步骤重新按照标准库定义了_[list]_，下面
    的所有定义和性质都可以从标准库中找到。*)

Inductive list (X: Type): Type :=
  | nil: list X
  | cons (x: X) (l: list X): list X.

(** 这里，_[nil]_表示，这是一个空列；_[cons]_表示一个非空列由一个元素（头元素）
    和另外一列元素（其余元素）构成，因此_[list]_可以看做用归纳类型表示的树结构的
    退化情况。下面是两个整数列表_[list Z]_的例子。*)

Check (cons Z 3 (nil Z)).
Check (cons Z 2 (cons Z 1 (nil Z))).

(** Coq中也可以定义整数列表的列表，_[list (list Z)]_。*)

Check (cons (list Z) (cons Z 2 (cons Z 1 (nil Z))) (nil (list Z))).

(** 我们可以利用Coq的隐参数机制与_[Arguments]_指令，让我们省略_[list]_定义中的类
    型参数。*)

Arguments nil {X}.
Arguments cons {X} _ _.

(** 例如，我们可以重写上面这些例子: *)

Check (cons 3 nil).
Check (cons 2 (cons 1 nil)).
Check (cons (cons 2 (cons 1 nil)) nil).

(** Coq标准库还提供了一些_[Notation]_让_[list]_相关的描述变得更简单。 *)

Notation "x :: y" := (cons x y)
  (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

(** 下面用同一个整数序列的三种表示方法来演示利用这些_[Notation]_的使用方法，读者
    不需要完全理解上面这些_[Notation]_声明的细节。*)

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1; 2; 3].

(** 下面介绍一些常用的关于_[list]_函数。根据Coq的要求，归纳类型的递归函数必须依据归纳
    定义的方式进行递归。换言之，要定义_[list]_类型上的递归函数，就要能够计算这个
    _[list]_取值为_[nil]_的结果，并将这个_[list]_取值为_[cons a l]_时的结果规约为取
    值为_[l]_时的结果。一些关于列表的直观概念，都需要通过这样的方式导出，例如列表的长
    度、列表第i项的值等等。   

    函数_[app]_表示列表的连接。*)

Fixpoint app {A: Type} (l1 l2: list A): list A :=
  match l1 with
  | nil        => l2
  | cons a l1' => cons a (app l1' l2)
  end.

(** 在Coq中一般可以用_[++]_表示_[app]_。 *)

Notation "x ++ y" := (app x y)
  (right associativity, at level 60).

(** 函数_[rev]_表示对列表取反。*)

Fixpoint rev {A} (l: list A) : list A :=
  match l with
  | nil    => nil
  | cons a l' => rev l' ++ [a]
  end.

(** 下面是一些例子关于_[app]_和_[rev]_的例子。*)

Example test_app1: [1; 2; 3] ++ [4; 5] = [1; 2; 3; 4; 5].
Proof. reflexivity.  Qed.
Example test_app2: [2] ++ [3] ++ [] ++ [4; 5] = [2; 3; 4; 5].
Proof. reflexivity.  Qed.
Example test_app3: [1; 2; 3] ++ nil = [1; 2; 3].
Proof. reflexivity.  Qed.
Example test_rev:  rev [1; 2; 3] = [3; 2; 1].
Proof. reflexivity.  Qed.

(** 下面是一些关于_[app]_和_[rev]_的重要性质，它们的证明留作习题。*)

(************)
(** 习题：  *)
(************)

Theorem app_assoc: forall A (l1 l2 l3: list A),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Theorem app_nil_r : forall A (l : list A),
  l ++ [] = l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Theorem rev_app_distr: forall A (l1 l2 : list A),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

Theorem rev_involutive : forall A (l : list A),
  rev (rev l) = l.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 如果熟悉函数式编程，不难发现，上面的_[rev]_定义尽管在数学是简洁明确的，但是
    其计算效率是比较低的。相对而言，利用下面的_[rev_append]_函数进行计算则效率较
    高。*)

Fixpoint rev_append {A} (l l': list A): list A :=
  match l with
  | []     => l'
  | h :: t => rev_append t (h :: l')
  end.

(** 下面分两步证明_[rev]_与_[rev_append]_之间的相关性。*)

(************)
(** 习题：  *)
(************)

Lemma rev_append_rev: forall A (l l': list A),
  rev_append l l' = rev l ++ l'.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Theorem rev_alt: forall A (l: list A),
  rev l = rev_append l [].
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 下面的_[map]_函数表示对一个_[list]_中的所有元素统一做映射。*)

Fixpoint map {X Y: Type} (f: X -> Y) (l: list X): (list Y) :=
  match l with
  | nil       => nil
  | cons x l' => cons (f x) (map f l')
  end.

(** 下面是一些例子： *)

Example test_map1: map (fun x => x - 2) [7; 5; 7] = [5; 3; 5].
Proof. reflexivity. Qed.
Example test_map2: map (fun x => x * x) [2; 1; 5] = [4; 1; 25].
Proof. reflexivity. Qed.
Example test_map3: map (fun x => [x]) [0; 1; 2; 3] = [[0]; [1]; [2]; [3]].
Proof. reflexivity. Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[map]_的性质。*)

Theorem map_app: forall X Y (f: X -> Y) (l l': list X),
  map f (l ++ l') = map f l ++ map f l'.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[map]_的性质。*)

Theorem map_rev : forall X Y (f: X -> Y) (l: list X),
  map f (rev l) = rev (map f l).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 在基于_[list]_的计算中，有两类常见的计算，一类是从左向右计算，一类是从右向左计算。
    以对整数序列求和为例，下面的_[sum_L2R]_刻画了从左向右的计算方法，而_[sum_R2L]_刻
    画了从右向左的计算方法。*)

Fixpoint sum_L2R_rec (s: Z) (l: list Z): Z :=
  match l with
  | nil       => s
  | cons z l' => sum_L2R_rec (s + z) l'
  end.

Definition sum_L2R (l: list Z): Z := sum_L2R_rec 0 l.

Fixpoint sum_R2L (l: list Z): Z :=
  match l with
  | nil       => 0
  | cons z l' => z + sum_R2L l'
  end.

(** 直观上看，两者的区别是：  

           _[sum_L2R [1; 3; 5; 7]]_ = _[(((0 + 1) + 3) + 5) + 7]_   

           _[sum_R2L [1; 3; 5; 7]]_ = _[1 + (3 + (5 + (7 + 0)))]_   

    许多列表上的运算都可以归结为从左向右计算和从右向左计算。Coq标准库把这样的通用计算模
    式刻画为_[fold_left]_与_[fold_right]_。*)

Fixpoint fold_left {A B: Type} (f: A -> B -> A) (l: list B) (a0: A): A :=
  match l with
  | nil       => a0
  | cons b l' => fold_left f l' (f a0 b)
  end.

Fixpoint fold_right {A B: Type} (f: A -> B -> B) (b0: B) (l: list A): B :=
  match l with
  | nil       => b0
  | cons a l' => f a (fold_right f b0 l')
  end.

(** 仔细观察，不难发现，_[sum_L2R]_与_[sum_R2L]_可以分别用_[fold_left]_与
    _[fold_right]_表示出来。下面是它们的对应关系。*)

Fact sum_L2R_rec_is_fold_left: forall (s: Z) (l: list Z),
  sum_L2R_rec s l = fold_left (fun z1 z2 => z1 + z2) l s.
Proof.
  intros.
  revert s; induction l; intros; simpl.
  + reflexivity.
  + apply IHl.
Qed.

Fact sum_L2R_is_fold_left: forall l: list Z,
  sum_L2R l = fold_left (fun z1 z2 => z1 + z2) l 0.
Proof.
  intros.
  unfold sum_L2R.
  apply sum_L2R_rec_is_fold_left.
Qed.

Fact sum_R2L_is_fold_right: forall l: list Z,
  sum_R2L l = fold_right (fun z1 z2 => z1 + z2) 0 l.
Proof.
  intros.
  induction l; simpl.
  + reflexivity.
  + rewrite IHl.
    reflexivity.
Qed.

(** 当然，我们都知道，根据加法结合律_[sum_L2R]_与_[sum_R2L]_应当相等。这可以通过加强
    归纳法完成证明。*)

Lemma sum_L2R_rec_sum_R2L: forall (s: Z) (l: list Z),
  sum_L2R_rec s l = s + sum_R2L l.
Proof.
  intros.
  revert s; induction l; intros; simpl.
  + lia.
  + rewrite IHl.
    lia.
Qed.

Theorem sum_L2R_sum_R2L: forall (l: list Z),
  sum_L2R l = sum_R2L l.
Proof.
  intros.
  unfold sum_L2R.
  rewrite sum_L2R_rec_sum_R2L.
  lia.
Qed.

(** 一般而言，要证明两项“从左向右”计算之间的关系比较容易，要证明两种“从右向左”计算之间
    的关系也比较容易。但是要证明“从左向右”与“从右向左”之间的关系往往就要复杂一些。上面
    我们采用的加强归纳法是一种常见的证明手段。*)

(************)
(** 习题：  *)
(************)

(** 请试着证明下面结论。第一小题将_[fold_left]_转化为_[fold_right]_。*)

Theorem fold_left_fold_right:
  forall {A B: Type} (f: A -> B -> A) (l: list B) (a0: A),
    fold_left f l a0 =
    fold_right (fun (b: B) (g: A -> A) (a: A) => g (f a b)) (fun a => a) l a0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 第二小题是将_[fold_right]_转化为_[fold_left]_。提示：尽管这一小题看上去与第一小
    题是对称的，但是它证明起来要复杂很多，可能需要引入一条辅助引理才能完成证明。*)
Theorem fold_right_fold_left:
  forall {A B: Type} (f: A -> B -> B) (b0: B) (l: list A),
    fold_right f b0 l =
    fold_left (fun (g: B -> B) (a: A) (b: B) => g (f a b)) l (fun b => b) b0.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


End ListDemo.

(** * Coq标准库中的string *)

Module StringDemo.

(** 除了一般性的列表_[list]_之外，Coq标准库中还定义了字符串这一数学对象。例如下面这些
    都是字符串。*)

Check "abc".
Check "Hello world".
Check "".

(** 字符串集合_[string]_的定义与_[list]_十分相似：  
        Inductive string :=
        | EmptyString: string
        | String: (c: ascii) (s: string).   
    其中，_[EmptyString]_就相当于_[nil]_，_[String]_就相当于_[cons]_，_[ascii]_表
    示所有ascii码的集合。因此，我们可以很容易的定义_[string]_与_[list]_之间的相互转
    化。双向的转化函数都可以用Coq结构递归函数定义。*)

Fixpoint list_ascii_of_string (s: string): list ascii :=
  match s with
  | EmptyString => nil
  | String c0 s0 => cons c0 (list_ascii_of_string s0)
  end.

Fixpoint string_of_list_ascii (l: list ascii): string :=
  match l with
  | nil => EmptyString
  | cons c0 l0 => String c0 (string_of_list_ascii l0)
  end.

(** 在此基础上，我们又可以利用Coq中的结构归纳法证明这两个转化函数互为反函数。*)

Lemma string_of_list_ascii_of_string:
  forall s: string, string_of_list_ascii (list_ascii_of_string s) = s.
Proof.
  intros.
  induction s; simpl.
  + reflexivity.
  + rewrite IHs.
    reflexivity.
Qed.

Lemma list_ascii_of_string_of_list_ascii:
  forall l: list ascii, list_ascii_of_string (string_of_list_ascii l) = l.
Proof.
  intros.
  induction l; simpl.
  + reflexivity.
  + rewrite IHl.
    reflexivity.
Qed.

(** 数学上，我们称一个函数_[f: A -> B]_是一个双射，当且仅当   

        _[forall a1 a2: A,  f a1 = f a2 -> a1 = a2]_   

        _[forall b: B, exists a: A, f a = b]_。   

    而在Coq中，往往会直接显式地写出函数和它的反函数，这样也便于在后续证明中使用
    _[rewrite]_重写指令证明。例如，要在上面两结论基础上，证明
    _[list_ascii_of_string]_是双射是容易的。*)

Lemma list_ascii_of_string_inj: forall s1 s2: string,
  list_ascii_of_string s1 = list_ascii_of_string s2 ->
  s1 = s2.
Proof.
  intros.
  rewrite <- (string_of_list_ascii_of_string s1).
  rewrite <- (string_of_list_ascii_of_string s2).
  rewrite H.
  reflexivity.
Qed.

Lemma list_ascii_of_string_surj: forall l: list ascii,
  exists s: string, list_ascii_of_string s =  l.
Proof.
  intros.
  exists (string_of_list_ascii l).
  apply list_ascii_of_string_of_list_ascii.
Qed.

End StringDemo.

(** 上面提到的这些转化函数与反函数性质都是Coq标准库中提供的定义与证明。*)

(** * Coq标准库中的nat *)

(** 在Coq中，许多数学上的集合可以用归纳类型定义。例如，Coq中自然数的定义就是最简
    单的归纳类型之一。  

    下面Coq代码可以用于查看_[nat]_在Coq中的定义。*)
Print nat.
(** 查询结果如下。  
    Inductive nat := O : nat | S: nat -> nat.   

    可以看到，自然数集合的归纳定义可以看做_[list]_进一步退化的结果。下面我们在
    Coq中定义自然数的加法，并且也试着证明一条基本性质：加法交换律。  


    由于Coq的标准库中已经定义了自然数以及自然数的加法。我们开辟一个_[NatDemo]_来
    开发我们自己的定义与证明。以免与Coq标准库的定义相混淆。*)

Module NatDemo.

(** 先定义自然数_[nat]_。*)

Inductive nat :=
| O: nat
| S (n: nat): nat.

(** 再定义自然数加法。*)

Fixpoint add (n m: nat): nat :=
  match n with
  | O => m
  | S n' => S (add n' m)
  end.

(** 下面证明加法交换律。*)

Theorem add_comm: forall n m,
  add n m = add m n.
Proof.
  intros.
  induction n.
  (** 证明到此处，我们发现我们需要首先证明_[n + 0 = n]_这条性质，我们先终止交换
      律的证明，而先证明这条引理。*)
Abort.

Lemma add_0_r: forall n, add n O = n.
Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn.
    reflexivity.
Qed.

Theorem add_comm: forall n m,
  add n m = add m n.
Proof.
  intros.
  induction n; simpl.
  + rewrite add_0_r.
    reflexivity.
  + (** 证明到此处，我们发现我们需要还需要证明关于_[m + (S n)]_相关的性质。*)
Abort.

Lemma add_succ_r: forall n m,
  add n (S m) = S (add n m).
Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn.
    reflexivity.
Qed.

(** 现在已经可以在Coq中完成加法交换律的证明了。*)

Theorem add_comm: forall n m,
  add n m = add m n.
Proof.
  intros.
  induction n; simpl.
  + rewrite add_0_r.
    reflexivity.
  + rewrite add_succ_r.
    rewrite IHn.
    reflexivity.
Qed.

(** 由于自然数范围内，数学意义上的减法是一个部分函数，因此，相关定义在Coq中并不常用。相
    对而言，自然数的加法与乘法在Coq中更常用。*)

Fixpoint mul (n m: nat): nat :=
  match n with
  | O => O
  | S p => add m (mul p m)
  end.

(** 下面列举加法与乘法的其它重要性质。*)

Theorem add_assoc:
  forall n m p, add n (add m p) = add (add n m) p.
Proof.
  intros n m p; induction n; simpl.
  + reflexivity.
  + simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem add_cancel_l:
  forall n m p, add p n = add p m <-> n = m.
Proof.
  intros n m p; split.
  + induction p; simpl; intros H.
    - tauto.
    - injection H as H.
      pose proof IHp H.
      tauto.
  + intros H.
    rewrite H.
    reflexivity.
Qed.

Theorem add_cancel_r:
  forall n m p, add n p = add m p <-> n = m.
Proof.
  intros n m p.
  rewrite (add_comm n p), (add_comm m p).
  apply add_cancel_l.
Qed.

Lemma mul_0_r: forall n, mul n O = O.
Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + apply IHn.
Qed.

Lemma mul_succ_r:
  forall n m, mul n (S m) = add (mul n m) n.
Proof.
  intros n m; induction n; simpl.
  + reflexivity.
  + rewrite IHn, add_succ_r.
    rewrite <- add_assoc.
    reflexivity.
Qed.

Theorem mul_comm:
  forall n m, mul n m = mul m n.
Proof.
  intros n m; induction n; simpl.
  + rewrite mul_0_r.
    reflexivity.
  + rewrite mul_succ_r.
    rewrite IHn, add_comm.
    reflexivity.
Qed.

Theorem mul_add_distr_r:
  forall n m p, mul (add n m) p = add (mul n p) (mul m p).
Proof.
  intros n m p; induction n; simpl.
  - reflexivity.
  - rewrite <- add_assoc, IHn.
    reflexivity.
Qed.

Theorem mul_add_distr_l:
  forall n m p, mul n (add m p) = add (mul n m) (mul n p).
Proof.
  intros n m p.
  rewrite (mul_comm n (add m p)), (mul_comm n m), (mul_comm n p).
  apply mul_add_distr_r.
Qed.

Theorem mul_assoc:
  forall n m p, mul n (mul m p) = mul (mul n m) p.
Proof.
  intros n m p; induction n; simpl.
  + reflexivity.
  + rewrite IHn, mul_add_distr_r.
    reflexivity.
Qed.

Theorem mul_1_l : forall n, mul (S O) n = n.
Proof. intros. simpl. apply add_0_r. Qed.

Theorem mul_1_r : forall n, mul n (S O) = n.
Proof. intros. rewrite mul_comm, mul_1_l. reflexivity. Qed.

End NatDemo.

(** 上面介绍的加法与乘法运算性质在Coq标准库中已有证明，其定理名称如下。*)

Check Nat.add_comm.
Check Nat.add_assoc.
Check Nat.add_cancel_l.
Check Nat.add_cancel_r.
Check Nat.mul_comm.
Check Nat.mul_add_distr_r.
Check Nat.mul_add_distr_l.
Check Nat.mul_assoc.
Check Nat.mul_1_l.
Check Nat.mul_1_r.

(** 前面已经提到，Coq在自然数集合上不便于表达减法等运算，因此，Coq用户有些时候可以选用
    _[Z]_而非_[nat]_。然而，由于其便于表示计数概念以及表述数学归纳法，_[nat]_依然有许
    多用途。例如，Coq标准库中的_[Nat.iter]_就表示函数多次迭代，具体而言，
    _[Nat.iter n f]_表示将函数_[f]_迭代_[n]_次的结果。其Coq定义如下：  

    Fixpoint iter {A: Type} (n: nat) (f: A -> A) (x: A): A :=
      match n with
      | O => x
      | S n' => f (iter n' f x)
      end.   

    它符合许多重要性质，例如：*)

Theorem iter_S: forall {A: Type} (n: nat) (f: A -> A) (x: A),
  Nat.iter n f (f x) = Nat.iter (S n) f x.

(** 注意，哪怕是如此简单的性质，我们还是需要在Coq中使用归纳法证明。*)

Proof.
  intros.
  induction n; simpl.
  + reflexivity.
  + rewrite IHn; simpl.
    reflexivity.
Qed.

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[Nat.iter]_的性质。*)

Theorem iter_add: forall {A: Type} (n m: nat) (f: A -> A) (x: A),
  Nat.iter (n + m) f x = Nat.iter n f (Nat.iter m f x).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[Nat.iter]_的性质。*)

Theorem iter_mul: forall {A: Type} (n m: nat) (f: A -> A) (x: A),
  Nat.iter (n * m) f x = Nat.iter n (Nat.iter m f) x.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


