Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.micromega.Psatz.
Require Import Basic.InductiveType.
Local Open Scope Z.

(** * 二叉树上的_[same_structure]_与等价关系 *)


(** 先前我们利用Coq归纳类型与递归函数定义了二叉树_[tree]_与二叉树结构相等
    _[same_structure]_。我们还证明过，_[same_structure]_具有传递性
    （_[same_structure_trans]_），事实上，我们还知道_[same_structure]_是一个等价关
    系！数学上，一个二元关系“≡”是一个等价关系当且仅当它满足下面三个性质：  

        (1) 自反性：_[forall a, a ≡ a]_   

        (2) 对称性：_[forall a b, a ≡ b -> b ≡ a]_   

        (3) 传递性：_[forall a b c, a ≡ b -> b ≡ c -> a ≡ c]_ *)


Lemma same_structure_refl: forall t: tree,
  same_structure t t.
Proof.
  intros.
  induction t; simpl.
  + tauto.
  + tauto.
Qed.

Lemma same_structure_symm: forall t1 t2: tree,
  same_structure t1 t2 -> same_structure t2 t1.
Proof.
  intros.
  revert t2 H; induction t1; simpl; intros.
  + destruct t2; simpl.
    - tauto.
    - tauto.
  + destruct t2; simpl.
    - tauto.
    - specialize (IHt1_1 t2_1).
      specialize (IHt1_2 t2_2).
      tauto.
Qed.

(** 基于等价关系，我们可以对等价的元素进行替换。 *)

Example same_structure_ex1: forall t1 t2 t3 t4,
  same_structure t1 t2 ->
  same_structure t3 t2 ->
  same_structure t3 t4 ->
  same_structure t1 t4.

(** 它的Coq证明如下：*)

Proof.
  intros t1 t2 t3 t4 H12 H32 H34.
  apply (same_structure_trans t1 t2 t4).
  + apply H12.
  + apply (same_structure_trans t2 t3 t4).
    - apply same_structure_symm.
      apply H32.
    - apply H34.
Qed.

(** 在上面的这段Coq证明中，使用了_[same_structure]_的对称性和传递性。然而，更直观的证
    明思路也许应当用_[rewrite]_来刻画。例如，当我们证明整数相等的类似性质时，我们可以
    下面这样写证明。*)

Example Zeq_ex: forall x1 x2 x3 x4: Z,
  x1 = x2 ->
  x3 = x2 ->
  x3 = x4 ->
  x1 = x4.
Proof.
  intros x1 x2 x3 x4 H12 H32 H34.
  rewrite H12, <- H32, H34.
  reflexivity.
Qed.

(** Coq标准库提供了自反、对称、传递与等价的统一定义，并基于这些统一定义提供了
    _[rewrite]_、_[reflexivity]_等证明指令支持。下面三条证明中，_[Reflexive]_、
    _[Symmetric]_与_[Transitive]_是Coq标准库对于自反、对称与传递的定义。Coq标准库还
    将这三个定义注册成了Coq的Class，这使得Coq能够提供一些特定的证明支持。这里的关键字
    也不再使用_[Lemma]_或_[Theorem]_，而是使用_[Instance]_，这表示Coq将在后续证明过
    程中为_[same_structure]_提供自反、对称与传递相关的专门支持。*)

Instance same_structure_refl': Reflexive same_structure.
Proof. unfold Reflexive. apply same_structure_refl. Qed.

Instance same_structure_symm': Symmetric same_structure.
Proof. unfold Symmetric. apply same_structure_symm. Qed.

Instance same_structure_trans': Transitive same_structure.
Proof. unfold Transitive. apply same_structure_trans. Qed.

(** Coq还将这三条性质打包起来，定义了等价关系_[Equivalence]_。要在Coq中证明
    _[same_structure]_是一个等价关系，可以使用_[split]_指令，将“等价关系”规约为“自反
    性”、“对称性”与“传递性”。*)

Instance same_structure_equiv: Equivalence same_structure.
Proof.
  split.
  + apply same_structure_refl'.
  + apply same_structure_symm'.
  + apply same_structure_trans'.
Qed.

(** 现在，我们可以用_[rewrite]_与_[reflexivity]_重新证明上面的性质：*)

Example same_structure_ex2: forall t1 t2 t3 t4,
  same_structure t1 t2 ->
  same_structure t3 t2 ->
  same_structure t3 t4 ->
  same_structure t1 t4.
Proof.
  intros t1 t2 t3 t4 H12 H32 H34.
  rewrite H12, <- H32, H34.
  reflexivity.
Qed.

(** 细究这个证明过程，_[rewrite H12]_利用   

        _[same_structure t1 t2]_   

    将_[same_structure t1 t4]_规约为了_[same_structure t2 t4]_，这其实就是使用了
    _[same_structure]_的传递性！类似的，_[rewrite <- H32]_使用了传递性与对称性，
    _[rewrite H34]_又一次使用了传递性，而最后的_[reflexivity]_使用了自反性。*)

(************)
(** 习题：  *)
(************)


(** 我们称两个整数模5同余当且仅当它们刚好差一个5的倍数。*)

Definition congr_mod5 (a b: Z): Prop :=
  exists k: Z, a - b = 5 * k.

(** 下面请证明模5同余是一个等价关系。*)

Instance congr_mod5_refl: Reflexive congr_mod5.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Instance congr_mod5_symm: Symmetric congr_mod5.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Instance congr_mod5_trans: Transitive congr_mod5.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Instance congr_mod5_equiv: Equivalence congr_mod5.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)
(************)
(** 习题：  *)
(************)


(** 如果把一个序列（_[list]_）看作环状的，那么   

        _[[1; 2; 3; 4]]_   

        _[[2; 3; 4; 1]]_   

        _[[3; 4; 1; 2]]_   

        _[[4; 1; 2; 3]]_   

    表示的是同一个环。下面定义的_[rotate]_就表示，可以通过轮转变换由一个序列得到另一个
    序列，换言之，这两个序列表示的是同一个环。*)

Definition rotate {A: Type} (l1 l2: list A): Prop :=
  exists lx ly, l1 = lx ++ ly /\ l2 = ly ++ lx.

(** 首先，请证明_[rotate]_具有自反性：*)

Instance rotate_refl {A: Type}: Reflexive (@rotate A).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 其次，请证明_[rotate]_具有对称性。*)

Instance rotate_symm {A: Type}: Symmetric (@rotate A).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 要证明_[rotate]_具有传递性要复杂一些。根据定义，  

        _[rotate l1 l2]_   

        _[rotate l2 l3]_   

    这两个条件等价于存在_[lx]_、_[ly]_、_[lu]_与_[lv]_使得：  

        _[l1 = lx ++ ly]_   

        _[l2 = ly ++ lx]_   

        _[l2 = lu ++ lv]_   

        _[l3 = lv ++ lu]_   

    观察中间两条性质，我们立即知道_[ly ++ lx = lu ++ v]_。这意味着，要么_[l2]_可以写
    成_[ly ++ l ++ lv]_的形式，并且   

        _[lx = l ++ lv]_   

        _[lu = ly ++ l]_；   

    要么_[l2]_可以写成_[lu ++ l ++ lx]_的形式，并且   

        _[ly = lu ++ l]_   

        _[lv = l ++ lx]_。   

    无论是两种情况中的哪一种成立，都足以帮助我们证明_[rotate l1 l3]_。下面，请首先证
    明这条证明传递性时需要用到的重要引理，请注意恰当选择归纳证明的对象，也要恰当选择加
    强归纳的方法。*)

Lemma app_split3: forall {A: Type} (lx ly lu lv: list A),
  ly ++ lx = lu ++ lv ->
  (exists l, ly = lu ++ l /\ lv = l ++ lx) \/
  (exists l, lu = ly ++ l /\ lx = l ++ lv).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 接下去，请用上面的引理_[app_split3]_证明_[rotate]_有传递性。*)

Instance rotate_trans {A: Type}: Transitive (@rotate A).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 现在我们已经证明了_[rotate]_是一个等价关系，因此就可以在Coq中写如下证明了。*)

Example rotate_ex: forall {A: Type} (l1 l2 l3 l4: list A),
  rotate l1 l2 ->
  rotate l3 l2 ->
  rotate l3 l4 ->
  rotate l1 l4.
Proof.
  intros A l1 l2 l3 l4 H12 H32 H34.
  rewrite H12, <- H32, H34.
  reflexivity.
Qed.



(** * 函数与等价关系 *)


Module PointwiseRelDemo.

(** 在Coq中，除了可以像前面那样构建归纳类型数学对象之间的等价关系之外，还可以构造函数之
    间的等价关系。例如，在考察_[A -> B]_类型的所有函数时，就可以基于_[B]_类型上的等价
    关系，利用“逐点等价”定义这些函数之间的等价关系。“逐点等价”说的是，函数_[f]_与
    _[g]_等价当且仅当对于任意一个定义域中的元素_[a]_都用_[f a]_与_[g a]_等价。这一定
    义就是Coq标准库中的_[pointwise_relation]_。 *)

Definition pointwise_relation
             (A: Type) {B: Type}
             (R: B -> B -> Prop)
             (f g: A -> B): Prop :=
  forall a: A, R (f a) (g a).

(** Coq标准库也证明了，如果_[R]_是等价关系，那么_[pointwise_relation A R]_也是等价关
    系。下面首先证明，如果_[R]_具有自反性，那么_[pointwise_relation A R]_也具有自反
    性。*)

Instance pointwise_reflexive: forall {A B: Type} {R: B -> B -> Prop},
  Reflexive R ->
  Reflexive (pointwise_relation A R).
Proof.
  intros.
  unfold Reflexive, pointwise_relation.
  intros.
  reflexivity.
Qed.

(** 在上面的证明中，之所以最后可以用_[reflexivity]_指令证明_[R (x a) (x a)]_是因为在
    证明目标中有一条前提_[H: Reflexive R]_。事实上，Coq对于等价关系等代数性质的支持，
    不仅仅限于用_[Instance]_注册过的结构，也包括在证明前提中预设的结构。此处既然假设了
    _[R]_具有自反性，而且自反性是使用Coq标准库中的_[Reflexive]_描述的，那么在证明过程
    中就可以使用_[reflexivity]_完成相关证明。下面是关于对称性的结论：只要_[R]_具有对
    称性，_[pointwise_relation A R]_就有对称性。*)

Instance pointwise_symmetric: forall {A B: Type} {R: B -> B -> Prop},
  Symmetric R ->
  Symmetric (pointwise_relation A R).
Proof.
  intros.
  unfold Symmetric, pointwise_relation.
  intros.
  symmetry.
  apply H0.
Qed.

(** 上面这段证明中的_[symmetry]_表示使用“对称性”。*)

Instance pointwise_transitive: forall {A B: Type} {R: B -> B -> Prop},
  Transitive R ->
  Transitive (pointwise_relation A R).
Proof.
  intros.
  unfold Transitive, pointwise_relation.
  intros.
  transitivity (y a).
  + apply H0.
  + apply H1.
Qed.

(** 上面这段证明中的_[transitivity (y a)]_表示使用“传递性”证明并选用_[y a]_作为中间
    元素。下面我们把关于自反、对称与传递的这三个结论打包起来。*)

Instance pointwise_equivalence: forall {A B: Type} {R: B -> B -> Prop},
  Equivalence R ->
  Equivalence (pointwise_relation A R).
Proof.
  intros.
  split.
  + apply pointwise_reflexive.
    apply Equivalence_Reflexive.
  + apply pointwise_symmetric.
    apply Equivalence_Symmetric.
  + apply pointwise_transitive.
    apply Equivalence_Transitive.
Qed.

End PointwiseRelDemo.

(************)
(** 习题：  *)
(************)


(** 我们称两个整数函数是模5意义上等价的，当且仅当它们在每一点上的函数值都模5同余。例如
    _[f(n) = n^5]_与_[g(n) = n]_就是模5意义上等价的。*)

Example congr_mod5_sample:
  (pointwise_relation Z congr_mod5)
    (fun n => n * n * n * n * n)
    (fun n => n).
Proof.
  unfold pointwise_relation, congr_mod5.
  intros.
  assert (exists k, a * (a - 1) * (a - 2) * (a - 3) * (a - 4) = 5 * k).
  {
    pose proof Z.mod_eq a 5 ltac:(lia).
    pose proof Z.mod_pos_bound a 5 ltac:(lia).
    assert (a mod 5 = 0 \/
            a mod 5 = 1 \/
            a mod 5 = 2 \/
            a mod 5 = 3 \/
            a mod 5 = 4) by lia; clear H0.
    destruct H1 as [? | [? | [? | [? | ?]]]].
    + exists ((a / 5) * (a - 1) * (a - 2) * (a - 3) * (a - 4)).
      nia.
    + exists (a * (a/5) * (a - 2) * (a - 3) * (a - 4)).
      nia.
    + exists (a * (a - 1) * (a/5) * (a - 3) * (a - 4)).
      nia.
    + exists (a * (a - 1) * (a - 2) * (a/5) * (a - 4)).
      nia.
    + exists (a * (a - 1) * (a - 2) * (a - 3) * (a/5)).
      nia.
  }
  destruct H as [k ?].
  exists (2 * a * a * a * a
        - 7 * a * a * a
        + 10 * a * a
        - 5 * a
        + k).
  nia.
Qed.

(** 下面请利用已有结论证明：模5意义下的函数等价是一种等价关系。 *)

Example func_equiv_sample:
  Equivalence (pointwise_relation Z congr_mod5).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(************)
(** 习题：  *)
(************)


(** 下面定义了一种新的函数间关系_[lift_rel]_。请证明，如果_[RA]_与_[RB]_都是等价关
    系，那么_[lift_rel RA RB]_也是一个等价关系。*)

Definition lift_rel
             {A B: Type}
             (RA: A -> A -> Prop)
             (RB: B -> B -> Prop)
             (f g: A -> B): Prop :=
  (forall a1: A, exists a2: A, RA a1 a2 /\ RB (f a1) (g a2)) /\
  (forall a1: A, exists a2: A, RA a1 a2 /\ RB (g a1) (f a2)).

Instance lift_rel_reflexive:
  forall {A B: Type} (RA: A -> A -> Prop) (RB: B -> B -> Prop),
    Reflexive RA ->
    Reflexive RB ->
    Reflexive (lift_rel RA RB).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Instance lift_rel_symmetric:
  forall {A B: Type} (RA: A -> A -> Prop) (RB: B -> B -> Prop),
    Symmetric (lift_rel RA RB).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Instance lift_rel_transitive:
  forall {A B: Type} (RA: A -> A -> Prop) (RB: B -> B -> Prop),
    Transitive RA ->
    Transitive RB ->
    Transitive (lift_rel RA RB).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

Instance lift_rel_equivalence:
  forall {A B: Type} (RA: A -> A -> Prop) (RB: B -> B -> Prop),
    Equivalence RA ->
    Equivalence RB ->
    Equivalence (lift_rel RA RB).
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)


(** 最后，除了可以定义函数之间的等价关系之外，我们还可以反过来利用函数构造等价关系。下
    面这条性质就表明，可以基于一个_[A -> B]_类型的函数_[f]_以及一个_[B]_上的等价关系
    构造一个_[A]_上的等价关系。这一_[A]_集合上的等价关系是：_[a1]_与_[a2]_等价当且仅
    当_[f a1]_与_[f a2]_等价。*)

Instance equiv_in_domain:
  forall {A B: Type} (f: A -> B) (R: B -> B -> Prop),
    Equivalence R ->
    Equivalence (fun a1 a2 => R (f a1) (f a2)).
Proof.
  intros.
  split.
  + unfold Reflexive.
    intros.
    reflexivity.
  + unfold Symmetric.
    intros.
    symmetry; tauto.
  + unfold Transitive.
    intros.
    transitivity (f y); tauto.
Qed.

(** * Coq中的_[Morphisms]_ *)


(** 前面我们已经证明了_[same_structure]_这一二元关系是自反、对称且传递的，换言之，
    _[same_structure]_是一个等价关系。下面我们进一步探讨_[same_structure]_符合的其
    它代数性质：许多树变换都能保持树结构的等价关系。例如：如果  

        _[same_structure t11 t12]_   

        _[same_structure t21 t22]_   

    那么_[Node t11 n1 t21]_与_[Node t12 n2 t22]_也是结构相同的。运用我们现在所学，
    这个性质可以写成下面引理。*)

Lemma Node_same_structure_congr: forall t11 t12 t21 t22 n1 n2,
  same_structure t11 t12 ->
  same_structure t21 t22 ->
  same_structure (Node t11 n1 t21) (Node t12 n2 t22).
Proof.
  intros.
  simpl.
  tauto.
Qed.

(** 类似地，_[tree_reverse]_也能保持树结构地等价关系。只不过这一引理需要用归纳法证
    明。归纳证明中的奠基步骤是要证明   

        _[same_structure (tree_reverse Leaf) (tree_reverse Leaf)]_   

    这是显然的。证明中的归纳步骤是要基于   

        _[same_structure (tree_reverse t11) (tree_reverse t21)]_   

        _[same_structure (tree_reverse t12) (tree_reverse t22)]_   

    这两条归纳假设推出：  

        _[same_structure
            (Node (tree_reverse t11) n1 (tree_reverse t12))
            (Node (tree_reverse t21) n2 (tree_reverse t22))]_。   

    我们现在已经知道_[same_structure]_是等价关系，也知道_[Node]_可以保持这一等价关
    系，因此我们希望可以像证明等式相关性质那样使用_[rewrite]_指令来完成这一证明。然而
    Coq并不支持我们现在这么做。*)

Example tree_reverse_same_structure_congr_ind_step:
  forall t11 t12 t21 t22 n1 n2,
    same_structure (tree_reverse t11) (tree_reverse t21) ->
    same_structure (tree_reverse t12) (tree_reverse t22) ->
    same_structure
      (Node (tree_reverse t11) n1 (tree_reverse t12))
      (Node (tree_reverse t21) n2 (tree_reverse t22)).
Proof.
  intros.
  Fail rewrite H, H0.
Abort.

(** 下面是_[same_structure]_与等号_[=]_的对比：*)

Example same_structure_vs_eq:
  forall t11 t12 t21 t22 n,
    tree_reverse t11 = tree_reverse t21 ->
    tree_reverse t12 = tree_reverse t22 ->
    Node (tree_reverse t11) n (tree_reverse t12) =
    Node (tree_reverse t21) n (tree_reverse t22).
Proof.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

(** 之所以Coq目前无法支持对_[same_structure]_如上面所示的那样利用_[rewrite]_指令重
    写，主要原因在于Coq无法基于引理  

        _[Node_same_structure_congr]_   

    的表述获知其中关键的代数结构。先前我们所使用的Coq中基于代数结构的证明指令都搭建在
    _[Reflexive]_、_[Symmetric]_、_[Transitive]_与_[Equivalence]_等专门定义的基础
    之上。Coq标准库其实也提供了“保持等价性”的Coq定义，这就是_[Proper]_。下面，我们利
    用_[Proper]_重述“_[Node]_保持_[same_structure]_”这一性质。*)

Definition any {A: Type} (a b: A): Prop := True.

Instance Node_same_structure_morphism:
  Proper (same_structure ==>
          any ==>
          same_structure ==>
          same_structure) Node.

(** 这个性质说得是：_[Node]_是一个三元函数，如果对其第一个参数做_[same_structure]_
    变换，对其第二个参数做任意变换，同时对其第三个参数做_[same_structure]_变换，那么
    这个三元函数的计算结果也会做_[same_structure]_变换。在证明这一结论时，需要展开
    _[Proper]_的定义，还需要展开_[==>]_的定义，它的Coq名字是_[respectful]_。*)

Proof.
  intros.
  unfold Proper, respectful.
  intros t11 t21 ? n1 n2 _ t12 t22 ?.
  simpl.
  tauto.
Qed.

(** 下面补充证明，_[any]_是一个自反关系。*)

Instance any_refl: forall A: Type, Reflexive (@any A).
Proof.
  intros.
  unfold Reflexive; intros.
  unfold any; tauto.
Qed.

(** 这样我们就可以让_[rewrite]_用上_[Node]_保持_[same_structure]_变换这一性质了。*)

Example tree_reverse_same_structure_congr_ind_step:
  forall t11 t12 t21 t22 n1 n2,
    same_structure (tree_reverse t11) (tree_reverse t21) ->
    same_structure (tree_reverse t12) (tree_reverse t22) ->
    same_structure
      (Node (tree_reverse t11) n1 (tree_reverse t12))
      (Node (tree_reverse t21) n2 (tree_reverse t22)).
Proof.
  intros.
  rewrite H, H0.
  simpl; split; reflexivity.
Qed.

(** 自然，_[tree_reverse]_保持_[same_structure]_也可以用_[Proper]_刻画。*)

Instance tree_reverse_same_structure_morphism:
  Proper (same_structure ==> same_structure) tree_reverse.
Proof.
  unfold Proper, respectful.
  intros t1.
  induction t1 as [| t11 IHt11 ? t12 IHt12]; intros t2 H;
    destruct t2 as [| t21 ? t22].
  + reflexivity.
  + simpl in H. tauto.
  + simpl in H. tauto.
  + simpl tree_reverse.
    simpl in H. destruct H as [Ht11 Ht12].
    specialize (IHt11 _ Ht11).
    specialize (IHt12 _ Ht12).
    rewrite IHt11, IHt12.
    simpl; split; reflexivity.
Qed.

(** 上面的例子中用_[Proper]_描述了_[Node]_与_[tree_reverse]_这两个函数的性质。其实
    _[Proper]_也可以用于描述谓词的性质。例如，下面性质说的是，如果对
    _[same_structure]_这个谓词的两个参数分别做_[same_structure]_变换，那么变换前后
    的两个命题要么全都成立要么全都不成立，即变换之前的命题成立当且仅当变换之后的命题成
    立，这个“当且仅当”就是下面定理描述中的_[iff]_。 *)

Instance same_structure_same_structure_morphism:
  Proper (same_structure ==> same_structure ==> iff) same_structure.
Proof.
  unfold Proper, respectful.
  intros.
  rewrite H, H0.
  reflexivity.
Qed.

(** 下面定义的_[structural_subtree]_描述了结构上的子树关系（不考虑节点上的数值）。*)

Fixpoint structural_subtree (t1 t2: tree): Prop :=
  match t2 with
  | Leaf =>
      same_structure t1 t2
  | Node t21 n2 t22 =>
      same_structure t1 t2 \/
      structural_subtree t1 t21 \/
      structural_subtree t1 t22
  end.

(** 很显然，对_[structural_subtree]_的参数做_[same_structure]_不改变命题的真假。*)

Instance structural_subtree_same_structure_morphism:
  Proper (same_structure ==> same_structure ==> iff) structural_subtree.
Proof.
  unfold Proper, respectful.
  intros t1 t1' Ht1 t2 t2' Ht2.
  revert t2' Ht2.
  induction t2 as [| t21 IHt21 n2 t22 IHt22]; intros;
    destruct t2' as [| t21' n2' t22'].
  + simpl.
    rewrite Ht1; reflexivity.
  + simpl in Ht2.
    tauto.
  + simpl in Ht2.
    tauto.
  + simpl.
    rewrite Ht2.
    rewrite Ht1 at 1.
    simpl in Ht2.
    destruct Ht2 as [Ht21 Ht22].
    specialize (IHt21 t21' Ht21).
    specialize (IHt22 t22' Ht22).
    tauto.
Qed.

(** 然而，如果对_[structural_subtree]_的两个参数都做_[structural_subtree]_变换，并
    不能确保变换前后_[structural_subtree]_性质不变。具体而言，如果已知   

        _[structural_subtree t1 t2]_   

    并对_[t1]_与_[t2]_做如下变换   

        _[structural_subtree t1 t1']_   

        _[structural_subtree t2 t2']_   

    并不能得出   

        _[structural_subtree t1' t2']_   

    这一结论。不过，如果修正从_[t1]_到_[t1']_的变换方向，_[structural_subtree]_这一
    性质就能被保持。具体而言，我们可以由：   

        _[structural_subtree t1 t2]_   

        _[structural_subtree t1' t1]_   

        _[structural_subtree t2 t2']_   

    推出   

        _[structural_subtree t1' t2']_。   

    这一性质可以用_[Proper]_概述为：*)

Instance structural_subtree_structural_subtree_morphism:
  Proper
    (structural_subtree -->
     structural_subtree ==>
     Basics.impl) structural_subtree.

(** 其中， _[-->]_表示第一个参数做_[structural_subtree]_的反向变换，“反向”这一概念对
    应的Coq定义是_[Basics.flip]_；另外，_[Basics.impl]_表示变换前的命题可以推出变换
    后的命题。*)

Proof.
  unfold Proper, respectful, Basics.flip, Basics.impl.
  intros t1 t1' Ht1 t2 t2' Ht2 H.
Abort.

(** 不过，要证明这一结论，比较好的方法是先证明_[structural_subtree]_具有传递性，再连
    续使用两次传递性完成证明。相关的证明留作习题。*)

(************)
(** 习题：  *)
(************)

(** 请证明_[structural_subtree]_具有传递性。提示：我们已经证明过，做
    _[same_structure]_变换能保持_[structural_subtree]_性质，因此，可以使用
    _[rewrite]_表述相关证明。*)

Instance structural_subtree_trans: Transitive structural_subtree.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 接下去，请运用传递性证明下面性质。*)

Instance structural_subtree_structural_subtree_morphism:
  Proper
    (structural_subtree -->
     structural_subtree ==>
     Basics.impl) structural_subtree.
Proof.
  unfold Proper, respectful, Basics.flip, Basics.impl.
  intros t1 t1' Ht1 t2 t2' Ht2 H.
Admitted. (* 请删除这一行_[Admitted]_并填入你的证明，以_[Qed]_结束。 *)

(** 不难看出，具有传递性的二元关系都具有这样的性质。换言之，如果_[R]_是一个二元关系，那
    么只要_[Transitive R]_成立，就有   

        _[Proper (R --> R ==> Basics.impl) R]_   

    成立。类似的，只要_[Equivalence R]_成立，就有   

        _[Proper (R ==> R ==> iff) R]_   

    成立。这也是Coq能够依据等价关系_[Equivalence]_性质提供_[rewrite]_支持的原因。*)



