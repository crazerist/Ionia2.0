Require Import Coq.Logic.ProofIrrelevance FunctionalExtensionality.
Require Import Classical_Prop.
Require Export vector.

Set Implicit Arguments.

Declare Scope path_scope.

Open Scope path_scope.

(* ######################################################################### *)
(** * Data *)

Section Data.

(** ** data *)

(** *** Definition *)

(** 定义 data 数据结构,num 构造子表示其为一个数, ary 构造子表示其为数组.
其中, ary 构造子需要包含原数组长度 m 自身数组长度 n 以及自身子数据类型 d: data,其中有约束关系 n <= m *)
Inductive data: Set:= 
 | num: data
 | ary m (n: fle m) (d: data): data.

(** *** Lemma *)

(** 如果原数组长度为0, 那么该数组长度也为 0 *)
Lemma data_fle_0: forall (n: fle 0) d,
 ary n d = ary '{0} d.
Proof. intros. vauto. Qed.

(** *** Definition *)

(** 定义一个 2 * 3 的数组类型 *)
Example myd: data:= ary '{2} (ary '{3} num).

(** ** optdata *)

(** *** Definition *)

(** 判断 data 数据类型是否合法, 当其类型为 num 或数组长度大于 0 并且其任意子数据类型为 num 或数组长度大于0时,判断合法.
当非法时,返回 None； 当合法时,返回 Some + 自身 *)
Fixpoint optdata (d: data): option data:= 
 match d with
 | num => Some d 
 | ary n d' => match (fle2nat n), (optdata d') with 
 | 0, _ => None
 | _, Some _ => Some d
 | _, _ => None
 end
 end.

(** *** Lemma *)

(** optdata 是总是返回自身的函数 *)
Lemma optdata_eq: forall d1 d2, optdata d1 = Some d2 -> d1 = d2.
Proof with vauto.
 intros d1 d2. destruct d1; simpl; intros. injection H; intros...
 destruct (fle2nat n)... destruct (optdata d1)...
Qed.

(** num 对于 optdata 总是合法 *)
Lemma optdata_num: optdata num = Some num.
Proof. vauto. Qed.

(** 如果该数组长度为 0, 那么返回 None *)
Lemma optdata_ary_0: forall m (n: fle m) d,
 fle2nat n = 0 -> optdata (ary n d) = None.
Proof. intros; simpl; rewrite H; vauto. Qed.

(** 如果该数组长度的原数组长度为0, 那么返回 None *)
Lemma optdata_fle_0: forall d (n: fle 0), optdata (ary n d) = None.
Proof. intros; simpl. rewrite (fle'_0_elem n); vauto. Qed.

(** 如果父数据类型返回 Some, 那么子数据类型也返回 Some *)
Lemma optdata_sub: forall {m n d},
 optdata (@ary m n d) = Some (ary n d) -> optdata d = Some d.
Proof with vauto.
 intros. simpl in H. destruct (fle2nat n)... 
 destruct (optdata d) eqn: E... apply optdata_eq in E...
Qed.

(** 如果子数据类型返回Some, 那么如果父数据类型长度大于 0 的情况下返回 Some *)
Lemma optdata_par: forall {m d} (n: fle m),
 0 < fle2nat n -> optdata d = Some d -> optdata (ary n d) = Some (ary n d).
Proof. intros. simpl. rewrite H0. destruct (fle2nat n); vauto. Qed.

(** 如果父数据类型返回 None 并且父数据类型长度大于0, 那么子数据类型返回 None *)
Lemma optdata_sub_none: forall {m d} (n: fle m),
 0 < fle2nat n -> optdata (ary n d) = None -> optdata d = None.
Proof with vauto. 
 intros. simpl in H0. destruct (fle2nat n)... destruct (optdata d)...
Qed.

(** 如果子数据类型返回i None, 那么父数据类型返回 None *)
Lemma optdata_par_none: forall {m n d},
 optdata d = None -> optdata (@ary m n d) = None.
Proof. intros. simpl; rewrite H. destruct (fle2nat n); vauto. Qed.

(** 如果一个长度为 n 的数据类型返回 Some, 那么相同子类型长度为 S n 的数据类型也返回 Some *)
Lemma optdata_Sn: forall {m n d} (E: S n <= m),
 optdata (ary [n | leS_le E] d) = Some (ary [n | leS_le E] d) -> 
 optdata (ary [S n | E] d) = Some (ary [S n | E] d).
Proof with vauto. 
 intros. simpl in *. destruct n... destruct (optdata d)...
Qed.

(** 如果一个长度为 S n 的数据类型返回 Some,那么若 0 < n, 则相同子类型长度为 n 的数据类型也返回 Some *)
Lemma optdata_Pred: forall {m n d} (E: S n <= m),
 0 < n -> optdata (ary [S n | E] d) = Some (ary [S n | E] d) ->
 optdata (ary [n | leS_le E] d) = Some (ary [n | leS_le E] d).
Proof with vauto.
 intros. simpl in *. destruct (optdata d)... destruct n...
Qed.

(** optdata 可被判别 *)
Lemma optdata_dec : forall d, {optdata d = Some d} + {optdata d = None}.
Proof with vauto.
  intro. destruct (optdata d) eqn : E... left. apply optdata_eq in E; subst...
Qed.


(** *** Example *)

(** 对于一个 2 * 3 的数组的数据类型来说, 合法 *)
Goal optdata myd = Some myd.
Proof. auto. Qed.

(** 对于一个 2 * 0 的数组的数据类型来说, 非法 *)
Goal optdata (ary '{2} (ary '{0} num)) = None.
Proof. auto. Qed.

End Data.

(** ** Auto *)

#[export] Hint Rewrite optdata_num optdata_ary_0 optdata_fle_0: dcore.

#[export] Hint Resolve optdata_eq optdata_sub optdata_par optdata_sub_none
optdata_par_none optdata_Sn optdata_Pred: dcore.


(* ######################################################################### *)

(** * Path *)

Section Path.

(** ** path *)

(** 定义 path 数据结构,Var 构造子表示其为一个输入字符串返回路径的函数, Ary 构造子表示其为路径数组.
其中, Ary 构造子需要包含原数组长度 n 访问序号 i, 有约束条件 i < n, 返回一个输入路径获得新路径的函数 *)
Inductive path:= 
 | Var: string -> path
 | Ary (n: nat) (i: fin n): path -> path.

(** *** Definition *)

(** 定义一个访问 "arr" 的 2 * 3 的数组的 1 * 2 位置 *)
Example mypt: path:= Ary '[1] (Ary '[2] (Var "arr")).

(** ** optpath *)

(** *** Definition *)

(** 判断 path 数据类型是否合法, 当其类型为 Var 或其限制长度大于 0 并且其任意子数据类型为 Var 或限制长度大于0时,判断合法.
当非法时,返回 None； 当合法时,返回 Some + 自身 *)
Fixpoint optpath (p: path): option path:= 
 match p with
 | Var _ => Some p
 | @Ary n i p' => match n, (optpath p') with 
 | 0, _ => None
 | _, Some _ => Some p
 | _, _ => None
 end
 end.

(** *** Lemma *)

(** optpath 是总是返回自身的函数 *)
Lemma optpath_eq: forall p1 p2, optpath p1 = Some p2 -> p1 = p2.
Proof with vauto.
 intros p1 p2. destruct p1; simpl; intros. injection H; intros...
 destruct n... destruct (optpath p1)...
Qed.

(** Var 对于 optpath 总是合法 *)
Lemma optpath_Var: forall s, optpath (Var s) = Some (Var s).
Proof. vauto. Qed.

(** 如果父路径类型返回 Some, 那么子路径类型也返回 Some *)
Lemma optpath_sub: forall {n i p},
 optpath (@Ary n i p) = Some (Ary i p) -> optpath p = Some p.
Proof with vauto.
 intros. simpl in H. destruct n... 
 destruct (optpath p) eqn: E... apply optpath_eq in E...
Qed.

(** 如果子路径类型返回Some, 那么如果父路径类型长度大于 0 的情况下返回 Some *)
Lemma optpath_par: forall {n p} (i: fin n),
 0 < fin2nat i -> optpath p = Some p -> optpath (Ary i p) = Some (Ary i p).
Proof. intros. simpl. rewrite H0. destruct n; vauto. Qed.

(** 如果父路径类型返回 None 并且父路径类型长度大于0, 那么子路径类型返回 None *)
Lemma optpath_sub_none: forall {n p} (i: fin n),
 0 < n -> optpath (Ary i p) = None -> optpath p = None.
Proof with vauto. 
 intros. simpl in H0. destruct n... destruct (optpath p)...
Qed.

(** 如果子路径类型返回i None, 那么父路径类型返回 None *)
Lemma optpath_par_none: forall {n i p},
 optpath p = None -> optpath (@Ary n i p) = None.
Proof. intros. simpl; rewrite H. destruct n; vauto. Qed.

(** 如果一个长度为 n 的路径类型返回 Some, 那么相同子类型长度为 S n 的路径类型也返回 Some *)
Lemma optpath_Sn: forall {n i p} (E: S i < n),
 optpath (Ary [i | ltS_lt E] p) = Some (Ary [i | ltS_lt E] p) -> 
 optpath (Ary [S i | E] p) = Some (Ary [S i | E] p).
Proof with vauto. 
 intros. simpl in *. destruct n... destruct (optpath p)...
Qed.

(** 如果一个长度为 S n 的路径类型返回 Some,那么若 0 < n, 则相同子类型长度为 n 的路径类型也返回 Some *)
Lemma optpath_Pred: forall {n i p} (E: S i < n),
 0 < n -> optpath (Ary [S i | E] p) = Some (Ary [S i | E] p) ->
 optpath (Ary [i | ltS_lt E] p) = Some (Ary [i | ltS_lt E] p).
Proof with vauto.
 intros. simpl in *. destruct n... destruct (optpath p)...
Qed.

(** *** Example *)

(** 对于一个 2 * 3 的数组的路径类型来说, 访问 1 * 3 合法 *)
Goal optpath mypt = Some mypt.
Proof. auto. Qed.

(** ** path_eqb *)

(** 定义 path_eq, 用来判断两个路径是否相同 *)
Fixpoint eqb (p1 p2: path): bool:= 
 match p1,p2 with
 | Var p3 , Var p4 => String.eqb p3 p4
 | @Ary n1 i1 p3 , @Ary n2 i2 p4 => 
 (n1 =? n2)%nat && (i1 =? i2)%nat && (eqb p3 p4)
 | _ , _ => false
 end.


Infix " =?":= eqb: path_scope.

(** *** Lemma *)


(** path_eqb 具有自反性 *)
Lemma eqb_refl: forall (p: path), p =? p = true.
Proof with auto.
 induction p. apply String.eqb_refl. simpl; rewrite !Nat.eqb_refl... 
Qed.

(** 如果前提条件具有非自反性,那么直接推出 False *)
Lemma eqb_refl_false: forall p: path, p =? p = false -> False.
Proof. intros. rewrite eqb_refl in H. inv H. Qed. 

(** path_eq 与 path_eqb 对应 *)
Lemma eqb_eq: forall (p1 p2: path),
 p1 =? p2 = true <-> p1 = p2.
Proof with vauto.
 vauto. 2: { apply eqb_refl. } generalize dependent p2.
 generalize dependent p1. induction p1, p2; intro H; inv H...
 - apply String.eqb_eq in H...
 - apply IHp1 in H1; subst. f_equal...
Qed.

(** path_neq 与nath_neqb 对应 *)
Lemma eqb_neq: forall (p1 p2: path),
 p1 =? p2 = false <-> p1 <> p2.
Proof with vauto.
 vauto.
 - (* p1 <> p2 *)
 apply (eqb_refl_false _ H).
 - (* (p1 =? p2) = false *)
 destruct (p1 =? p2) eqn: E; auto. exfalso; apply H. apply eqb_eq...

Qed.

(** path_eqb 具有传递性 *)
Lemma eqb_sym: forall (p1 p2: path) (b: bool),
 p1 =? p2 = b -> p2 =? p1 = b.
Proof with vauto.
 destruct b...
 - (* (p2 =? p1) = true *)
 apply eqb_eq. symmetry; apply eqb_eq...
 - (* (p2 =? p1) = false *)
 apply eqb_neq. symmetry; apply eqb_neq...
Qed.

(** path_eqb 具有传递性 *)
Lemma eqb_trans: forall (p1 p2 p3: path),
 p1 =? p2 = true -> p2 =? p3 = true -> p1 =? p3 = true.
Proof with vauto.
 intros. apply eqb_eq in H. apply eqb_eq in H0. apply eqb_eq...
Qed. 

(** 当 n1 = n2, i1 = i2, p1 = p2 时, Ary n1 i1 p1 = Ary n2 i2 p2 *)
Lemma Ary_eq_l: forall n1 n2 (i1: fin n1) (i2: fin n2) p1 p2,
 n1 = n2 -> (fin2nat i1 = fin2nat i2)%nat -> p1 = p2 ->
 Ary i1 p1 = Ary i2 p2.
Proof. intros; subst. f_equal; vauto. Qed.

(** 当 Ary n1 i1 p1 = Ary n2 i2 p2时, 有 n1 = n2, i1 = i2, p1 = p2 *)
Lemma Ary_eq_r: forall n1 n2 (i1: fin n1) (i2: fin n2) p1 p2,
 Ary i1 p1 = Ary i2 p2 ->
 n1 = n2 /\ (fin2nat i1 = fin2nat i2)%nat /\ p1 = p2.
Proof. intros. inversion H; vauto. Qed.

(** 当 n1 = n2, i1 = i2, p1 = p2 时, Ary n1 i1 p1 = Ary n2 i2 p2; 反之亦然 *)
Lemma Ary_eq: forall n1 n2 (i1: fin n1) (i2: fin n2) p1 p2,
 (n1 = n2) /\ (fin2nat i1 = fin2nat i2)%nat /\ p1 = p2 <->
 Ary i1 p1 = Ary i2 p2.
Proof with vauto. split; intros. apply Ary_eq_l... apply Ary_eq_r... Qed.

(** 当 i1: fin n = i2: fin n , p1 = p2 时, Ary i1 p1 = Ary i2 p2 *)
Lemma Ary_eq_l': forall n (i1: fin n) (i2: fin n) p1 p2,
 i1 = i2 -> p1 = p2 ->
 Ary i1 p1 = Ary i2 p2.
Proof. intros; subst. f_equal; vauto. Qed.

(** 当 Ary i1 p1 = Ary i2 p2时, 有 n1 = n2, i1 = i2, p1 = p2 *)
Lemma Ary_eq_r': forall n (i1: fin n) (i2: fin n) p1 p2,
 Ary i1 p1 = Ary i2 p2 ->
 i1 = i2 /\ p1 = p2.
Proof. intros. apply Ary_eq_r in H; vauto. Qed.

(** 当 i1: fin n = i2: fin n , p1 = p2 时, Ary i1 p1 = Ary i2 p2; 反之亦然 *)
Lemma Ary_eq': forall n (i1: fin n) (i2: fin n) p1 p2,
 i1 = i2 /\ p1 = p2 <-> Ary i1 p1 = Ary i2 p2.
Proof with vauto. split; intros. apply Ary_eq_l'... apply Ary_eq_r'... Qed.

(** 当 n1 <> n2 时, Ary n1 i1 p1 <> Ary n2 i2 p2 *)
Lemma Ary_neq_l1: forall n1 n2 (i1: fin n1) (i2: fin n2) p1 p2,
 n1 <> n2 -> Ary i1 p1 <> Ary i2 p2.
Proof. unfold not; intros. apply Ary_eq in H0; apply H; vauto. Qed.

(** 当 i1 <> i2 时, Ary n1 i1 p1 <> Ary n2 i2 p2 *)
Lemma Ary_neq_l2: forall n1 n2 (i1: fin n1) (i2: fin n2) p1 p2,
 fin2nat i1 <> fin2nat i2 -> Ary i1 p1 <> Ary i2 p2.
Proof. unfold not; intros. apply Ary_eq in H0; apply H; vauto. Qed.

(** 当 p1 <> p2 时, Ary n1 i1 p1 <> Ary n2 i2 p2 *)
Lemma Ary_neq_l3: forall n1 n2 (i1: fin n1) (i2: fin n2) p1 p2,
 p1 <> p2 -> Ary i1 p1 <> Ary i2 p2.
Proof. unfold not; intros. apply Ary_eq in H0; apply H; vauto. Qed.

(** 当 i1: fin n <> i2: fin n 时, Ary i1 p1 <> Ary i2 p2 *)
Lemma Ary_neq_l1': forall n (i1: fin n) (i2: fin n) p1 p2,
 i1 <> i2 -> Ary i1 p1 <> Ary i2 p2.
Proof. unfold not; intros. apply Ary_eq' in H0; apply H; vauto. Qed.

(** 当 p1 <> p2 时, Ary i1 p1 <> Ary i2 p2 *)
Lemma Ary_neq_l2': forall n (i1: fin n) (i2: fin n) p1 p2,
 p1 <> p2 -> Ary i1 p1 <> Ary i2 p2.
Proof. unfold not; intros. apply Ary_eq in H0; apply H; vauto. Qed.

(** *** Example *)

(** 测试 Path.eqb 的自反性 *)
Goal mypt =? Ary '[1] (Ary '[2] (Var "arr")) = true.
Proof. auto. Qed.

(** 当路径不同时, 能够判断不相同 *)
Goal mypt =? Ary '[1] (Ary '[2] (Var "arr1")) = false.
Proof. auto. Qed.

(** 当地址不同时,能够判断不相同 *)
Goal mypt =? Ary '[1] (Ary (@fin_0S 2) (Var "arr")) = false.
Proof. auto. Qed.

(** 当访问权限不同时,能够判断不相同 *)
Goal Ary '[1] (Ary '[0] (Var "arr")) =? Ary '[1] (Ary (@fin_0S 2) (Var "arr")) = false.
Proof. auto. Qed.

End Path.

(** ** Notation *)

Infix " =?":= eqb: path_scope.

(** ** Auto *)

#[export] Hint Rewrite eqb_eq eqb_neq: dcore.

#[export] Hint Resolve eqb_refl eqb_refl_false eqb_sym eqb_trans Ary_eq_l' Ary_eq_l: dcore.

(** ** Ltac *)

(** 定义 path_simpl: 
1.将路径等式标准化
2.化简部分路径等式
3.将路径的自然数比较转换为数学形式
4.它通过递归调用确保所有可以简化的假设都被处理 *)
Ltac path_simpl:= 
 repeat match goal with
 | [ H: (true = _) |- _ ] => symmetry in H
 | [ H: (false = _) |- _ ] => symmetry in H
 | [ H: context [(?x =? ?x)] |- _ ] => rewrite eqb_refl in H
 | [ H: ?x =? ?x = true |- _ ] => clear H
 | [ H: ?x =? ?x = false |- _ ] => destruct (eqb_refl_false ?x H)
 | [ H: (_ =? _ = true) |- _ ] => apply eqb_eq in H
 | [ H: (_ =? _ = false) |- _ ] => apply eqb_neq in H
 | [ |- true = _ ] => symmetry
 | [ |- false = _ ] => symmetry
 | [ |- context [(?x =? ?x)]] => rewrite eqb_refl
 | [ |- ?x =? ?x = true ] => apply eqb_refl
 | [ |- (_ =? _ = true) ] => apply eqb_eq
 | [ |- (_ =? _ = false) ] => apply eqb_neq
 | [ |- context[ (?x =? ?y) ]] => let E:= fresh "E" in destruct (x =? y) eqn: E
 end.


(* ######################################################################### *)

(** * Expersion *)

Section Expersion.

(** ** exp *)

(** 定义 exp, 将数据结构转化为表达式, 当为 num时,转为 R; 当为数组时,转化为 R 的数组 *)
Fixpoint exp (d: data): Set:= 
 match d with
 | num => R
 | ary n d => vector (exp d) n
 end.

(** *** Lemma *)

(** 如果 d1 = d2, 那么类型 exp d1 与 exp d2 相同 *)
Lemma exp'_eq: forall {A: Set} {d1 d2}, d1 = d2 -> exp d1 = exp d2.
Proof. vauto. Qed.

(** 证明 exp (ary '{0} d) 为 unit *)
Lemma exp'_0: forall d , exp (ary '{0} d) = unit.
Proof. vauto. Qed.

(** 证明 exp (ary '{0} d)只有一个元素 *)
Lemma exp'_0_elem: forall d (e: exp (ary '{0} d)), e = (tt: vector (exp d) 0).
Proof. intros. destruct e. vauto. Qed.

(** 证明 exp (ary '{0} d) 唯一性 *)
Lemma exp'_0_unique: forall {d} (e e': exp (ary '{0} d)), e = e'.
Proof. intros. rewrite !exp'_0_elem. apply exp'_0_elem. Qed.

(** *** Example *)

(** 构造 exp23 实例, ((1,2,3),(4,5,6) *)
Example myexp: exp myd:= [[1,2,3],[4,5,6]]%R.

(** ** exp_unfold *)

(** 定义 exp_unfold, 将表达式形式转化成向量形式 *)
Definition exp_unfold {m n d} {E : n <= m} (e: exp (ary [n|E] d)) : vector (exp d) n:= e.

(** *** Lemma *)

(** 经过 exp_unfold 后的与原先相同 *)
Definition exp_unfold_eq: forall {m n d} {E : n <= m} (e: exp (ary [n|E] d)),
 exp_unfold e = e.
Proof. vauto. Qed.

(** *** Example *)

(** exp23 实例经过 exp_unfold 转换后仍为本身 *)
Goal (exp_unfold myexp: vector (vector R 3) 2) = [[1,2,3],[4,5,6]]%R.
Proof. vauto. Qed.

(** ** exp_fold *)

(** 定义 exp_fold, 将向量形式转化成表达式形式 *)
Definition exp_fold {m n d} (E: n <= m) (e: vector (exp d) n): exp (ary [n | E] d):= e.

(** *** Lemma *)

(** 经过 exp_unfold后的与原先相同 *)
Lemma exp_fold_eq: forall {m n d} (e: vector (exp d) n) (E: n <= m),
 exp_fold E e = e.
Proof. vauto. Qed.

(** 先经过 exp_fold 再经过 exp_unfold 与 原先相同 *)
Lemma exp_unfold_fold: forall m n d (E: n <= m) (e: vector (exp d) n),
 exp_unfold (exp_fold E e) = e.
Proof. vauto. Qed.

(** 先经过 exp_unfold 再经过 exp_fold 与 原先相同 *)
Lemma exp_fold_unfold: forall m n d (E: n <= m) (e: exp (ary [n | E] d)),
 exp_fold E (exp_unfold e) = e.
Proof. vauto. Qed.

(** *** Example *)

(** exp23 实例经过 exp_unfold 再经过 exp_fold 转换后仍为本身 *)
Goal exp_fold (le_n 2) (exp_unfold myexp) = [[1,2,3],[4,5,6]]%R.
Proof. auto. Qed.

(** ** exp_des *)

(** *** Definition *)

(** 定义 exp_des, 将 exp (ary (S n) d) 转化为 (exp (ary n d)) 与 (exp d) *)
Definition exp_des {m n d} {E: S n <= m} (e: exp (ary [S n | E] d)): exp (@ary m [n | leS_le E] d) * exp d.
Proof. simpl in e; destruct e. exact (v, e). Defined.

(** *** Lemma *)

(** 对 exp_des 来说, 整体 exp_unfold 等于头部 exp_unfold *)
Lemma exp_unfold_des : forall {m n d} {E : S n <= m} (e : exp (ary [S n | E] d)),
  exp_unfold e = (exp_unfold (fst (exp_des e)), (snd (exp_des e))).
Proof. intros. destruct e; fauto. Qed.

(** 对 exp_des 来说，整体 exp_fold 等于头部 exp_fold *)
Lemma exp_des_fold : forall {m n d} (E : S n <= m) (ve : vector (exp d) (S n)),
  exp_des (exp_fold E ve) = (exp_fold (leS_le E) (fst ve), (snd ve)).
Proof. intros. destruct ve; fauto. Qed.

(** *** Example *)

(** 将 ((1,2,3),(4,5,6)) 拆分得 (((1,2,3)),(4,5,6)) *)
Goal exp_des myexp = ([[1,2,3]],[4,5,6])%R.
Proof. auto. Qed.

(** ** exp_con *)

(** *** Definition *)

(** 将 exp_con, 将表达式组合起来 *)
Definition exp_con {m n d} {E: S n <= m} (e: exp (@ary m [n | leS_le E] d) * exp d): exp (ary [S n | E] d).
Proof. exact e. Defined.

(** *** Lemma *)

(** 对 exp_con 来说, 整体 exp_unfold 等于头部 exp_unfold *)
Lemma exp_unfold_con : forall {m n d} {E : S n <= m} 
  (ve : exp (ary [n | leS_le E] d)) (e : exp d),
  exp_unfold (exp_con (ve, e)) = (exp_unfold ve, e).
Proof. intros. fauto. Qed.

(** 对 exp_des 来说，整体 exp_fold 等于头部 exp_fold *)
Lemma exp_con_fold : forall {m n d} (E : S n <= m) 
  (ve : vector (exp d) n) (e : exp d),
  exp_con (exp_fold (leS_le E) ve, e) = exp_fold E (ve, e).
Proof. intros. fauto. Qed.

(** 一个表达式先拆分后组合依旧为该表达式本身 *)
Lemma exp_con_des: forall m n d {E: S n <= m} (e: exp (ary [S n| E] d)),
 exp_con (exp_des e) = e.
Proof. unfold exp_des, exp_con; intros. destruct e; vauto. Qed.

(** 两个表达式先组合后拆分依旧为该两个表达式本身 *)
Lemma exp_des_con: forall m n d {E: S n <= m} (e: exp (@ary m [n | leS_le E] d) * exp d) ,
 exp_des (exp_con e) = e.
Proof. unfold exp_des, exp_con; intros. destruct e; vauto. Qed.

(** *** Example *)

(** 将 (((1,2,3)), (4,5,6)) 组合得到 ((1,2,3),(4,5,6)) *)
Goal exp_con (exp_des myexp) = [[1,2,3],[4,5,6]]%R.
Proof. auto. Qed.


(** ** exp_default *)

(** *** Definition *)

(** 定义 exp_default, 表达式的默认值为 R0 或者 R0 的数组 *)
Fixpoint exp_default {d}: exp d:= 
 match d with
 | num => R0
 | ary n d => v_make (fun i: fin n => exp_default)
 end.

(** *** Lemma *)

(** 当 d 为 num 时,直接返回 R0 *)
Lemma exp_default_num: @exp_default num = R0.
Proof. vauto. Qed.

(** 当 d 为 ary n d 时, 返回一个经过 exp_fold 转变的 vector *)
Lemma exp_default_ary: forall {m n d},
 @exp_default (@ary m n d) = exp_fold (fle_proof n) (v_make (fun i: fin n => exp_default)).
Proof. vauto. Qed.

(** *** Example *)

(** 对一个 2 * 3 的数组使用 exp_default, 得到 ((R0,R0,R0), (R0,R0,R0)) *)
Goal @exp_default myd = [[R0,R0,R0],[R0,R0,R0]].
Proof. auto. Qed.

(** ** e_idx *)

(** *** Definition *)

(** 定义 e_idx, 用于访问 exp 表达式的内部值 *)
Definition e_idx {m n d} (v: exp (@ary m n d)) i: exp d:= 
 v_idx (@exp_default d) v i.

Notation " a |[ i ] ":= (e_idx a i) (at level 2).

(** *** Lemma *)

(** 证明对于 e_idx 来说, (v, e): ary (S n) d 头部为 v *)
Lemma e_idx_head: forall m n d {E: S n <= m} (ve: exp (@ary m [n | leS_le E] d)) (e: exp d) i,
 (exp_con (ve, e)) |[FS[i]] = ve |[i].
Proof. intros. unfold exp_con, e_idx. apply v_idx_head. Qed.

(** 证明对于 e_idx 来说, (v, e): ary (S n) d 头部为 v *)
Lemma e_idx_head_H: forall m n d {E: S n <= m} (ve: exp (@ary m [n | leS_le E] d)) (e: exp d) 
 (i: fin (S n)) (E1: i < n),
 (exp_con (ve, e)) |[i] = ve |[FP[E1]].
Proof. intros. unfold exp_con, e_idx. apply v_idx_head_H. Qed.

(** 证明对于 e_idx 来说, (v, e): ary (S n) d 尾部为 e *)
Lemma e_idx_tail: forall m n d {E: S n <= m} (ve: exp (@ary m [n | leS_le E] d)) (e: exp d),
 (exp_con (ve, e)) |['[n]] = e.
Proof. intros. unfold exp_con, e_idx. apply v_idx_tail. Qed.

(** 对于 e1 e2: vector, 若 e1 = e2, 则对于 i: fin n, 通过 e_idx 获取的值相同; 反之亦然 *)
Lemma e_idx_eq_e: forall {m n d} (e1 e2: exp (@ary m n d)),
 e1 = e2 <-> (forall i, e1 |[i] = e2 |[i]).
Proof. intros. apply v_idx_eq_v. Qed.

(** *** Example *)

(** exp23 实例的 0 2 位置为 3 *)
Example e_idx_test : myexp |[(fin_0S)] |['[2]] = 3%R.
Proof. auto. Qed.

(** ** exp2exp *)

(** *** Definition*)

(** 将 exp m n d 转换为 exp m' n d *)
Definition exp2exp {m m' n d} {E : n <= m} (e : exp (ary [n | E] d)) (E' : n <= m')
  : exp (ary [n | E'] d).
Proof. exact e. Defined.

Notation "EE[ e | E ]":= (exp2exp e E).

(** *** Lemma *)

(** exp2exp等于先展开再按照 m' 折叠 *)
Lemma exp2exp_eq: forall {m m' n d} {E : n <= m} (e : exp (ary [n | E] d)) (E' : n <= m'),
  EE[ e | E ] = exp_fold E' (exp_unfold e).
Proof. vauto. Qed.

(** 通过 e_idx 取经过 exp2exp 转变的 exp值不变 *)
Lemma e_idx_exp2exp: forall m m' n d (E : n <= m) (e : exp (ary [n | E] d)) (E' : n <= m') i,
  EE[ e | E'] |[i] = e |[i].
Proof. vauto. Qed.

(** *** Example *)

(** 经过 exp2exp 转变后的 myexp 取 (0,2) 为 3*)
Example exp2exp_test : EE[ myexp | Nat.le_succ_diag_r 2] |[(fin_0S)] |['[2]] = 3%R.
Proof. auto. Qed.

(** ** optexp *)

(** *** Definition *)

(** 定义 optexp, 根据 d 的合法性来判断 *)
Definition optexp {d : data} (e : exp d) : option (exp d) :=
  match (optdata d) with
  | Some d => Some e
  | None => None
  end.

(** *** Lemma *)

(** optexp 是总是返回自身的函数 *)
Lemma optexp_eq: forall d  (e1 e2 : exp d), optexp e1 = Some e2 -> e1 = e2.
Proof with vauto.
 intros. unfold optexp in H. destruct (optdata d); inv H...
Qed.

(** 当 optdata d = Some d 时, optexp e = Some e; 反之亦然 *)
Lemma optexp_Some_eq : forall d (e : exp d),
  optdata d = Some d <-> optexp e = Some e.
Proof with vauto.
  unfold optexp; split... rewrite H...
  destruct (optdata d) eqn : E. f_equal.
  apply optdata_eq in E... inv H.
Qed.

(** 当 optdata d = Some d 时, optexp e = Some e *)
Lemma optexp_Some_eq_l : forall d (e : exp d),
  optdata d = Some d -> optexp e = Some e.
Proof. intros. apply optexp_Some_eq; vauto. Qed.

(** 当 optexp e = Some e 时, optdata d = Some e *)
Lemma opt_exp_Some_eq_r : forall d (e : exp d),
  optexp e = Some e -> optdata d = Some d.
Proof. intros. apply optexp_Some_eq in H; vauto. Qed.

(** 当 optdata d = None 时, optexp e = None; 反之亦然 *)
Lemma optexp_None_eq : forall d (e : exp d),
  optdata d = None <-> optexp e = None.
Proof with vauto.
  unfold optexp; split... rewrite H...
  destruct (optdata d) eqn : E...
Qed.

(** 当 optdata d = None 时, optexp e = None *)
Lemma optexp_None_eq_l : forall d (e : exp d),
  optdata d = None -> optexp e = None.
Proof. intros. apply optexp_None_eq; vauto. Qed.

(** 当 optexp e = None 时, optdata d = None *)
Lemma optexp_None_eq_r : forall d (e : exp d),
  optexp e = None -> optdata d = None.
Proof. intros. apply optexp_None_eq in H; vauto. Qed.

(** 当 optexp e = None时， e = exp_default d *)
Lemma optexp_None_default : forall d (e : exp d),
  optexp e = None -> e = @exp_default d.
Proof with vauto.
  induction d...
  - apply optexp_None_eq in H. inv H.
  - apply optexp_None_eq in H.
    destruct (classic (0 < fle2nat n)).
    + apply optdata_sub_none in H... apply e_idx_eq_e...
      rewrite exp_default_ary. unfold exp_fold... unfold e_idx.
      rewrite v_idx_make... apply IHd. apply optexp_None_eq...
    + destruct n as [n Hn]. clear H. simpl in H0. assert (n = 0)...
Qed.

(** ** seq_make *)

(** *** Definition *)

(** 定义 seq_make, 将一个生成exp d的函数组合成 exp (ary n d) *)
Definition seq_make {n d} (f : fin n -> exp d) : exp (ary '{n} d) := v_make f.

(** *** Lemma *)

(** 展开 seq_make *)
Lemma seq_make_unfold: forall {n d} (f: fin n -> exp d),
  seq_make f = exp_fold (le_n n) (v_make f).
Proof. auto. Qed.

(** 展开 seq_make (S n) *)
Lemma seq_make_Sn: forall n d (f: fin (S n) -> exp d),
  seq_make f = exp_con (seq_make (fun i => f FS[i]), f '[n]).
Proof. auto. Qed.

(** 化简 seq_make_0 *)
Lemma seq_make_0 : forall d (f : fin 0 -> exp d),
  seq_make f = (tt : exp (ary '{0} d)).
Proof. auto. Qed.

(** 对于 seq_make f 的第 i 位等于直接 f i *)
Lemma seq_make_idx : forall d n (f: fin n -> exp d) i,
 (seq_make f)|[i] = f i.
Proof. fauto. apply v_idx_make. Qed.

(** ** seq_make *)

(** *** Definition *)

Definition par_make {n d} (f : fin n -> exp d) : exp (ary '{n} d) := v_make f.

(** *** Lemma *)

(** 展开 par_make *)
Lemma par_make_unfold: forall {n d} (f: fin n -> exp d),
  par_make f = exp_fold (le_n n) (v_make f).
Proof. auto. Qed.

(** 展开 par_make (S n) *)
Lemma par_make_Sn: forall n d (f: fin (S n) -> exp d),
  par_make f = exp_con (EE[par_make (fun i => f FS[i]) | Nat.le_succ_diag_r n], f '[n]).
Proof. auto. Qed.

(** 展开 par_make (S n) *)
Lemma par_make_Sn_H: forall m n d (E : S n <= m) (f: fin (S n) -> exp d),
  par_make f = exp_con (EE[par_make (fun i => f FS[i]) | leS_le E], f '[n]).
Proof. auto. Qed.

(** 化简 par_make_0 *)
Lemma par_make_0 : forall d (f : fin 0 -> exp d),
  par_make f = (tt : exp (ary '{0} d)).
Proof. auto. Qed.

(** 对于 par_make f 的第 i 位等于直接 f i *)
Lemma par_make_idx : forall d n (f: fin n -> exp d) i,
 (par_make f)|[i] = f i.
Proof. fauto. apply v_idx_make. Qed.

End Expersion.

(** ** Notation *)

Notation " a |[ i ] ":= (e_idx a i) (at level 2).

Notation "EE[ e | E ]":= (exp2exp e E).

(** ** Auto *)

#[export] Hint Rewrite exp'_0 exp'_0_elem exp_unfold_fold exp_fold_unfold exp_con_des
exp_des_con exp_default_num e_idx_head e_idx_head_H e_idx_tail e_idx_exp2exp seq_make_Sn 
par_make_Sn_H seq_make_0 seq_make_idx par_make_Sn par_make_0 par_make_idx: dcore.

#[export] Hint Resolve exp'_0_unique exp_unfold_eq exp_fold_eq exp_default_ary e_idx_eq_e
exp2exp_eq optexp_eq optexp_Some_eq optexp_None_eq optexp_None_default seq_make_unfold 
par_make_unfold: dcore.

(* ######################################################################### *)

(** * Accessor *)

Section Accessor.

(** ** acc *)

(** 定义 acc, 将数据结构转化为路径表达式. 当为 num时,转为 path; 当为数组时,转化为 path 的数组 *)
Fixpoint acc (d: data): Set:= 
 match d with
 | num => path 
 | ary n d => vector (acc d) n
 end.

(** *** Lemma *)

(** 如果 d1 = d2, 那么类型 acc d1 与 acc d2 相同 *)
Lemma acc'_eq: forall {A: Set} {d1 d2}, d1 = d2 -> acc d1 = acc d2.
Proof. vauto. Qed.

(** 证明 acc (ary '{0} d) 为 unit *)
Lemma acc'_0: forall d , acc (ary '{0} d) = unit.
Proof. vauto. Qed.

(** 证明 acc (ary '{0} d)只有一个元素 *)
Lemma acc'_0_elem: forall d (a: acc (ary '{0} d)), a = (tt: vector (exp d) 0).
Proof. intros. destruct a. vauto. Qed.

(** 证明 acc (ary '{0} d) 唯一性 *)
Lemma acc'_0_unique: forall {d} (a a': acc (ary '{0} d)), a = a'.
Proof. intros. rewrite !acc'_0_elem. apply acc'_0_elem. Qed.

(** *** Example *)

(** 0 < 2 *)
Example _0lt2: 0 < 2. Proof. lia. Qed.

(** 1 < 2 *)
Example _1lt2: 1 < 2. Proof. lia. Qed.

(** 0 < 3 *)
Example _0lt3: 0 < 3. Proof. lia. Qed.

(** 1 < 3 *)
Example _1lt3: 1 < 3. Proof. lia. Qed.

(** 2 < 3 *)
Example _2lt3: 2 < 3. Proof. lia. Qed.

(** 访问 arr 数组的 （0,0) 位置 *)
Example arr_00:= (Ary F[_0lt3] (Ary F[_0lt2] (Var "arr"))).

(** 访问 arr 数组的 （0,1) 位置 *)
Example arr_01:= (Ary F[_1lt3] (Ary F[_0lt2] (Var "arr"))).

(** 访问 arr 数组的 （0,2) 位置 *)
Example arr_02:= (Ary F[_2lt3] (Ary F[_0lt2] (Var "arr"))).

(** 访问 arr 数组的 （1,0) 位置 *)
Example arr_10:= (Ary F[_0lt3] (Ary F[_1lt2] (Var "arr"))).

(** 访问 arr 数组的 （1,1) 位置 *)
Example arr_11:= (Ary F[_1lt3] (Ary F[_1lt2] (Var "arr"))).

(** 访问 arr 数组的 （1,2) 位置 *)
Example arr_12:= (Ary F[_2lt3] (Ary F[_1lt2] (Var "arr"))).

(** 构造 acc23 实例, 存储对应访问 数组 arr 2 * 3 数组位置的地址 *)
Example acc23_example: acc myd:= 
 [[arr_00, arr_01, arr_02],[arr_10, arr_11,arr_12]].

(** ** acc_unfold *)

(** 定义 acc_unfold, 将路径表达式形式转化成向量形式 *)
Definition acc_unfold {m n d} (a: acc (@ary m n d)): vector (acc d) n:= a.

(** *** Lemma *)

(** 经过 acc_unfold 后的与原先相同 *)
Definition acc_unfold_eq: forall {m n d} (a: acc (@ary m n d)),
 acc_unfold a = a.
Proof. vauto. Qed.

(** *** Example *)

(** acc23 实例经过 acc_unfold 转换后仍为本身 *)
Example acc_unfold_test: (acc_unfold acc23_example: vector (vector path 3) 2) = 
 [[arr_00, arr_01, arr_02],[arr_10, arr_11,arr_12]].
Proof. vauto. Qed.

(** ** acc_fold *)

(** 定义 acc_fold, 将向量形式转化成路径表达式形式 *)
Definition acc_fold {m n d} (E: n <= m) (a: vector (acc d) n): acc (ary [n | E] d):= a.

(** *** Lemma *)

(** 经过 acc_unfold后的与原先相同 *)
Lemma acc_fold_eq: forall {m n d} (a: vector (acc d) n) (E: n <= m),
 acc_fold E a = a.
Proof. vauto. Qed.

(** 先经过 acc_fold 再经过 acc_unfold 与 原先相同 *)
Lemma acc_unfold_fold: forall m n d (E: n <= m) (e: vector (acc d) n),
 acc_unfold (acc_fold E e) = e.
Proof. vauto. Qed.

(** 先经过 acc_unfold 再经过 acc_fold 与 原先相同 *)
Lemma acc_fold_unfold: forall m n d (E: n <= m) (a: acc (ary [n | E] d)),
 acc_fold E (acc_unfold a) = a.
Proof. vauto. Qed.

(** *** Example *)

(** acc23 实例经过 acc_unfold 再经过 acc_fold 转换后仍为本身 *)
Example acc_fold_test: acc_fold (le_n 2) (acc_unfold acc23_example) = 
 [[arr_00, arr_01, arr_02],[arr_10, arr_11,arr_12]].
Proof. auto. Qed.

(** ** acc_des *)

(** *** Definition *)

(** 定义 acc_des, 将 acc (ary (S n) d) 转化为 (acc (ary n d)) 与 (acc d) *)
Definition acc_des {m n d} {E: S n <= m} (a: acc (ary [S n | E] d)): acc (@ary m [n | leS_le E] d) * acc d.
Proof. simpl in a; destruct a. exact (v, a). Defined.

(** *** Example *)

(** 将 ((1,2,3),(4,5,6)) 拆分得 (((1,2,3)),(4,5,6)) *)
Example acc_des_test: acc_des acc23_example = 
 ([[arr_00, arr_01, arr_02]],[arr_10, arr_11,arr_12]).
Proof. auto. Qed.

(** ** acc_con *)

(** *** Definition *)

(** 将 acc_con, 将路径表达式组合起来 *)
Definition acc_con {m n d} {E: S n <= m} (a: acc (@ary m [n | leS_le E] d) * acc d): acc (ary [S n | E] d).
Proof. exact a. Defined.

(** *** Lemma *)

(** 一个表达式先拆分后组合依旧为该表达式本身 *)
Lemma acc_con_des: forall m n d {E: S n <= m} (a: acc (ary [S n| E] d)),
 acc_con (acc_des a) = a.
Proof. unfold acc_des, acc_con; intros. destruct a; vauto. Qed.

(** 两个表达式先组合后拆分依旧为该两个表达式本身 *)
Lemma acc_des_con: forall m n d {E: S n <= m} (a: acc (@ary m [n | leS_le E] d) * acc d) ,
 acc_des (acc_con a) = a.
Proof. unfold acc_des, acc_con; intros. destruct a; vauto. Qed.

(** *** Example *)

(** 将 (((1,2,3)), (4,5,6)) 组合得到 ((1,2,3),(4,5,6)) *)
Example acc_con_test: acc_con (acc_des acc23_example) = 
 [[arr_00, arr_01, arr_02],[arr_10, arr_11,arr_12]].
Proof. auto. Qed.

(** ** acc_default *)

(** *** Definition *)

(** 定义 acc_default, 表达式的默认值为 R0 或者 R0 的数组 *)
Fixpoint acc_default {d}: acc d:= 
 match d with
 | num => Var ""
 | ary n d => v_make (fun i: fin n => acc_default)
 end.

(** *** Lemma *)

(** 当 d 为 num 时,直接返回 Var "" *)
Lemma acc_default_num: @acc_default num = Var "".
Proof. vauto. Qed.

(** 当 d 为 ary n d 时, 返回一个经过 acc_fold 转变的 vector *)
Lemma acc_default_ary: forall {m n d},
 @acc_default (@ary m n d) = acc_fold (fle_proof n) (v_make (fun i: fin n => acc_default)).
Proof. vauto. Qed.

(** *** Example *)

(** 空路径 *)
Example p_default:= Var "".

(** 对一个 2 * 3 的数组使用 acc_default, 得到 ((p_default,p_default,p_default), (p_default,p_default,p_default)) *)
Example acc_default_test: @acc_default myd = 
 [[p_default,p_default,p_default],[p_default,p_default,p_default]].
Proof. auto. Qed.

(** ** a_idx *)

(** *** Definition *)

(** 定义 a_idx, 用于访问 acc 表达式的内部值 *)
Definition a_idx {m n d} (v: acc (@ary m n d)) i: acc d:= 
 v_idx (@acc_default d) v i.

Notation " a |{ i } ":= (a_idx a i) (at level 2).

(** *** Lemma *)

(** 证明对于 a_idx 来说, (v, a): ary (S n) d 头部为 v *)
Lemma a_idx_head: forall m n d {E: S n <= m} (va: acc (@ary m [n | leS_le E] d)) (a: acc d) i,
 (acc_con (va, a)) |{FS[i]} = va |{i}.
Proof. intros. unfold acc_con, a_idx. apply v_idx_head. Qed.

(** 证明对于 a_idx 来说, (v, e): ary (S n) d 头部为 v *)
Lemma a_idx_head_H: forall m n d {E: S n <= m} (va: acc (@ary m [n | leS_le E] d)) (a: acc d) 
 (i: fin (S n)) (E1: i < n),
 (acc_con (va, a)) |{i} = va |{FP[E1]}.
Proof. intros. unfold acc_con, a_idx. apply v_idx_head_H. Qed.

(** 证明对于 a_idx 来说, (v, e): ary (S n) d 尾部为 a *)
Lemma a_idx_tail: forall m n d {E: S n <= m} (va: acc (@ary m [n | leS_le E] d)) (a: acc d),
 (acc_con (va, a)) |{'[n]} = a.
Proof. intros. unfold acc_con, a_idx. apply v_idx_tail. Qed.

(** 对于 e1 e2: vector, 若 e1 = e2, 则对于 i: fin n, 通过 a_idx 获取的值相同; 反之亦然 *)
Lemma a_idx_eq_a: forall {m n d} (a1 a2: acc (@ary m n d)),
 a1 = a2 <-> (forall i, a1 |{i} = a2 |{i}).
Proof. intros. apply v_idx_eq_v. Qed.

(** *** Example *)

(** acc23 实例的 0 2 位置为 3 *)
Example a_idx_test: acc23_example |{(fin_0S)} |{'[2]} = arr_02.
Proof. auto. Qed.

(** ** acc2acc *)

(** *** Definition*)

(** 将 acc m n d 转换为 acc m' n d *)
Definition acc2acc {m m' n d} {E : n <= m} (a : acc (ary [n | E] d)) (E' : n <= m')
  : acc (ary [n | E'] d).
Proof. exact a. Defined.

Notation "AA[ a | E ]":= (acc2acc a E).

(** *** Lemma *)

(** acc2acc等于先展开再按照 m' 折叠 *)
Lemma acc2acc_eq: forall {m m' n d} {E : n <= m} (e : acc (ary [n | E] d)) (E' : n <= m'),
  AA[ e | E ] = acc_fold E' (acc_unfold e).
Proof. vauto. Qed.

(** 通过 e_idx 取经过 acc2acc 转变的 acc值不变 *)
Lemma a_idx_acc2acc: forall m m' n d {E : n <= m} (e : acc (ary [n | E] d)) (E' : n <= m') i,
  AA[ e | E'] |{i} = e |{i}.
Proof. vauto. Qed.

(** *** Example *)

(** 经过 acc2acc 转变后的 acc23_example 取 (0,2) 为 arr_02*)
Example acc2acc_test : AA[ acc23_example | Nat.le_succ_diag_r 2] |{(fin_0S)} |{'[2]} = arr_02.
Proof. auto. Qed.


(** ** optacc *)

(** *** Definition *)

(** 定义 optacc, 根据 d 的合法性来判断 *)
Definition optacc {d : data} (e : acc d) : option (acc d) :=
  match (optdata d) with
  | Some d => Some e
  | None => None
  end.

(** *** Lemma *)

(** optacc 是总是返回自身的函数 *)
Lemma optacc_eq: forall d  (a1 a2 : acc d), optacc a1 = Some a2 -> a1 = a2.
Proof with vauto.
 intros. unfold optacc in H. destruct (optdata d); inv H...
Qed.

(** 当 optdata d = Some d 时, optacc e = Some e; 反之亦然 *)
Lemma optacc_Some_eq : forall d (e : acc d),
  optdata d = Some d <-> optacc e = Some e.
Proof with vauto.
  unfold optacc; split... rewrite H...
  destruct (optdata d) eqn : E. f_equal.
  apply optdata_eq in E... inv H.
Qed.

(** 当 optdata d = Some d 时, optacc e = Some e *)
Lemma optacc_Some_eq_l : forall d (e : acc d),
  optdata d = Some d -> optacc e = Some e.
Proof. intros. apply optacc_Some_eq; vauto. Qed.

(** 当 optacc e = Some e 时, optdata d = Some e *)
Lemma opt_acc_Some_eq_r : forall d (e : acc d),
  optacc e = Some e -> optdata d = Some d.
Proof. intros. apply optacc_Some_eq in H; vauto. Qed.

(** 当 optdata d = None 时, optacc e = None; 反之亦然 *)
Lemma optacc_None_eq : forall d (e : acc d),
  optdata d = None <-> optacc e = None.
Proof with vauto.
  unfold optacc; split... rewrite H...
  destruct (optdata d) eqn : E...
Qed.

(** 当 optdata d = None 时, optacc e = None *)
Lemma optacc_None_eq_l : forall d (e : acc d),
  optdata d = None -> optacc e = None.
Proof. intros. apply optacc_None_eq; vauto. Qed.

(** 当 optacc e = None 时, optdata d = None *)
Lemma optacc_None_eq_r : forall d (e : acc d),
  optacc e = None -> optdata d = None.
Proof. intros. apply optacc_None_eq in H; vauto. Qed.


(** ** accp *)

(** *** Definition *)

(** 定义 accp, 通过输入路径来直接构造一个 acc d *)
Fixpoint accp {d: data} (p: path): acc d:= 
 match d with
 | num => p: acc num
 | @ary m n d' => v_make (fun i: fin n => @accp d' (@Ary m FF'[i | n] p)) (* array of length m *)
end.

(** *** Lemma *)

(** 当 d 为 num 时, 直接返回 p *)
Lemma accp_num: forall p, @accp num p = p.
Proof. vauto. Qed.

(** 当 d 为 arr 时, 返回经过 a_fold 的 vector *)
Lemma accp_ary: forall {m n d} p,
 @accp (@ary m n d) p = acc_fold (fle_proof n) (v_make (fun i: fin n => accp  (@Ary m FF'[i | n] p))).
Proof. vauto. Qed.

(** 化简 accp Sn *)
Lemma accp_Sn: forall m n d p {E: S n <= m},
 @accp (ary [S n| E] d) p = (acc_con (accp p,
 accp (Ary FF'[ '[ n] | [S n | E]] p))).
Proof.
 intros; unfold acc_con; simpl. f_equal; f_equal. fun_ext. f_equal; f_equal. apply fin_eq; vauto.
Qed.

(** 化简 a_idx_accp *)
Lemma a_idx_accp : forall m n d p {E :  n <= m} i,
  (@accp (ary [n | E] d) p) |{i} = accp (Ary FF'[i | [n | E]] p).
Proof. intros. simpl. unfold a_idx. rewrite v_idx_make. auto. Qed.

(** *** Example *)

(** 证明通过 accp (Var "arr") 生成的路径数组与 acc23 实例相同 *)
Example myacc := @accp myd (Var "arr").

Example accp_test: myacc = acc23_example.
Proof. unfold myacc, acc23_example. simpl. unfold arr_00,arr_01, arr_02, arr_10, arr_11, arr_12.
 repeat f_equal; vauto. 
Qed.

End Accessor.

(** ** Notation *)

Notation " a |{ i } ":= (a_idx a i) (at level 2).

Notation "AA[ a | E ]":= (acc2acc a E).

(** ** Auto *)

#[export] Hint Rewrite acc'_0 acc'_0_elem acc_unfold_fold acc_fold_unfold
acc_con_des acc_des_con acc_default_num a_idx_head a_idx_head_H a_idx_tail a_idx_acc2acc
 accp_num accp_Sn a_idx_accp: dcore.

#[export] Hint Resolve acc'_0_unique acc_default_ary a_idx_eq_a acc2acc_eq
optacc_eq optacc_Some_eq optacc_None_eq accp_ary: dcore.


(* ######################################################################### *)
(** * Ltac *)

(** ** data_simpl *)

(** 定义 vector 化简: 
1. 分析 v: vector 0 的前提
2. 分析 i: fin 1 和 i: fle n 的前提
3. 若目标为 < 或者 <= , 尝试通过 fin 或者 fle 的性质证明
4. 若目标为 = , 尝试通过 fin_eq 进行分析 *)
Ltac data_simpl:= idtac.

(** 定义 vauto, 包含本所定义的一些引理和定义 *)
Ltac dauto:= 
 repeat (quan_simpl; bool_simpl; opt_simpl; pair_simpl; fun_simpl; data_simpl; path_simpl;
 vec_simpl; f_simpl); subst; 
 autorewrite with vcore dcore fcore core; auto with dcore vcore fcore core;
 try lia; try apply proof_irrelevance.
