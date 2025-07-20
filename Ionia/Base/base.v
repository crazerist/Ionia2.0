Require Export Arith Reals Nat Bool String List Lia Lra.
Require Import Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.

Set Implicit Arguments.


(* ######################################################################### *)
(** * Basic Ltac *)

(** ** inv *)

(** 引入后在进行分解假设 H *)
Ltac inv H:= intros; inversion H.

(** ** fun_ext *)

(** 函数化简 *)
Ltac fun_ext:= apply functional_extensionality; intros.

(** ** quan_simpl *)

(** 当 if 后两个结果相同时，去掉 if *)
Lemma if_same : forall {A : Set} (b : bool) (a : A),
  (if b then a else a) = a.
Proof. destruct b; auto. Qed.

(** 量词化简:
1.当目标中存在存在量词， 尝试引入 
2.当目标中存在 /\ 或 <->, 尝试分解
3.当目标中存在if,尝试去除
4.当假设中存在存在量词, 尝试分解
5.当假设中存在 /\ 尝试分解
6.当假设中存在 if，尝试去除
7.当假设中存在 x<>x 时, 直接判定否 *)

Ltac quan_simpl:=
 repeat match goal with
 | [ |- forall _, _ ] => intros
 | [ |- _ <-> _ ] => split
 | [ |- _ /\ _ ] => split
 | [ |- context[ if ?b then ?a else ?a]] => rewrite if_same
 | [ |- _ <> _ ] => intro
 | [ H: exists _, _ |- _] => destruct H
 | [ H:  _ /\ _ |- _] => destruct H
 | [ H: context[ if ?b then ?a else ?a] |- _ ] => rewrite if_same in H
 | [ H: ?x <> ?x |- _ ] => exfalso; apply H; reflexivity
 end.

(** ** bool_simpl *)

(** 布尔表达式化简:
1.将布尔值的等式标准化
2.将布尔值的自然数比较转换为数学形式
3.将布尔值的逻辑运算拆分为更简单的子假设
4.它通过递归调用确保所有可以简化的假设都被处理 *)
Ltac bool_simpl:=
 repeat match goal with
 | [ H: (true = _) |- _ ] => symmetry in H
 | [ H: (false = _) |- _ ] => symmetry in H
 | [ H: (_ <? _ = true)%nat |- _ ] => apply Nat.ltb_lt in H
 | [ H: (_ <? _ = false)%nat |- _ ] => apply Nat.ltb_nlt in H
 | [ H: (_ =? _ = true)%nat |- _ ] => apply Nat.eqb_eq in H
 | [ H: (_ =? _ = false)%nat |- _ ] => apply Nat.eqb_neq in H
 | [ H: (_ && _ = true) |- _ ] => apply andb_true_iff in H; destruct H
 | [ H: (_ && _ = false) |- _ ] => apply andb_false_iff in H; destruct H
 | [ H: context[(true && ?b)] |- _ ] => rewrite andb_true_l in H
 | [ H: context[(?b && true)] |- _ ] => rewrite andb_true_r in H
 | [ H: context[(false && ?b)] |- _ ] => rewrite andb_false_l in H
 | [ H: context[(?b && false)] |- _ ] => rewrite andb_false_r in H
 | [ |- true = _ ] => symmetry
 | [ |- false = _ ] => symmetry
 | [ |- (_ <? _ = true)%nat ] => apply Nat.ltb_lt
 | [ |- (_ <? _ = false)%nat ] => apply Nat.ltb_nlt
 | [ |- (_ =? _ = true)%nat ] => apply Nat.eqb_eq
 | [ |- (_ =? _ = false)%nat ] => apply Nat.eqb_neq
 | [ |- (_ && _ = true) ] => apply andb_true_intro; split
 | [ |- (_ && _ = false) ] => apply andb_false_iff
 | [ |- context[(true && ?b)] ] => rewrite andb_true_l
 | [ |- context[(?b && true)] ] => rewrite andb_true_r
 | [ |- context[(false && ?b)] ] => rewrite andb_false_l
 | [ |- context[(?b && false)] ] => rewrite andb_false_r
 | [ |- context[ (?x =? ?y) ]] => let E:= fresh "E" in destruct (x =? y) eqn:E
 end.

(** ** opt_simp *)

(** 可选项化简: 将假设中的可选项拆解成自假设或者直接判定否，将目标中的可选项化简 *)
Ltac opt_simpl:=
 repeat match goal with
 | [ H: Some _ = Some _ |- _ ] => inv H; clear H
 | [ H: Some _ = None |- _ ] => inv H
 | [ H: None = Some _ |- _ ] => inv H
 | [ |- Some _ = Some _ ] => f_equal
 end.

(** ** pair_simpl *)

(** 对偶化简: 将假设的中对偶拆解, 将目标中的对偶拆分成子目标 *)
Ltac pair_simpl:=
 repeat match goal with
 | [ H: (_, _) = (_, _) |- _ ] => inv H; clear H
 | [ H: context [fst (_,_) ] |- _ ] => simpl fst in H
 | [ H: context [snd (_,_) ] |- _ ] => simpl snd in H
 | [ |- (_, _) = (_, _) ] => f_equal
 | [ |- context [fst (_, _) ]] => simpl fst
 | [ |- context [snd (_, _) ]] => simpl snd
 end.

(** ** fun_simpl *)

(** 函数简化 ： 将证明两个函数相等 *)
Ltac fun_simpl:= 
 repeat match goal with
 | [ |- (fun _ => _ ) = (fun _ => _) ] => apply functional_extensionality; intros
 end.

(** ** step_auto *)

(** 将之前几种化简方式组合并化简 *)
Ltac step_auto:=
 repeat (quan_simpl; bool_simpl; opt_simpl; pair_simpl; fun_simpl);
 subst; auto; try lia; try apply proof_irrelevance.

(* ######################################################################### *)
(** * Untils *)

Section Utils.

(** ** Nat Lemma *)

(** 证明 n + 2 = S (S n) *)
Lemma add_2_r: forall n, n + 2 = S (S n).
Proof. step_auto. Qed.

(** 证明对于自然航左乘一个数的零次幂, 等于这个数的本身 *)
Lemma pow_0_mul_1: forall i j, i ^ O * j = j.
Proof. step_auto. Qed.

(** 证明对于自然航左乘一个数的 S n 次幂, 等于这个数左乘一个数的 n 次幂 再左乘这个数 *)
Lemma pow_Sn_mul: forall n i j, i ^ S n * j = i * (i ^ n * j).
Proof. intros. rewrite Nat.pow_succ_r'. step_auto. Qed.

(** 将 ~ (val < m) 和 val < m + n 组合成 val - m < n *)
Lemma offset_proof: forall val m n,
 val < m + n -> ~ (val < m) -> val - m < n.
Proof. step_auto. Qed.

(** 若 k <= n, 则 k + (n - k) = n *)
Lemma sub_proof: forall n k, k <= n -> k + (n - k) = n.
Proof. step_auto. Qed.

(** 若 S i <= n, 则 i <= n *)
Lemma leS_le : forall i n, S i <= n -> i <= n.
Proof. lia. Qed.

(** 若 S i < n, 则 i < n *)
Lemma ltS_lt : forall i n, S i < n -> i < n.
Proof. lia. Qed.

(** 若 0 < 0, 则返回 False *)
Lemma _0lt0_False : 0 < 0 -> False.
Proof. lia. Qed.

Lemma sub_le_trans : forall a b c, a - b <= c -> a <= c + b.
Proof. intros. lia. Qed.

(** 后续常用的三个引理 *)
Lemma nat_lem1 : forall {x}, 1 <= x + 1 + 2 * 0.
Proof. lia. Qed.

Lemma nat_lem2 : forall {x}, 3 <= x + 1 + 2 * 1.
Proof. lia. Qed.

Lemma nat_lem2' : forall {x}, 3 <= x + 2 + 2 * 1.
Proof. lia. Qed.

Lemma nat_lem3 : forall {x}, 5 <= x + 1 + 2 * 2.
Proof. lia. Qed.

Lemma nat_lem4 : 0 < 1. Proof. lia. Qed.
Lemma nat_lem5 : 0 < 2. Proof. lia. Qed.
Lemma nat_lem6 : 0 < 3. Proof. lia. Qed.

Lemma nat_lem4' : forall {x}, 0 < x + 1. Proof. lia. Qed.
Lemma nat_lem5' : forall {x}, 0 < x + 2. Proof. lia. Qed.
Lemma nat_lem6' : forall {x}, 0 < x + 3. Proof. lia. Qed.

Lemma nat_lem7 : forall x, 1 <= x -> 0 < x. Proof. lia. Qed.

(** ** Unit Lemma *)

(** 证明 unit 中只有一个元素 tt *)
Lemma unit_elem: forall (u: unit), u = tt.
Proof. intros. destruct u. step_auto. Qed.

(** 证明 unit 中的元素唯一 *)
Lemma unit_unique: forall (u1 u2: unit), u1 = u2.
Proof. intros. rewrite !unit_elem. apply unit_elem. Qed.

(** ** n_reduce *)

(** *** Definition *)

(** 定义 n_reduce, 从 n - 1 到 0 对 val 依次进行 f i *)
Fixpoint n_reduce {B:Set} (f: nat -> B -> B) (val: B) (n: nat): B:=
 match n with
 | 0 => val
 | S n' => n_reduce f (f n' val) n'
 end.

(** *** Lemma *)

(** 化简 n_reduce (S n) *)
Lemma n_reduce_Sn: forall (B: Set) (f: nat -> B -> B) val n,
 n_reduce f val (S n) = n_reduce f (f n val) n.
Proof. step_auto. Qed.

(** 化简 n_reduce 0 *)
Lemma n_reduce_0: forall (B: Set) (f: nat -> B -> B) val,
 n_reduce f val 0 = val.
Proof. step_auto. Qed.

(** 对于 n_reduce 产生结果为 true, 那么初始值也为 true *)
Lemma n_reduce_true: forall (n: nat) (f: nat -> bool) val,
 n_reduce (fun i y => (y && f i)) val n = true -> val = true.
Proof.
 induction n; step_auto. apply IHn in H. step_auto.
Qed.

(** 如果两个函数在 0 ~ n - 1 上表现相同, 那么其在 n_reduce n 上返回结果相同 *)
Lemma n_reduce_eq: forall {B: Set} {n} (f f': nat -> B -> B) val,
 (forall i, i < n -> f i = f' i) -> n_reduce f val n = n_reduce f' val n.
Proof.
 induction n; step_auto. simpl. replace (f' n val) with (f n val). 
 apply IHn; step_auto. rewrite H; step_auto.
Qed.

(** *** Example *)

(** 从 3 到 0 依次对 1 累加等于 6 *)
Example n_reduce_example1 : n_reduce Nat.add 0 4 = 6. 
Proof. auto. (* 0+(1+(2+(3+0)))) = 6 *) Qed.

(** 从 4 到 1 一次对 1 累成等于 24 *)
Example n_reduce_example2 : n_reduce (fun x y => Nat.mul (x + 1) y) 1 4 = 24.
Proof. auto. (* 1*(2*(3*(4*1))) = 24 *) Qed.

(** ** n_forall *)

(** *** Definition *)

(** 定义 n_forall, 表示是否对任意 n - 1 到 0 的数 f 均返回 true *)
Definition n_forall (n:nat) (f: nat -> bool): bool:=
 n_reduce (fun x y => y && f x) true n.

(** *** Lemma *)

(** 化简 n_forall (S n) *)
Lemma n_forall_Sn: forall n (f: nat -> bool),
 n_forall (S n) f = f n && n_forall n f.
Proof with step_auto; simpl.
 unfold n_forall... destruct (f n)... induction n...
Qed.

(** 化简 n_forall 0 *)
Lemma n_forall_0: forall (f: nat -> bool),
 n_forall 0 f = true.
Proof. step_auto. Qed.

(** 证明, 当 i < n 时有 f i = true, 那么对于 n_forall n 返回 true *)
Lemma n_forall_eq_r: forall n (f: nat -> bool), 
 (forall i, i < n -> f i = true) -> n_forall n f = true.
Proof with step_auto.
 induction n... rewrite n_forall_Sn...
Qed.

(** 证明, 当 n_forall n 返回 true 时, 那么对于 i < n 时有 f i = true *)
Lemma n_forall_eq_l: forall n (f: nat -> bool), 
 n_forall n f = true -> (forall i, i < n -> f i = true). 
Proof with step_auto.
 induction n... rewrite n_forall_Sn in H...
 destruct (i =? n) eqn : E... apply IHn...
Qed.

(** 证明, 当 i < n 时有 f i = true, 那么对于 n_forall n 返回 true; 反之亦然 *)
Lemma n_forall_eq: forall n (f: nat -> bool),
 (forall i, i < n -> f i = true) <-> n_forall n f = true.
Proof.
 split. apply n_forall_eq_r. apply n_forall_eq_l.
Qed.

(** 证明, 当 n < m 时, 若对 m 来说 n_forall 返回 true, 那么对于 n 来说也返回 true *)
Lemma n_forall_true: forall n m (f: nat -> bool),
 n < m -> n_forall m f = true -> n_forall n f = true.
Proof with step_auto.
 step_auto. apply n_forall_eq... apply n_forall_eq_l with (i:= i) in H0... 
Qed.

(** 证明, 当 n < m 时, 若对 m 来说 n_forall 返回 false, 那么对于 n 来说也返回 false *)
Lemma n_forall_false: forall n m (f: nat -> bool),
 n < m -> n_forall n f = false -> n_forall m f = false.
Proof.
 step_auto. apply not_true_is_false; intro. (* 假设对于 m 来说返回 true *)
 apply (n_forall_true _ H) in H1. rewrite H0 in H1; inv H1.
Qed.

(** *** Example *)

(** 对于所有 0 至 3 的数 均小于 5, 该命题正确 *)
Example n_forall_example1 : n_forall 4 (fun x => x <? 5) = true.
Proof. auto. Qed.

(** 对于所有 0 至 3 的数 均小于 3, 该命题错误 *)
Example n_forall_example2 : n_forall 4 (fun x => x <? 3) = false.
Proof. auto. Qed.

(** ** cur *)

(** *** Definition *)

(** 定义 cur 化 *)
Definition cur {A B C:Set} (f: A -> B -> C): A * B -> C:=
 fun xy: A * B => f (fst xy) (snd xy).

(** 定义还原 cur 化 *)
Definition uncur {A B C:Set} (f: A * B -> C): A -> B -> C:=
 fun x y => f (x,y).

(** *** Lemma *)

(** 一个函数经过 cur 化再还原等于原函数 *)
Lemma uncur_cur: forall (A B C: Set) (f: A -> B -> C), uncur (cur f) = f.
Proof. step_auto. Qed.

(** 一个cur化的函数经过还原再 cur 化等于原函数 *)
Lemma cur_uncur: forall (A B C: Set) (f: A * B -> C), cur (uncur f) = f.
Proof. step_auto. fun_ext. destruct x; step_auto. Qed.

End Utils.

(** ** Auto *)


#[export] Hint Rewrite unit_elem n_reduce_Sn n_reduce_0 n_forall_Sn n_forall_0
uncur_cur cur_uncur : core.

#[export] Hint Resolve add_2_r pow_0_mul_1 pow_Sn_mul offset_proof sub_proof
unit_unique n_reduce_true n_reduce_eq n_forall_eq n_forall_true n_forall_false : core.


(* ######################################################################### *)
(** * Notations *)

(** ** exist *)
Notation " [ n | ]":= (exist _ n _).

Notation " [ n | H ]":= (exist _ n H).

(** ** pair *)
Notation "[ x1 , .. , xn ]":= (.. (tt,x1) .., xn).


(* ######################################################################### *)
(** * Ltac *)

(** ** bauto *)

(** 定义 bauto， 包含本文件所定义的一些引理和定义 *)
Ltac bauto:=
 repeat (quan_simpl; bool_simpl; opt_simpl; pair_simpl; fun_simpl);
 subst; autorewrite with core ; auto with core; try lia; try apply proof_irrelevance.