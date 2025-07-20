Require Import EqdepFacts.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Classical_Pred_Type.
Require Import Classical_Prop.
Require Export finfle.

Set Implicit Arguments.


(* ######################################################################### *)
(** * Vector *)

Section Vec.

(** ** vector *)

(** *** Definition *)

(** vector 的定义 *)
Fixpoint vector (A: Set) (n: nat): Set:= 
 match n with
 | O => unit
 | S n => ((vector A n) * A)%type
 end.

(** *** Lemma *)

(** 如果 n = m, 那么类型 vector n 与 vector m 相同 *)
Lemma vec'_eq: forall {A: Set} {n m}, n = m -> vector A n = vector A m.
Proof. fauto. Qed.

(** 证明 vector 0 为 unit *)
Lemma vec'_0: forall (A: Set), vector A 0 = unit.
Proof. fauto. Qed.

(** 证明 vector A 0 只有一个元素 *)
Lemma vec'_0_elem: forall (A: Set) (v: vector A 0), v = (tt: vector A 0).
Proof. intros. destruct v. auto. Qed.

(** 证明 vector A 0 唯一性 *)
Lemma vec'_0_unique: forall {A: Set} (v v': vector A 0), v = v'.
Proof. intros. rewrite !vec'_0_elem. apply vec'_0_elem. Qed.

(** 证明 vector 1 为 (unit * A) *)
Lemma vec'_1: forall {A: Set}, vector A 1 = (unit * A)%type.
Proof. fauto. Qed.

(** *** Example *)

(** 构造 vec3 实例, (1,2,3) *)
Example vec3_example: vector nat 3:= [1, 2, 3].

(** ** v_nth *)

(** *** Definition *)

(** v_nth 的定义 *)
Fixpoint v_nth {A: Set} {n: nat} d: (vector A n) -> nat -> A:= 
 match n with
 | O => fun _ _ => d
 | S n' => fun v i => 
 if i =? n' then snd v else v_nth d (fst v) i
 end.

(** *** Lemma *)

(** 可以证明当 i < n 时候, v_nth 的取值与默认值无关 *)
Lemma v_nth_eq_d: forall {A: Set} {n} d d' i (v: vector A n),
 i < n -> v_nth d v i = v_nth d' v i.
Proof with fauto.
 destruct n... induction n...
 - replace i with 0...
 - destruct v. simpl. destruct (i =? S n) eqn: E. auto. apply IHn...
Qed.

(** 证明对于 v_nth 来说, 当取值超出范围时, 返回 d *)
Lemma v_nth_beyond: forall (A: Set) n d i (v: vector A n),
 ~ (i < n) -> v_nth d v i = d.
Proof with fauto.
 induction n... destruct v as [v e]. simpl... apply IHn...
Qed.

(** 证明对于 v_nth 来说, (v, e): vector (S n) 头部为 v *)
Lemma v_nth_head: forall (A: Set) n d i (v: vector A n) e,
 i < n -> v_nth d ((v, e): vector A (S n)) i = v_nth d v i.
Proof. fauto. simpl. fauto. Qed.

(** 证明对于 v_nth 来说, (v, e): vector (S n) 尾部为 e *)
Lemma v_nth_tail: forall (A: Set) n d (v: vector A n) e,
 v_nth d ((v, e): vector A (S n)) n = e.
Proof. fauto. simpl. fauto. Qed.

(** 将 v_nth (v, e) 化简 *)
Lemma v_nth_Sn: forall (A: Set) n d i (v: vector A n) e,
 v_nth d ((v, e): vector A (S n)) i = if i =? n then e else v_nth d v i.
Proof. fauto; simpl; fauto. Qed.

(** 对于任意 v ： vector, 无论怎样取 x, 均返回默认值 *)
Lemma v_nth_0: forall (A: Set) d i (v: vector A 0), v_nth d v i = d.
Proof. fauto; simpl; fauto. Qed.

(** 对于 v1 v2: vector, 若 v1 = v2, 则对于 i: fin n, 通过 v_nth 获取的值相同; 反之亦然 *)
Lemma v_nth_eq_v: forall (A: Set) n d (v1 v2: vector A n),
 v1 = v2 <-> (forall i: fin n, v_nth d v1 i = v_nth d v2 i).
Proof with fauto.
 induction n... destruct v1 as [v1 e1]. destruct v2 as [v2 e2]. f_equal.
 - destruct IHn with (v1:= v1) (v2:= v2) (d:= d). apply H1; intros.
 specialize H with FS[i]. simpl in H. clear H0; clear H1.
 destruct (i =? n) eqn: E... assert (i < n) by fauto...
 - specialize H with '[n]. erewrite !v_nth_tail in H...
Qed.

(** *** Example *)

(** 对 vec3 的实例取 1 得 2 *)
Goal v_nth 0 vec3_example 1 = 2.
Proof. auto. Qed.

(** 对 vec3 的实例取 3 得 0 *)
Goal v_nth 0 vec3_example 3 = 0.
Proof. auto. Qed.

(** ** v_idx *)

(** *** Definition *)

(** v_idx 的定义, 通过 fin 类型的数获取其中元素 *)
Definition v_idx {A: Set} {n: nat} (d: A): (vector A n) -> fin n -> A:= 
 fun v i => v_nth d v i.

(** *** Lemma *)

(** 可以证明 v_idx 的取值与默认值无关 *) 
Lemma v_idx_eq_d: forall {A: Set} {n} d d' i (v: vector A n),
 v_idx d v i = v_idx d' v i.
Proof with fauto. unfold v_idx... apply v_nth_eq_d... Qed.

(** 证明对于 v_idx 来说, (v, e): vector (S n) v_idx 头部为 v *)
Lemma v_idx_head: forall (A: Set) n d i (v: vector A n) e,
 v_idx d ((v, e): vector A (S n)) FS[i] = v_idx d v i.
Proof with fauto. unfold v_idx... apply v_nth_head... Qed.

(** 证明对于 v_idx 来说, (v, e): vector (S n) v_idx 头部为 v *)
Lemma v_idx_head_H: forall (A: Set) n d (i: fin (S n)) (v: vector A n) e (H: i < n),
 v_idx d ((v, e): vector A (S n)) i = v_idx d v FP[H].
Proof with fauto. unfold v_idx... apply v_nth_head... Qed.

(** 证明对于 v_idx 来说, (v, e): vector (S n) v_idx 尾部为 e *)
Lemma v_idx_tail: forall (A: Set) n d (v: vector A n) e,
 v_idx d ((v, e): vector A (S n)) '[n] = e.
Proof with fauto. unfold v_idx... apply v_nth_tail... Qed.

(** 对于 v1 v2: vector, 若 v1 = v2, 则对于 i: fin n, 通过 v_idx 获取的值相同; 反之亦然 *)
Lemma v_idx_eq_v: forall {A: Set} {n} d (v1 v2: vector A n),
 v1 = v2 <-> (forall i: fin n, v_idx d v1 i = v_idx d v2 i).
Proof. unfold v_idx. apply v_nth_eq_v. Qed.

(** *** Example *)

(** vec 3 的实例 (1,2,3) 的 v_idx '[2] 为 3 *)
Goal v_idx 0 vec3_example '[2] = 3.
Proof. auto. Qed.

(** ** v_eqb *)

(** *** Definition *)

(** 定义 v_eqb, 判断两个类型相同 vector 是否相等 *)
Fixpoint v_eqb {A: Set} {n} (f: A -> A -> bool) {struct n}: vector A n -> vector A n -> bool:= 
 match n with 
 | O => fun _ _ => true (* 长度为 0 的向量总是相等 *) 
 | S n' => fun v1 v2 => 
 let (v1_head, v1_tail):= (v1: vector A (S n')) in 
 let (v2_head, v2_tail):= (v2: vector A (S n')) in 
 v_eqb f v1_head v2_head && f v1_tail v2_tail
 end.

(** *** Lemma *)

(** v_eqb 具有自反性 *)
Lemma v_eqb_refl: forall {A: Set} {n} (v: vector A n) (f: A -> A -> bool), 
 (forall a, f a a = true) -> v_eqb f v v = true.
Proof with fauto.
 induction n... destruct v; simpl...
Qed.

(** v_eqb 具有对称性 *)
Lemma v_eqb_sym: forall {A: Set} {n} (v v': vector A n) (f: A -> A -> bool),
 (forall a b, f a b = f b a) -> v_eqb f v v' = v_eqb f v' v.
Proof with fauto.
 induction n... destruct v, v'; simpl. rewrite IHn, H...
Qed.

(** v_eqb 具有传递性 *)
Lemma v_eqb_trans: forall {A: Set} {n} (v1 v2 v3: vector A n) (f: A -> A -> bool),
 (forall a b c, f a b = true -> f b c = true -> f a c = true) ->
 v_eqb f v1 v2 = true -> v_eqb f v2 v3 = true -> v_eqb f v1 v3 = true.
Proof with fauto.
 induction n... destruct v1, v2, v3; simpl in *...
 - apply IHn with v0; auto.
 - apply H with a0; auto.
Qed.

(** v_eqb 与 eq 映射 *)
Lemma v_eqb_true_iff: forall {A: Set} {n} (v v': vector A n) (f: A -> A -> bool),
 (forall a b: A, f a b = true <-> a = b ) ->
 v_eqb f v v' = true <-> v = v'.
Proof with fauto.
 induction n... destruct v as [v e]. destruct v' as [v' e']; simpl in H0...
 - specialize IHn with (v:= v) (v':= v') (f:= f). apply IHn in H. apply H...
 - apply H...
 - apply v_eqb_refl... apply H...
Qed.

(** v_eqb 的可判定性 *) 
Lemma v_eqb_dec: forall {A: Set} {n} (v v': vector A n) (f: A -> A -> bool),
 {v_eqb f v v' = true} + {v_eqb f v v' = false}.
Proof with fauto.
 induction n... destruct v, v'. simpl. destruct (IHn v v0 f); destruct (f a a0).
 left... right... right... right...
Qed.

(** ** v_make *)

(** *** Definition *)

(** 通过有限函数 fin m -> A 构造 vector *)
Fixpoint v_make {A: Set} {n}: (fin n -> A) -> vector A n:= 
 match n with
 | 0 => fun _ => tt: vector A 0
 | S n' => fun u => (v_make (fun i => u FS[i]), u '[n'])
 end.

(** *** Lemma *)

(** 如果构造函数 f f' 相等, 那么通过 v_make构造出来的也应相等 *)
Lemma v_make_eq: forall {A: Set} {n} (f f': fin n -> A),
 f = f' -> v_make f = v_make f'.
Proof. induction n; fauto. Qed.

(** v_make (u: fin (S m) -> A) 的化简 *)
Lemma v_make_Sn: forall (A: Set) n (u: fin (S n) -> A),
 v_make u = (v_make (fun i => u FS[i]), u '[n]).
Proof. auto. Qed.

(** 如果构造函数恒为 d, 那么构造函数面对 Sn 时的化简 *)
Lemma v_make_Sn_d: forall (A: Set) n (d: A),
 v_make(fun i: fin (S n) => d) = (v_make (fun i => d), d).
Proof. fauto. Qed.

(** 化简 v_make 0 *)
Lemma v_make_0: forall (A: Set) (f: fin 0 -> A),
 v_make f = (tt: vector A 0).
Proof. fauto. Qed.

(** 通过对 v 进行 v_nth 的函数来进行构造 v_make, 构造结果依旧为 v *)
Lemma v_make_nth: forall (A: Set) n d (v: vector A n),
 v_make (v_nth d v) = v.
Proof with fauto.
 induction n... destruct v as [v e]... rewrite v_make_Sn...
 - replace (fun i: fin n => v_nth d ((v, e): vector A (S n)) FS[ i]) with
 (fun x: fin n => v_nth d v x)... rewrite v_nth_head...
 - rewrite v_nth_tail...
Qed.

(** 通过索引访问向量 v_make f 的第 i 个元素, 等价于直接通过函数 f 计算索引 i 对应的值 *)
Lemma v_nth_make: forall (A: Set) n d i (f: fin n -> A) (H: i < n),
 v_nth d (v_make f) i = f F[H].
Proof with fauto.
 induction n... simpl. destruct (i =? n) eqn: E...
 - f_equal...
 - assert (i < n) by fauto. rewrite IHn with (H:= H0). f_equal...
Qed.

(** 通过对 v 进行 v_idx 的函数来进行构造 v_make, 构造结果依旧为 v *)
Lemma v_make_idx: forall (A: Set) n d (v: vector A n),
 v_make (v_idx d v) = v.
Proof with fauto.
 induction n... destruct v as [v e]... rewrite v_make_Sn...
 - replace (fun i: fin n => v_idx d ((v, e): vector A (S n)) FS[ i]) with
 (fun x: fin n => v_idx d v x)... rewrite v_idx_head...
 - replace (fin_lstH (Nat.lt_0_succ n)) with '[n] by fauto.
 rewrite v_idx_tail...
Qed.

(** 通过索引访问向量 v_make f 的第 i 个元素, 等价于直接通过函数 f 计算索引 i 对应的 *)
Lemma v_idx_make: forall (A: Set) n d i (f: fin n -> A),
 v_idx d (v_make f) i = f i.
Proof with fauto.
 induction n... simpl. destruct (i =? n)%nat eqn: E...
 - (* i = n *)
 replace i with '[n] by fauto. rewrite v_idx_tail...
 - (* i <> n *)
 assert (i < n). pose proof (fin_proof i)... rewrite v_idx_head_H with (H:= H).
 rewrite IHn. f_equal...
Qed.

(** 通过对 v: vector (vector A n) m 进行 v_idx 的函数来进行构造 v_make, 构造结果依旧为 v *)
Lemma v_make_idx2: forall (A: Set) m n d vd (v: vector (vector A n) m),
 v_make (fun i: fin m => v_make (fun j: fin n => v_idx d (v_idx vd v i) j)) = v.
Proof.
 intros. erewrite <- v_make_idx. apply v_make_eq.
 unfold v_idx at 3. fun_ext. rewrite v_make_idx. reflexivity.
Qed.

(** *** Example *)

(** 构造一个 vec_make 3 的实例 *)
Example vec_make3_example:= v_make (fun i: fin 3 => i + 1).

(** 解析这个实例 *)
Goal vec_make3_example = [1,2,3].
Proof. auto. Qed.


End Vec.

(** ** Arguments *)

Arguments v_make {A} {n}.

Arguments v_nth {A} {n}.

Arguments v_idx {A} {n}.

(** ** Auto *)

#[export] Hint Rewrite vec'_0 vec'_0_elem v_nth_beyond v_nth_tail v_nth_Sn v_nth_0 v_idx_head 
v_idx_head_H v_idx_tail v_make_Sn v_make_Sn_d v_make_0 v_make_nth v_nth_make 
v_make_idx v_idx_make v_make_idx2 : vcore.

#[export] Hint Resolve vec'_0_unique v_eqb_refl v_eqb_sym v_eqb_trans vec'_eq vec'_0 v_nth_eq_d
v_nth_eq_v v_idx_eq_d v_eqb_true_iff v_make_eq : vcore.


(* ######################################################################### *)
(** * Vector Function *)

Section Vec_Fun.

(** ** v_length *)

(** *** Definition *)

(** 定义 v_length, 返回 v 的长度 *)
Definition v_length {A: Set} {n} (v: vector A n):= n.

(** *** Lemma *)

(** 对任意 v 而言, 如果其为 tt, 那么其长度就为 0; 反之亦然 *)
Lemma v_length_0: forall {A: Set} v,
 v = (tt: vector A 0) <-> v_length v = 0.
Proof. fauto. Qed.

(** 对任意v而言, 如果其不为 tt, 那么其长度就不为 0 *)
Lemma v_length_neq0: forall {A: Set} v,
 v <> (tt: vector A 0) <-> v_length v <> 0.
Proof. fauto. Qed.

(** *** Example *)

(** vec3_example 的 v_length 为 3 *)
Goal v_length ((tt, 1, 2, 3): vector nat 3) = 3.
Proof. auto. Qed.

(** ** v_default *)

(** *** Definition *)

(** 定义 v_default, 可以构造一个每个元素均相同的 vector *)
Definition v_default {A: Set} n (d: A): vector A n:= 
 v_make (fun i: fin n => d).

(** *** Lemma *)

(** 化简 v_default (S n) *)
Lemma v_default_Sn: forall (A: Set) n (d: A),
 v_default (S n) d = (v_default n d, d).
Proof. fauto. Qed.

(** 化简 v_default 0 *)
Lemma v_default_0: forall (A: Set) (d: A),
 v_default 0 d = (tt: vector A 0).
Proof. fauto. Qed.

(** 对 v_default n x 生成的 vector 通过 v_nth 取其内部元素, 其元素为 x *)
Lemma v_nth_default: forall (A: Set) n (d: A) i,
 i < n -> v_nth d (v_default n d) i = d.
Proof with fauto.
 induction n... rewrite v_default_Sn. rewrite v_nth_Sn... apply IHn...
Qed.

(** 对 v_default n x 生成的 vector 通过 v_idx 取其内部元素, 其元素为 x *)
Lemma v_idx_default: forall (A: Set) n (d: A) i,
 v_idx d (v_default n d) i = d.
Proof with fauto. unfold v_idx... apply v_nth_default... Qed.

(** *** Example *)

(** 分解 v_default 3 1 为 (1, 1, 1) *)
Goal v_default 3 1 = [1, 1, 1].
Proof. auto. Qed.

(** ** v_map *)

(** *** Definition *)

(** 定义 v_map, 对 vector 中的每个元素进行操作 *)
Definition v_map {A B: Set} {n} d (f: A -> B) (v: vector A n): vector B n:= 
 v_make (fun i => f (v_idx d v i)).

(** *** Lemma *)

(** 化简 v_map (S n) *)
Lemma v_map_Sn: forall (A B: Set) n d (f: A -> B) (v: vector A n) e,
 v_map d f ((v, e): vector A (S n)) = (v_map d f v, f e).
Proof with fauto.
 unfold v_map... rewrite v_make_Sn...
 - apply v_make_eq... f_equal. apply v_idx_head.
 - f_equal. apply v_idx_tail.
Qed.

(** 化简 v_map 0 *)
Lemma v_map_0: forall (A B: Set) d (f: A -> B) (v: vector A 0),
 v_map d f v = (tt: vector A 0).
Proof. fauto. Qed.

(** 对 v_default n x 生成的 vector 通过 v_nth 取其内部元素, 其元素为 x *)
Lemma v_nth_map: forall (A B: Set) n d i (f: A -> B) (v: vector A n),
 i < n -> v_nth (f d) (v_map d f v) i = f (v_nth d v i).
Proof with fauto.
 induction n... destruct v as [v e]. 
 rewrite v_map_Sn. rewrite v_nth_Sn...
 - f_equal. rewrite v_nth_tail...
 - rewrite IHn... f_equal. rewrite v_nth_head...
Qed.

(** 对 v_default n x 生成的 vector 通过 v_idx 取其内部元素, 其元素为 x *)
Lemma v_idx_map: forall (A B: Set) n d i (f: A -> B) (v: vector A n),
 v_idx (f d) (v_map d f v) i = f (v_idx d v i).
Proof.
 intros. unfold v_idx. apply v_nth_map. fauto.
Qed.

(** 对某个数组先 v_map f 再 v_map g 等于直接 map f g *)
Lemma v_map_map: forall n (A B C: Set) d d' (f: A->B) (g: B->C) (v: vector A n),
 v_map d' g (v_map d f v) = v_map d (fun a => g (f a)) v.
Proof with fauto.
 unfold v_map... apply v_make_eq. fun_ext. f_equal. rewrite v_idx_make...
Qed.

(** *** Example *)

(** 对 (1, 1, 1) 中每个元素使用 map 进行 + 1 得到 (2, 2, 2) *)
Goal v_map 0 S ([1, 1, 1]: vector nat 3) = [2, 2, 2].
Proof. auto. Qed.

(** ** v_reduce *)

(** *** Definition *)

(** 定义 v_reduce, 从左到右展开到一个元素 *)
Fixpoint v_reduce {A B: Set} {n} (f: A -> B -> B) (init_val: B): (vector A n) -> B:= 
 match n with
 | O => fun _ => init_val
 | S n' => fun v => f (snd v) (v_reduce f init_val (fst v))
 end.

(** 化简 v_reduce (S n) *)
Lemma v_reduce_Sn: forall (A B: Set) n (f: A -> B -> B) val (v: vector A n) e,
 v_reduce f val ((v, e): vector A (S n)) = f e (v_reduce f val v).
Proof. fauto. Qed.

(** 化简 v_reduce 0 *)
Lemma v_reduce_0: forall (A B: Set) (f: A -> B -> B) val (v: vector A 0),
 v_reduce f val v = val.
Proof. fauto. Qed.

(** 将 v_map 中的函数与 v_reduce的函数结合 *)
Lemma v_reduce_map: forall (A B: Set) n d (f: A -> B -> B) (g: A -> A) val (v: vector A n),
 v_reduce f val (v_map d g v) = v_reduce (fun x y => f (g x) y) val v.
Proof.
 induction n; fauto. destruct v as [v e]. rewrite v_map_Sn.
 rewrite !v_reduce_Sn. f_equal. apply IHn.
Qed.

(** *** Example *)

(** 对 (0, 1, 2, 3) 中每个数使用 add 展开, 初始值为 0 *)
Goal v_reduce Nat.add 0 ([0, 1, 2, 3]: vector nat 4) = 6. 
Proof. auto. (* = 3+(2+(1+(0+0))) = 6 *) Qed.

(** ** v_max *)

(** *** Definition *)

(** 定义 v_max, 目标是寻找极值 *)
Fixpoint v_max_aux {A: Set} {n: nat} (f: A -> A -> bool): (vector A (S n)) -> A:= 
 match n with
 | 0 => fun v => snd v
 | S n' => fun v =>
 if f (snd v) (v_max_aux f (fst v))
 then snd v
 else (v_max_aux f (fst v))
 end.

Definition v_max {A:Set} {n} (f : A -> A -> bool) (v : vector A n) (E: 0 < n) : A.
Proof.
  destruct n. exfalso. apply (_0lt0_False E). exact (v_max_aux f v). Defined.

(** *** Lemma *)

(** 展开 v_max *)
Lemma v_max_unfold : forall {A:Set} n (f : A -> A -> bool) (v : vector A (S n)) (E: 0 < S n),
  v_max f v E = v_max_aux f v.
Proof. unfold v_max; fauto. Qed.

(** 化简 v_max (S n) *)
Lemma v_max_Sn': forall (A: Set) n (f: A -> A -> bool) (v: vector A (S n)) e,
 v_max_aux f ((v, e): vector A (S (S n))) = 
 if f e (v_max_aux f v) then e else v_max_aux f v.
Proof. fauto. Qed.

Lemma v_max_Sn: forall (A: Set) n (f: A -> A -> bool) (v: vector A n) e {E: 0 < n},
 v_max f ((v, e): vector A (S n)) (Nat.lt_0_succ n) = 
 if f e (v_max f v E) then e else v_max f v E.
Proof.
  intros. destruct n. inv E. rewrite v_max_unfold. apply v_max_Sn'.
Qed.

(** 化简 v_max 0 *)
Lemma v_max_0': forall (A: Set) (f: A -> A -> bool) (v: vector A 1),
 v_max_aux f v = snd v.
Proof. fauto. Qed.

(** 对于任意 v: vector S n来说, 如果判定函数具有反对称性和传递性
 v_max返回的值大于或者就为任意由 i < S n, v_nth i 得来的值 *)
Lemma v_max_nth': forall {A: Set} {n} d i (f: A -> A -> bool) (v: vector A (S n)),
 (forall a b, f a b = true <-> f b a = false) ->
 (forall a b c, f a b = true -> f b c = true -> f a c = true) ->
 i < S n -> f (v_max_aux f v) (v_nth d v i) = true \/ (v_max_aux f v) = (v_nth d v i).
Proof with fauto.
 induction n; intros. 
 - (* n = 0 *)
 right; simpl. replace (i =? 0) with true...
 - (* n <> 0 *) 
 destruct v as [v e]. destruct (i =? S n) eqn : E; bool_simpl.
 + (* n = S n *)
 subst. rewrite !v_nth_tail. rewrite !v_max_Sn'.
 destruct (f e (v_max_aux f v)) eqn : E. right; auto.
 left; apply H; auto.
 + (* n < S n *)
 erewrite !v_nth_head; try lia. rewrite !v_max_Sn'.
 destruct IHn with (f := f) (v := v) (d := d) (i := i); auto; try lia;
 destruct (f e (v_max_aux f v)) eqn : E0.
 * (* f e (v_nth d v i) = true *)
 left. apply H0 with (v_max_aux f v); auto.
 * (* f (v_max_aux f v) (v_nth d v i) = true *)
 left. auto.
 * (* f e (v_nth d v i) = true *)
 left. rewrite <- H2; auto.
 * (* v_max_aux f v = v_nth d v i *)
 right. auto.
Qed.

Lemma v_max_nth: forall {A: Set} {n} d i (f: A -> A -> bool) (v: vector A n) {E:0 < n},
 (forall a b, f a b = true <-> f b a = false) ->
 (forall a b c, f a b = true -> f b c = true -> f a c = true) ->
 i < n -> f (v_max f v E) (v_nth d v i) = true \/ (v_max f v E) = (v_nth d v i).
Proof.
  intros. destruct n. inv H1. rewrite v_max_unfold. apply v_max_nth'; auto.
Qed.

(** 对于任意 v: vector S n来说, 如果判定函数具有反对称性和传递性
 v_max返回的值大于或者就为任意由 v_idx i 得来的值 *)
Lemma v_max_idx': forall {A: Set} {n} d i (f: A -> A -> bool) (v: vector A (S n)),
 (forall a b, f a b = true <-> f b a = false) ->
 (forall a b c, f a b = true -> f b c = true -> f a c = true) ->
 f (v_max_aux f v) (v_idx d v i) = true \/ (v_max_aux f v) = (v_idx d v i).
Proof.
 intros. destruct @v_max_nth' with (A := A) (f := f) (v := v) (d := d) (i := i); auto. apply fin_proof.
Qed.

Lemma v_max_idx: forall {A: Set} {n} d i (f: A -> A -> bool) (v: vector A n) {E:0 < n},
 (forall a b, f a b = true <-> f b a = false) ->
 (forall a b c, f a b = true -> f b c = true -> f a c = true) ->
 f (v_max f v E) (v_idx d v i) = true \/ (v_max f v E) = (v_idx d v i).
Proof.
 intros. destruct @v_max_nth with (A := A) (f := f) (v := v) (d := d) (i := i) (E:=E); auto. apply fin_proof.
Qed.

(** *** Example *)

(** 0 < 5 *)
Example _0lt5 : 0 < 5. Proof. lia. Qed.

(** (3, 8, 12, 5, 7) 的最大值为 12 *)
Goal v_max (fun x y => Nat.ltb y x) ([3, 8, 12, 5, 7]: vector nat 5) _0lt5 = 12.
Proof. auto. Qed.

(** ** v_zip *)

(** *** Definition *)

(** 定义 v_zip, 将两个相同长度不同类型的 vector 压缩成同一个 vector *)
Definition v_zip {A B: Set} {n} d d' (v: vector A n) (v': vector B n): vector (A * B) n:= 
 v_make (fun i => (v_idx d v i,v_idx d' v' i)).

(** *** Lemma *)

(** 对于 vzip v' v来说, 通过 v_nth 取值等于 先通过 v_nth v 和 v_nth v' 取值再压缩 *)
Lemma v_nth_zip: forall (A B: Set) n d d' i (v: vector A n) (v': vector B n),
 v_nth (d, d') (v_zip d d' v v') i = (v_nth d v i, v_nth d' v' i).
Proof with fauto.
 induction n... destruct v as [v e]. destruct v' as [v' e'].
 unfold v_zip at 1. rewrite v_make_Sn. rewrite v_nth_Sn.
 destruct (i =? n) eqn : E... simpl...
 destruct (i <? n) eqn : E1 ...
 - (* i < n *)
 rewrite <- IHn. f_equal.
 unfold v_zip at 1. apply v_make_eq. fun_ext...
 rewrite v_idx_head... rewrite v_idx_head...
 - (* i > n *)
 erewrite !v_nth_beyond...
Qed.

(** 对于 vzip v' v来说, 通过 v_nth 取值等于 先通过 v_idx v 和 v_idx v' 取值再压缩 *)
Lemma v_idx_zip: forall(A B: Set) n d d' i (v: vector A n) (v': vector B n),
 v_idx (d, d') (v_zip d d' v v') i = (v_idx d v i, v_idx d' v' i).
Proof. intros. unfold v_idx. apply v_nth_zip. Qed.

(** 化简 v_zip (S n) *)
Lemma v_zip_Sn: forall (A B: Set) n d d' (v: vector A n) (v': vector B n) e e',
 v_zip d d' ((v, e): vector A (S n)) ((v', e'): vector B (S n)) = 
 (v_zip d d' v v', (e, e')).
Proof with fauto.
 unfold v_zip... rewrite v_make_Sn; simpl. f_equal.
 - (* (v_idx d (v, e) FS[ i], v_idx d' (v', e') FS[i]) = 
 (v_idx d v i, v_idx d' v' i) *)
 apply v_make_eq. fun_ext. f_equal; apply v_idx_head.
 - (* (v_idx d (v, e) '[ n], v_idx d' (v', e') '[ n]) = (e, e') *)
 f_equal; apply v_idx_tail.
Qed.

(** 化简 v_zip 0 *)
Lemma v_zip_0: forall (A B: Set) d d' (v: vector A 0) (v': vector B 0),
 v_zip d d' v v' = (tt: vector (A * B) 0).
Proof. fauto. Qed.

(** cur f 作用于配对向量 v_zip v v' 的通过 v_nth 获取的 第 i 个元素, 等价于 f 分别作用于 v 和 v' 的第 i 个元素 *)
Lemma f_v_nth_zip: 
 forall (A B C: Set) n d d' i (f: A -> B -> C) (v: vector A n) (v': vector B n),
 (cur f) (v_nth (d, d') (v_zip d d' v v') i) = f (v_nth d v i) (v_nth d' v' i).
Proof. intros. rewrite v_nth_zip. fauto. Qed.

(** cur f 作用于配对向量 v_zip v v' 的通过 v_idx 获取的第 i 个元素, 等价于 f 分别作用于 v 和 v' 的第 i 个元素 *)
Lemma f_v_idx_zip: 
 forall (A B C: Set) n d d' i (f: A -> B -> C) (v: vector A n) (v': vector B n),
 (cur f) (v_idx (d, d') (v_zip d d' v v') i) = f (v_nth d v i) (v_idx d' v' i).
Proof. intros. rewrite v_idx_zip. auto. Qed.

(** 对一个 v_zip v v' 后的 vector 进行遍历, 等于先通过v_nth对 v 和 v'进行遍历, 然后进行组合 *)
Lemma v_map_zip_nth: 
 forall (A B C: Set) n d d' (f: A -> B -> C) (v: vector A n) (v': vector B n),
 v_map (d, d') (cur f) (v_zip d d' v v') = v_make (fun i => f (v_nth d v i) (v_nth d' v' i)).
Proof. fauto. unfold v_map at 1. apply v_make_eq. fun_ext. apply f_v_nth_zip. Qed.

(** 对一个 v_zip v v' 后的 vector 进行遍历, 等于先通过v_idx对 v 和 v'进行遍历, 然后进行组合 *)
Lemma v_map_zip_idx: 
 forall (A B C: Set) n d d' (f: A -> B -> C) (v: vector A n) (v': vector B n),
 v_map (d, d') (cur f) (v_zip d d' v v') = v_make (fun i => f (v_idx d v i) (v_idx d' v' i)).
Proof. fauto. unfold v_map at 1. apply v_make_eq. fun_ext. apply f_v_idx_zip. Qed.

(** 对 v v': vector 先 map 在 v_zip 等于先 v_zip 再 map *)
Lemma v_zip_map: forall (A B A' B': Set) n d d' vd vd' (v: vector A n) (v': vector A' n)
 (f: A -> B) (g: A' -> B'),
 v_zip vd vd' (v_map d f v) (v_map d' g v') = 
 v_map (d, d') (fun xy => (f (fst xy), g (snd xy))) (v_zip d d' v v').
Proof with fauto.
 induction n... destruct v as [v e]. destruct v' as [v' e'].
 rewrite !v_map_Sn. rewrite !v_zip_Sn. rewrite !v_map_Sn. simpl. f_equal; auto.
Qed.

(** 对于由 v_zip 构成的 vector 经 v_nth 选取变换后再由 v_make 构成的数组等于
 先由 v_nth 选取后再由 v_zip 变换后由 v_make 构成的数组 *)
Lemma v_make_nth_zip: forall n (A B C: Set) d d' (f: A -> B -> C) (g: fin n -> fin n)
 (v: vector A n) (v': vector B n),
 v_make (fun i => (cur f) (v_nth (d, d') (v_zip d d' v v') (g i))) = 
 v_make (fun i => f (v_nth d v (g i)) (v_nth d' v' (g i))).
Proof. intros. apply v_make_eq. fun_ext. apply f_v_nth_zip. Qed.

(** 对于由 v_zip 构成的 vector 经 v_idx 选取变换后再由 v_make 构成的数组等于
 先由 v_idx 选取后再由 v_zip 变换后由 v_make 构成的数组 *)
Lemma v_make_idx_zip: forall n (A B C: Set) d d' (f: A -> B -> C) (g: fin n -> fin n)
 (v: vector A n) (v': vector B n),
 v_make (fun i => (cur f) (v_idx (d, d') (v_zip d d' v v') (g i))) = 
 v_make (fun i => f (v_idx d v (g i)) (v_nth d' v' (g i))).
Proof. intros. apply v_make_eq. fun_ext. apply f_v_idx_zip. Qed.

(** 对于由 v_zip 构成的二维 vector 经 v_nth 选取变换后再由 v_make 构成的数组等于
 先由 v_nth 选取后再由 v_zip 变换后由 v_make 构成的数组 *)
Lemma v_make_nth_zip2: 
 forall m n (A B C: Set) d d' (f: A -> B -> C) (g: fin m -> fin n -> fin (m * n))
 (v: vector A (m * n)) (v': vector B (m * n)),
 v_make (fun i => v_make (fun j => (cur f) (v_nth (d, d') (v_zip d d' v v') (g i j)))) = 
 v_make (fun i => v_make (fun j => f (v_nth d v (g i j)) (v_nth d' v' (g i j)))).
Proof. intros. apply v_make_eq; fun_ext. apply v_make_eq; fun_ext. apply f_v_nth_zip. Qed.

(** 对于由 v_zip 构成的二维 vector 经 v_idx 选取变换后再由 v_make 构成的数组等于
 先由 v_nth 选取后再由 v_zip 变换后由 v_make 构成的数组 *)
Lemma v_make_idx_zip2: 
 forall m n (A B C: Set) d d' (f: A -> B -> C) (g: fin m -> fin n -> fin (m * n))
 (v: vector A (m * n)) (v': vector B (m * n)),
 v_make (fun i => v_make (fun j => (cur f) (v_idx (d, d') (v_zip d d' v v') (g i j)))) = 
 v_make (fun i => v_make (fun j => f (v_idx d v (g i j)) (v_nth d' v' (g i j)))).
Proof. intros. apply v_make_eq; fun_ext. apply v_make_eq; fun_ext. apply f_v_nth_zip. Qed.

(** *** Example *)

(** 由 (1, 2, 3) 和 (true, true, true) 压缩成为 ((1,true), (2,true), (3,true)) *)
Example v_zip_example:= v_zip 0 false ([1,2,3]: vector nat 3) ([true,true,true]: vector bool 3).

Goal v_zip_example = [(1, true), (2, true), (3, true)].
Proof. auto. Qed.

(** ** v_unzip *)

(** *** Definition *)

(** 定义 v_unzipl, 用于获取压缩左边的元素 *)
Definition v_unzipl {A B: Set} {n} (d: A * B) (v: vector (A * B) n): vector A n:= 
 v_make (fun i => fst (v_idx d v i)).

(** 定义 v_unzipr, 用于获取压缩左边的元素 *)
Definition v_unzipr {A B: Set} {n} (d: A * B) (v: vector (A * B) n): vector B n:= 
 v_make (fun i => snd (v_idx d v i)).

(** *** Lemma *)

(** 化简 v_unzipl (S n) *)
Lemma v_unzipl_Sn: forall (A B: Set) n d (v: vector (A * B) n) e,
 v_unzipl d ((v, e): (vector (A * B) (S n))) = (v_unzipl d v, fst e).
Proof with fauto.
 induction n; intros.
 - (* n = 0 *)
 unfold v_unzipl. rewrite !v_make_Sn; rewrite !v_make_0. rewrite v_idx_tail; auto.
 - (* n <> 0 *)
 destruct v as [v a]. unfold v_unzipl at 1. rewrite v_make_Sn. f_equal.
 + (* v_make (fun i : fin (S n) => fst (v_idx d (v, a, e) FS[ i])) = 
 v_unzipl d (v, a) *)
 rewrite IHn. rewrite v_make_Sn. f_equal.
 * (* v_make (fun i : fin n => fst (v_idx d (v, a, e) FS[ FS[ i]])) = 
 v_unzipl d v *)
 apply v_make_eq. fun_ext. f_equal. rewrite v_idx_head. apply v_idx_head.
 * (* fst (v_idx d (v, a, e) FS[ '[ n]]) = fst a *)
 f_equal. rewrite v_idx_head. apply v_idx_tail.
 + (* fst (v_idx d (v, a, e) '[ S n]) = fst e *)
 f_equal. apply v_idx_tail.
Qed.

(** 化简 v_unzipl 0 *)
Lemma v_unzipl_0: forall (A B: Set) d (v: vector (A * B) 0),
 v_unzipl d v = (tt: vector A 0).
Proof. fauto. Qed.

(** 化简 v_unzipr (S n) *)
Lemma v_unzipr_Sn: forall (A B: Set) n d (v: vector (A * B) n) e,
 v_unzipr d ((v, e): (vector (A * B) (S n))) = (v_unzipr d v, snd e).
Proof.
 induction n; intros.
 - (* n = 0 *)
 unfold v_unzipr. rewrite !v_make_Sn; rewrite !v_make_0. rewrite v_idx_tail; auto.
 - (* n <> 0 *)
 destruct v as [v a]. unfold v_unzipr at 1. rewrite v_make_Sn. f_equal.
 + (* v_make (fun i : fin (S n) => fst (v_idx d (v, a, e) FS[ i])) = 
 v_unzipl d (v, a) *)
 rewrite IHn. rewrite v_make_Sn. f_equal.
 * (* v_make (fun i : fin n => fst (v_idx d (v, a, e) FS[ FS[ i]])) = 
 v_unzipl d v *)
 apply v_make_eq. fun_ext. f_equal. rewrite v_idx_head. apply v_idx_head.
 * (* fst (v_idx d (v, a, e) FS[ '[ n]]) = fst a *)
 f_equal. rewrite v_idx_head. apply v_idx_tail.
 + (* fst (v_idx d (v, a, e) '[ S n]) = fst e *)
 f_equal. apply v_idx_tail.
Qed.

(** 化简 v_unzipr 0 *)
Lemma v_unzipr_0: forall (A B: Set) d (v: vector (A * B) 0),
 v_unzipr d v = (tt: vector A 0).
Proof. fauto. Qed.

(** 一个 vector 经过 unzip 再经过 v_zip 为该 vector 本身 *)
Lemma v_zip_unzip: forall (A B: Set) n d d' (v: vector (A * B) n),
 v_zip d d' (v_unzipl (d, d') v) (v_unzipr (d, d') v) = v.
Proof.
 induction n; intros.
 - (* n = 0 *)
 rewrite v_zip_0. apply unit_unique.
 - (* n <> 0 *)
 destruct v. rewrite v_unzipl_Sn. rewrite v_unzipr_Sn.
 rewrite v_zip_Sn. f_equal. apply IHn. destruct p; auto.
Qed.

(** v v: vector 经过 v_unzipl 为 v *)
Lemma v_unzipl_zip: forall (A B: Set) n d d' (v: vector A n) (v': vector B n),
 v_unzipl (d, d') (v_zip d d' v v') = v.
Proof.
 induction n; intros.
 - (* n = 0 *)
 rewrite v_zip_0. rewrite v_unzipl_0. apply unit_unique.
 - (* n <> 0 *)
 destruct v as [v e]. destruct v' as [v' e'].
 rewrite v_zip_Sn. rewrite v_unzipl_Sn. f_equal. apply IHn.
Qed.

(** v v: vector 经过 v_unzipe 为 v' *)
Lemma v_unzipr_zip: forall (A B: Set) n d d' (v: vector A n) (v': vector B n),
 v_unzipr (d, d') (v_zip d d' v v') = v'.
Proof.
 induction n; intros.
 - (* n = 0 *)
 rewrite v_zip_0. rewrite v_unzipr_0. apply unit_unique.
 - (* n <> 0 *)
 destruct v as [v e]. destruct v' as [v' e'].
 rewrite v_zip_Sn. rewrite v_unzipr_Sn. f_equal. apply IHn.
Qed.

(** 由 (f i, g i) 构造的 vector 经过 z_unzipl 等于由 f i 构造的 vector *)
Lemma v_unzipl_make: forall (A B: Set) n (d: A * B) f g,
 v_unzipl d (v_make (fun i => (f i, g i))) = v_make (fun i: fin n => f i).
Proof. 
 intros. unfold v_unzipl. apply v_make_eq. fun_ext.
 rewrite v_idx_make. auto.
Qed.

(** 由 (f i, g i) 构造的 vector 经过 z_unzipr 等于由 g i 构造的 vector *)
Lemma v_unzipr_make: forall (A B: Set) n (d: A * B) f g,
 v_unzipr d (v_make (fun i => (f i, g i))) = v_make (fun i: fin n => g i).
Proof.
 intros. unfold v_unzipr. apply v_make_eq. fun_ext.
 rewrite v_idx_make. auto.
Qed.

(** *** Example *)

(** 由 ((1,true), (2,true), (3,true)) 左解压为 (1, 2, 3) *)
Goal v_unzipl (0, false) v_zip_example = [1,2,3].
Proof. auto. Qed.

(** 由 ((1,true), (2,true), (3,true)) 左解压为 (true, true, true) *)
Goal v_unzipr (0, false) v_zip_example = [true, true, true].
Proof. auto. Qed.

End Vec_Fun.

(** ** Auto *)

#[export] Hint Rewrite v_default_Sn v_default_0 v_nth_default v_idx_default v_map_Sn v_map_0 v_nth_map 
v_idx_map v_map_map v_reduce_Sn v_reduce_0 v_max_Sn' v_max_Sn v_max_0' v_nth_zip v_idx_zip 
v_zip_Sn v_zip_0 f_v_nth_zip f_v_idx_zip v_map_zip_nth v_map_zip_idx v_zip_map v_make_nth_zip 
v_make_idx_zip v_make_nth_zip2 v_make_idx_zip2 v_unzipl_Sn v_unzipl_0 v_unzipr_Sn v_unzipr_0 v_zip_unzip
v_unzipl_zip v_unzipl_make v_unzipr_make: vcore.

#[export] Hint Resolve v_length_0 v_length_neq0 v_max_nth' v_max_nth v_max_idx' v_max_idx: vcore.

(* ######################################################################### *)
(** * Vector Dimension *)

Section Vec_Dimen.

(** ** v_split *)

(** *** Definition *)

(** 定义 v_split, 将二维数组拆成行向量的集合 *)
Definition v_split {A: Set} {m n} d (v: vector A (m * n)): vector (vector A n) m:= 
 v_make (fun i: fin m => v_make (fun j: fin n => v_idx d v (fin_2to1d i j))).

(** *** Lemma *)

(** 访问 v_split 后生成的二维向量的结果, 等于通过 v_nth 直接访问一维向量的结果 *)
Lemma v_nth_split: forall (A: Set) m n d (v: vector A (m * n)) i j,
 i < m -> j < n -> v_nth d (v_nth (v_default n d) (v_split d v) i) j = v_nth d v (i * n + j).
Proof.
 intros. unfold v_split; simpl. rewrite v_nth_make with (H := H).
 rewrite v_nth_make with (H := H0). unfold v_idx; f_equal.
Qed.

(** 访问 v_split 后生成的二维向量的结果, 等于通过 v_idx 直接访问一维向量的结果 *)
Lemma v_idx_split: forall (A: Set) m n d (v: vector A (m * n)) i j,
 v_idx d (v_idx (v_default n d) (v_split d v) i) j = v_idx d v (fin_2to1d i j).
Proof. intros. unfold v_split at 1. rewrite !v_idx_make. auto. Qed.

(** 当 m = 0时, v_split 为空 *)
Lemma v_split_m_0: forall (A: Set) n d (v: vector A (0 * n)),
 v_split d v = (tt: vector A 0).
Proof. intros. unfold v_split. rewrite !v_make_0. auto. Qed.

(** 当 n = 0 时, v_split 生成为长度为 m 内容全部为 tt 的向量 *)
Lemma v_split_n_0: forall (A: Set) m d (v: vector A (m * 0)),
 v_split d v = v_default m tt.
Proof. 
 intros. unfold v_split, v_default. apply v_make_eq.
 fun_ext. rewrite !v_make_0. auto.
Qed.

(** 对 v 进行分割、映射和重新组合的操作, 等价于直接通过索引计算每个元素的值 *)
Lemma v_map_split: forall (m n: nat) (A B: Set) d vd (f: A -> B) (v: vector A (m*n)),
 v_map vd (fun v0 => v_map d f v0) (v_split d v) = 
 v_make (fun i => v_make (fun j => f (v_idx d v (fin_2to1d i j)))).
Proof.
 intros. unfold v_map. f_equal. fun_ext. f_equal. fun_ext.
 f_equal. unfold v_split. rewrite !v_idx_make. auto.
Qed.

(** *** Example *)

(** 将 (1,2,3,4,5,6,7,8,9) 拆成 3 * 3 得 ((1,2,3), (4,5,6), (7,8,9)) *)
Goal v_split 0 ([1,2,3,4,5,6,7,8,9]: vector nat (3 * 3)) = [[1,2,3],[4,5,6],[7,8,9]].
Proof. auto. Qed.

(** ** v_join *)

(** *** Definition *)

(** 定义 v_joint, 将行向量转化为二维数组 *)
Definition v_join {A: Set} {m n: nat} d (v: vector (vector A n) m): vector A (m * n):= 
 v_make (fun x: fin (m * n) => let (i, j):= (fin_1to2d x) in
 v_idx d (v_idx (v_default n d) v i) j).

(** *** Lemma *)

(** 访问 v_join 后生成的一维向量的结果, 等于通过 v_nth 直接访问二维向量的结果 *)
Lemma v_nth_join: forall (A: Set) m n d i (v: vector (vector A n) m),
 i < m * n ->
 v_nth d (v_join d v) i = 
 v_nth d (v_nth (v_default n d) v (i / n)) (i mod n).
Proof. 
 intros. unfold v_join; simpl. rewrite v_nth_make with (H := H).
 destruct (fin_1to2d F[ H]) eqn : E. unfold v_idx. f_equal.
 f_equal. replace i with (fin2nat F[H]). rewrite <- fin_1to2d_row.
 rewrite E; auto. auto. replace i with (fin2nat F[H]).
 rewrite <- fin_1to2d_col. rewrite E; auto. auto.
Qed.

(** 访问 v_join 后生成的一维向量的结果, 等于通过 v_idx 直接访问二维向量的结果 *)
Lemma v_idx_join: forall (A: Set) m n d x (v: vector (vector A n) m),
 v_idx d (v_join d v) x = let (i, j):= (fin_1to2d x) in v_idx d (v_idx (v_default n d) v i) j.
Proof. intros. unfold v_join. rewrite !v_idx_make. auto. Qed.

(** 当 m = 0时, v_split 为空 *)
Lemma v_join_m_0: forall (A: Set) n d (v: vector (vector A n) 0),
 v_join d v = (tt: vector A 0).
Proof. intros. unfold v_join. rewrite !v_make_0. auto. Qed.

(** 当 n = 0 时, v_split 生成为长度为 m * 0 内容为 d *)
Lemma v_join_n_0: forall (A: Set) m (d: A) (v: vector (vector A 0) m),
 v_join d v = v_make (fun i: fin (m * 0) => d).
Proof.
 intros. unfold v_join, v_default. apply v_make_eq. fun_ext. destruct x. lia.
Qed.

(** 一个 vector 先经过 v_join 再经过 v_split 等于原 vector *)
Lemma v_split_join: forall (A: Set) m n d (v: vector (vector A n) m),
 v_split d (v_join d v) = v.
Proof. 
 intros. unfold v_split; unfold v_join.
 replace v with (v_make (fun i : fin m => v_make (fun j : fin n => v_idx d (v_idx (v_default n d) v i) j)))
 by apply v_make_idx2.
 apply v_make_eq. fun_ext. apply v_make_eq. fun_ext. rewrite v_idx_make.
 rewrite fin_1to2d_2to1d. f_equal. f_equal. apply v_make_idx2.
Qed.

(** 一个 vector 先经过 v_split 再经过 v_join 等于原 vector *)
Lemma v_join_split: forall (A: Set) m n d (v: vector A (n * m)),
 v_join d (v_split d v) = v.
Proof. 
 intros. unfold v_split; unfold v_join.
 replace v with (v_make (fun x : fin (n * m) => v_idx d v x)) by apply v_make_idx.
 apply v_make_eq. fun_ext. destruct (fin_1to2d x) eqn : E.
 rewrite !v_idx_make. f_equal. rewrite <- fin_2to1d_1to2d. f_equal; rewrite E; auto.
Qed.

(** 对 v 进行组合、映射和重新分割的操作, 等价于直接通过索引计算每个元素的值 *)
Lemma v_map_join: forall (A B: Set) m n d (f: A -> B) (v: vector (vector A n) m),
 v_map d f (v_join d v) = 
 v_make (fun (x: fin (m * n)) => 
 let (i, j):= (fin_1to2d x) in 
 f (v_idx d (v_idx (v_default n d) v i) j)).
Proof.
 intros. unfold v_map. f_equal. fun_ext. destruct fin_1to2d eqn: E.
 f_equal. rewrite v_idx_join. rewrite E; auto.
Qed.

(* 对 v 进行分割、映射和组合的操作, 等价于直接映射 *)
Lemma v_map_join_split: forall (A B: Set) m n d d' (f: A -> B) (v: vector A (m*n)),
 v_map d f v = v_join d' (v_map (v_default n d) (v_map d f) (v_split d v)).
Proof.
 intros. rewrite v_map_split. unfold v_map, v_join.
 apply v_make_eq. fun_ext. destruct (fin_1to2d x) eqn : E.
 rewrite <- v_idx_map. unfold v_map. rewrite !v_idx_make.
 f_equal. f_equal. replace f0 with (fst (fin_1to2d x)) by (rewrite E; auto).
 replace f1 with (snd (fin_1to2d x)) by (rewrite E; auto).
 symmetry; apply fin_2to1d_1to2d.
Qed.

(** *** Example *)

(** 将 (1,2,3,4,5,6,7,8,9) 拆成 3 * 3 得 ((1,2,3), (4,5,6), (7,8,9)) *)
Goal v_split 0 ([1,2,3,4,5,6,7,8,9]: vector nat (3 * 3)) = [[1,2,3],[4,5,6],[7,8,9]].
Proof. auto. Qed.

End Vec_Dimen.

(** ** Auto *)

#[export] Hint Rewrite v_nth_split v_idx_split v_split_m_0 v_split_n_0 v_map_split
v_nth_join v_idx_join v_join_m_0 v_join_n_0 v_split_join v_map_join v_map_join_split: vcore.


(* ######################################################################### *)
(** * Vector Combination *)

Section Vec_Comb.

(** ** v_iterate *)

(** *** Definition *)

(** 定义 v_iteratre, 对每行进行迭代 *)
Fixpoint v_iterate {A: Set} {i j: nat} (n: nat) (f: forall m, vector A (i * m) -> vector A m) 
: vector A ((i ^ n) * j) -> vector A j:= 
 match n with
 | O => fun (v: vector A (i^O*j)) => eq_rec (i ^ O * j) (vector A) v j (pow_0_mul_1 i j) 
 | S n' => fun v => v_iterate n' f (f ((i ^ n')*j)
 (eq_rec (i ^ S n' * j) (vector A) v (i * (i ^ n' * j)) (pow_Sn_mul n' i j)))
 end.

(** ** v_concat *)

(** *** Definition *)

(** 定义 v_concat, 将两个向量连接成一个向量 *)

Definition v_concat {A: Set} {m n: nat} d (v: vector A m) (v': vector A n): vector A (m + n):= 
 v_make (fun (i: fin (m + n)) => 
 if i <? m then v_nth d v i else v_nth d v' (i - m)).

(** *** Lemma *)

(** 当连接左边长度为 0 时, 直接返回右向量 *)
Lemma v_concat_0_l: forall (A: Set) n d (v: vector A 0) (v': vector A n),
 v_concat d v v' = v'.
Proof.
 destruct n; intros.
 - (* n = 0 *)
 destruct v, v' ; auto.
 - (* n <> 0 *)
 unfold v_concat. simpl(0 + S n). 
 rewrite <- v_make_nth with (v := v') (d := d).
 apply v_make_eq; fun_ext. destruct (Nat.ltb_spec0 x 0).
 lia. replace (fin2nat x - 0) with (fin2nat x) by lia.
 rewrite v_nth_make with (H := fin_proof x). f_equal.
Qed.

(** 当连接右边长度为 0 时, 直接返回左向量 *)
Lemma v_concat_0_r: forall (A: Set) n d (v: vector A n) (v': vector A 0),
 v_concat d v v' = v_make (fun i: fin (n + 0) => v_idx d v FF[i|plus_n_O _]).
Proof.
 destruct n; intros.
 - (* n = 0 *)
 destruct v, v' ; auto.
 - (* n <> 0 *)
 unfold v_concat. simpl(0 + S n). 
 rewrite <- v_make_nth with (v := v') (d := d).
 apply v_make_eq; fun_ext. destruct (Nat.ltb_spec0 x 0).
 lia. replace (x <? S n) with true. unfold v_idx; f_equal. 
 pose proof (fin_proof x). fauto.
Qed.

(** *** Example *)

(** 将 (1,2) 与 (3,4,5) 连接, 得 (1,2,3,4,5) *)
Goal v_concat 0 ([1,2]: vector nat 2) ([3,4,5]: vector nat 3) = [1,2,3,4,5].
Proof. auto. Qed.

(** ** v_padl *)

(** *** Definition *)

(** 定义 v_padl, 将长度为 n 的向量扩展成 k + n *)
Definition v_padl {A: Set} {n} d (k: nat) (v: vector A n): vector A (k + n):= 
 v_make (fun (i: fin (k + n)) =>
 if i <? k then d else v_nth d v (i - k)).

(** *** Lemma *)

(** 左拓展 0 等于本身 *)
Lemma v_padl_0: forall (A: Set) n d (v: vector A n),
 v_padl d 0 v = v.
Proof.
 intros. unfold v_padl. simpl.
 replace (fun i : fin n => v_nth d v (i - 0)) with (fun i : fin n => v_nth d v i).
 apply v_make_idx. fun_ext. f_equal. lia.
Qed.

(** 左扩展 n 等于 左连接 n 长度的默认值 *)
Lemma v_padl_eq_concat: forall {A: Set} {n} d k (v: vector A n),
 v_padl d k v = v_concat d (v_default k d) v.
Proof.
 intros. unfold v_padl, v_concat. apply v_make_eq; fun_ext.
 destruct (x <? k) eqn : E; fauto.
 symmetry. apply v_nth_default. pose proof (fin_proof x). lia.
Qed.

(** *** Example *)

(** 将 (1,2,3) 左扩展 2 个 0, 得 (0,0,1,2,3) *)
Goal v_padl 0 2 ([1,2,3]: vector nat 3) = [0,0,1,2,3].
Proof. auto. Qed.

(** *** v_padr *)

(** *** Definition *)

(** 定义 v_padr, 将长度为 n 的向量扩展成 n + k *)
Definition v_padr {A: Set} {n} d (k: nat) (v: vector A n): vector A (n + k):= 
 v_make (fun (i: fin (n + k)) =>
 if i <? n then v_nth d v i else d).

(** *** Lemma *)

(** 右拓展 0 等于本身 *)
Lemma v_pardr_0: forall (A: Set) n d (v: vector A n),
 v_padr d 0 v = v_make (fun i: fin (n + 0) => v_nth d v i).
Proof.
 intros. unfold v_padr. apply v_make_eq. fun_ext.
 replace (x <? n) with true; auto.
 pose proof (fin_proof x); fauto.
Qed.

(** 右扩展 n 等于 右连接 n 长度的默认值 *)
Lemma v_padr_eq_concat: forall {A: Set} {n} d k (v: vector A n),
 v_padr d k v = v_concat d v (v_default k d).
Proof.
 intros. unfold v_padr, v_concat. apply v_make_eq; fun_ext.
 destruct (x <? n) eqn : E; fauto.
 symmetry. apply v_nth_default. pose proof (fin_proof x). lia.
Qed.

(** *** Example *)

(** 将 (1,2,3) 右扩展 2 个 0, 得 (1,2,3,0,0) *)
Goal v_padr 0 2 ([1,2,3]: vector nat 3) = [1,2,3,0,0].
Proof. auto. Qed.

(** *** v_truncl *)

(** *** Definition *)

(** 从一个长度为 n 的向量 v 中截取前 k 个元素, 生成一个新的长度为 k 的向量 *)
Definition v_truncl {A: Set} {n} (d: A) (k: nat) 
 (H_le: k <= n) (v: vector A n): vector A k:= 
 v_make (fun (i: fin k) => v_idx d v FF[FSn[ i | n - k ]|eq_sym(sub_proof H_le)]).

(** *** Lemma *)

(** 从一个长度为 n 的向量 v 中截取前 0 个元素为 tt *)
Lemma v_truncl_0: forall (A: Set) n d (v: vector A n),
 v_truncl d (Nat.le_0_l n) v = tt. 
Proof. auto. Qed.

(** 从一个长度为 n 的向量 v 中截取前 n 个元素为自身 *)
Lemma v_truncl_n: forall (A: Set) n d (v: vector A n),
 v_truncl d (Nat.le_refl n: n<= n) v = v.
Proof.
 destruct n; intros. apply unit_unique. (* 排除 n = 0 的情况 *)
 unfold v_truncl,v_idx. destruct v as [v e].
 rewrite v_make_Sn. fauto.
 - (* v_make (fun i : fin n => v_nth d (v, e) i) = v *)
 rewrite <- v_make_nth with (v := v) (d := d).
 apply v_make_eq; fun_ext. destruct x; simpl.
 replace (x =? n) with false; fauto.
 rewrite v_nth_make with (H := l). f_equal; auto.
 - (* v_nth d (v, e) n = e *)
 apply v_nth_tail.
Qed.

(** 将长度为 m 和 n 的向量连接后, 再左截取 m 个长度, 等于原长为 m 的向量 *)
Lemma v_truncl_concat: forall {A: Set} {m n} d (v: vector A m) v',
 v_truncl d (Nat.le_add_r m n) (v_concat d v v') = v.
Proof.
 intros. apply v_nth_eq_v with (d := d); intros.
 unfold v_truncl. assert (i < m). apply fin_proof.
 rewrite v_nth_make with (H := H). unfold v_idx.
 replace (fin2nat (FF[ FSn[ F[ H] | m + n - m] | eq_sym (sub_proof (Nat.le_add_r m n))]))
 with (fin2nat i). unfold v_concat. assert (i < m + n). lia.
 rewrite v_nth_make with (H := H0). simpl. replace (i <? m) with true; fauto. simpl. auto.
Qed.

(** 将长度为 n 向量右扩展 k 后, 再左截取 m 个长度, 等于原向量 *)
Lemma v_truncl_padr: forall (A: Set) n d k (v: vector A n),
 v_truncl d (Nat.le_add_r n k) (v_padr d k v) = v.
Proof.
 intros. apply v_nth_eq_v with (d := d); intros.
 unfold v_truncl. assert (i < n). apply fin_proof.
 rewrite v_nth_make with (H := H). unfold v_idx.
 replace (fin2nat (FF[ FSn[ F[ H] | n + k - n] | eq_sym (sub_proof (Nat.le_add_r n k))]))
 with (fin2nat i). unfold v_padr. assert (i < n + k). lia.
 rewrite v_nth_make with (H := H0). simpl. replace (i <? n) with true; fauto. simpl; auto.
Qed.

(** *** Example *)

(** 证明 3 <= 5 *)
Lemma _3le5: 3 <= 5. Proof. lia. Qed.

(** 对于 (1,2,3,4,5), 截取前3得 (1,2,3) *)
Goal v_truncl 3 _3le5 [1,2,3,4,5] = [1,2,3].
Proof. auto. Qed.

(** *** v_truncr *)

(** *** Definition *)

(** 从一个长度为 n 的向量 v 中截取后 k 个元素, 生成一个新的长度为 k 的向量 *)
Definition v_truncr {A: Set} {n} (d: A) (k: nat) 
 (H_le: k <= n) (v: vector A n): vector A k:= 
 v_make (fun (i: fin k) => v_idx d v FF[Fsn[ i | n - k ]|eq_sym(sub_proof H_le)]).

(** *** Lemma *)

(** 从一个长度为 n 的向量 v 中截取前 0 个元素为 tt *)
Lemma v_truncr_0: forall (A: Set) n d (v1: vector A n),
 v_truncr d (Nat.le_0_l n) v1 = tt. 
Proof. auto. Qed.

(** 从一个长度为 n 的向量 v 中截取前 n 个元素为自身 *)
Lemma v_truncr_n: forall (A: Set) n d (v: vector A n),
 v_truncr d (Nat.le_refl n: n<= n) v = v.
Proof.
 destruct n; intros. apply unit_unique. (* 排除 n = 0 的情况 *)
 unfold v_truncr,v_idx. destruct v as [v e].
 rewrite v_make_Sn. fauto.
 - (* v_make (fun i : fin n => v_nth d (v, e) i) = v *)
 rewrite <- v_make_nth with (v := v) (d := d).
 apply v_make_eq; fun_ext. destruct x; simpl.
 replace (x + (n - n)) with x by lia.
 replace (x =? n) with false; fauto.
 rewrite v_nth_make with (H := l). f_equal; auto.
 - (* v_nth d (v, e) n = e *)
 simpl. replace (n + (n - n) =? n) with true; fauto.
Qed.

(** 将长度为 m 和 n 的向量连接后, 再右截取 n 个长度, 等于原长为 n 的向量 *)
Lemma v_truncr_concat: forall {A: Set} {m n} d (v: vector A m) v',
 v_truncr d (Nat.le_add_l n m) (v_concat d v v') = v'.
Proof.
 intros. apply v_nth_eq_v with (d := d); intros.
 unfold v_truncr. assert (i < n). apply fin_proof.
 rewrite v_nth_make with (H := H). unfold v_idx.
 replace (fin2nat (FF[ Fsn[ F[ H] | m + n - n] | eq_sym (sub_proof (Nat.le_add_l n m))]))
 with (i + m). unfold v_concat. assert (i + m < m + n). lia.
 rewrite v_nth_make with (H := H0). simpl. replace (i + m <? m) with false; fauto.
 f_equal; fauto. simpl; fauto.
Qed.

(** 将长度为 n 向量左扩展 k 后, 再右截取 m 个长度, 等于原向量 *)
Lemma v_truncr_padl: forall (A: Set) n d k (v: vector A n),
 v_truncr d (Nat.le_add_l n k) (v_padl d k v) = v.
Proof.
 intros. apply v_nth_eq_v with (d := d); intros.
 unfold v_truncr. assert (i < n). apply fin_proof.
 rewrite v_nth_make with (H := H). unfold v_idx.
 replace (fin2nat (FF[ Fsn[ F[ H] | k + n - n] | eq_sym (sub_proof (Nat.le_add_l n k))]))
 with (i + k). unfold v_padl. assert (i + k < k + n). lia.
 rewrite v_nth_make with (H := H0). simpl. replace (i + k <? k) with false; fauto.
 f_equal; fauto. simpl; fauto.
Qed.

(** *** Example *)

(** 对于 (1,2,3,4,5), 截取后3得 (1,2,3) *)
Goal v_truncr 3 _3le5 [1,2,3,4,5] = [3,4,5].
Proof. auto. Qed.

(** *** v_trans *)

(** *** Definition *)

(** 定义 v_trans 表示转置 *)
Definition v_trans {A: Set} {n m: nat} d (v: vector (vector A m) n): vector (vector A n) m:= 
 v_make (fun i => v_make (fun j => v_idx d (v_idx (v_default m d) v j) i)).

(** *** Lemma *)

(** 对于任意二维向量, 专置两次等于本身 *)
Lemma v_trans_trans: forall (A: Set) m n d (v: vector (vector A m) n),
 v_trans d (v_trans d v) = v.
Proof.
 intros; unfold v_trans. rewrite v_nth_eq_v with (d := v_default m d).
 intro. rewrite v_nth_make with (H := fin_proof i).
 rewrite v_nth_eq_v with (d := d). intro.
 rewrite v_nth_make with (H := fin_proof i0).
 unfold v_idx; simpl. rewrite v_nth_make with (H := fin_proof i0).
 rewrite v_nth_make with (H := fin_proof i). simpl. auto.
Qed.

(** *** Example *)

(** 将 ((1,2,3),(4,5,6),(7,8,9), (10,11,12))转置成((1,4,7,10),(2,5,8,11),(3,6,9,12)) *)
Goal v_trans 0 ([[1,2,3],[4,5,6],[7,8,9],[10,11,12]]: vector (vector nat 3) 4) = 
 [[1, 4, 7, 10], [2, 5, 8, 11], [3, 6, 9, 12]].
Proof. auto. Qed.

End Vec_Comb.

(** ** Auto *)

#[export] Hint Rewrite v_concat_0_l v_concat_0_r v_padl_0 v_pardr_0 v_truncl_0 v_truncl_n
v_truncl_padr v_truncr_0 v_truncr_n v_truncr_padl: vcore.

#[export] Hint Resolve v_padl_eq_concat v_padr_eq_concat v_truncl_concat 
v_truncr_concat: vcore.

(* ######################################################################### *)
(** * Vector Option*)

Section Vec_Opt.

(** ** v_optmk *)

(** *** Definition *)

(** 定义 v_optmk, 若其中一个访问出错，则返回 None *)
Fixpoint v_optmk {n} {A : Set} {struct n} : (fin n -> option A) -> option (vector A n) :=
 match n with
 | 0 => fun _ => Some (tt : vector A 0)
 | S n' => fun (u : fin (S n') -> option A) =>
 match u '[n'] with
 | Some e => 
 match v_optmk (fun i => u (fin2finS i)) with
 | Some e' => Some (e', e)
 | None => None
 end
 | None => None
 end
 end.

(** *** Lemma *)

(** 如果构造函数 f f' 相等, 那么通过 v_optmk 构造出来的也应相等 *)
Lemma v_optmk_eq: forall {A: Set} {n} (f f': fin n -> option A),
 f = f' -> v_optmk f = v_optmk f'.
Proof. induction n; fauto. Qed.

(** 化简 v_optmk (S n) *)
Lemma v_optmk_Sn : forall {A : Set} {n} (u : fin (S n) -> option A),
 v_optmk u = match u '[n] with (* 检查最后一个元素 *)
 | Some e => 
 match v_optmk (fun i => u (fin2finS i)) with (* 递归检查前m'个元素 *)
 | Some e' => Some (e', e) (* 构造向量 *)
 | None => None
 end
 | None => None
 end.
Proof. auto. Qed.

(** 化简 v_optmk 0 *)
Lemma v_optmk_0 : forall (A : Set) (u : fin 0 -> option A),
 v_optmk u = Some tt.
Proof. auto. Qed.

(** 通过对 v 进行 v_nth 的函数来进行构造 v_optmk, 构造结果依旧为 v *)
Lemma v_optmk_nth: forall (A: Set) n d (v: vector A n),
 v_optmk (fun i => Some (v_nth d v i)) = Some v.
Proof with fauto.
 induction n... simpl; f_equal... destruct v as [v e]. rewrite v_optmk_Sn...
 replace (fun i : fin n => Some (v_nth d ((v, e) : vector A (S n)) FS[ i])) with
 (fun i : fin n => Some (v_nth d v i)). 
 2: { fun_ext; f_equal. rewrite v_nth_head... } 
 rewrite IHn... apply v_nth_tail.
Qed.

(** 当v_optmk 成功时, 通过索引访问向量 v_opt f 的第 i 个元素, 等价于直接通过函数 f 计算索引 i 对应的值 *)
Lemma v_nth_optmk: forall (A: Set) n d i v (f: fin n -> option A) (H: i < n),
 v_optmk f = Some v -> Some (v_nth d v i) = f F[H].
Proof with fauto.
 induction n... simpl. rewrite v_optmk_Sn in H0. destruct (f '[n]) eqn : E. 
 2: { inv H0. } destruct (v_optmk (fun i : fin n => f FS[ i])) eqn : E0. 2: { inv H0. }
 inv H0. simpl. destruct (i =? n) eqn: E1...
 - rewrite <- E. f_equal...
 - assert (i < n). lia. rewrite IHn with (f := fun i : fin n => f FS[i]) (H := H0).
 f_equal... apply E0.
Qed.

(** 通过对 v 进行 v_idx 的函数来进行构造 v_optmk, 构造结果依旧为 v *)
Lemma v_optmk_idx: forall (A: Set) n d (v: vector A n),
 v_optmk (fun i => Some (v_idx d v i)) = Some v.
Proof with fauto.
 induction n... simpl; f_equal... destruct v as [v e]. rewrite v_optmk_Sn...
 replace (fun i : fin n => Some (v_idx d ((v, e) : vector A (S n)) FS[ i])) with
 (fun i : fin n => Some (v_idx d v i)). 
 2: { fun_ext; f_equal. rewrite v_idx_head... } 
 rewrite IHn... apply v_nth_tail.
Qed.

(** 当v_optmk 成功时, 通过索引访问向量 v_opt f 的第 i 个元素, 等价于直接通过函数 f 计算索引 i 对应的值 *)
Lemma v_idx_optmk: forall (A: Set) n d i v (f: fin n -> option A),
 v_optmk f = Some v -> Some (v_idx d v i) = f i.
Proof with fauto.
 induction n... rewrite v_optmk_Sn in H. destruct (f '[n]) eqn : E. 
 2: { inv H. } destruct (v_optmk (fun i : fin n => f FS[ i])) eqn : E0. 2: { inv H. }
 inv H. destruct (i =? n)%nat eqn: E1...
 - replace i with '[n] by fauto. rewrite E. f_equal; rewrite v_idx_tail...
 - assert (i < n). { pose proof (fin_proof i). lia. }
 replace (v_idx d ((v0, a) : vector A (S n)) i) with (v_idx d v0 F[H]).
 2: { unfold v_idx. symmetry. apply v_nth_head. auto. }
 rewrite IHn with (f := fun i : fin n => f FS[i])... f_equal...
Qed.

Lemma v_make_optmk : forall (A : Set) n (f: fin n -> A),
  Some (v_make f) = v_optmk (fun i => Some (f i)).
Proof with fauto.
  induction n... rewrite v_make_Sn, v_optmk_Sn. rewrite <- IHn...
Qed.

(** 当 v_optmk 返回 Some 时，对所有 u 返回的也为 Some *)
Lemma v_optmk_Some_eq_l : forall {A : Set} {n} (u : fin n -> option A),
 (exists v, v_optmk u = Some v) -> (forall i , exists e, u i = Some e).
Proof with fauto.
 induction n... rewrite v_optmk_Sn in H. destruct (u '[n]) eqn : E. 2: { inv H. }
 destruct (v_optmk (fun i : fin n => u FS[ i])) eqn : E0.
 2: { inv H. } destruct (i =? n)%nat eqn : E1...
 - exists a. rewrite <- E. f_equal...
 - assert (i < n). { pose proof (fin_proof i). lia. }
 destruct IHn with (u := (fun i : fin n => u FS[ i])) (i := F[H])... 
 exists v... exists x. rewrite <- H0. f_equal...
Qed.

(** 当所有 u 返回的为 Some 时; v_optmk 返回也是 Some *)
Lemma v_optmk_Some_eq_r : forall {A : Set} {n} (u : fin n -> option A),
 (forall i, exists e, u i = Some e) -> (exists v, v_optmk u = Some v).
Proof with fauto.
 induction n... exists tt. apply v_optmk_0.
 destruct IHn with (u := fun i : fin n => u FS[i])...
 specialize H with '[n]... exists ((x, x0) : vector A (S n)).
 rewrite v_optmk_Sn. rewrite H. rewrite H0...
Qed.

(** 当 v_optmk 返回 Some 时，对所有 u 返回的也为 Some; 反之亦然 *)
Lemma v_optmk_Some_eq : forall {A : Set} {n} (u : fin n -> option A),
 (exists v, v_optmk u = Some v) <-> (forall i , exists e, u i = Some e).
Proof. split; [apply v_optmk_Some_eq_l | apply v_optmk_Some_eq_r]; fauto. Qed.

(** *** Example *)

(** 通过函数生成 Some [0,1,2] *)
Example my_v_opt := v_optmk (fun x : fin 3 => Some (fin2nat x)).

(** 测试 v_optmk, 生成 Some [0,1,2] *)
Example v_optmk_test : my_v_opt = Some [0,1,2].
Proof. auto. Qed.

(** ** v_optdes *)

(** *** Definition *)

(** 定义 v_optdes， 将一个 option (vector S n) 拆解 *)
Definition v_optdes {A : Set} {n : nat} (v : option (vector A (S n))) :
 option (vector A n) * option A :=
 match v with
 | None => (None, None)
 | Some v' => let (h, d) := v' in (Some h, Some d)
 end.

(** *** Lemma *)

(** 化简 v_optdes None *)
Lemma v_optdes_None : forall (A : Set) {n : nat},
 v_optdes (None : option (vector A (S n))) = (None, None).
Proof. fauto. Qed.

(** 化简 v_option Some *)
Lemma v_optdes_Some : forall (A : Set) {n : nat} (v : (vector A (S n))),
 v_optdes (Some v) = (Some (fst v), Some (snd v)).
Proof. intros; destruct v; fauto. Qed.

(** *** Example *)

(** 测试拆解 Some [0,1,2] *)
Example v_optdes_test : v_optdes my_v_opt = (Some [0,1], Some 2).
Proof. auto. Qed.

(** ** v_optcon *)

(** *** Definition *)

(** 定义 v_optcon， 将一个 option (vector n) 和 option A组合成 option (vector S n) *)
Definition v_optcon {A : Set} {n : nat} (p : option (vector A n) * option A) :
 option (vector A (S n)):=
 let (v, e) := p in 
 match v, e with
 | Some v', Some e' => Some (v', e')
 | _, _ => None
 end.

(** *** Lemma *)

(** 化简 v_optcon (None， _) *)
Lemma v_optcon_Nonel : forall (A : Set) {n : nat} a,
 v_optcon ((None : option (vector A n)), a) = None.
Proof. fauto. Qed.

(** 化简 v_optcon (v， None) *)
Lemma v_optcon_Noner : forall (A : Set) {n : nat} (v : option (vector A n)),
 v_optcon (v, None) = None.
Proof. intros. destruct v; fauto. Qed.

(** 化简 v_option Some *)
Lemma v_optcon_Some : forall (A : Set) {n : nat} (v : vector A n) (e : A),
 v_optcon (Some v, Some e) = Some ((v, e) : vector A (S n)).
Proof. intros. fauto. Qed.

(** 先 v_optdes 再 v_optcon 等于本身 *)
Lemma v_optcon_optdes : forall (A : Set) {n : nat} (v : option (vector A (S n))),
 v_optcon (v_optdes v) = v.
Proof with fauto. 
 intros. destruct v.
 - rewrite v_optdes_Some. rewrite v_optcon_Some... destruct v...
 - rewrite v_optdes_None. rewrite v_optcon_Nonel...
Qed.

(** 如果两个值均正常，那么先 v_optcon 再 v_opdes 等于本身 *)
Lemma v_optdes_optcon : forall (A : Set) {n : nat} (v : vector A n) (e : A),
 v_optdes (v_optcon (Some v, Some e)) = (Some v, Some e).
Proof. fauto. Qed.

(** *** Example *)

(** 测试合成 Some [0,1,2] *)
Example v_optcon_test : my_v_opt = @v_optcon nat 2 (Some [0,1], Some 2).
Proof. auto. Qed.

(** v_optnth *)

(** *** Definition *)

(** v_optnth 的定义 *)
Fixpoint v_optnth {A : Set} {n: nat} : option (vector A n) -> nat -> option A :=
 match n with
 | 0 => fun _ _ => None
 | S n' => fun (v : option (vector A (S n'))) i =>
 match v with
 | None => None
 | Some v' => if (i=? n') then Some (snd v') else v_optnth (Some (fst v')) i
 end
 end.

(** *** Lemma *)

(** 但 v = None 时， 恒返回 None *)
Lemma v_optnth_None : forall (A : Set) {n} i,
 v_optnth (None : option (vector A n)) i = None.
Proof. destruct n; fauto. Qed.

(** 但 v = Some v' 时， 正常返回 *)
Lemma v_optnth_Some : forall (A : Set) {n} d (v :vector A n) i,
 i < n -> v_optnth (Some v) i = Some (v_nth d v i).
Proof with fauto.
 induction n... destruct v as [v' e] eqn : E. simpl. 
 destruct (i =? n) eqn : E0... rewrite IHn with (d:=d)...
Qed.

(** 证明对于 v_optnth 来说, 当 v 返回正常值并取值超出范围时, 返回 None *)
Lemma v_optnth_beyond: forall (A: Set) n i (v: option (vector A n)),
 ~ (i < n) -> v_optnth v i = None.
Proof with fauto.
 induction n... simpl. destruct v... rewrite IHn...
Qed.

(** 证明对于 v_optnth 来说, e 有正常返回值时 , (v, e): option vector (S n) 头部为 v *)
Lemma v_optnth_head: forall (A: Set) n i (v: option (vector A n)) e,
 i < n -> v_optnth (v_optcon (v, Some e)) i = v_optnth v i.
Proof with fauto.
 intros. destruct v. 2 :{ rewrite v_optcon_Nonel. rewrite !v_optnth_None... }
 rewrite v_optcon_Some. rewrite !v_optnth_Some with (d:=e)... apply v_nth_head...
Qed.

(** 证明对于 v_optnth 来说, (v, e) 有正常返回值时 , (v, e): option vector (S n) 头部为 v *)
Lemma v_optnth_head_Some: forall (A: Set) n i (v: (vector A n)) (e : A),
 i < n -> v_optnth (Some ((v, e) : vector A (S n))) i = v_optnth (Some v) i.
Proof with fauto. intros. rewrite !v_optnth_Some with (d:=e)... apply v_nth_head... Qed.

(** 证明对于 v_optnth 来说, (v, e) 无正常返回值时 , (v, e): option vector (S n) 头部为 v *)
Lemma v_optnth_head_None: forall (A: Set) n i,
 i < n -> v_optnth (None : option (vector A (S n))) i = v_optnth (None : option (vector A n)) i.
Proof with fauto. intros. rewrite !v_optnth_None... Qed.

(** 证明对于 v_optnth 来说, v有正常返回值时， (v, e): vector (S n) 尾部为 e *)
Lemma v_optnth_tail: forall (A: Set) n (v: vector A n) e,
 v_optnth (v_optcon (Some v, e) )n = e.
Proof with fauto.
 intros. destruct e.
 - rewrite v_optcon_Some. rewrite !v_optnth_Some with (d:= a)... apply v_nth_tail...
 - rewrite v_optcon_Noner...
Qed.

(** 证明对于 v_optnth 来说, (v, e) 有正常返回值时 , (v, e): option vector (S n) 尾部为 e *)
Lemma v_optnth_tail_Some: forall (A: Set) n (v: (vector A n)) (e : A),
 v_optnth (Some ((v, e) : vector A (S n))) n = Some e.
Proof with fauto. intros. rewrite !v_optnth_Some with (d:= e)... apply v_nth_tail... Qed.

(** 证明对于 v_optnth 来说, (v, e) 无正常返回值时 , (v, e): option vector (S n) 尾部为 e *)
Lemma v_optnth_tail_None: forall (A: Set) n,
 v_optnth (None : option (vector A (S n))) n = None.
Proof with fauto. intros. rewrite !v_optnth_None... Qed.

(** 将 v_nth (v, e) 化简 *)
Lemma v_optnth_Sn: forall (A: Set) n i (v: vector A n) e,
 v_optnth (v_optcon (Some v, Some e)) i = if i =? n then Some e else v_optnth (Some v) i.
Proof with fauto.
 intros... apply v_optnth_tail. destruct (classic (i < n)).
 apply v_optnth_head... rewrite !v_optnth_beyond...
Qed.

(** 对于 v1 v2: vector, 若 v1 = v2, 则对于 i: fin n, 通过 v_nth 获取的值相同; 反之亦然 *)
Lemma v_optnth_eq: forall (A: Set) n (v1 v2: option (vector A n)),
 0 < n -> v1 = v2 <-> (forall i, v_optnth v1 i = v_optnth v2 i).
Proof with fauto.
 split... induction n... destruct v1, v2.
 - destruct v as [v1 e1]. destruct v0 as [v2 e2]. f_equal.
 specialize IHn with (v1:=Some v1) (v2:=Some v2). destruct (n =? 0) eqn : E.
 + fauto. specialize H0 with 0. rewrite !v_optnth_tail_Some in H0...
 + assert (0 < n). fauto. clear E; rename H1 into E. apply IHn in E...
 specialize H0 with n. rewrite !v_optnth_tail_Some in H0...
 specialize H0 with i. destruct (classic (i < n)). rewrite !v_optnth_head_Some in H0...
 rewrite !v_optnth_beyond...
 - specialize H0 with n. rewrite v_optnth_Some with (d:= snd v) in H0...
 rewrite v_optnth_None in H0. inv H0.
 - specialize H0 with n. rewrite v_optnth_Some with (d:= snd v) in H0...
 rewrite v_optnth_None in H0. inv H0.
 - auto.
 Qed.

(** 通过对 v 进行 v_optnth 的函数来进行构造 v_make, 构造结果依旧为 v *)
Lemma v_optmk_optnth: forall (A: Set) n (v: option (vector A n)),
 0 < n -> v_optmk (v_optnth v) = v.
Proof with fauto.
 induction n... destruct v.
 - destruct v as [v' e]. rewrite v_optmk_Sn. rewrite v_optnth_tail_Some.
 replace (fun i : fin n => v_optnth (Some ((v', e) : vector A (S n))) FS[ i]) with 
 (fun i : fin n => v_optnth (Some v') i) by (fun_ext; rewrite v_optnth_head_Some; fauto).
 destruct n. rewrite v_optmk_0... rewrite IHn...
 - simpl...
Qed.

(** 通过索引访问向量 v_optmk f 的第 i 个元素, 等价于直接通过函数 f 计算索引 i 对应的值 *)
Lemma v_optnth_optmk: forall (A: Set) n i (f: fin n -> option A) (E: i < n),
 v_optmk f <> None -> v_optnth (v_optmk f) i = f F[E].
Proof with fauto.
 intros. destruct (v_optmk f) eqn : E0... clear H.
 induction n... destruct v as [v' e]. destruct (i =? n) eqn: E1...
 - rewrite v_optnth_Some with (d:=e)... rewrite v_nth_tail. rewrite v_optmk_Sn in E0.
 destruct (f '[n]) eqn : E1. 2 :{ inv E0. }
 destruct (v_optmk (fun i : fin n => f FS[ i])). 2 :{ inv E0. }
 replace F[E] with '[n] by fauto. rewrite E1. inv E0...
 - assert (i < n)... clear E1; rename H into E1. rewrite v_optnth_head_Some...
 specialize IHn with (f:= fun i => f FS[i]) (E:= E1) (v:=v'). rewrite IHn. f_equal...
 clear IHn. rewrite v_optmk_Sn in E0. destruct (f '[n]). 2 :{ inv E0. }
 destruct (v_optmk (fun i : fin n => f FS[ i])) eqn : E2. 2 :{ inv E0. } inv E0...
Qed.

(** *** Example *)

(** 对 my_v_opt 的实例取 1 得 Some 1 *)
Example v_optnth_test1: v_optnth my_v_opt 1 = Some 1.
Proof. auto. Qed.

(** 对 my_v_opt 的实例取 3 得 None *)
Example v_optnth_test2: v_optnth my_v_opt 3 = None.
Proof. auto. Qed.

(** ** v_optidx *)

(** *** Definition *)

(** 定义 v_optidx， 对可选项的 vector 安全获取 *)
Definition v_optidx {A : Set} {n: nat} (v : option (vector A n)) (i : fin n) : option A :=
  v_optnth v i.

(** *** Lemma *)

(** 但 v = None 时， 恒返回 None *)
Lemma v_optidx_None : forall (A : Set) {n} i,
 v_optidx (None : option (vector A n)) i = None.
Proof. intros. unfold v_optidx. apply v_optnth_None. Qed.

(** 但 v = Some v' 时， 正常返回 *)
Lemma v_optidx_Some : forall (A : Set) {n} d (v :vector A n) i,
  v_optidx (Some v) i = Some (v_nth d v i).
Proof. intros. unfold v_optidx. apply v_optnth_Some; fauto. Qed.

(** 证明对于 v_optidx 来说, e 有正常返回值时 , (v, e): option vector (S n) 头部为 v *)
Lemma v_optidx_head: forall (A: Set) n (i: fin n) (v: option (vector A n)) e,
  v_optidx (v_optcon (v, Some e)) FS[i] = v_optidx v i.
Proof. intros. unfold v_optidx. apply v_optnth_head. fauto. Qed.

(** 证明对于 v_optnth 来说, (v, e) 有正常返回值时 , (v, e): option vector (S n) 头部为 v *)
Lemma v_optidx_head_Some: forall (A: Set) n (i : fin n) (v: (vector A n)) (e : A),
 v_optidx (Some ((v, e) : vector A (S n))) FS[i] = v_optidx (Some v) i.
Proof. intros. unfold v_optidx. apply v_optnth_head_Some. fauto. Qed.

(** 证明对于 v_optnth 来说, (v, e) 无正常返回值时 , (v, e): option vector (S n) 头部为 v *)
Lemma v_optidx_head_None: forall (A: Set) n (i : fin n),
  v_optidx (None : option (vector A (S n))) FS[i] = v_optidx (None : option (vector A n)) i.
Proof. intros. unfold v_optidx. apply v_optnth_head_None. fauto. Qed.

(** 证明对于 v_optidx 来说, e 有正常返回值时 , (v, e): option vector (S n) 头部为 v *)
Lemma v_optidx_head_H : forall (A: Set) n (i: fin (S n)) (v: option (vector A n)) e (E: i < n),
  v_optidx (v_optcon (v, Some e)) i = v_optidx v FP[E].
Proof. intros. unfold v_optidx. apply v_optnth_head. fauto. Qed.

(** 证明对于 v_optidx 来说, (v, e) 有正常返回值时 , (v, e): option vector (S n) 头部为 v *)
Lemma v_optidx_head_Some_H: forall (A: Set) n (i : fin (S n)) (v: (vector A n)) (e : A) (E: i < n),
 v_optidx (Some ((v, e) : vector A (S n))) i = v_optidx (Some v) FP[E].
Proof. intros. unfold v_optidx. apply v_optnth_head_Some. fauto. Qed.

(** 证明对于 v_optidx 来说, (v, e) 无正常返回值时 , (v, e): option vector (S n) 头部为 v *)
Lemma v_optidx_head_None_H: forall (A: Set) n (i : fin (S n)) (E: i < n),
  v_optidx (None : option (vector A (S n))) i = v_optidx (None : option (vector A n)) FP[E].
Proof. intros. unfold v_optidx. apply v_optnth_head_None. fauto. Qed.

(** 证明对于 v_optidx 来说, v有正常返回值时， (v, e): vector (S n) 尾部为 e *)
Lemma v_optidx_tail: forall (A: Set) n (v: vector A n) e,
 v_optidx (v_optcon (Some v, e) ) '[n] = e.
Proof. intros. unfold v_optidx. apply v_optnth_tail. Qed.

(** 证明对于 v_optidx 来说, (v, e) 有正常返回值时 , (v, e): option vector (S n) 尾部为 e *)
Lemma v_optidx_tail_Some: forall (A: Set) n (v: (vector A n)) (e : A),
 v_optidx (Some ((v, e) : vector A (S n))) '[n] = Some e.
Proof. intros. unfold v_optidx. apply v_optnth_tail_Some. Qed.

(** 证明对于 v_optidx 来说, (v, e) 无正常返回值时 , (v, e): option vector (S n) 尾部为 e *)
Lemma v_optidx_tail_None: forall (A: Set) n,
 v_optidx (None : option (vector A (S n))) '[n] = None.
Proof. intros. unfold v_optidx. apply v_optnth_tail_None. Qed.

(** 对于 v1 v2: vector, 若 v1 = v2, 则对于 i: fin n, 通过 v_nth 获取的值相同; 反之亦然 *)
Lemma v_optidx_eq: forall (A: Set) n (v1 v2: option (vector A n)),
 0 < n -> v1 = v2 <-> (forall i: fin n, v_optidx v1 i = v_optidx v2 i).
Proof with fauto.
  unfold v_optidx. split; intros. apply v_optnth_eq...
  apply v_optnth_eq... destruct (classic (i < n)). rename H1 into E.
  specialize H0 with F[E]. apply H0. rewrite !v_optnth_beyond...
Qed.

(** 通过对 v 进行 v_optidx 的函数来进行构造 v_make, 构造结果依旧为 v *)
Lemma v_optmk_optidx: forall (A: Set) n (v: option (vector A n)),
 0 < n -> v_optmk (v_optidx v) = v.
Proof. intros. unfold v_optidx. apply v_optmk_optnth. fauto. Qed.

(** 通过索引访问向量 v_optmk f 的第 i 个元素, 等价于直接通过函数 f 计算索引 i 对应的值 *)
Lemma v_optidx_optmk: forall (A: Set) n (i : fin n) (f: fin n -> option A) (E: i < n),
 v_optmk f <> None -> v_optidx (v_optmk f) i = f i.
Proof with fauto.
 intros. unfold v_optidx. rewrite v_optnth_optmk with (E:=E)... f_equal...
Qed.

(** *** Example *)

(** 对 my_v_opt 的实例取 '[2] 得 Some 2 *)
Example v_optidx_test: v_optidx my_v_opt '[2] = Some 2.
Proof. auto. Qed.

End Vec_Opt.

(** ** Tactics *)

(** *** Auto *)

#[export] Hint Rewrite v_optmk_0 v_optmk_nth v_optmk_idx v_optdes_None v_optdes_Some
v_optcon_Nonel v_optcon_Noner v_optcon_Some v_optcon_optdes v_optdes_optcon v_optnth_None
v_optnth_tail v_optnth_tail_Some v_optnth_tail_None v_optnth_Sn  v_optmk_optnth 
v_optnth_optmk v_optidx_None v_optidx_Some  v_optidx_head v_optidx_head_Some 
v_optidx_head_None v_optidx_head_H v_optidx_head_Some_H v_optidx_head_None_H v_optidx_tail
v_optidx_tail_Some v_optidx_tail_None v_optmk_optidx v_optidx_optmk: vcore.

#[export] Hint Resolve v_optmk_eq  v_nth_optmk v_idx_optmk v_optmk_Some_eq v_optnth_Some 
v_optnth_beyond v_optnth_head v_optnth_head_Some v_optnth_head_None
v_optnth_eq  v_optidx_eq : vcore.


(* ######################################################################### *)
(** * Ltac *)

(** ** vec_simpl *)

(** 定义 vector 化简:
1. 分析 v : vector 0 的前提 *)
Ltac vec_simpl:=
 repeat match goal with
 | [ v : vector ?A 0 |- _ ] => replace v with (tt : vector ?A 0) by vec'_0_unique
 end.

(** 定义 vauto, 包含本所定义的一些引理和定义 *)
Ltac vauto:=
 repeat (quan_simpl; bool_simpl; opt_simpl; pair_simpl; fun_simpl; vec_simpl; f_simpl); subst; 
 autorewrite with vcore fcore core; auto with vcore fcore core;
 try lia; try apply proof_irrelevance.  
