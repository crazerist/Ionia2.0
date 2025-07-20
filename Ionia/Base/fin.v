Require Import Coq.Logic.ProofIrrelevance.
Require Export base.

Set Implicit Arguments.


(* ######################################################################### *)
(** * Fin *)

Section Fin.

(** ** fin *)

(** *** Definition *)

(** 定义 fin n 为小于 n 的自然数 *)
Definition fin (n: nat): Set:= {i: nat | i < n}.

(** *** Lemma *)

(** 证明 fin 0 是空的 *)
Lemma fin'_0: fin 0 -> False.
Proof. intros [i Hi]. bauto. Qed.

(** 证明 fin m * 0 是空的 *)
Lemma fin'_0_r: forall {m}, fin (m * 0) -> False.
Proof. intros m [i Hi]. bauto. Qed.

(** 证明 fin 0 * m 是空的 *)
Lemma fin'_0_l: forall {n}, fin (0 * n) -> False.
Proof. intros n [i Hi]. bauto. Qed.

(** 如果存在 fin n 这个数, 那么 0 < n *)
Lemma fin'_lt: forall {n} (i: fin n), 0 < n.
Proof.
 intros. destruct (zerop n); bauto. destruct (fin'_0 i).
Qed.

(** 如果 n = m, 那么类型 fin n 与 fin m 相同 *)
Lemma fin'_eq: forall n m, n = m -> fin n = fin m.
Proof. bauto. Qed.

(** *** Example *)

(** 定义 fin 3 的一个实例 *)
Example fin3_example: fin 3:= exist _ 2 (Nat.lt_succ_diag_r 2).

(** ** fin2nat *)

(** *** Definition *)

(** 将 fin n 转换为 nat *)
Definition fin2nat {n: nat} (i: fin n): nat:=
 match i with
 | exist _ i _ => i 
 end.

(** *** Lemma *)

(** 证明 fin n 中的元素小于 n *)
Lemma fin_proof: forall {n} (i: fin n), fin2nat i < n.
Proof. bauto. destruct i as [i H]. bauto. Qed.

(** 证明 fin n 中元素小于等于 n *)
Lemma fin_le: forall {n} (i: fin n), fin2nat i <= n.
Proof. bauto. pose proof (fin_proof i). bauto. Qed.

(** 证明若 n <= m, 则 fin n 中的元素小于 m *)
Lemma fin_lt: forall {n m} (i: fin n), n <= m -> fin2nat i < m.
Proof. intros. pose (fin_proof i). bauto. Qed.

(** 证明 fin n 中的元素小于 S n *)
Lemma fin_proof_S: forall {n} (i: fin n), fin2nat i < S n.
Proof. bauto. pose proof (fin_proof i). bauto. Qed.

(** 证明对于任意 i: fin n, 有 S i < S n *)
Lemma fin_proof_SS: forall {n} (i: fin n), S (fin2nat i) < S n.
Proof. bauto. pose proof (fin_proof i). bauto. Qed.

(** 证明当两个 fin n 类型数的内部值相等时,这两个数相等; 反之亦然 *)
Lemma fin_eq: forall {n} (i1 i2: fin n), fin2nat i1 = fin2nat i2 <-> i1 = i2.
Proof with bauto.
 bauto. destruct i1, i2. simpl in H... f_equal...
Qed.

(** 证明当两个 fin n 类型数的内部值相等时,这两个数相等 *)
Lemma fin_eq': forall {n} (i1 i2: fin n), fin2nat i1 = fin2nat i2 -> i1 = i2.
Proof. intros; apply fin_eq. bauto. Qed.

(** 证明当两个 fin n 类型数的内部值不等时,这两个数不等; 反之亦然 *)
Lemma fin_neq: forall {n} (i1 i2: fin n), fin2nat i1 <> fin2nat i2 <-> i1 <> i2.
Proof with bauto. unfold not... apply H. apply fin_eq... Qed.

(** 证明 fin 1 只含有一个元素 0 *)
Lemma fin'_1_elem: forall (i: fin 1), fin2nat i = 0.
Proof. intros [i Hi]. simpl. bauto. Qed.

(** 证明 fin 1 是唯一的 *)
Lemma fin'_1_unique: forall (i i': fin 1), i = i'.
Proof. bauto. apply fin_eq. rewrite !fin'_1_elem. bauto. Qed.

(** *** Example *)

(** 提取 fin 3 实例中的自然数 *)
Example fin2nat_example : fin2nat fin3_example = 2.
Proof. auto. Qed.

(** ** fin_eq_dec *)

(** *** Definition *)

(** fin_eq 的可判定性 *)
Definition fin_eq_dec {n: nat} (x y: fin n): {x = y} + {x <> y}.
Proof with bauto.
 destruct x as [i Hi]. destruct y as [j Hj]. unfold not.
 destruct (Nat.eq_dec i j) as [Hij | Hij]. (* 根据nat_eq的可判定性分情况讨论 *)
 - (* i = j | - {x = y} *)
 left. apply fin_eq...
 - (* i <> j | - {x <> y} *)
 right... apply fin_eq in H...
Defined.

(** ** nat2fin *)

(** *** Definition *)

(** 将 nat 转换为 fin *)
Definition nat2fin {n i} (H: i < n): fin n:=
 exist _ i H.

(** *** Lemma *)

(** 一个数先经过 nat2fin 再经过 fin2nat 依旧为其本身 *)
Lemma fin2nat_nat2fin: forall n i (H: i < n), fin2nat (nat2fin H) = i.
Proof. bauto. Qed.

(** 一个数先经过 fin2nat 再经过 nat2fin 依旧为其本身 *)
Lemma nat2fin_fin2nat: forall n (i: fin n), nat2fin (fin_proof i) = i.
Proof. bauto. apply fin_eq. apply fin2nat_nat2fin. Qed.

(** 证明, 当 i: fin 时有 f i = true, 那么对于 n_forall n 返回 true *)
Lemma n_forall_fin_r: forall n (f: nat -> bool), 
 (forall i: fin n , f (fin2nat i) = true) -> n_forall n f = true.
Proof with bauto.
 bauto. apply n_forall_eq... destruct H with (nat2fin H0)...
Qed.

(** 证明, 当 n_forall n 返回 true 时, 那么对于 i: fin 时有 f i = true *)
Lemma n_forall_fin_l: forall n (f: nat -> bool), 
 n_forall n f = true -> (forall i: fin n, f (fin2nat i) = true). 
Proof with bauto.
 bauto. apply n_forall_eq with n... apply fin_proof.
Qed.

(** 证明, 当 i: fin 时有 f i = true, 那么对于 n_forall n 返回 true; 反之亦然 *)
Lemma n_forall_fin: forall n (f: nat -> bool), 
 (forall i: fin n , f (fin2nat i) = true) <-> n_forall n f = true.
Proof with bauto.
 bauto. apply n_forall_fin_r... apply n_forall_fin_l...
Qed.

End Fin.

(** ** Notation *)

Notation "F[ H ]":= (nat2fin H).

(** ** Coercion *)

Coercion fin2nat: fin >-> nat.

(** ** Auto *)

#[export] Hint Rewrite fin'_1_elem fin2nat_nat2fin nat2fin_fin2nat: fcore.

#[export] Hint Resolve fin'_0 fin'_0_r fin'_0_l fin'_lt fin'_eq fin_eq' fin_proof fin_le 
fin_lt fin_proof_S fin_proof_SS fin_eq fin_neq fin'_1_unique n_forall_fin: fcore.


(* ######################################################################### *)
(** * Fin Zero Elem *)

Section Fin_0.

(** ** fin_0H *)

(** *** Definitino *)

(** 定义 fin n 的零元素 *)
Definition fin_0H {n: nat} (H: 0 < n): fin n:=
 exist _ 0 H.

(** *** Lemma *)

(** fin_0H 生成的数内部值为 0 *)
Lemma fin_0H_elem: forall n (H: 0 < n), fin2nat (fin_0H H) = 0.
Proof. bauto. Qed.

(** *** Example *)

(** 由H: 0 < n 生成fin 3 的零元素 *)
Example fin_0H_example: fin2nat (fin_0H (Nat.lt_0_succ 2)) = 0.
Proof. auto. Qed.

(** ** fin_0 *)

(** *** Definition *)

(** 定义 fin_0, 返回 fin n 的 Some 零元素(如果存在),否则返回 None *)
Definition fin_0 {n: nat}: option (fin n):=
 match n with
 | 0 => None (* n = 0 时返回 None *)
 | S n' => Some (exist _ 0 (Nat.lt_0_succ n')) (* n > 0 时返回 Some fin0 *)
 end.

(** *** Lemma *)

(** 当 n 大于 0 时, fin0_auto 有返回值,且返回值为 fin_0H *)
Lemma fin_0_H: forall n (H: 0 < n), fin_0 = Some (fin_0H H).
Proof with bauto. destruct n... simpl... apply fin_eq... Qed.

(** *** Example *)

(** 自动生成 fin3 的零元素 *)
Example fin0_example :  match (@fin_0 3) with
 | None => False
 | Some i => fin2nat i = 0
 end.
Proof. simpl. bauto. Qed.

(** ** fin_0S *)

(** *** Definition *)

(** 定义 fin0, 返回 fin (S n) 的零元素 *)
Definition fin_0S {n: nat}: fin (S n):= exist _ 0 (Nat.lt_0_succ n).

(** *** Lemma *)

(** fin0S 生成的数内部值为 0 *)
Lemma fin_0S_elem: forall n , fin2nat (@fin_0S n) = 0.
Proof. bauto. Qed.

(** 对于任意 n, fin0 的返回值与 fin0S 相同 *)
Lemma fin_0_0S: forall n, @fin_0 (S n) = Some fin_0S.
Proof. bauto. Qed.

(** 对于任意 n, fin0S 与fin_0H (H: 0 < S n) 相同 *)
Lemma fin_0S_0H: forall n, fin_0S = fin_0H (Nat.lt_0_succ n).
Proof. bauto. Qed.

(** *** Example *)

(** 自动生存fin 3的零元素 *)
Example fin0S_example: fin 3:= fin_0S.

Goal fin2nat fin0S_example = 0.
Proof. auto. Qed.

End Fin_0.

(** ** Auto *)
#[export] Hint Rewrite fin_0H_elem fin_0_H fin_0S_elem fin_0_0S: fcore.


(* ######################################################################### *)
(** * Fin Last Elem *)

Section Fin_Last.

(** ** fin_lstH *)

(** *** Definition *)

(** 定义 fin n 的末元素 *)
Lemma fin_lstH_aux: forall n, 0 < n -> pred n < n.
Proof. bauto. Qed.

Definition fin_lstH {n: nat} (H: 0 < n): fin n:=
 exist _ (pred n) (fin_lstH_aux H).

(** *** Example *)

(** 由 H: 0 < n 生成 fin 3的末元素 *)
Example fin_lstH_example: fin 3:= fin_lstH (Nat.lt_0_succ 2).

Goal fin2nat fin_lstH_example = 2.
Proof. bauto. Qed.

(** ** fin_lst *)

(** *** Definition *)

(** 定义 fin_lst, 返回 fin n 的 Some 末元素（如果存在）,否则返回 None *)
Definition fin_lst {n: nat}: option (fin n):=
 match n with
 | 0 => None (* n = 0 时返回 None *)
 | S n' => Some (exist _ n' (Nat.lt_succ_diag_r n')) (* n > 0 时返回 Some fin_lst *)
 end.

(** *** Lemma *)

(** 当 n 大于 0 时,fin0_auto 有返回值,且返回值为 fin_lstH *)
Lemma fin_lst_lstH: forall n (H: 0 < n), fin_lst = Some (fin_lstH H).
Proof. intros. destruct n. bauto. simpl. f_equal. apply fin_eq; simpl. auto. Qed.

(** *** Example *)

(** 自动生成 fin3 的零元素 *)
Example fin_lst_example: option (fin 3):= fin_lst.

Goal match fin_lst_example with
 | None => False
 | Some i => fin2nat i = 2
 end.
Proof.  simpl. bauto. Qed.

(** ** fin_lstS *)

(** *** Definition *)

(** 定义 fin_lstS,返回 fin (S n) 的零元素*)
Definition fin_lstS {n: nat}: fin (S n):= exist _ n (Nat.lt_succ_diag_r n).

(** *** Lemma *)

(** 对于任意 n, fin_lst 的返回值与 fin_lstS 相同 *)
Lemma fin_lst_lstS: forall n, @fin_lst (S n) = Some fin_lstS.
Proof. bauto. Qed.

(** 对于任意 n, fin_lstS 与fin_lstH (H: 0 < S n)相同 *)
Lemma fin_lstS_lstH: forall n, fin_lstS = fin_lstH (Nat.lt_0_succ n).
Proof. bauto. apply fin_eq; bauto. Qed.

(** *** Example *)

(** 自动生存fin 3的零元素 *)
Example fin_lstS_example: fin 3:= fin_lstS.

Goal fin2nat fin_lstS_example = 2.
Proof. auto. Qed.

End Fin_Last.

(** ** Notation *)

Notation "'[ i ]":= (@fin_lstS i).

(** ** Auto *)

#[export] Hint Rewrite fin_lst_lstH fin_lst_lstS fin_lstS_lstH: fcore.

(* ######################################################################### *)
(** * Fin Size Operation *)

Section Fin_Size.

(** ** fin2fin *)

(** *** Definition *)

(** 一个数为 fin n 且 n = m, 将其转化为 fin m *)
Definition fin2fin {n m} (i: fin n) (H: m = n): fin m:=
 F[Nat.lt_stepr _ _ _ (fin_proof i) (eq_sym H)].

(** *** Lemma *)

(** 一个数经过 fin2fin 后,其内部值保持不变 *)
Lemma fin2fin_eq: forall n m (i: fin n) (H: m = n), fin2nat (fin2fin i H) = fin2nat i.
Proof. bauto. Qed.

(** 一个数经过 fin2fin 后,其约束值仍小于原值 *)
Lemma fin2fin'_lt: forall n m (i: fin n) (H: m = n), (fin2nat (fin2fin i H)) < n. 
Proof. bauto. apply fin_proof. Qed.

(** *** Example *)

(** 将 fin 3 的实例类型转换为 fin (2 + 1), 其内部值保持不变 *)
Goal fin2nat (fin2fin (fin3_example) (Nat.add_1_r _): fin (2 + 1)) = 2.
Proof. bauto. Qed.

(** ** fin2finS *)

(** *** Definition *)

(** 将 fin n 转换为 fin (S n) *)
Definition fin2finS {n: nat} (i: fin n): fin (S n):=
 exist _ (fin2nat i) (Nat.lt_lt_succ_r _ _ (proj2_sig i)).

(** *** Lemma *)

(** fin2finS 生成的 i' 转换为 nat 仍小于 n *)
Lemma fin2finS'_lt: forall {n} (i: fin n), fin2finS i < n.
Proof. bauto. simpl. apply fin_proof. Qed.

(** 如果 P 对于任意 fin (S n) 的元素成立, 那么对于 fin n 的元素也成立 *)
Lemma fin2finS_P: forall {n} (P: fin (S n) -> Prop),
 (forall i: fin (S n), P i) -> (forall i: fin n, P (fin2finS i)).
Proof. bauto. Qed.

(** 如果 f 对于任意 fin (S n) 的元素返回值均为 v, 那么对于 fin n 的元素也返回 v *)
Lemma fin2finS_f: forall {A n} v (f: fin (S n) -> A),
 (forall i: fin (S n), f i = v) -> (forall i: fin n, f (fin2finS i) = v).
Proof. bauto. Qed.     

(** *** Example *)

(** 将 fin 3 的实例转换为 fin 4 *)
Example fin4_example: fin 4:= fin2finS fin3_example.

Goal fin2nat fin4_example = 2.
Proof. auto. Qed.

(** ** finS2fin *)

(** *** Definition *)

(** 将fin (n + m)转换为 fin n *)
Definition finS2fin {n: nat} {i: fin (S n)} (H: fin2nat i < n): fin n:=
 exist _ (fin2nat i) H.

(** *** Lemma *)

(** 一个数先经过 finS2fin 再经过 fin2finS 依旧为其本身 *)
Lemma fin2finS_finS2fin: forall n (i: fin (S n)) (H: fin2nat i < n),
 fin2finS (finS2fin H) = i.
Proof. bauto. apply fin_eq; bauto. Qed.

(** 一个数先经过 fin2finS 再经过 finS2fin 依旧为其本身 *)
Lemma finS2fin_fin2finS: forall n (i: fin n), @finS2fin n (fin2finS i) (fin_proof i) = i.
Proof. bauto. apply fin_eq; bauto. Qed.

(** ** fin2finSn *)

(** *** Definition *)

(** 将 fin n 转换为 fin (n + m) *)
Definition fin2finSn {n} (m: nat) (i: fin n): fin (n + m):=
 exist _ (fin2nat i) (Nat.lt_lt_add_r _ _ m (fin_proof i)).

(** *** Lemma *)

(** fin2finSn生成的 i' 转换为 nat 仍小于 n *)
Lemma fin2finSn'_lt: forall {n} m (i: fin n), fin2finSn m i < n.
Proof. bauto. simpl. apply fin_proof. Qed.

(** 当一个数 fin2finSn 0 时,其不变 *)
Lemma fin2finSn_0: forall n (i: fin n), fin2finSn 0 i = fin2fin i (Nat.add_0_r _).
Proof. bauto. apply fin_eq; bauto. Qed.

(** 当一个数 fin2finSn 1 时,相当于其 finS *)
Lemma fin2finSn_1: forall n (i: fin n), fin2finSn 1 i = fin2fin (fin2finS i) (Nat.add_1_r _).
Proof. bauto. apply fin_eq; bauto. Qed.

(** 当一个数 fin2finSn 2 时,相当于其 finS 后在 finS *)
Lemma fin2finSn_2: forall n (i: fin n), 
 fin2finSn 2 i = fin2fin (fin2finS (fin2finS i)) (add_2_r _).
Proof. bauto. apply fin_eq; bauto. Qed.

(** 如果 P 对于任意 fin (n + m) 的元素成立, 那么对于 fin n 的元素也成立 *)
Lemma fin2finSn_P: forall {n m} (P: fin (n + m) -> Prop),
 (forall i: fin (n + m), P i) -> (forall i: fin n, P (fin2finSn m i)).
Proof. bauto. Qed.

(** 如果 f 对于任意 fin (n + m) 的元素返回值均为 v, 那么对于 fin n 的元素也返回 v *)
Lemma fin2finSn_f: forall {A n m} v (f: fin (n + m) -> A),
 (forall i: fin (n + m), f i = v) -> (forall i: fin n, f (fin2finSn m i) = v).
Proof. intros. apply (H (fin2finSn m i)). Qed.

(** *** Example *)

(** 对 fin 3 的实例进行 fin2finSn2得到 fin (3 + 2), 其内部值为 2 *)
Goal fin2nat (fin2finSn 2 fin3_example: fin (3 + 2)) = 2.
Proof. auto. Qed.

(** ** finSn2fin *)

(** *** Definition *)

(** 将fin (S n)转换为 fin n *)
Definition finSn2fin {n m: nat} {i: fin (n + m)} (H: fin2nat i < n): fin n:=
 exist _ (fin2nat i) H.

(** *** Lemma *)

(** 一个数先经过 finSn2fin 再经过 fin2finSn 依旧为其本身 *)
Lemma fin2finSn_finSn2fin: forall n m (i: fin (n + m)) (H: fin2nat i < n),
 fin2finSn m (finSn2fin H) = i.
Proof. bauto. apply fin_eq; bauto. Qed.

(** 一个数先经过 fin2finSn 再经过 finSn2fin 依旧为其本身 *)
Lemma finSn2fin_fin2finSn: forall n m (i: fin n), 
 @finSn2fin n m (fin2finSn m i) (fin_proof i) = i.
Proof. bauto. apply fin_eq; bauto. Qed.

End Fin_Size.

(** ** Notation *)

Notation "FF[ i | H ]":= (fin2fin i H).
Notation "FS[ i ]":= (fin2finS i).
Notation "FP[ H ]":= (finS2fin H).
Notation "FSn[ i | n ]":= (fin2finSn n i).
Notation "FPn[ H ]":= (finS2fin H).

(** ** Auto *)

#[export] Hint Rewrite fin2fin_eq fin2finS_finS2fin finS2fin_fin2finS fin2finSn_0 fin2finSn_1 fin2finSn_2
fin2finSn_finSn2fin finSn2fin_fin2finSn: fcore.

#[export] Hint Resolve fin2fin'_lt fin2finS'_lt fin2finS_f fin2finSn'_lt fin2finSn_f: fcore.


(* ######################################################################### *)
(** * Fin Element Operation *)

Section Fin_Elem.

(** ** fin_S *)

(** *** Definition *)

(** 由 i: fin n 构建 S i: fin (S n) *)
Definition fin_S {n: nat} (i: fin n): fin (S n):=
 F[proj1 (Nat.succ_lt_mono i n) (fin_proof i)].

(** *** Lemma *)

(** 由 fin_S 构造出的元素大于零 *)
Lemma fin'_S_lt: forall {n} (i: fin n), 0 < fin2nat (fin_S i).
Proof.
 bauto. simpl. destruct (zerop (fin_S i)); bauto. (* 将目标转为证明 fin_S i = 0 不成立 *)
Qed.

(** 对数 i 先进行 nat2fin 然后 fin_S,新生成的数内部值为 i + 1 *)
Lemma fin'_S_add: forall n i (H: i < n) , fin2nat (fin_S F[H]) = i + 1.
Proof. bauto. simpl. bauto. Qed.

(** 对一个数 fin_S 后,新生成的数内部值等于原内部值 + 1 *)
Lemma fin_S_succ: forall n (i: fin n), fin2nat (fin_S i) = i + 1.
Proof. bauto. simpl. bauto. Qed.

(** 对一个数 fin_S 后,取其内部值 pred 后等于原内部值 *)
Lemma fin_S_pred: forall n (i: fin n), pred (fin_S i) = fin2nat i.
Proof. bauto. Qed.

(** *** Example *)

(** 对内部值为 2 的 fin 3 进行 fin_S 后,生成内部值为 3 的 fin 4 *)
Goal fin2nat (fin_S fin3_example) = 3.
Proof. auto. Qed.

(** ** fin_P *)

(** *** Definition *)

(** 由 i: fin (S n) 构建 pred i: fin n *)
Lemma fin_P_aux: forall {n i}, 0 < i -> i < S n -> pred i < n.
Proof. bauto. Qed.

Definition fin_P {n} (i: fin (S n)) (H: 0 < i): fin n:=
 F[fin_P_aux H (fin_proof i)].

(** *** Lemma *)

(** 对数 i 先进行 nat2fin 然后 fin_P,新生成的数内部值为 i - 1 *)
Lemma fin_P_sub: forall n i (H1: i < (S n)) (H2: 0 < i) , fin2nat (fin_P F[H1] H2) = i - 1.
Proof. bauto. simpl. bauto. Qed.

(** 对一个数 fin_P 后,新生成的数内部值等于原内部值 - 1 *)
Lemma fin_P_pred: forall n (i: fin (S n)) (H: 0 < i), fin2nat (fin_P i H) = fin2nat i - 1.
Proof. bauto. simpl. bauto. Qed.

(** 对一个数 fin_P 后,取其内部值 S 后等于原内部值 *)
Lemma fin_P_s: forall n (i: fin (S n)) (H: 0 < i), S (fin_P i H) = fin2nat i.
Proof. bauto. simpl. bauto. Qed.

(** 一个内部值不为 0 且 0 < n 的 fin n 数先经过 fin_P 再经过 fin_S 依旧为其本身 *)
Lemma fin_S_P: forall n (i: fin (S n)) (H: 0 < i), 
 fin_S (fin_P i H) = i.
Proof. bauto. apply fin_eq; bauto. simpl. bauto. Qed.

(** 一个数先经过 fin_S 再经过 fin_P 依旧为其本身 *)
Lemma fin_P_S: forall n (i: fin n), fin_P (fin_S i) (fin'_S_lt i) = i.
Proof. bauto. apply fin_eq; bauto. Qed.

(** *** Example *)

(** 对内部值为 2 的 fin 3 进行 fin_S 后,生成内部值为 1 的 fin 2 *)
Goal fin2nat (fin_P fin3_example Nat.lt_0_2) = 1.
Proof. auto. Qed.

(** ** fin_Sn *)

(** *** Definition *)

(** 由 i: fin n 构建 i + m: fin (n + m) *)
Definition fin_Sn {n} m (i: fin n): fin (n + m).
Proof.
 destruct i as [x Hi]. apply (exist _ (x + m)). (* 构造 i + m 的证明 *)
 apply Nat.add_lt_mono_r. exact Hi.
Defined.

(** *** Lemma *)

(** 由 fin_Sn m 构造出的元素大于等于m*)
Lemma fin'_Sn_lt: forall {n m} (i: fin n), m <= fin_Sn m i.
Proof.
 intros. replace (fin2nat (fin_Sn m i)) with (i + m).
 bauto. destruct i; bauto.
Qed.

(** 对数 i 先进行 nat2fin 然后 fin_Sn m, 新生成的数内部值为 i + m *)
Lemma fin_Sn_add: forall n i m (H: i < n), fin2nat (fin_Sn m F[H]) = i + m.
Proof. bauto; destruct i; bauto. Qed.

(** 对一个数 fin_Sn m 后,新生成的数内部值等于原内部值 + m *)
Lemma fin_Sn_succ: forall n m (i: fin n), fin2nat (fin_Sn m i) = fin2nat i + m.
Proof. bauto; destruct i; bauto. Qed.

(** 对一个数 fin_Sn m 后,取其内部值 - m 后等于原内部值 *)
Lemma fin_Sn_sub: forall n m (i: fin n), (fin_Sn m i) - m = fin2nat i.
Proof. bauto; destruct i; bauto. simpl. bauto. Qed.

(** 对一个数 fin_Sn 0 后,其值不变 *)
Lemma fin_Sn_0: forall n (i: fin n), fin_Sn 0 i = FF[i | Nat.add_0_r _].
Proof. bauto. apply fin_eq; destruct i; bauto. Qed.

(** 对一个数 fin_Sn 1 后,其值相当于对其 fin_S *)
Lemma fin_Sn_1: forall n (i: fin n), fin_Sn 1 i = FF[(fin_S i) | Nat.add_1_r _].
Proof. bauto. apply fin_eq; destruct i; bauto. simpl. bauto. Qed.

(** 对一个数 fin_Sn 2 后,其值相当于对其 fin_S 后在对其 fin_S *)
Lemma fin_Sn_2: forall n (i: fin n), fin_Sn 2 i = FF[(fin_S (fin_S i)) | add_2_r _].
Proof. bauto. apply fin_eq; destruct i; bauto. simpl. bauto. Qed.

(** *** Example *)

(** 对 fin 3 的实例进行 fin_Sn 2后得到类型为 fin (3 + 2)的数,其内部值为 4 *)
Goal fin2nat (fin_Sn 2 fin3_example: fin (3 + 2)) = 4.
Proof. auto. Qed.

(** ** fin_Pn *)

(** *** Definition *)

(** 由 i: fin (S n) 构建 pred i: fin n *)

Lemma fin_Pn_aux: forall {n m i}, m <= i -> i < n + m -> i - m < n.
Proof. bauto. Qed.

Definition fin_Pn {n m} (i: fin (n + m)) (H: m <= i): fin n:=
 F[fin_Pn_aux H (fin_proof i)].

(** *** Lemma *)

(** 对数 i 先进行 nat2fin 然后 fin_Pn m,新生成的数内部值为 i - m *)
Lemma fin_Pn_sub: forall n m i (H1: i < (n + m)) (H2: m <= i) , 
 fin2nat (fin_Pn F[H1] H2) = i - m.
Proof. bauto. Qed.

(** 对一个数 fin_Pn m 后,新生成的数内部值等于原内部值 - m *)
Lemma fin_Pn_pred: forall n m (i: fin (n + m)) (H: m <= i), 
 fin2nat (fin_Pn i H) = fin2nat i - m.
Proof. bauto. Qed.

(** 对一个数 fin_P 后,取其内部值 + m 后等于原内部值 *)
Lemma fin_Pn_s: forall n m (i: fin (n + m)) (H: m <= i), fin_Pn i H + m = fin2nat i.
Proof. bauto. simpl. bauto. Qed.

(** 一个内部值不为 0 且 m <= n 的 fin n 数先经过 fin_Pn m 再经过 fin_Sn m 依旧为其本身 *)
Lemma fin_Sn_Pn: forall n (i: fin (S n)) (H: 0 < i), 
 fin_S (fin_P i H) = i.
Proof. bauto. apply fin_eq; bauto. simpl. bauto. Qed.

(** 一个数先经过 fin_Sn 再经过 fin_Pn 依旧为其本身 *)
Lemma fin_Pn_Sn: forall n m (i: fin n), fin_Pn (fin_Sn m i) (fin'_Sn_lt i) = i.
Proof. bauto. apply fin_eq; destruct i; simpl. bauto. Qed.

(** 对一个数 fin_Pn 0 后,其值不变 *)
Lemma fin_Pn_0: forall n (i: fin (n + 0)),
 fin_Pn i (le_0_n _) = FF[i | eq_sym (Nat.add_0_r _)].
Proof. bauto. apply fin_eq; destruct i; bauto. simpl. bauto. Qed.

(** 对一个数 fin_Pn 1 后,其值相当于对其 fin_P *)

Lemma fin_Pn_1_aux: forall n, 1 <= n -> 0 < n.
Proof. bauto. Qed.

Lemma fin_Pn_1: forall n (i: fin (n + 1)) (H: 1 <= i), 
 fin_Pn i H = fin_P FF[i | eq_sym (Nat.add_1_r _)] (fin_Pn_1_aux H).
Proof. bauto. apply fin_eq; destruct i; bauto. simpl. bauto. Qed.

(** 对一个数 fin_Pn 2 后,其值相当于对其 fin_P 后在对其 fin_P *)

Lemma fin_Pn_2_aux: forall n, 2 <= n -> 0 < n.
Proof. bauto. Qed.

Lemma fin_Pn_2_aux': forall n, 2 <= n -> 0 < pred n.
Proof. bauto. Qed. 

Lemma fin_Pn_2: forall n (i: fin (n + 2)) (H: 2 <= i), 
 fin_Pn i H = fin_P (fin_P FF[i | eq_sym (add_2_r _)] (fin_Pn_2_aux H)) (fin_Pn_2_aux' H).
Proof. bauto. apply fin_eq; destruct i; bauto. simpl. bauto. Qed.

End Fin_Elem.

(** ** Notation *)

Notation "Fs[ i ]":= (fin_S i).
Notation "Fp[ i | H ]":= (fin_P i H).
Notation "Fsn[ i | m ]":= (fin_Sn m i).
Notation "Fpn[ i | H ]":= (fin_Pn i H).

(** ** Auto *)

#[export] Hint Rewrite fin'_S_add fin_S_succ fin_S_pred fin_P_sub fin_P_pred fin_P_s
fin_S_P fin_P_S fin_Sn_add fin_Sn_succ fin_Sn_sub fin_Sn_0 fin_Sn_1 fin_Sn_2 fin_Pn_sub
fin_Pn_pred fin_Pn_s fin_Sn_Pn fin_Pn_Sn fin_Pn_0 fin_Pn_1 fin_Pn_2: fcore.

#[export] Hint Resolve fin'_S_lt fin'_Sn_lt: fcore.


(* ######################################################################### *)
(** * Fin Fun Operation *)

Section Fin_Fun.

(** *** fin_Pf *)

(** *** Definition *)

(** 定义 fin_Pf, 将 fin (S n) -> A 转变为 fin n -> A *)
Definition fin_Pf {B: Set} {n: nat} (f: fin (S n) -> B): fin n -> B:=
 fun i => f FS[i].

(** *** Lemma *)

(** 对于任意 i: fin n, 其在fin_Pf f 和 FS[i] 在 f 上表现相同 *)
Lemma fin_Pf_eq: forall (B: Set) n (f: fin (S n) -> B) i,
 (fin_Pf f) i = f FS[i].
Proof. bauto. Qed.

(** *** Example *)

(** 对于函数 fun i: fin 4 => fin2nat i 来说, 进行 fin_Pf 后取 '[2] 返回 2 *)
Goal (fin_Pf (fun i: fin 4 => fin2nat i)) '[2] = 2.
Proof. auto. Qed.

(** *** fin_Pnf *)

(** *** Definition *)

(** 定义 fin_Pnf, 将 fin (n + m) -> A 转变为 fin n -> A *)
Definition fin_Pnf {B: Set} {n m: nat} (f: fin (n + m) -> B): fin n -> B:=
 fun i => f FSn[i | m].

(** *** Lemma *)

(** 对于任意 i: fin n, 其在fin_Pf f 和 FS[i] 在 f 上表现相同 *)
Lemma fin_Pnf_eq: forall (B: Set) n m (f: fin (n + m) -> B) i,
 (fin_Pnf f) i = f FSn[i | m].
Proof. bauto. Qed.

(** 对于一个函数 fin_Pnf 0, 其定义域不变 *)
Lemma fin_Pnf_0: forall (B: Set) n (f: fin (n + 0) -> B) i,
 (fin_Pnf f) i = f FF[i | Nat.add_0_r _].
Proof.
 bauto. rewrite fin_Pnf_eq. f_equal. apply fin_eq; bauto.
Qed.

(** 对于一个函数 fin_Pnf 1, 其定义域 - 1 *)
Lemma fin_Pnf_1: forall (B: Set) n (f: fin (n + 1) -> B) i,
 (fin_Pnf f) i = f FF[FS[i] | Nat.add_1_r _].
Proof.
 bauto. rewrite fin_Pnf_eq. f_equal. apply fin_eq; bauto.
Qed.

(** 对于一个函数 fin_Pnf 2, 其定义域 - 2 *)
Lemma fin_Pnf_2: forall (B: Set) n (f: fin (n + 2) -> B) i,
 (fin_Pnf f) i = f FF[FS[FS[i]] | add_2_r _].
Proof.
 bauto. rewrite fin_Pnf_eq. f_equal. apply fin_eq; bauto.
Qed.

(** *** Example *)

(** 对于函数 fun i: fin (3 + 2) => fin2nat i 来说, 进行 fin_Pnf 后取 '[2] 返回 2 *)
Goal (fin_Pnf (fun i: fin (3 + 2) => fin2nat i)) '[2] = 2.
Proof. auto. Qed.

(** ** fin2natf1 *)

(** *** Definition *)

(** 定义 fin2natf1, 将一个 f: fin n -> A 函数转化为 nat -> B *)
Definition fin2natf1 {B: Set} {n} (d: B) (f: fin n -> B): nat -> B:=
 fun (i: nat) => match lt_dec i n with
 | left H => f F[H]
 | right _ => d
 end.

(** *** Lemma *)

(** 当 i < n 时, fin2natf1 取 f F[H] *)
Lemma fin2natf1_Hlt: forall (B: Set) n i d (f: fin n -> B) (H: i < n),
 (fin2natf1 d f) i = f F[H].
Proof with bauto.
 unfold fin2natf1... destruct (lt_dec i n)... f_equal; apply fin_eq...
Qed.

(** 当 ~ (i < n) 时, fin2natf1 取 f F[H] *)
Lemma fin2natf1_Hge: forall (B: Set) n i d (f: fin n -> B),
 ~ (i < n) -> (fin2natf1 d f) i = d.
Proof with bauto.
 unfold fin2natf1... destruct (lt_dec i n)...
Qed.

(** 当输入为 i: fin n时候, fin2natf1 取 f i *)
Lemma fin2natf1_eq: forall (B: Set) n (i: fin n) d (f: fin n -> B),
 (fin2natf1 d f) i = f i.
Proof. 
 bauto. rewrite fin2natf1_Hlt with (H:= fin_proof i). 
 f_equal. apply fin_eq; bauto.
Qed.

(** 化简 fin2natf1 Sn *)
Lemma fin2natf1_Sn: forall (B: Set) n d (f: fin (S n) -> B) ,
 fin2natf1 d f = 
 fun i: nat => if i =? n then f '[n] else fin2natf1 d (fin_Pf f) i.
Proof with bauto.
 bauto. fun_ext. destruct (x =? n) eqn: E; bauto.
 - (* x = n *)
 rewrite fin2natf1_Hlt with (H:= (fin_proof '[n])).
 f_equal. apply fin_eq...
 - destruct (lt_dec x n).
 + (* x < n *)
 rewrite fin2natf1_Hlt with (H:= l).
 assert (x < S n). bauto. rewrite fin2natf1_Hlt with (H:= H).
 rewrite fin_Pf_eq. f_equal. apply fin_eq...
 + (* x > n *)
 rewrite !fin2natf1_Hge...
Qed.

(** 化简 fin2natf1 0 *)
Lemma fin2natf1_0: forall (B: Set) d (f: fin 0 -> B) ,
 fin2natf1 d f = fun x => d.
Proof. bauto. Qed.

(** *** Example *)

(** 对于 fin 3 => 1 经过 fin2natf1 后取 2 返回 1*)
Goal (fin2natf1 0 (fun x: fin 3 => 1)) 2 = 1.
Proof. auto. Qed. 

(** 对于 fin 3 => 1 经过 fin2natf1 后取 3 返回 默认值*)
Goal (fin2natf1 0 (fun x: fin 3 => 1)) 3 = 0.
Proof. auto. Qed.

(** ** fin2natf2 *)

(** *** Definition *)

(** 定义 fin2natf1, 将一个 f: fin n -> B -> B 函数转化为 nat -> B -> B *)
Definition fin2natf2 {B: Set} {n: nat} (f: fin n -> B -> B): nat -> B -> B:=
 fun i x =>
 match lt_dec i n with
 | left H => f F[H] x
 | right _ => x
 end.

(** *** Lemma *)

(** 当 i < n 时, fin2natf2 取 f F[H] *)
Lemma fin2natf2_Hlt: forall (B: Set) n i (f: fin n -> B -> B) (H: i < n),
 (fin2natf2 f) i = f F[H].
Proof with bauto.
 unfold fin2natf2... destruct (lt_dec i n).
 fun_ext. f_equal. apply fin_eq... bauto.
Qed.

(** 当 ~ (i < n) 时, fin2natf2 返回 一个返回自身的函数 *)
Lemma fin2natf2_Hge: forall (B: Set) n (i: nat) (f: fin n -> B -> B),
 ~ (i < n) -> (fin2natf2 f) i = fun x => x.
Proof with bauto.
 unfold fin2natf2... destruct (lt_dec i n)...
Qed.

(** 当输入为 i: fin n时候, fin2natf2 取 f i *)
Lemma fin2natf2_eq: forall (B: Set) n (i: fin n) (f: fin n -> B -> B),
 (fin2natf2 f) i = f i.
Proof.
 bauto. rewrite fin2natf2_Hlt with (H:= fin_proof i). 
 f_equal. apply fin_eq; bauto.
Qed.

(** 化简 fin2natf2 S n *)
Lemma fin2natf2_Sn: forall (B: Set) n (f: fin (S n) -> B -> B),
 fin2natf2 f = fun i => if i =? n then f '[n] else fin2natf2 (fin_Pf f) i.
Proof with bauto.
 bauto. fun_ext. destruct (x =? n) eqn: E...
 - (* x = n *)
 rewrite fin2natf2_Hlt with (H:= (fin_proof '[n])).
 f_equal. apply fin_eq...
 - destruct (lt_dec x n).
 + (* x < n *)
 rewrite fin2natf2_Hlt with (H:= l).
 assert (x < S n). bauto. rewrite fin2natf2_Hlt with (H:= H).
 rewrite fin_Pf_eq. f_equal. apply fin_eq...
 + (* x > n *)
 rewrite !fin2natf2_Hge...
Qed.

(** 化简 fin2natf2 0 *)
Lemma fin2natf2_0: forall (B: Set) (f: fin 0 -> B -> B) ,
 fin2natf2 f = fun i => fun x => x.
Proof. bauto. Qed.

(** *** Example *)

(** 对于 fin 3 => S 经过 fin2natf2 后取 2 返回 S *)
Goal (fin2natf2 (fun x: fin 3 => S)) 2 = S.
Proof. auto. Qed. 

(** 对于 fin 3 => S 经过 fin2natf2 后取 3 返回 一个返回自身的函数*)
Goal (fin2natf2 (fun x: fin 3 => S)) 3 = fun x => x.
Proof. auto. Qed.

(** ** i_reduce *)

(** *** Defnition *)

(** 定义 i_reduce, 对 i: fin n 从 n - 1 到 0 对 val 依次进行 f i *)
Definition i_reduce {B: Set} {n} (f: fin n -> B -> B) (val: B): B:=
 n_reduce (fin2natf2 f) val n. 

(** *** Lemma *)

(** 化简 i_reduce (S n) *)
Lemma i_reduce_Sn: forall (B: Set) n (f: fin (S n) -> B -> B) (val: B),
 i_reduce f val = i_reduce (fin_Pf f) (f '[n] val).
Proof with bauto.
 unfold i_reduce... replace (fin2natf2 f n val) with (f '[ n] val).
 - (* n_reduce (fin2natf2 f) (f '[ n] val) n =
 n_reduce (fin2natf2 (fun i : fin n => f FS[ i])) (f '[ n] val) n *)
 apply n_reduce_eq... rewrite !fin2natf2_Hlt with (H := H).
 assert (i < S n) by bauto. replace i with (fin2nat F[H0]) at 1 by bauto.
 rewrite fin2natf2_eq. rewrite fin_Pf_eq. f_equal. apply fin_eq...
 - (* f '[ n] val = fin2natf2 f n val *)
 rewrite fin2natf2_Sn. replace (n =? n) with true...
Qed.

(** 化简 i_reduce 0 *)
Lemma i_reduce_0: forall (B: Set) (f: fin 0 -> B -> B) (val: B),
 i_reduce f val = val.
Proof. bauto. Qed.

(** 对于 i_reduce 产生结果为 true, 那么初始值也为 true *)
Lemma i_reduce_true: forall {n: nat} (f: fin n -> bool) val,
 i_reduce (fun i y => (y && f i)) val = true -> val = true.
Proof.
 induction n; bauto. (* 排除 n = 0 *)
 rewrite i_reduce_Sn in H. apply IHn in H. bauto.
Qed.

(** 如果两个函数在 0 ~ n - 1 上表现相同, 那么其在 n_reduce n 上返回结果相同 *)
Lemma i_reduce_eq: forall {B: Set} {n} (f f': fin n -> B -> B) val,
 (forall i: fin n , f i = f' i) -> i_reduce f val = i_reduce f' val.
Proof with bauto.
 induction n... rewrite !i_reduce_Sn. 
 replace (f' '[n] val) with (f '[n] val)... apply IHn...
 f_equal; fun_ext; apply H. rewrite H...
Qed.

(** *** Example *)

(** 从 3 到 0 依次对 1 累加等于 7 *)
Goal i_reduce (fun i: fin 4 => (Nat.add i)) 0 = 6. 
Proof. auto. (* 0 + (1 + (2 + (3 + 0)))) = 6 *) Qed.

(** ** i_forall *)

(** *** Definition *)

(** 定义 i_forall, 表示是否对任意 n - 1 到 0 的数 f 均返回 true *)
Definition i_forall {n: nat} (f: fin n -> bool): bool:=
 i_reduce (fun x y => y && f x) true.

(** *** Lemma *)

(** 化简 i_forall (S n) *)
Lemma i_forall_Sn: forall n (f: fin (S n) -> bool),
 i_forall f = f '[n] && i_forall (fin_Pf f).
Proof with bauto.
 unfold i_forall... rewrite i_reduce_Sn. destruct (f '[n])...
 induction n... rewrite i_reduce_Sn. apply IHn.
Qed.

(** 化简 i_forall 0 *)
Lemma i_forall_0: forall (f: fin 0 -> bool),
 i_forall f = true.
Proof. auto. Qed.

(** 证明, 当 i: fin n 时有 f i = true, 那么对于 i_forall n 返回 true *)
Lemma i_forall_r: forall {n} (f: fin n -> bool), 
 (forall i: fin n, f i = true) -> i_forall f = true.
Proof with bauto.
 induction n... rewrite i_forall_Sn... apply IHn...
 rewrite fin_Pf_eq. apply H.
Qed.

(** 证明, 当 i_forall n 返回 true 时, 那么对于 i: fin n 时有 f i = true *)
Lemma i_forall_l: forall {n} (f: fin n -> bool), 
 i_forall f = true -> (forall i: fin n, f i = true). 
Proof with bauto.
 induction n... destruct (fin'_0 i). rewrite i_forall_Sn in H...
 destruct (i =? n) eqn: E...
 - (* i = n *)
 replace i with '[n]... apply fin_eq...
 - (* i <> n *)
 assert (i < n). pose (fin_proof i)...
 replace i with FS[FP[H1]]. rewrite <- fin_Pf_eq...
 apply fin_eq...
Qed.

(** 证明, 当 i: fin n 时有 f i = true, 那么对于 i_forall n 返回 true; 反之亦然 *)
Lemma i_forall_eq: forall {n} (f: fin n -> bool), 
 (forall i: fin n, f i = true) <-> i_forall f = true.
Proof. split. apply i_forall_r. apply i_forall_l. Qed.

(** 证明, 若对 f: fin (n + m) 来说 i_forall 返回 true, 那么对于 f': fin n 来说也返回 true *)
Lemma i_forall_true: forall {n m} (f: fin (n + m) -> bool),
 i_forall f = true -> i_forall (fin_Pnf f) = true.
Proof with bauto.
 bauto. apply i_forall_eq... apply i_forall_l with (i:= FSn[i|m]) in H...
Qed.

(** 证明, 若对于 f': fin n 来说 i_forall 返回 false, 那么对于 f: fin (n + m) 来说返回 false *)
Lemma i_forall_false: forall n m (f: fin (n + m) -> bool),
 i_forall (fin_Pnf f) = false -> i_forall f = false.
Proof.
 bauto. apply not_true_is_false; unfold not; bauto. (* 假设对于 m 来说返回 true *)
 apply i_forall_true in H0. rewrite H in H0; inv H0.
Qed.

(** *** Example *)

(** 对于所有 0 至 3 的数 均小于 5, 该命题正确*)
Goal i_forall (fun x: fin 4 => x <? 5) = true.
Proof. auto. Qed.

(** 对于所有 0 至 3 的数 均小于 3, 该命题错误*)
Goal i_forall (fun x: fin 4 => x <? 3) = false.
Proof. auto. Qed.

End Fin_Fun.

(** ** Auto *)

#[export] Hint Rewrite fin_Pf_eq fin_Pnf_eq fin_Pnf_0 fin_Pnf_1 fin_Pnf_2 fin2natf1_Hlt
fin2natf1_Hge fin2natf1_eq fin2natf1_Sn fin2natf1_0 fin2natf2_Hlt fin2natf2_Hge fin2natf2_eq
fin2natf2_Sn fin2natf2_0 i_reduce_Sn i_reduce_0 i_forall_0: fcore.

#[export] Hint Resolve i_reduce_true i_reduce_eq i_forall_eq i_forall_true
i_forall_false: fcore.


(* ######################################################################### *)
(** * Fin Dimension *)

Section Fin_Dimen.

(** ** fin_2to1d *)

(** *** Definition *)

(** 定义 fin_2to1daux, 将两个数 fin n 与 fin m 代表地址上的二维, 返回地址上的一维 *)
Lemma fin_2to1d_aux: forall m n i j: nat,
 i < m -> j < n -> i * n + j < m * n.
Proof with bauto.
 bauto. apply Nat.lt_le_trans with (m:= i * n + n)...
 replace (i * n + n) with ((i + 1) * n) by bauto.
 apply Nat.mul_le_mono_r...
Qed.

Definition fin_2to1d {m n: nat} (i: fin m) (j: fin n): fin (m * n):=
 let x:= i * n + j in
 let H: x < m * n:= fin_2to1d_aux (fin_proof i) (fin_proof j) in
 exist _ x H.

(** *** Example *)

(** 访问 3*4 的数组的第 2 行第 3 列元素, 就是访问一维的 11 位置 *)
Goal fin2nat (fin_2to1d '[2] '[3]: fin (3 * 4)) = 11.
Proof. auto. Qed.

(** ** fin_1to2d *)

(** *** Definition *)

(** 定义 fin_1to2, 将地址上的一维, 返回将两个数 fin n 与 fin m 代表地址上的二维 *)
Lemma fin_lto2d_aux_Hr: forall {m n} (i: fin (m * (S n))),
 i / (S n) < m.
Proof.
 intros. destruct i; simpl fin2nat. 
 apply Nat.Div0.div_lt_upper_bound; bauto.
Qed.

Lemma fin_lto2d_aux_Hc: forall {m n} (i: fin (m * (S n))),
 i mod (S n) < S n.
Proof.
 intros. destruct i; simpl fin2nat.
 apply Nat.mod_upper_bound; bauto.
Qed.

Definition fin_1to2d {m n: nat}: fin (m * n) -> fin m * fin n:= 
 match n with
 | 0 => fun i: fin (m * 0) => False_rect _ (fin'_0_r i)
 | S n' => fun i: fin (m * (S n')) =>
 let row:= i / (S n') in 
 let col:= i mod (S n') in
 let Hr: row < m:= fin_lto2d_aux_Hr i in
 let Hc: col < S n':= fin_lto2d_aux_Hc i in
 (F[Hr],F[Hc])
 end.

(** *** Lemma *)

(** fin_1to2d 的行向量为 x / n *)
Lemma fin_1to2d_row: forall m n (x: fin (m * n)),
 fin2nat (fst (fin_1to2d x)) = x / n.
Proof with bauto.
 unfold fin_1to2d... destruct n. destruct (fin'_0_r x). simpl...
Qed.

(** fin_1to2d 的行向量为 x mod n *)
Lemma fin_1to2d_col: forall m n (x: fin (m * n)),
 fin2nat (snd (fin_1to2d x)) = x mod n.
Proof with bauto.
 unfold fin_1to2d... destruct n. destruct (fin'_0_r x). simpl...
Qed.

(** 将一维地址先二维化再一维化仍然为该地址本身 *)
Lemma fin_2to1d_1to2d: forall m n (i: fin (m * n)),
 fin_2to1d (fst (fin_1to2d i)) (snd (fin_1to2d i)) = i.
Proof with bauto.
 unfold fin_2to1d; unfold fin_1to2d... apply fin_eq...
 destruct n... destruct (fin'_0_r i)...
 replace (fst (divmod i n 0 n)) with (i / S n) by bauto.
 replace ((n - snd (divmod i n 0 n))) with (i mod S n) by bauto.
 simpl. rewrite Nat.mul_comm. symmetry. apply Nat.div_mod_eq.
Qed.

(** 将二维地址先一维化再二维化仍然为该地址本身 *)
Lemma fin_1to2d_2to1d: forall m n (i: fin m) (j: fin n),
 fin_1to2d (fin_2to1d i j) = (i, j).
Proof with bauto.
 unfold fin_2to1d; unfold fin_1to2d... destruct n. destruct (fin'_0 j). 
 assert (i < m). apply fin_proof. assert (j < S n). apply fin_proof.
 f_equal; apply fin_eq; simpl...
 - (* (i * S n + j) / S n = i *)
 replace (fst (divmod (i * S n + j) n 0 n)) with ((i * S n + j) / S n) by bauto.
 rewrite Nat.div_add_l. rewrite Nat.div_small... bauto.
 - (* (i * S n + j) mod S n = j *)
 replace (n - snd (divmod (i * S n + j) n 0 n)) with ((i * S n + j) mod S n) by auto.
 rewrite Nat.add_comm. rewrite Nat.Div0.mod_add. apply Nat.mod_small...
Qed.

End Fin_Dimen.

(** ** Auto *)
#[export] Hint Rewrite fin_1to2d_row fin_1to2d_col fin_2to1d_1to2d fin_1to2d_2to1d: fcore.
