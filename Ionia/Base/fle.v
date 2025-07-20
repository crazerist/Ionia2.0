Require Import Coq.Logic.ProofIrrelevance.
Require Export base.

Set Implicit Arguments.


(* ######################################################################### *)
(** * Fle *)

Section Fle.

(** ** fle *)

(** *** Definition *)

(* 定义有限域 fle n, 表示小于等于 n 的自然数 *)
Definition fle (n: nat):= { i: nat | i <= n }.

(** *** Lemma *)

(** 如果 n = m, 那么类型 fle n 与 fle m 相同 *)
Lemma fle'_eq: forall n m, n = m -> fle n = fle m.
Proof. bauto. Qed.

(** *** Example *)

(** 定义 fle 3 的一个实例 *)
Example fle3_example: fle 3:= exist _ 2 (Nat.le_succ_diag_r 2).

(** ** fle2nat *)

(** *** Definition *)

(** 将 fle n 转换为 nat *)
Definition fle2nat {n} (i: fle n): nat:=
 match i with
 | exist _ i _ => i 
 end.

(** *** Lemma *)

(** 证明 fle n 中的元素小于等于 n *)
Lemma fle_proof: forall {n} (i: fle n), fle2nat i <= n.
Proof. bauto. destruct i as [i H]. bauto. Qed.

(** 证明若 n <= m, 则 fle n 中的元素小于等于 m *)
Lemma fle_le: forall {n m} (i: fle n), n <= m -> fle2nat i <= m.
Proof. bauto. pose (fle_proof i). bauto. Qed.

(** 证明若 n < m, 则 fle n 中的元素小于 m*)
Lemma fle_lt: forall {n m} (i: fle n), n < m -> fle2nat i < m.
Proof. bauto. pose (fle_proof i). bauto. Qed.

(** 证明 fle n 中的元素小于 S n *)
Lemma fle_proof_S: forall {n} (i: fle n), fle2nat i < S n.
Proof. bauto. pose (fle_proof i). bauto. Qed.

(** 证明对于任意 i: fle n, 有 S i <= S n *)
Lemma fle_proof_SS: forall {n} (i: fle n), S (fle2nat i) <= S n.
Proof. bauto. pose (fle_proof i). bauto. Qed.

(** 证明当两个 fle n 类型数的内部值相等时,这两个数相等; 反之亦然 *)
Lemma fle_eq: forall n (i1 i2: fle n), fle2nat i1 = fle2nat i2 <-> i1 = i2.
Proof with bauto.
 bauto. destruct i1, i2. simpl in H... f_equal...
Qed.

(** 证明当两个 fle n 类型数的内部值相等时,这两个数相等 *)
Lemma fle_eq': forall n (i1 i2: fle n), fle2nat i1 = fle2nat i2 -> i1 = i2.
Proof. intros; apply fle_eq. bauto. Qed.

(** 证明当两个 fle n 类型数的内部值不等时,这两个数不等; 反之亦然*)
Lemma fle_neq: forall n (i1 i2: fle n), fle2nat i1 <> fle2nat i2 <-> i1 <> i2.
Proof with bauto. unfold not... apply H. apply fle_eq... Qed.

(** 证明 fle 0 只含有一个元素 0 *)
Lemma fle'_0_elem: forall (i: fle 0), fle2nat i = 0.
Proof. intros [i Hi]. simpl. bauto. Qed.

(** 证明 fle 0 是唯一的 *)
Lemma fle'_0_unique: forall (i i': fle 0), i = i'.
Proof. bauto. apply fle_eq. rewrite !fle'_0_elem. bauto. Qed.

(** *** Example *)

(** 提取 fle 3 实例中的自然数 *)
Goal fle2nat fle3_example = 2.
Proof. auto. Qed.

(** ** fle_eq_dec *)

(** *** Definition *)

(** fle_eq 的可判定性 *)
Definition fle_eq_dec {n} (x y: fle n): {x = y} + {x <> y}.
Proof with bauto.
 destruct x as [i Hi]. destruct y as [j Hj]. (* 拆分 x y: fle n *)
 destruct (Nat.eq_dec i j) as [Hij | Hij]. (* 根据nat_eq的可判定性分情况讨论 *)
 - (* i = j |- {x = y} *)
 left... f_equal...
 - (* i <> j |- {x <> y} *)
 unfold not; right... inv H...
Defined.

(** ** nat2fle *)

(** *** Defnition *)

(** 将 nat 转换为 fle *)
Definition nat2fle {n i} (H: i <= n): fle n:=
 exist _ i H.

(** *** Lemma *)

(** 一个数先经过 nat2fle 再经过 fle2nat 依旧为其本身 *)
Lemma fle2nat_nat2fle: forall n i (H: i <= n), fle2nat (nat2fle H) = i.
Proof. bauto. Qed.

(** 一个数先经过 fle2nat 再经过 nat2fle 依旧为其本身 *)
Lemma nat2fle_fle2nat: forall n (i: fle n), nat2fle (fle_proof i) = i.
Proof. bauto. apply fle_eq. apply fle2nat_nat2fle. Qed.

(** 证明, 当 i: fle 时有 f i = true, 那么对于 n_forall (S n) 返回 true *)
Lemma n_forall_fle_r: forall n (f: nat -> bool), 
 (forall i: fle n , f (fle2nat i) = true) -> n_forall (S n) f = true.
Proof.
 intros. apply n_forall_eq; bauto. assert (i <= n) by lia.
 destruct H with (nat2fle H1). bauto.
Qed.

(** 证明, 当 n_forall (S n) 返回 true 时, 那么对于 i: fle 时有 f i = true *)
Lemma n_forall_fle_l: forall n (f: nat -> bool), 
 n_forall (S n) f = true -> (forall i: fle n, f (fle2nat i) = true). 
Proof.
 intros. apply n_forall_eq with (S n); auto. apply fle_proof_S.
Qed.

(** 证明, 当 i: fle 时有 f i = true, 那么对于 n_forall (S n) 返回 true; 反之亦然 *)
Lemma n_forall_fle: forall n (f: nat -> bool), 
 (forall i: fle n , f (fle2nat i) = true) <-> n_forall (S n) f = true.
Proof. split. apply n_forall_fle_r. apply n_forall_fle_l. Qed.

End Fle.

(** ** Notation *)

Notation "F'[ H ]":= (nat2fle H).

(** ** Coercion *)

Coercion fle2nat: fle >-> nat.

(** ** Auto *)

#[export] Hint Rewrite fle'_0_elem fle2nat_nat2fle nat2fle_fle2nat: fcore.

#[export] Hint Resolve fle'_eq fle_proof fle_le fle_lt fle_proof_S fle_proof_SS
fle_eq fle_eq' fle_neq fle'_0_unique n_forall_fle: fcore.


(* ######################################################################### *)
(** * Fle Zero Elem *)

Section Fle_Zero.

(** ** fle_0 *)

(** *** Definition *)

(** 定义 fle_0, 返回 fle n 的零元素 *)
Definition fle_0 {n}: fle n:= (exist _ 0 (Nat.le_0_l n)).

(** *** Lemma *)

(** fle0 生成的数内部值为 0 *)
Lemma fle_0_elem: forall n , fle2nat (@fle_0 n) = 0.
Proof. auto. Qed.

(** *** Example *)

(** 自动生成 fle3 的零元素 *)
Goal fle2nat (fle_0: fle 3) = 0.
Proof. auto. Qed.

End Fle_Zero.

(** ** Auto *)

#[export] Hint Rewrite fle_0_elem: fcore.


(* ######################################################################### *)
(** * Fle Last Elem *)

Section Fle_Last.

(** ** fle_lst *)

(** *** Definition *)

(** 定义 fleN, 返回 fle n 的末元素 *)
Definition fle_lst {n}: fle n:= (exist _ n (le_n n)).

(** *** Lemma *)

(** fle_lst 生成的数内部值为 n *)
Lemma fle_lst_elem: forall n , fle2nat (@fle_lst n) = n.
Proof. bauto. Qed.

(** 自动生成 fle3 的末元素 *)
Goal fle2nat (fle_lst: fle 3) = 3.
Proof. bauto. Qed.

End Fle_Last.

(** ** Notation *)

Notation " '{ n } ":= (@fle_lst n).

(** ** Auto *)

#[export] Hint Rewrite fle_lst_elem: fcore.


(* ######################################################################### *)
(** * Fle Size Operation *)

Section Fle_Size.

(** ** fle2fle *)

(** *** Definition *)

(** 一个数为 fle n 且 n = m, 将其转化为 fle m *)
Lemma fle2fle_aux: forall a b c, a <= b -> b = c -> a <= c.
Proof. bauto. Qed.

Definition fle2fle {n m} (i: fle n) (H: m = n): fle m:=
 F'[fle2fle_aux (fle_proof i) (eq_sym H)].

(** *** Lemma *)

(** 一个数经过 fle2fle 后,其内部值保持不变 *)
Lemma fle2fle_eq: forall n m (i: fle n) (H: m = n), fle2nat (fle2fle i H) = fle2nat i.
Proof. intros. simpl; auto. Qed.

(** *** Example *)

(** 将 fle 3 的实例类型转换为 fle (2 + 1), 其内部值保持不变 *)
Goal fle2nat (fle2fle (fle3_example) (Nat.add_1_r _): fle (2 + 1)) = 2.
Proof. auto. Qed.

(** ** fle2fleS *)

(** *** Definition *)

(** 将 fle n 转换为 fle (S n) *)
Definition fle2fleS {n} (i: fle n): fle (S n):=
 exist _ (fle2nat i) (Nat.le_le_succ_r _ _ (proj2_sig i)).

(** *** Lemma *)

(** fle2fleS 生成的 i' 转换为 nat 仍小于等于 n *)
Lemma fle2fleS_le: forall {n} (i: fle n), fle2fleS i <= n.
Proof. bauto. pose proof (fle_proof i); bauto. Qed.

(** 如果 P 对于任意 fle (S n) 的元素成立, 那么对于 fle n 的元素也成立 *)
Lemma fle2fleS_P: forall {n} (P: fle (S n) -> Prop),
 (forall i: fle (S n), P i) -> (forall i: fle n, P (fle2fleS i)).
Proof. intros. apply (H (fle2fleS i)). Qed.

(** 如果 f 对于任意 fle (S n) 的元素返回值均为 v, 那么对于 fle n 的元素也返回 v *)
Lemma fle2fleS_f: forall {A n} v (f: fle (S n) -> A),
 (forall i: fle (S n), f i = v) -> (forall i: fle n, f (fle2fleS i) = v).
Proof. intros. apply (H (fle2fleS i)). Qed.

(** *** Example *)

(** 将 fle 3 的实例转换为 fle 4 *)
Example fle4_example: fle 4:= fle2fleS fle3_example.

Goal fle2nat fle4_example = 2.
Proof. auto. Qed.

(** ** fleS2fle *)

(** *** Definition *)

(** 将fle (S n)转换为 fle n *)
Definition fleS2fle {n} {i: fle (S n)} (H: fle2nat i <= n): fle n:=
 exist _ (fle2nat i) H.

(** *** Lemma *)

(** 一个数先经过 fleS2fle 再经过 fle2fleS 依旧为其本身 *)
Lemma fle2fleS_fleS2fle: forall n (i: fle (S n)) (H: fle2nat i <= n),
 fle2fleS (fleS2fle H) = i.
Proof. bauto. apply fle_eq; bauto. Qed.

(** 一个数先经过 fle2fleS 再经过 fleS2fle 依旧为其本身 *)
Lemma fleS2fle_fle2fleS: forall n (i: fle n), @fleS2fle n (fle2fleS i) (fle_proof i) = i.
Proof. bauto. apply fle_eq; bauto. Qed.

(** ** fle2fleSn *)

(** *** Definition *)

(** 将 fle n 转换为 fle (n + m) *)

Lemma fle2fleSn_aux: forall a b c, a <= b -> a <= b + c.
Proof. bauto. Qed.

Definition fle2fleSn {n} (m: nat) (i: fle n): fle (n + m):=
 exist _ (fle2nat i) (@fle2fleSn_aux _ _ m (fle_proof i)).

(** *** Lemma *)

(** fle2fleSn 生成的 i' 转换为 nat 仍小于等于 n *)
Lemma fle2fleSn_lt: forall {n} m (i: fle n), fle2fleSn m i <= n.
Proof. bauto; simpl. apply fle_proof. Qed.

(** 当一个数 fle2fleSn 0 时,其不变 *)
Lemma fle2fleSn_0: forall n (i: fle n), fle2fleSn 0 i = fle2fle i (Nat.add_0_r _).
Proof. bauto. apply fle_eq; bauto. Qed.

(** 当一个数 fle2fleSn 1 时,相当于其 fleS *)
Lemma fle2fleSn_1: forall n (i: fle n), fle2fleSn 1 i = fle2fle (fle2fleS i) (Nat.add_1_r _).
Proof. bauto. apply fle_eq; bauto. Qed.

(** 当一个数 fle2fleSn 2 时,相当于其 fleS 后在 fleS *)
Lemma fle2fleSn_2: forall n (i: fle n), 
 fle2fleSn 2 i = fle2fle (fle2fleS (fle2fleS i)) (add_2_r _).
Proof. bauto. apply fle_eq; bauto. Qed.

(** 如果 P 对于任意 fle (n + m) 的元素成立, 那么对于 fle n 的元素也成立 *)
Lemma fle2fleSn_P: forall {n m} (P: fle (n + m) -> Prop),
 (forall i: fle (n + m), P i) -> (forall i: fle n, P (fle2fleSn m i)).
Proof. bauto. Qed.

(** 如果 f 对于任意 fle (n + m) 的元素返回值均为 v, 那么对于 fle n 的元素也返回 v *)
Lemma fle2fleSn_f: forall {A n m} v (f: fle (n + m) -> A),
 (forall i: fle (n + m), f i = v) -> (forall i: fle n, f (fle2fleSn m i) = v).
Proof. bauto. Qed.

(** *** Example *)

(** 对 fle 3 的实例进行 fle2fleSn2得到 fle (3 + 2), 其内部值为 2 *)
Goal fle2nat (fle2fleSn 2 fle3_example: fle (3 + 2)) = 2.
Proof. auto. Qed.

(** ** fleSn2fle *)

(** *** Definition *)

(** 将fle (n + m)转换为 fle n *)
Definition fleSn2fle {n m} {i: fle (n + m)} (H: fle2nat i <= n): fle n:=
 exist _ (fle2nat i) H.

(** *** Lemma *)

(** 一个数先经过 fleSn2fle 再经过 fle2fleSn 依旧为其本身 *)
Lemma fle2fleSn_fleSn2fle: forall n m (i: fle (n + m)) (H: fle2nat i <= n),
 fle2fleSn m (fleSn2fle H) = i.
Proof. bauto. apply fle_eq; bauto. Qed.

(** 一个数先经过 fle2fleSn 再经过 fleSn2fle 依旧为其本身 *)
Lemma fleSn2fle_fle2fleSn: forall n m (i: fle n), 
 @fleSn2fle n m (fle2fleSn m i) (fle_proof i) = i.
Proof. bauto. apply fle_eq; bauto. Qed.

End Fle_Size.

(** ** Notation *)

Notation "F'F[ i | H ]":= (fle2fle i H).
Notation "F'S[ i ]":= (fle2fleS i).
Notation "F'P[ H ]":= (fleS2fle H).
Notation "F'Sn[ i | n ]":= (fle2fleSn n i).
Notation "F'Pn[ H ]":= (fleS2fle H).

(** ** Auto *)

#[export] Hint Rewrite fle2fle_eq fle2fleS_fleS2fle fleS2fle_fle2fleS fle2fleSn_0
fle2fleSn_1 fle2fleSn_2 fle2fleSn_fleSn2fle fleSn2fle_fle2fleSn: fcore.

#[export] Hint Resolve fle2fleS_le fle2fleS_f fle2fleSn_lt fle2fleSn_f: fcore.


(* ######################################################################### *)
(** * Fle Element Operation *)

Section Fle_Elem.

(** ** fle_S *)

(** *** Definition *)

(** 由 i: fle n 构建 S i: fle (S n) *)
Definition fle_S {n } (i: fle n): fle (S n):=
 F'[proj1 (Nat.succ_le_mono i n) (fle_proof i)].

(** *** Lemma *)

(** 由 fle_S 构造出的元素大于零 *)
Lemma fle_S_lt: forall {n} (i: fle n), 0 < fle2nat (fle_S i).
Proof. bauto. destruct (zerop (fle_S i)); bauto. simpl in e. bauto. Qed.

(** 对数 i 先进行 nat2fle 然后 fle_S,新生成的数内部值为 i + 1 *)
Lemma fle_S_add: forall n i (H: i <= n) , fle2nat (fle_S F'[H]) = i + 1.
Proof. bauto; simpl. bauto. Qed.

(** 对一个数 fle_S 后,新生成的数内部值等于原内部值 + 1 *)
Lemma fle_S_succ: forall n (i: fle n), fle2nat (fle_S i) = i + 1.
Proof. bauto; simpl. bauto. Qed.

(** 对一个数 fle_S 后,取其内部值 pred 后等于原内部值 *)
Lemma fle_S_pred: forall n (i: fle n), pred (fle_S i) = fle2nat i.
Proof. bauto. Qed.

(** *** Example *)

(** 对内部值为 2 的 fle 3 进行 fle_S 后,生成内部值为 3 的 fle 4 *)
Goal fle2nat (fle_S fle3_example) = 3.
Proof. auto. Qed.

(** ** fle_P *)

(** *** Definition *)

(** 由 i: fle (S n) 构建 pred i: fle n *)
Lemma fle_P_aux: forall {n i}, i <= S n -> pred i <= n.
Proof. lia. Qed.

Definition fle_P {n} (i: fle (S n)): fle n:=
 F'[fle_P_aux (fle_proof i)].

(** *** Lemma *)

(** 对数 i 先进行 nat2fle 然后 fle_P,新生成的数内部值为 i - 1 *)
Lemma fle_P_sub: forall n i (H1: i <= (S n)) , fle2nat (fle_P F'[H1]) = i - 1.
Proof. bauto; simpl. bauto. Qed.

(** 对一个数 fle_P 后,新生成的数内部值等于原内部值 - 1 *)
Lemma fle_P_pred: forall n (i: fle (S n)), fle2nat (fle_P i) = fle2nat i - 1.
Proof. bauto; simpl. bauto. Qed.

(** 对一个内部值不为 0 的数 fle_P 后,取其内部值 S 后等于原内部值 *)
Lemma fle_P_s: forall n (i: fle (S n)), fle2nat i <> 0 -> S (fle_P i) = fle2nat i.
Proof. bauto. simpl. bauto. Qed.

(** 一个内部值不为 0 且 0 < n 的 fle n 数先经过 fle_P 再经过 fle_S 依旧为其本身 *)
Lemma fle_S_P: forall n (i: fle (S n)), fle2nat i <> 0 -> fle_S (fle_P i) = i.
Proof. bauto. apply fle_eq; simpl. bauto. Qed.

(** 一个数先经过 fle_S 再经过 fle_P 依旧为其本身 *)
Lemma fle_P_S: forall n (i: fle n), fle_P (fle_S i) = i.
Proof. bauto. apply fle_eq; simpl. bauto. Qed.

(** *** Example *)

(** 对内部值为 2 的 fle 3 进行 fle_S 后,生成内部值为 1 的 fle 2 *)
Goal fle2nat (fle_P fle3_example) = 1.
Proof. auto. Qed.

(** ** fle_Sn *)

(** *** Definition *)

(** 由 i: fle n 构建 i + m: fle (n + m) *)
Definition fle_Sn {n} m (i: fle n): fle (n+m).
Proof.
 destruct i as [x Hi]. apply (exist _ (x + m)). (* 构造 i + m 的证明 *)
 apply Nat.add_le_mono_r. exact Hi.
Defined.

(** *** Lemma *)

(** 由 fle_Sn m 构造出的元素大于等于m*)
Lemma fle_Sn_lt: forall {n} m (i: fle n), m <= fle_Sn m i.
Proof. 
 bauto. replace (fle2nat (fle_Sn m i)) with (i + m); bauto.
 destruct i; simpl; bauto.
Qed.

(** 对数 i 先进行 nat2fle 然后 fle_Sn m, 新生成的数内部值为 i + m *)
Lemma fle_Sn_add: forall n m i (H: i <= n), fle2nat (fle_Sn m F'[H]) = i + m.
Proof. bauto; destruct i; bauto. Qed.

(** 对一个数 fle_Sn m 后,新生成的数内部值等于原内部值 + m *)
Lemma fle_Sn_succ: forall n m (i: fle n), fle2nat (fle_Sn m i) = fle2nat i + m.
Proof. bauto; destruct i; bauto. Qed.

(** 对一个数 fle_Sn m 后,取其内部值 - m 后等于原内部值 *)
Lemma fle_Sn_sub: forall n m (i: fle n), (fle_Sn m i) - m = fle2nat i.
Proof. bauto; destruct i; simpl. bauto. Qed.

(** 对一个数 fle_Sn 0 后,其值不变 *)
Lemma fle_Sn_0: forall n (i: fle n), fle_Sn 0 i = F'F[i | Nat.add_0_r _].
Proof. bauto. apply fle_eq; destruct i; bauto. Qed.

(** 对一个数 fle_Sn 1 后,其值相当于对其 fle_S *)
Lemma fle_Sn_1: forall n (i: fle n), fle_Sn 1 i = F'F[(fle_S i) | Nat.add_1_r _].
Proof. bauto. apply fle_eq; destruct i; simpl; bauto. Qed.

(** 对一个数 fle_Sn 2 后,其值相当于对其 fle_S 后在对其 fle_S *)
Lemma fle_Sn_2: forall n (i: fle n), fle_Sn 2 i = F'F[(fle_S (fle_S i)) | add_2_r _].
Proof. bauto. apply fle_eq; destruct i; simpl; bauto. Qed.

(** *** Example *)

(** 对 fle 3 的实例进行 fle_Sn 2后得到类型为 fle (3 + 2)的数,其内部值为 4 *)
Goal fle2nat (fle_Sn 2 fle3_example: fle (3 + 2)) = 4.
Proof. auto. Qed.

(** ** fle_Pn *)

(** *** Definition *)

(** 由 i: fle (S n) 构建 pred i: fle n *)

Lemma fle_Pn_aux: forall {n m i}, m <= i -> i <= n + m -> i - m <= n.
Proof. lia. Qed.

Definition fle_Pn {n m} (i: fle (n + m)) (H: m <= i): fle n:=
 F'[fle_Pn_aux H (fle_proof i)].

(** *** Lemma *)

(** 对数 i 先进行 nat2fle 然后 fle_Pn m,新生成的数内部值为 i - m *)
Lemma fle_Pn_sub: forall n m i (H1: i <= (n + m)) (H2: m <= i) , 
 fle2nat (fle_Pn F'[H1] H2) = i - m.
Proof. bauto. Qed.

(** 对一个数 fle_Pn m 后,新生成的数内部值等于原内部值 - m *)
Lemma fle_Pn_pred: forall n m (i: fle (n + m)) (H: m <= i), 
 fle2nat (fle_Pn i H) = fle2nat i - m.
Proof. bauto. Qed.

(** 对一个数 fle_Pn 后,取其内部值 + m 后等于原内部值 *)
Lemma fle_Pn_add: forall n m (i: fle (n + m)) (H: m <= i), fle_Pn i H + m = fle2nat i.
Proof. bauto. simpl. bauto. Qed.

(** 一个内部值不为 0 且 m <= n 的 fle n 数先经过 fle_Pn m 再经过 fle_Sn m 依旧为其本身 *)
Lemma fle_Sn_Pn: forall n m (i: fle (n + m)) (H: m <= i),
 fle_Sn m (fle_Pn i H) = i.
Proof. bauto. apply fle_eq; destruct i; simpl. simpl in H; bauto. Qed.

(** 一个数先经过 fle_Sn 再经过 fle_Pn 依旧为其本身 *)
Lemma fle_Pn_Sn: forall n m (i: fle n), fle_Pn (fle_Sn m i) (fle_Sn_lt m i) = i.
Proof. bauto. apply fle_eq; destruct i; simpl. bauto. Qed.

(** 对一个数 fle_Pn 0 后,其值不变 *)
Lemma fle_Pn_0: forall n (i: fle (n + 0)),
 fle_Pn i (le_0_n _) = F'F[i | eq_sym (Nat.add_0_r _)].
Proof. bauto. apply fle_eq; destruct i; simpl. bauto. Qed.

(** 对一个数 fle_Pn 1 后,其值相当于对其 fle_P *)

Lemma fle_Pn_1_aux: forall n, 1 <= n -> 0 < n.
Proof. bauto. Qed.

Lemma fle_Pn_1: forall n (i: fle (n + 1)) (H: 1 <= i), 
 fle_Pn i H = fle_P F'F[i | eq_sym (Nat.add_1_r _)].
Proof. bauto. apply fle_eq; destruct i; simpl. bauto. Qed.

Lemma fle_Pn_2_aux: forall n, 2 <= n -> 0 < n.
Proof. bauto. Qed.

Lemma fle_Pn_2_aux': forall n, 2 <= n -> 0 < pred n.
Proof. bauto. Qed. 

(** 对一个数 fle_Pn 2 后,其值相当于对其 fle_P 后在对其 fle_P *)
Lemma fle_Pn_2: forall n (i: fle (n + 2)) (H: 2 <= i), 
 fle_Pn i H = fle_P (fle_P F'F[i | eq_sym (add_2_r _)]).
Proof. bauto. apply fle_eq; destruct i; simpl. bauto. Qed.

End Fle_Elem.

(** ** Notation *)

Notation "F's[ i ]":= (fle_S i).
Notation "F'p[ i | H ]":= (fle_P i H).
Notation "F'sn[ i | m ]":= (fle_Sn m i).
Notation "F'pn[ i | H ]":= (fle_Pn i H).

(** ** Auto *)

#[export] Hint Rewrite fle_S_add fle_S_succ fle_S_pred fle_P_sub fle_P_pred 
fle_P_s fle_S_P fle_P_S fle_Sn_add fle_Sn_add fle_Sn_succ fle_Sn_sub fle_Pn_sub
fle_Sn_0 fle_Sn_1 fle_Sn_2 fle_Pn_pred fle_Pn_add fle_Sn_Pn fle_Pn_Sn
fle_Pn_0 fle_Pn_1 fle_Pn_2: fcore.

#[export] Hint Resolve fle_S_lt fle_Sn_lt: fcore.


(* ######################################################################### *)
(** * Fle Fun Operation *)

Section Fle_Fun.

(** *** fle_Pf *)

(** *** Definition *)

(** 定义 fle_Pf, 将 fle (S n) -> A 转变为 fle n -> A *)
Definition fle_Pf {B: Set} n (f: fle (S n) -> B): fle n -> B:=
 fun i => f F'S[i].

(** *** Lemma *)

(** 对于任意 i: fle n, 其在fle_Pf f 和 F'S[i] 在 f 上表现相同 *)
Lemma fle_Pf_eq: forall (B: Set) n (f: fle (S n) -> B) i, (fle_Pf f) i = f F'S[i].
Proof. bauto. Qed.

(** *** Example *)

(** 对于函数 fun i: fle 3 => fle2nat i 来说, 进行 fle_Pf 后取 '{2} 返回 2 *)
Goal (fle_Pf (fun i: fle 3 => fle2nat i)) '{2} = 2.
Proof. auto. Qed.

(** *** fle_Pnf *)

(** *** Definition *)

(** 定义 fle_Pnf, 将 fle (n + m) -> A 转变为 fle n -> A *)
Definition fle_Pnf {B: Set} {n m} (f: fle (n + m) -> B): fle n -> B:=
 fun i => f F'Sn[i | m].

(** *** Lemma *)

(** 对于任意 i: fle n, 其在fle_Pf f 和 FS[i] 在 f 上表现相同 *)
Lemma fle_Pnf_eq: forall (B: Set) n m (f: fle (n + m) -> B) i,
 (fle_Pnf f) i = f F'Sn[i | m].
Proof. bauto. Qed.

(** 对于一个函数 fle_Pnf 0, 其定义域不变 *)
Lemma fle_Pnf_0: forall (B: Set) n (f: fle (n + 0) -> B) i,
 (fle_Pnf f) i = f F'F[i | Nat.add_0_r _].
Proof. bauto. rewrite fle_Pnf_eq. f_equal. apply fle_eq; bauto. Qed.

(** 对于一个函数 fle_Pnf 1, 其定义域 - 1 *)
Lemma fle_Pnf_1: forall (B: Set) n (f: fle (n + 1) -> B) i,
 (fle_Pnf f) i = f F'F[F'S[i] | Nat.add_1_r _].
Proof. bauto. rewrite fle_Pnf_eq. f_equal. apply fle_eq; bauto. Qed.

(** 对于一个函数 fle_Pnf 2, 其定义域 - 2 *)
Lemma fle_Pnf_2: forall (B: Set) n (f: fle (n + 2) -> B) i,
 (fle_Pnf f) i = f F'F[F'S[F'S[i]] | add_2_r _].
Proof. bauto. rewrite fle_Pnf_eq. f_equal. apply fle_eq; bauto. Qed.

(** *** Example *)

(** 对于函数 fun i: fle (3 + 2) => fle2nat i 来说, 进行 fle_Pnf 后取 '{2} 返回 2 *)
Goal (fle_Pnf (fun i: fle (2 + 2) => fle2nat i)) '{2} = 2.
Proof. auto. Qed.

(** ** fle2natf1 *)

(** *** Definition *)

(** 定义 fle2natf1, 将一个 f: fle n -> A 函数转化为 nat -> B *)
Definition fle2natf1 {B: Set} {n} (d: B) (f: fle n -> B): nat -> B:=
 fun (i: nat) => match le_dec i n with
 | left H => f F'[H]
 | right _ => d
 end.

(** *** Lemma *)

(** 当 i <= n 时, fle2natf1 取 f F'[H] *)
Lemma fle2natf1_eq: forall (B: Set) n i d (f: fle n -> B) (H: i <= n),
 (fle2natf1 d f) i = f F'[H].
Proof.
 bauto. unfold fle2natf1. destruct (le_dec i n); bauto.
 f_equal. apply fle_eq; bauto.
Qed.

(** 当 ~ (i <= n) 时, fle2natf1 取 f F'[H] *)
Lemma fle2natf1_beyond: forall (B: Set) n i d (f: fle n -> B),
 ~ (i <= n) -> (fle2natf1 d f) i = d.
Proof.
  bauto. unfold fle2natf1. destruct (le_dec i n); bauto.
Qed.

(** 当输入为 i: fle n时候, fle2natf1 取 f i *)
Lemma fle2natf1_fle: forall (B: Set) n (i: fle n) d (f: fle n -> B),
 (fle2natf1 d f) i = f i.
Proof.
 bauto. rewrite fle2natf1_eq with (H:= fle_proof i).
 f_equal; apply fle_eq; bauto.
Qed.

(** 化简 fle2natf1 Sn *)
Lemma fle2natf1_Sn: forall (B: Set) n d (f: fle (S n) -> B) ,
 fle2natf1 d f = 
 fun i: nat => if i =? S n then f '{S n} else fle2natf1 d (fle_Pf f) i.
Proof with bauto.
 bauto. fun_ext. destruct (x =? S n) eqn: E...
 - (* x = S n *)
 apply fle2natf1_eq.
 - destruct (le_dec x n).
 + (* x <= n *)
  rewrite fle2natf1_eq with (H:= l).
  assert (x <= S n) by bauto. rewrite fle2natf1_eq with (H:= H).
  rewrite fle_Pf_eq. f_equal. apply fle_eq...
 + (* x > n *)
  rewrite !fle2natf1_beyond...
Qed.

(** 化简 fle2natf1 0 *)
Lemma fle2natf1_0: forall (B: Set) d (f: fle 0 -> B) ,
 fle2natf1 d f = fun x => if x =? 0 then f '{0} else d.
Proof with bauto.
 bauto. fun_ext. destruct (x =? 0) eqn: E...
 - (* x = 0 *) 
 assert (0 <= 0) by bauto. rewrite fle2natf1_eq with (H:= H).
 f_equal. apply fle_eq...
 - (* x <> 0 *)
 apply fle2natf1_beyond. lia.
Qed.

(** *** Example *)

(** 对于 fle 3 => 1 经过 fle2natf1 后取 3 返回 1*)
Goal (fle2natf1 0 (fun x: fle 3 => 1)) 3 = 1.
Proof. auto. Qed.

(** 对于 fle 3 => 1 经过 fle2natf1 后取 3 返回 默认值*)
Goal (fle2natf1 0 (fun x: fle 3 => 1)) 4 = 0.
Proof. auto. Qed.

(** ** fle2natf2 *)

(** *** Definition *)

(** 定义 fle2natf1, 将一个 f: fle n -> B -> B 函数转化为 nat -> B -> B *)
Definition fle2natf2 {B: Set} {n} (f: fle n -> B -> B): nat -> B -> B:=
 fun i x =>
 match le_dec i n with
 | left H => f F'[H] x
 | right _ => x
 end.

(** *** Lemma *)

(** 当 i <= n 时, fle2natf2 取 f F[H] *)
Lemma fle2natf2_eq: forall (B: Set) n i (f: fle n -> B -> B) (H: i <= n),
 (fle2natf2 f) i = f F'[H].
Proof with bauto.
 unfold fle2natf2... destruct (le_dec i n)...
 fun_ext; f_equal. apply fle_eq...
Qed.

(** 当 ~ (i <= n) 时, fle2natf2 返回 一个返回自身的函数 *)
Lemma fle2natf2_beyond: forall (B: Set) n i (f: fle n -> B -> B),
 ~ (i <= n) -> (fle2natf2 f) i = fun x => x.
Proof. bauto. unfold fle2natf2. destruct (le_dec i n); tauto. Qed.

(** 当输入为 i: fle n时候, fle2natf2 取 f i *)
Lemma fle2natf2_fle: forall (B: Set) n (i: fle n) (f: fle n -> B -> B),
 (fle2natf2 f) i = f i.
Proof. 
 bauto. rewrite fle2natf2_eq with (H:= fle_proof i). 
 f_equal. apply fle_eq; bauto.
Qed.

(** 化简 fle2natf2 S n *)
Lemma fle2natf2_Sn: forall (B: Set) n (f: fle (S n) -> B -> B),
 fle2natf2 f = fun i => if i =? S n then f '{S n} else fle2natf2 (fle_Pf f) i.
Proof with bauto.
 bauto. fun_ext. destruct (x =? S n) eqn: E...
 - (* x = S n *)
 assert (S n <= S n) by bauto. rewrite fle2natf2_eq with (H:= H).
 f_equal. apply fle_eq...
 - destruct (le_dec x n).
 + (* x <= n *)
  rewrite fle2natf2_eq with (H:= l).
  assert (x <= S n) by bauto. rewrite fle2natf2_eq with (H:= H).
  rewrite fle_Pf_eq. f_equal. apply fle_eq...
 + (* ~ (x <= n) *)
  rewrite !fle2natf2_beyond...
Qed.

(** 化简 fle2natf2 0 *)
Lemma fle2natf2_0: forall (B: Set) (f: fle 0 -> B -> B) ,
 fle2natf2 f = fun i => if i =? 0 then f '{0} else fun x => x.
Proof with bauto.
 bauto. fun_ext. destruct (x =? 0) eqn: E...
 - (* x = 0 *) 
 assert (0 <= 0) by bauto. rewrite fle2natf2_eq with (H:= H).
 f_equal. apply fle_eq...
 - (* x <> 0 *)
 apply fle2natf2_beyond...
Qed.

(** *** Example *)

(** 对于 fle 3 => S 经过 fle2natf2 后取 3 返回 S *)
Goal (fle2natf2 (fun x: fle 3 => S)) 3 = S.
Proof. auto. Qed. 

(** 对于 fle 3 => S 经过 fle2natf2 后取 4 返回 一个返回自身的函数*)
Goal (fle2natf2 (fun x: fle 3 => S)) 4 = fun x => x.
Proof. auto. Qed.

(** ** e_reduce *)

(** *** Defnition *)

(** 定义 e_reduce, 对 i: fle n 从 n 到 0 对 val 依次进行 f i *)
Definition e_reduce {B: Set} {n} (f: fle n -> B -> B) (val: B): B:=
 n_reduce (fle2natf2 f) val (S n). 

(** *** Lemma *)

(** 化简 e_reduce (S n) *)
Lemma e_reduce_Sn: forall (B: Set) n (f: fle (S n) -> B -> B) (val: B),
 e_reduce f val = e_reduce (fle_Pf f) (f '{S n} val).
Proof with bauto.
 intros; unfold e_reduce. rewrite n_reduce_Sn. 
 replace (fle2natf2 f (S n) val) with (f '{ S n} val).
 - (* n_reduce (fle2natf2 f) (f '{ S n} val) (S n) =
  n_reduce (fle2natf2 (fun i: fle n => f F'S[ i])) (f '{ S n} val) (S n) *)
 apply n_reduce_eq... assert (i <= n)...
 replace i with (fle2nat F'[H0]) at 2 by bauto.
 assert (i <= S n)... replace i with (fle2nat F'[H1]) at 1 by bauto.
 rewrite !fle2natf2_fle. rewrite fle_Pf_eq. f_equal. apply fle_eq...
 - (* f '{ S n} val = fle2natf2 f (S n) val *)
 rewrite fle2natf2_Sn. replace (S n =? S n) with true by bauto...
Qed.

(** 化简 e_reduce 0 *)
Lemma e_reduce_0: forall (B: Set) (f: fle 0 -> B -> B) (val: B),
 e_reduce f val = f '{0} val.
Proof. 
 intros. unfold e_reduce. simpl. rewrite fle2natf2_0.
 replace (0 =? 0) with true; bauto.
Qed.

(** 对于 e_reduce 产生结果为 true, 那么初始值也为 true *)
Lemma e_reduce_true: forall {n} (f: fle n -> bool) val,
 e_reduce (fun x y => (y && f x)) val = true -> val = true.
Proof.
 induction n; bauto.
 - (* n = 0 *)
 unfold e_reduce in H. simpl in H. rewrite fle2natf2_0 in H.
 replace (0 =? 0) with true in H; bauto.
 - (* n <> 0 *)
 rewrite e_reduce_Sn in H. apply IHn in H. bauto.
Qed.

(** 如果两个函数在 0 ~ n上表现相同, 那么其在 e_reduce n 上返回结果相同 *)
Lemma n_reduce_eq: forall {B: Set} {n} (f f': fle n -> B -> B) val,
 (forall i: fle n , f i = f' i) -> e_reduce f val = e_reduce f' val.
Proof with bauto.
 induction n... rewrite !e_reduce_0... rewrite H...
 rewrite !e_reduce_Sn. replace (f '{ S n} val) with (f' '{ S n} val)...
 apply IHn... f_equal; fun_ext; apply H. rewrite H...
Qed.

(** *** Example *)

(** 从 3 到 0 依次对 1 累加等于 7 *)
Goal e_reduce (fun i: fle 3 => (Nat.add i)) 0 = 6. 
Proof. auto. (* 0+(1+(2+(3+0)))) = 6 *) Qed.

(** ** e_forall *)

(** *** Definition *)

(** 定义 e_forall, 表示是否对任意 n 到 0 的数 f 均返回 true *)
Definition e_forall {n} (f: fle n -> bool): bool:=
 e_reduce (fun x y => y && f x) true.

(** *** Lemma *)

(** 化简 e_forall (S n) *)
Lemma e_forall_Sn: forall n (f: fle (S n) -> bool),
 e_forall f = f '{S n} && e_forall (fle_Pf f).
Proof with bauto.
 unfold e_forall... rewrite e_reduce_Sn. destruct (f '{S n})... 
 induction n... rewrite e_reduce_Sn. apply IHn.
Qed.

(** 化简 e_forall 0 *)
Lemma e_forall_0: forall (f: fle 0 -> bool),
 e_forall f = f '{0}.
Proof with bauto. unfold e_forall... rewrite e_reduce_0... Qed.

(** 证明, 当 i: fle n 时有 f i = true, 那么对于 i_forall n 返回 true *)
Lemma e_forall_r: forall n (f: fle n -> bool), 
 (forall i: fle n, f i = true) -> e_forall f = true.
Proof with bauto.
 induction n... rewrite e_forall_0; apply H. rewrite e_forall_Sn... apply IHn...
 rewrite fle_Pf_eq. apply H.
Qed.

(** 证明, 当 e_forall n 返回 true 时, 那么对于 i: fle n 时有 f i = true *)
Lemma e_forall_l: forall n (f: fle n -> bool), 
 e_forall f = true -> (forall i: fle n, f i = true). 
Proof with bauto.
 induction n...
 - (* i = 0 *)
 unfold e_forall in H. rewrite e_reduce_0 in H...
 replace i with '{0}... apply fle'_0_unique.
 - (* i <> 0 *)
 rewrite e_forall_Sn in H... destruct (i =? S n) eqn: E...
 + (* i = S n *)
 replace i with '{S n}... apply fle_eq...
 + (* i <> S n *)
 assert (i <= n). pose (fle_proof i)...
 replace i with F'S[F'P[H1]]. rewrite <- fle_Pf_eq.
 apply IHn... apply fle_eq...
Qed.

(** 证明, 当 i: fle n 时有 f i = true, 那么对于 e_forall n 返回 true; 反之亦然 *)
Lemma e_forall_eq: forall n (f: fle n -> bool), 
 (forall i: fle n, f i = true) <-> e_forall f = true.
Proof. 
 split; intro. apply e_forall_r; apply H. apply e_forall_l; auto. 
Qed.

(** 证明, 若对 f: fle (n + m) 来说 e_forall 返回 true, 那么对于 f': fle n 来说也返回 true *)
Lemma e_forall_true: forall n m (f: fle (n + m) -> bool),
 e_forall f = true -> e_forall (fle_Pnf f) = true.
Proof with bauto.
 intros. apply e_forall_eq...
 apply e_forall_l with (i:= F'Sn[i|m]) in H...
Qed.

(** 证明, 若对于 f': fle n 来说 i_forall 返回 false, 那么对于 f: fle (n + m) 来说返回 false *)
Lemma e_forall_false: forall n m (f: fle (n + m) -> bool),
 e_forall (fle_Pnf f) = false -> e_forall f = false.
Proof with bauto.
 intros. apply not_true_is_false; unfold not... (* 假设对于 m 来说返回 true *)
 apply e_forall_true in H0. rewrite H in H0; inv H0.
Qed.

(** *** Example *)

(** 对于所有 0 至 3 的数 均小于 5, 该命题正确*)
Goal e_forall (fun x: fle 3 => x <? 5) = true.
Proof. auto. Qed.

(** 对于所有 0 至 3 的数 均小于 3, 该命题错误*)
Goal e_forall (fun x: fle 4 => x <? 3) = false.
Proof. auto. Qed.

End Fle_Fun.

(** ** Auto *)

#[export] Hint Rewrite fle_Pf_eq fle_Pnf_0 fle_Pnf_1 fle_Pnf_2 fle2natf1_eq fle2natf1_beyond
fle2natf1_fle fle2natf1_Sn fle2natf1_0 fle2natf2_eq fle2natf2_beyond fle2natf2_fle
fle2natf2_Sn fle2natf2_0 e_reduce_Sn e_reduce_0 e_forall_Sn e_forall_0: fcore.

#[export] Hint Resolve e_reduce_true n_reduce_eq e_forall_eq: fcore.

