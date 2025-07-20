Require Import Coq.Logic.ProofIrrelevance FunctionalExtensionality.
Require Import Classical_Prop.
Require Export data.

Set Implicit Arguments.

Open Scope path_scope.

(* ######################################################################### *)

(** * Environment *)

Section Environment.

(** ** env *)

(** *** Definition *)

(** 定义 env, 输入一个地址 path 返回一个表达式 exp num 的可选值 *)
Definition env := path -> option (exp num). 

(** *** Lemma *)

(** 若对于任意 x, env1 x = env2 x, 那么 env1 = env2; 反之亦然 *)
Lemma env_eq : forall (eta1 eta2 : env),
 (forall p, eta1 p = eta2 p) <-> eta1 = eta2.
Proof. dauto. fun_ext. dauto. Qed.

(** env 是可被判别的 *)
Lemma env_dec : forall (eta : env) p, {exists e : exp num, eta p = Some e} + {eta p = None}.
Proof. intros. destruct (eta p); [left; exists e | right]; dauto. Qed.

(** ** env_empty *)

(** *** Definition *)

(** 定义 env_empty, 表示空环境 *)
Definition env_empty : env := 
 fun _ => None.

(** *** Lemma *)

(** 对于任意路径, 空环境均返回 None *)
Lemma env_empty_correct : forall p, env_empty p = None.
Proof. dauto. Qed.

(** ** env_def *)

(** *** Definition *)

(** 定义 env_def, 表示当前环境存在该 path *)
Definition env_def (eta : env) (p : path) := exists e : exp num, eta p = Some e.

(** *** Lemma *)

(** 如果 eta p = Some e, 那么 env_def 命题成立 *)
Lemma env_def_correct : forall (eta : env) p e, eta p = Some e -> env_def eta p.
Proof. intros. exists e; auto. Qed.

(** 对任意 p 而言, env_def empty p 命题不成立 *)
Lemma env_def_empty : forall (p : path), ~ env_def env_empty p.
Proof. unfold not; intros. inv H. rewrite env_empty_correct in H0. inv H0. Qed.

(** ** env_undef *)

(** 定义 env_undef, 表示当前环境存在该 path *)
Definition env_undef (eta : env) (p : path) := eta p = None.

(** *** Lemma *)

(** 如果 eta p = None, 那么 env_undef 命题成立 *)
Lemma env_undef_correct : forall (eta : env) p, eta p = None -> env_undef eta p.
Proof. intros. auto. Qed.

(** 对于任意 p 而言, env_undef empty p 命题成立 *)
Lemma env_undef_empty : forall (p : path), env_undef env_empty p.
Proof. intros. unfold env_undef. apply env_empty_correct. Qed.

(** 如果 env_def 命题成立, 那么 env_undef 命题不成立 *)
Lemma env_def_undef : forall (eta : env) (p : path),
 env_def eta p -> ~ env_undef eta p.
Proof. unfold not; intros. inv H; inv H0. rewrite H1 in H3; inv H3. Qed.

(** 如果 env_undef 命题成立, 那么 env_def 命题不成立 *)
Lemma env_undef_def : forall (eta : env) (p : path),
 env_undef eta p -> ~ env_def eta p.
Proof. unfold not; intros. inv H; inv H0. rewrite H1 in H2; inv H2. Qed.

(** 对于任意 env 和 path, path 要么存在在该环境中要么不存在 *)
Lemma env_def_dec : forall (p : path) (eta : env), {env_def eta p} + {env_undef eta p}.
Proof. intros. destruct (eta p) eqn : E; [left; exists e | right] ; dauto. Qed.

(** *** env_Undef *)

(** *** Definition *)

(** 定义env_Undef, 表示路径组A中所有子路径均未定义 *)
Fixpoint env_Undef {d} (eta : env) (a : acc d) {struct d} : Prop.
Proof.
  destruct d as [|m' n']. exact (env_undef eta a).
  exact (forall i : fin n', env_Undef d eta (a|{i})).
Defined.

(** *** Lemma *)

(** 化简 env_Undef num *)
Lemma env_Undef_num : forall eta (a : acc num),
  env_Undef eta a <-> env_undef eta a.
Proof. dauto. Qed.

(** 化简 env_Undef ary *)
Lemma env_Undef_ary : forall {m n d} eta (a : acc (@ary m n d)),
  env_Undef eta a <-> (forall i : fin n, env_Undef eta (a|{i})).
Proof. dauto. Qed.

(** 对于任意 a 而言, env_Undef empty a 命题成立 *)
Lemma env_Undef_empty : forall {d} (a : acc d), env_Undef env_empty a.
Proof.
  induction d; intros. apply env_Undef_num. apply env_undef_empty.
  apply env_Undef_ary. intros. apply IHd; auto.
Qed.

(** ** env_update *)

(** *** Definition *)

(** 定义 env_update, 向环境中添加单个元素 *)
Definition env_update (eta : env) (p : path) (e : exp num) : env := 
 fun x => if (x =? p) then Some e else eta x.

Notation "p '!->' e ';' eta" := (env_update eta p e)
 (at level 100, e at next level, right associativity).

(** *** Lemma *)

(** 在环境 p !-> e ; eta 中, p 取 e *)
Lemma env_update_eq : forall eta p e,
 (p !-> e ; eta) p = Some e.
Proof. unfold env_update; dauto. Qed.

(** 在环境 p !-> e ; eta 中, 若 x <> p, 那么 x 取 eta x *)
Lemma env_update_neq : forall eta p x e,
 x <> p -> (p !-> e ; eta) x = eta x.
Proof. unfold env_update; dauto. dauto. Qed.

(** 环境 p !-> e1 ; p !-> e2 ; eta 等于环境 p !-> e1 ; eta *)
Lemma env_update_shadow : forall eta p e1 e2,
 (p !-> e1 ; p !-> e2 ; eta) = (p !-> e1 ; eta).
Proof with dauto. intros. apply env_eq... unfold env_update... Qed.

(** 当 p1 <> p2 时, env_update 可以排序 *)
Lemma env_update_permute : forall eta p1 p2 e1 e2,
 p1 <> p2 ->
 (p1 !-> e1 ; p2 !-> e2 ; eta) = (p2 !-> e2 ; p1 !-> e1 ; eta).
Proof with dauto.
 intros. apply env_eq... unfold env_update... dauto.
Qed.

(** 对于 p !-> e; eta 来说非空 *)
Lemma env_update_empty : forall eta p e,
 ~ ((p !-> e; eta) = env_empty).
Proof. 
 unfold not; intros. rewrite <- env_eq in H. specialize H with p. 
 rewrite env_update_eq in H. rewrite env_empty_correct in H. inv H.
Qed.

(** 对于 p !-> e; eta 来说, env_def p 恒成立 *)
Lemma env_def_update_eq : forall eta p e,
 env_def (p !-> e ; eta) p.
Proof. intros. exists e. apply env_update_eq. Qed.

(** 对于 p !-> e; eta 来说, 若 x <> p, 则返回 env_def eta x *)
Lemma env_def_update_neq : forall eta p e x,
 x <> p -> (env_def (p !-> e ; eta) x <-> env_def eta x). 
Proof with dauto.
 intros...
 - (* env_def eta x *)
 inv H0. rewrite env_update_neq in H1... apply env_def_correct with x0...
 - (* env_def (p !-> e; eta) x *)
 inv H0. exists x0. rewrite env_update_neq...
Qed.

(** 对于 p !-> e; eta 来说, env_def x 的结果为 x = p \/ env_def eta x *)
Lemma env_def_update : forall eta p e x,
 env_def (p !-> e ; eta) x <-> (x = p \/ env_def eta x).
Proof with dauto.
 intros...
 - (* x = p \/ env_def eta x *)
 inv H. unfold env_update in H0. destruct (x =? p) eqn : E.
 left... right; apply env_def_correct with x0...
 - (* env_def (p !-> e; eta) x *)
 destruct H; subst. apply env_def_update_eq.
 destruct (classic (x = p)); subst. apply env_def_update_eq.
 rewrite env_def_update_neq...
Qed.

(** 对于 p !-> e; eta 来说, env_undef p 恒不成立 *)
Lemma env_undef_update_eq : forall eta p e,
 ~ env_undef (p !-> e ; eta) p.
Proof. intros. apply env_def_undef. apply env_def_update_eq. Qed.

(** 对于 p !-> e; eta 来说, 若 x <> p, 则返回 env_undef eta x *)
Lemma env_undef_update_neq : forall eta p e x,
 x <> p -> (env_undef (p !-> e ; eta) x <-> env_undef eta x). 
Proof with dauto.
 intros...
 - (* env_undef eta x *)
 inv H0. rewrite env_update_neq in H2...
 - (* env_def (p !-> e; eta) x *)
 inv H0. unfold env_undef. rewrite env_update_neq...
Qed.

(** 对于 p !-> e; eta 来说, env_undef x 的结果为 x <> p /\ env_undef eta x *)
Lemma env_undef_update : forall eta p e x,
 env_undef (p !-> e ; eta) x <-> (x <> p /\ env_undef eta x).
Proof with dauto.
 intros...
 - (* x <> p *)
 inv H. rewrite env_update_eq in H1...
 - (* env_def eta x *)
 inv H. destruct (classic (x = p)); subst.
 rewrite env_update_eq in H1. inv H1. rewrite env_update_neq in H1...
 - (* env_undef (p !-> e; eta) x *)
 unfold env_undef. rewrite env_update_neq...
Qed.

(** *** Example *)

(** 对于 p2 !-> 2 ; p1 !-> 1; eta 而言, p1 取 1 *)
Example env_update_test : (Var "p2" !-> 2%R ; Var "p1" !-> 1%R ; env_empty) (Var "p1") = Some 1%R.
Proof. auto. Qed.

(** ** env_remove *)

(** *** Definition *)

(** 定义 env_remove, 向环境中删除单个元素 *)
Definition env_remove (eta : env) (p : path) : env := 
 fun x => if (x =? p) then None else eta x.

Notation "'!' p ';' eta" := (env_remove eta p) (at level 100, right associativity).

(** *** Lemma *)

(** 在环境 ! p ; eta 中, p 取 None *)
Lemma env_remove_eq : forall eta p,
 (!p ; eta) p = None.
Proof. unfold env_remove; dauto. Qed.

(** 在环境 !p ; eta 中, 若 x <> p, 那么 x 取 eta x *)
Lemma env_remove_neq : forall eta p x,
 x <> p -> (!p ; eta) x = eta x.
Proof. unfold env_remove; dauto. dauto. Qed.

(** 环境 !p1 ; !p2 ; eta 等于环境 !p1 ; eta *)
Lemma env_remove_shadow : forall eta p,
 (!p ; !p ; eta) = (!p ; eta).
Proof with dauto. intros. apply env_eq... unfold env_remove... Qed.

(** 当 p1 <> p2 时, env_remove 可以排序 *)
Lemma env_remove_permute : forall eta p1 p2,
 (!p1 ; !p2 ; eta) = (!p2; !p1; eta).
Proof with dauto.
 intros. apply env_eq... unfold env_remove...
Qed.

(** 对于 !p; env_emtpy 来说等价于 env_emtpy *)
Lemma env_remove_empty : forall p,
 (!p; env_empty) = env_empty.
Proof.
 intros. rewrite <- env_eq; intros. unfold env_remove. destruct (p0 =? p) eqn : E.
 symmetry; apply env_empty_correct. auto.
Qed.

(** 对于 !p; eta 来说, env_def p 恒不成立 *)
Lemma env_def_remove_eq : forall eta p,
 ~ env_def (!p ; eta) p.
Proof. unfold not; intros. inv H. rewrite env_remove_eq in H0. inv H0. Qed.

(** 对于 !p; eta 来说, 若 x <> p, 则返回 env_def eta x *)
Lemma env_def_remove_neq : forall eta p x,
 x <> p -> (env_undef (!p ; eta) x <-> env_undef eta x). 
Proof with dauto.
 intros...
 - (* env_undef eta x *)
 inv H0. rewrite env_remove_neq in H2...
 - (* env_undef (!p; eta) x *)
 inv H0. unfold env_undef. rewrite env_remove_neq...
Qed.

(** 对于 !p; eta 来说, env_def x 的结果为 x <> p /\ env_def eta x *)
Lemma env_def_remove : forall eta p x,
 env_def (!p ; eta) x <-> (x <> p /\ env_def eta x).
Proof with dauto.
 intros...
 - (* x <> p *)
 inv H. destruct (env_def_remove_eq H).
 - (* env_def eta x *)
 inv H. destruct (classic (x = p)); subst.
 rewrite env_remove_eq in H0. inv H0. rewrite env_remove_neq in H0...
 apply env_def_correct with x0...
 - (* env_undef (!p; eta) x *)
 unfold env_def. inv H0. exists x0. rewrite env_remove_neq...
Qed.


(** 对于 !p; eta 来说, env_undef p 恒成立 *)
Lemma env_undef_remove_eq : forall eta p,
 env_undef (!p ; eta) p.
Proof. intros. unfold env_undef. apply env_remove_eq. Qed.

(** 对于 !p; eta 来说, 若 x <> p, 则返回 env_undef eta x *)
Lemma env_undef_remove_neq : forall eta p x,
 x <> p -> (env_undef (!p ; eta) x <-> env_undef eta x). 
Proof with dauto.
 intros...
 - (* env_undef eta x *)
 inv H0. rewrite env_remove_neq in H2...
 - (* env_undef (!p; eta) x *)
 inv H0. unfold env_undef. rewrite env_remove_neq...
Qed.

(** 对于 !p; eta 来说, env_undef x 的结果为 x <> p /\ env_undef eta x *)
Lemma env_undef_remove : forall eta p x,
 env_undef (!p ; eta) x <-> (x = p \/ env_undef eta x).
Proof with dauto.
 intros...
 - (* x = p \/ env_undef eta x *)
 inv H. unfold env_remove in H1. destruct (x =? p) eqn : E.
 left... right; apply env_undef_correct...
 - (* env_undef (!p; eta) x *)
 destruct H; subst. apply env_undef_remove_eq.
 destruct (classic (x = p)); subst. apply env_undef_remove_eq.
 rewrite env_def_remove_neq...
Qed.

(** 先在环境中添加元素再删除元素等于直接删除元素 *)
Lemma env_remove_update : forall (eta : env) p e,
 (!p; p !-> e; eta) = (!p; eta).
Proof.
 intros. unfold env_remove, env_update. fun_ext. destruct (x =? p); dauto.
Qed.

(** 若一元素在环境中无定义, 先在环境中添加元素再删除元素等于原环境 *)
Lemma env_remove_update_undef : forall (eta : env) p e x,
 env_undef eta x -> (!p; p !-> e; eta) x = eta x.
Proof with dauto.
 intros. rewrite env_remove_update. inv H. destruct (classic (x = p)).
 - subst. rewrite env_remove_eq... 
 - rewrite env_remove_neq...
Qed.

(** 先在环境中删除元素再添加元素等于直接添加元素 *)
Lemma env_update_remove : forall (eta : env) p e,
 (p !-> e; !p; eta) = (p !-> e; eta).
Proof.
 intros. unfold env_remove, env_update. fun_ext. destruct (x =? p); dauto.
Qed.

(** *** Example *)

(** 对于 !p1 ; p2 !-> 2 ; p1 !-> 1; eta 而言, p1 取空 *)
Example env_remove_test1 : 
 (! Var "p1" ; Var "p2" !-> 2%R ; Var "p1" !-> 1%R ; env_empty) (Var "p1") = None.
Proof. auto. Qed.

(** 对于 !p1 ; p2 !-> 2 ; p1 !-> 1; eta 而言, p2 取2 *)
Example env_remove_test2 : 
 (! Var "p1" ; Var "p2" !-> 2%R ; Var "p1" !-> 1%R ; env_empty) (Var "p2") = Some 2%R.
Proof. auto. Qed.

End Environment.

(** ** Notation *)

Notation "p '!->' e ';' eta" := (env_update eta p e) (at level 100, e at next level, right associativity).

Notation "'!' p ';' eta" := (env_remove eta p) (at level 100, right associativity).

(** ** Auto *)

#[export] Hint Rewrite env_empty_correct env_update_eq env_update_neq env_update_shadow
env_remove_eq env_remove_neq env_remove_shadow env_remove_empty env_remove_update 
env_remove_update_undef env_update_remove : ocore.

#[export] Hint Resolve env_eq env_def_correct env_def_empty env_undef_correct env_undef_empty
env_def_undef env_undef_def env_update_permute env_def_update_eq env_remove_permute
env_remove_permute env_undef_remove_eq : ocore.


(* ######################################################################### *)

(** * Command *)

Section Command.

(** ** comm *)

(** *** Definition *)

(** 定义 comm, 代表环境转变的函数 *)
Definition comm := env -> env.

(** *** Lemma *)

(** 当 c1 = c2 时, 经过 c1 和 c2 转变的 eta 相同 *)
Lemma comm_eq : forall (c1 c2 : comm),
 (forall eta : env, c1 eta = c2 eta) <-> c1 = c2.
Proof. dauto. fun_ext. dauto. Qed.

(** *** Example *)

(** 将 arr 数组的 0 * 1 位置置为 -2 *)
Example myc1 : comm := fun eta => env_update eta (myacc |{F[_0lt2]} |{F[_1lt3]}) (-2)%R.

(** 将 arr 数组的 1 * 1 位置置空 *)
Example myc2 : comm := fun eta => env_remove eta (myacc |{F[_1lt2]} |{F[_1lt3]}).

(** ** new *)

(** *** Definition *)

(** 定义 new, 创建一个 comm *)

Definition new {d:data} (f: acc d -> comm) (a: acc d): comm := 
  f a.

(** ** seq *)

(** *** Definition *)

(** 定义 seq, 将两个 comm 结合起来 *)
Definition seq (p1 p2 : comm) : comm := fun eta => p2 (p1 eta).

Notation " p1 '; p2 " := (seq p1 p2) (right associativity,at level 65).

(** *** Lemma *)

(** seq 满足结合律 *)
Lemma seq_assoc : forall c1 c2 c3, c1 '; c2 '; c3 = (c1 '; c2) '; c3 .
Proof. dauto. Qed.

(** 将 seq 折叠 *)
Lemma seq_fold : forall eta c1 c2, c2 (c1 eta) = (c1 '; c2) eta.
Proof. auto. Qed.

(** *** Example *)

(** 将 myc1 与 myc2 结合 *)
Example seq_test : comm := myc1 '; myc2.

(** ** skip *)

(** *** Definition *)

(** 定义 skip, 代表环境不转变的函数 *)
Definition skip : comm := fun eta => eta.

(** *** Lemma *)

(** 化简 skip '; c *)
Lemma skip_l : forall c, skip '; c = c.
Proof. dauto. Qed.

(** 化简 c '; skip *)
Lemma skip_r : forall c : comm, c '; skip = c.
Proof. dauto. Qed.

(** *** Example *)

(** 测试 skip '; myc1 *)
Example skip_test : skip '; myc1 = myc1.
Proof. auto. Qed.

(** ** If *)

(** *** Definition *)

(** 定义 If, 根据 bool 进行判断 *)
Definition If (b : bool) (c1 c2 : comm) : comm := 
 fun (eta : env) => if b then c1 eta else c2 eta.

(** *** Lemma *)

(** 化简 If true *)
Lemma If_true : forall c1 c2, If true c1 c2 = c1.
Proof. dauto. Qed.

(** 化简 If false *)
Lemma If_false : forall c1 c2, If false c1 c2 = c2.
Proof. dauto. Qed.

(** 化简 If b c c *)
Lemma If_same : forall b c, If b c c = c.
Proof. intros; unfold If; fun_ext. destruct b; dauto. Qed.

(** *** Definition *)

(** 测试 If false myc1 myc2 *)
Example If_test : If false myc1 myc2 = myc2.
Proof. auto. Qed.

(** ** comm_seq *)

(** *** Definition *)

(** 定义 comm_seq, 根据一个生成 comm 的函数, 组合成新的 comm *)
Fixpoint comm_seq {n} : (fin n -> comm) -> comm := 
 match n with
 | O => fun (_ : _ ) => skip
 | S n' => fun (f : fin (S n') -> comm) =>
 comm_seq (fun i => f FS[i]) '; f '[n']
 end.

(** *** Lemma *)

(** 化简 comm_seq (S n) *)
Lemma comm_seq_Sn : forall n (f : fin (S n) -> comm),
 comm_seq f = comm_seq (fun i : fin n => f FS[i]) '; f '[n].
Proof. auto. Qed.

(** 化简 comm_seq 0 *)
Lemma comm_seq_0 : forall (f : fin 0 -> comm),
 comm_seq f = skip.
Proof. dauto. Qed.

(** 化简 comm_seq m * 0 *)
Lemma comm_seq_mul_0_r : forall n (f : fin (n * 0) -> comm),
 comm_seq f = skip.
Proof. induction n; dauto. Qed.

(** 化简 comm_seq 0 * m *)
Lemma comm_seq_mul_0_l : forall n (f : fin (0 * n) -> comm),
 comm_seq f = skip.
Proof. induction n; dauto. Qed.

(** 当 f 返回不便值时, comm_seq 返回 skip *)
Lemma comm_seq_no_change : forall n,
 comm_seq (fun (i : fin n) (eta : env) => eta) = skip.
Proof. induction n; dauto. Qed.

(** 当 f 内部可交换, 并且 f 内任意一项与 c 可交换, 则 f 与 c 可交换 *)
Lemma comm_seq_comm1 : forall n (f : fin n -> comm) (c : comm),
 (forall i j , i <> j -> f i '; f j = f j '; f i ) ->
 (forall i , f i '; c = c '; f i ) ->
 comm_seq f '; c = c '; comm_seq f.
Proof with dauto.
 induction n... rewrite comm_seq_Sn. rewrite <- seq_assoc.
 rewrite H0. rewrite !seq_assoc. f_equal. apply IHn...
 apply H... inv H2...
Qed.

(** 当 f 和 g 内部可交换, 并且 f 与 g 内任意一项可交换, 则 f 与 g 可交换 *)
Lemma comm_seq_comm2 : forall m n (f : fin m -> comm) (g : fin n -> comm),
 (forall i j, i <> j -> f i '; f j = f j '; f i ) ->
 (forall i j, i <> j -> g i '; g j = g j '; g i) ->
 (forall i j, f i '; g j = g j '; f i) ->
 comm_seq f '; comm_seq g = comm_seq g '; comm_seq f.
Proof with dauto.
 induction m; destruct n... rewrite !comm_seq_Sn.
 rewrite <- !seq_assoc. rewrite seq_assoc with (c1 := f '[m]).
 rewrite seq_assoc with (c1 := g '[n]). rewrite <- !comm_seq_comm1...
 3 : { apply H0... inv H3... } 2 : { apply H... inv H3... }
 rewrite <- !seq_assoc. rewrite seq_assoc. 
 rewrite seq_assoc with (c1 := comm_seq (fun i : fin n => g FS[ i])). f_equal.
 2 : { apply H1. } apply IHm... apply H... inv H3... apply H0... inv H3...
Qed.

(** *** Example *)

(** 对 f : (i = 0 then myc1 else myc2) 进行 seq_for 得到 myc1 '; myc2 *)
Example comm_seq_test : 
 comm_seq (fun i : fin 2 => if (i =? (@fin_0S 1))%nat then myc1 else myc2) = myc1 '; myc2.
Proof. auto. Qed.

(** ** seq_rev *)

(** *** Definition *)

(** 定义 comm_seq_rev, 是 seq_for 的反方向 *)
Fixpoint comm_seq_rev {n : nat} : (fin n -> comm)-> comm := 
 match n with
 | O => fun _ => skip
 | S n' => fun (p : fin (S n') -> comm)
 => p '[n'] '; comm_seq_rev (fun i => p FS[i]) 
 end.

(** *** Lemma *)

(** 化简 comm_seq_rev (S n) *)
Lemma comm_seq_rev_Sn : forall n (f : fin (S n) -> comm),
 comm_seq_rev f = f '[n] '; comm_seq_rev (fun i : fin n => f FS[i]).
Proof. auto. Qed.

(** 化简 comm_seq_rev 0 *)
Lemma comm_seq_rev_0 : forall (f : fin 0 -> comm),
 comm_seq_rev f = skip.
Proof. dauto. Qed.

(** 化简 comm_seq_rev m * 0 *)
Lemma comm_seq_rev_mul_0_r : forall n (f : fin (n * 0) -> comm),
 comm_seq_rev f = skip.
Proof. induction n; dauto. Qed.

(** 化简 comm_seq 0 * m *)
Lemma comm_seq_rev_mul_0_l : forall n (f : fin (0 * n) -> comm),
 comm_seq_rev f = skip.
Proof. induction n; dauto. Qed.

(** 当 f 返回不便值时, comm_seq 返回 skip *)
Lemma comm_seq_rev_no_change : forall n,
 comm_seq_rev (fun (i : fin n) (eta : env) => eta) = skip.
Proof. induction n; dauto. Qed.


(** *** Example *)

(** 对 f : (i = 0 then myc1 else myc2) 进行 seq_for 得到 myc1 '; myc2 *)
Example comm_seq_rev_test : 
 comm_seq_rev (fun i : fin 2 => if (i =? (@fin_0S 1))%nat then myc1 else myc2) = myc2 '; myc1.
Proof. auto. Qed.

(** ** comm_par *)

(** *** Definition *)

(** 定义 comm_par, 根据一个生成 acc d -> comm 的函数和 acc (ary '{m} d) *)
Fixpoint comm_par {m n d} {E : n <= m} : acc (ary [n | E] d) -> (fin n -> acc d -> comm) -> comm.
Proof.
  destruct n.
  - intros a f. exact skip.
  - intros a f. exact (comm_par m n d (leS_le E) (fst (acc_des a)) (fun i => f FS[i]) '; f '[n] (snd (acc_des a))).
Defined.

(** *** Lemma *)

(** 化简 comm_par (S n) *)
Lemma comm_par_Sn : forall m n d {E : S n <= m} (a : acc (ary [S n|E] d)) (f : fin (S n) -> acc d -> comm),
 comm_par a f = comm_par (fst (acc_des a)) (fun i : fin n => f FS[i]) '; f '[n] (snd (acc_des a)).
Proof. auto. Qed.

(** 化简 comm_par 0 *)
Lemma comm_par_0 : forall m d {E : 0 <= m} (a : acc (ary [0|E] d)) (f : fin 0 -> acc d -> comm),
 comm_par a f = skip.
Proof. dauto. Qed.

(** 化简 comm_par m * 0 *)
Lemma comm_par_mul_0_r : forall m n d {E : n * 0 <= m} 
  (a : acc (ary [n*0|E] d)) (f : fin (n * 0) -> acc d -> comm),
 comm_par a f = skip.
Proof. induction n; dauto. Qed.

(** 化简 comm_par 0 * m *)
Lemma comm_par_mul_0_l : forall m n d {E : 0 * n <= m} 
  (a : acc (ary [0*n|E] d)) (f : fin (0 * n) -> acc d -> comm),
 comm_par a f = skip.
Proof. induction n; dauto. Qed.

(** 当 f 返回不便值时, comm_par 返回 skip *)
Lemma comm_par_no_change : forall m n d {E : n <= m} (a : acc (ary [n|E] d)),
 comm_par a (fun (i : fin n) (a : acc d) (eta : env) => eta) = skip.
Proof.
 induction n; dauto. rewrite comm_par_Sn. rewrite IHn. auto.
Qed.

(** ** par_rev *)

(** *** Definition *)

(** 定义 comm_par_rev, 是 par_for 的反方向 *)
Fixpoint comm_par_rev {m n d} {E : n <= m} : acc (ary [n | E] d) -> (fin n -> acc d -> comm) -> comm.
Proof.
  destruct n.
  - intros a f. exact skip.
  - intros a f. exact (f '[n] (snd (acc_des a)) '; comm_par_rev m n d (leS_le E) (fst (acc_des a)) (fun i => f FS[i])).
Defined.

(** *** Lemma *)

(** 化简 comm_par_rev (S n) *)
Lemma comm_par_rev_Sn : forall m n d {E: S n <= m} 
  (a: acc (ary [S n|E] d)) (f : fin (S n) -> acc d -> comm),
 comm_par_rev a f = 
 f '[n] (snd (acc_des a)) '; comm_par_rev (fst (acc_des a)) (fun i => f FS[i]).
Proof. auto. Qed.

(** 化简 comm_par_rev 0 *)
Lemma comm_par_rev_0 : forall m d {E: 0 <= m} 
  (a: acc (ary [0|E] d)) (f : fin 0 -> acc d -> comm),
 comm_par_rev a f = skip.
Proof. dauto. Qed.

(** 化简 comm_par_rev m * 0 *)
Lemma comm_par_rev_mul_0_r : forall m n d {E: n * 0 <= m} 
  (a: acc (ary [n * 0 |E] d)) (f : fin (n * 0) -> acc d -> comm),
 comm_par_rev a f = skip.
Proof. induction n; dauto. Qed.

(** 化简 comm_par 0 * m *)
Lemma comm_par_rev_mul_0_l : forall m n d {E: 0 * n <= m} 
  (a: acc (ary [0 * n |E] d)) (f : fin (0 * n) -> acc d -> comm),
 comm_par_rev a f = skip.
Proof. induction n; dauto. Qed.

(** 当 f 返回不便值时, comm_par_rev 返回 skip *)
Lemma comm_par_rev_no_change : forall m n d {E: n <= m} (a: acc (ary [n |E] d)),
 comm_par_rev a (fun (i : fin n) (a : acc d) (eta : env) => eta) = skip.
Proof. 
 induction n; dauto. rewrite comm_par_rev_Sn. rewrite IHn. auto.
Qed.

(** ** assign *)

(** *** Definition *)

(** 定义 assign; 将表达式数组 exp d 赋值给 acc d *)
Fixpoint assign {d : data} : acc d -> exp d -> comm := 
 match d with
 | num => fun a e eta => 
 env_update eta a e
 | ary n d' => fun a e =>
 comm_seq (fun i =>(assign a|{i} e|[i]) )
end.

Notation " a | := e " := (assign a e) (at level 60).

(** *** Lemma *)

(** 展开 assign num *)
Lemma assign_num : forall (a : acc num) (e : exp num), a | := e = fun eta => (a !-> e ; eta).
Proof. auto. Qed.

(** 展开 assign ary *)
Lemma assign_ary : forall {m n d} (a : acc (@ary m n d)) (e : exp (ary n d)),
 (a | := e) = comm_seq (fun i => assign a|{i} e|[i]).
Proof. auto. Qed.

(** 化简 assign (S n) *)
Lemma assign_Sn : forall m n d {E : S n <= m} (va : acc (@ary m [n | leS_le E ] d)) (a : acc d)
 (ve : exp (ary [n | leS_le E] d)) (e : exp d) ,
 (acc_con (va, a) | := exp_con (ve, e)) = (va | := ve '; a | := e).
Proof.
 intros. simpl. f_equal; [f_equal; fun_ext |]; f_equal; dauto.
Qed.

(** 化简 assign 0 *)
Lemma assign_0 : forall m d (E : 0 <= m) (a : acc (@ary m [0 | E] d)) (e : exp (ary [0 | E] d)),
 (a | := e) = skip.
Proof. auto. Qed.

(** 证明对于 a |:= e 和 AA[a] |:= EE[e] 来说, 等价 *)
Lemma assign_eq : forall {m m' n d} {E : n <= m} (E': n <= m')
  (a : acc (ary [n | E] d)) (e : exp (ary [n | E] d)),
  AA[ a | E'] |:= EE[e | E'] = a |:= e.
Proof with dauto.
  intros. rewrite !assign_ary. f_equal.
Qed.

(** *** Example *)

(** 定义一个给 myacc 赋值的环境 *)
Example myenv1 := (myacc | := myexp) env_empty.

(** 证明 arr 的 1 * 1 位置对应 myexp 1 * 1 位置的数 5 *)
Example assign_tes1 : myenv1 arr_11 = Some 5%R.
Proof. auto. Qed.

(** 更新这个环境 *)
Example myenv2 := (myc1 '; myc2) myenv1.

(** 再次访问错误 *)
Example assign_test2 : myenv2 arr_11 = None.
Proof. auto. Qed.

(** ** vrm *)

(** *** Definition *)

(** 定义 vrm, 针对不同数据类型整体释放空间 *)
Fixpoint vrm {d : data} : acc d -> comm := 
 match d with
 | num => fun a eta => env_remove eta a
 | ary n d' => fun (a : acc(ary n d')) => comm_seq_rev (fun i => (vrm a|{i}) )
 end.

(** 化简 vrm num *)
Lemma vrm_num :
  forall (a : acc num), vrm a = fun eta => env_remove eta a.
Proof. auto. Qed.

(** 化简 vrm ary *)
Lemma vrm_ary :
  forall m n d (a : acc (@ary m n d)), vrm a = comm_seq_rev (fun i => (vrm a|{i})).
Proof. auto. Qed.

(** 化简 vrm (S n) *)
Lemma vrm_Sn : 
 forall m n d {E : S n <= m} (va : acc (@ary m [n | leS_le E] d)) (a : acc d),
 vrm (acc_con (va, a)) = vrm a '; vrm va.
Proof. intros; simpl. f_equal; f_equal; dauto. Qed.

(** 化简 vrm 0 *)
Lemma vrm_0 : forall m d (a : acc (@ary m fle_0 d)), vrm a = skip.
Proof. dauto. Qed.

(** 对任意 d和任意 a : acc d, vrm 满足交换律 *)
Lemma vrm_comm_aux : forall {d1 d2},
 (forall (a1 : acc d1) (a2 : acc d2), vrm a1 '; vrm a2 = vrm a2 '; vrm a1) ->
 forall {m n} (a1 : acc (@ary m n d1)) (a2 : acc d2),
 vrm a1 '; vrm a2 = vrm a2 '; vrm a1.
Proof with dauto.
 intros d1 d2 H. destruct n as [n E]. induction n... destruct (acc_des a1) as [v e] eqn : E0.
 replace a1 with (acc_con (v, e)) by (rewrite <- E0; apply acc_con_des).
 rewrite vrm_Sn. rewrite <- seq_assoc. rewrite IHn. rewrite !seq_assoc. f_equal...
Qed.

Lemma vrm_comm_aux' : forall {d1 d2},
 (forall (a1 : acc d1) (a2 : acc d2), vrm a1 '; vrm a2 = vrm a2 '; vrm a1) ->
 forall {m1 n1 m2 n2} (a1 : acc (@ary m1 n1 d1)) (a2 : acc (@ary m2 n2 d2)),
 vrm a1 '; vrm a2 = vrm a2 '; vrm a1.
Proof with dauto.
 intros d1 d2 H. destruct n1 as [n1 E]. induction n1... destruct (acc_des a1) as [v e] eqn : E0.
 replace a1 with (acc_con (v, e)) by (rewrite <- E0; apply acc_con_des).
 rewrite vrm_Sn. rewrite <- seq_assoc. rewrite IHn1. rewrite !seq_assoc. f_equal...
 symmetry. apply vrm_comm_aux...
Qed.

Lemma vrm_comm : forall {d1 d2} (a1 : acc d1) (a2 : acc d2),
 vrm a1 '; vrm a2 = vrm a2 '; vrm a1.
Proof with dauto.
 induction d1; induction d2...
 - unfold seq; simpl. fun_ext. apply env_remove_permute.
 - symmetry. apply vrm_comm_aux...
 - apply vrm_comm_aux...
 - apply vrm_comm_aux'...
Qed.

(** 当重复 vrm 时, 等于单次 vrm *)
Lemma vrm_shadow : forall d (a : acc d),
 vrm a '; vrm a = vrm a.
Proof with dauto.
 induction d as [|m [n E]]; intros...
 - unfold seq, vrm; simpl. fun_ext. rewrite env_remove_shadow...
 - induction n... destruct (acc_des a) as [v e] eqn : E0.
 replace a with (acc_con (v, e)) by (rewrite <- E0; apply acc_con_des).
 rewrite vrm_Sn. rewrite seq_assoc. rewrite <- seq_assoc with (c1 := vrm e).
 rewrite vrm_comm. rewrite !seq_assoc. rewrite IHd. rewrite <- !seq_assoc. rewrite IHn...
Qed.


(** 先赋值紧接着释放等于直接释放 *)
Lemma vrm_assign : forall d (a : acc d) (e : exp d),
 (a | := e) '; vrm a = vrm a.
Proof with dauto.
 induction d as [|m [n E]]; intros.
 - simpl. fun_ext. apply env_remove_update.
 - induction n... destruct (acc_des a) as [va a'] eqn : E0.
 replace a with (acc_con (va, a')) by (rewrite <- E0; apply acc_con_des).
 destruct (exp_des e) as [ve e'] eqn : E1.
 replace e with (exp_con (ve, e')) by (rewrite <- E1; apply exp_con_des).
 rewrite vrm_Sn. rewrite assign_Sn. rewrite seq_assoc. 
 rewrite <- seq_assoc with (c1 := va | := ve) (c2 := a' | := e'). rewrite IHd.
 rewrite <- seq_assoc. rewrite vrm_comm. rewrite seq_assoc. rewrite IHn...
Qed.



(** *** Example *)

(** 定义一个释放了 arr 的环境 *)
Example myenv3 := vrm myacc myenv1.

(** 试图访问 arr 的 0 0 位置失败 *)
Example vrm_test : myenv3 arr_00 = None.
Proof. auto. Qed.

(** ** access *)

(** *** Definition *)

(** 定义安全的环境访问接口 *)
Fixpoint access_aux {d : data} (eta : env) : acc d -> option (exp d) := 
 match d with
 | num => fun p => eta p
 | ary n d1 => fun p => v_optmk (fun i : fin n => access_aux eta p|{i})
 end.

Definition access {d : data} (eta : env) : acc d -> option (exp d) := 
 match (optdata d) with
 | Some _ => access_aux eta (* 类型有效才执行查找 *)
 | None => fun _ => None (* 类型无效直接返回None *)
 end.

(** 定义在 access (S n) 下的访问方式 *)
Definition access_helper {m n d} {E : S n <= m} 
 (ve : option (exp (ary [n | leS_le E] d))) (e : option (exp d)) 
 : option (exp (ary [S n | E] d)) := 
 match e, ve with
 | Some e', Some ve' => Some (exp_con (ve', e'))
 | _, _ => None
 end.

(** *** Lemma *)

(** 展开 access_aux num *)
Lemma access_num : forall (eta : env) (a : acc num),
 access_aux eta a = eta (a : path).
Proof. auto. Qed.

(** 展开 access_aux ary *)
Lemma access_ary : forall {m n d} (eta : env) (a : acc (@ary m n d)),
 access_aux eta a = (v_optmk (fun i : fin n => access_aux eta a|{i}) : option (exp (ary n d))).
Proof. auto. Qed.

(** 通过 access 判断环境相同 *)
Lemma access_eq_env : forall (eta eta' : env),
  (forall (x : path), access_aux eta (@accp num x) = access_aux eta' (accp x)) <-> eta = eta'.
Proof with vauto.  split... apply env_eq; intros. specialize H with p... Qed.

Lemma access_eq_env' : forall (eta eta' : env),
  (forall d (a : acc d), access eta a = access eta' a) <-> eta = eta'.
Proof with vauto.  split... apply env_eq; intros. specialize H with num (accp p)... Qed.

(** 化简 access (S n) *)
Lemma access_Sn : forall m n d (eta : env) {E : S n <= m} (va : acc (ary [n |leS_le E] d)) (a : acc d),
 access_aux eta (acc_con (va, a)) = access_helper (access_aux eta va) (access_aux eta a).
Proof with dauto.
 intros. rewrite access_ary. unfold access_helper. simpl in *.
 replace (access_aux eta (acc_con (va, a)) |{ '[ n]}) with (access_aux eta a).
 2 : { f_equal. symmetry... } destruct (access_aux eta a)... 
 replace (fun i : fin n => access_aux eta (acc_con (va, a)) |{ FS[ i]}) with
 (fun i : fin n => access_aux eta (va : acc (ary [n | leS_le E] d)) |{ i}).
 2 : { fun_ext... }
 destruct (v_optmk (fun i : fin n => access_aux eta (va : acc (ary [n | leS_le E] d)) |{ i}))...
Qed.

(** 化简 access_helper (S n) *)
Lemma access_helper_Sn : forall {m n d} {E : S n <= m} (ve : option (exp (ary [n | leS_le E] d))) (e : option (exp d)) ve' e',
 ve = Some ve' -> e = Some e' -> access_helper ve e = Some (exp_con (ve', e')).
Proof. intros. unfold access_helper. subst. dauto. Qed.

(** 当先通过 accp 赋值后, 如果访问的路径不同; 那么可以去除该赋值; 如果相同, 则返回该赋值 *)
Lemma access_assign_aux : forall {n n' m d} (p1 p2 : path) (E : n <= m) (E' : n' < m) e x,
 (p1 =? p2) = false ->
 (forall (p1 p2 : path) (e : exp d) x,
 access_aux ((accp p1 | := e) x) (accp p2) = 
 if p1 =? p2 then Some e else access_aux x (accp p2)) ->
 access_aux ((@accp (ary [n | E] d) p1 | := e) x) (@accp d (Ary [n' | E'] p2)) = 
 access_aux x (accp (Ary [n' | E'] p2)).
Proof with dauto.
 induction n... destruct (exp_des e) as [ve e'] eqn : E0.
 replace e with (exp_con (ve, e')) by (rewrite <- E0; apply exp_con_des).
 erewrite <- IHn with (x := x) (e := ve) (p1 := p1). 2 : { dauto. } 
 2 : { intros. apply H0. } clear IHn. rewrite assign_Sn.
 unfold seq. rewrite H0.
 replace (Ary FF'[ fin_lstH (Nat.lt_0_succ n) | [S n | E]] p1 =? Ary [n' | E'] p2) with false.
 2 : { dauto. inv H1... } dauto.
Qed.

Lemma access_assign' : forall d (p1 p2 : path) (e : exp d) (eta : env),
 access_aux ((accp  p1 | := e) eta) (accp p2) = if p1 =? p2 then Some e else access_aux eta (accp p2).
Proof with dauto.
 induction d; intros; destruct (p1 =? p2) eqn : E0... 
 - simpl. apply env_update_eq.
 - simpl. apply env_update_neq... 
 - destruct n as [n E0]. induction n. simpl in *... 
 rewrite !accp_Sn. destruct (exp_des e) as [ve e'] eqn : E1.
 replace e with (exp_con (ve, e')) by (rewrite <- E1; apply exp_con_des). 
 rewrite access_Sn. apply access_helper_Sn.
 + destruct n. simpl... specialize IHn with (E0 := leS_le E0).
 rewrite <- IHn. clear IHn. rewrite !access_ary.
 apply v_optmk_eq. fun_ext. rewrite assign_Sn. unfold seq. rewrite a_idx_accp.
 rewrite IHd.
 replace (Ary FF'[ '[ S n] | [S (S n) | E0]] p2 =? Ary FF'[ x | [S n | leS_le E0]] p2) with false.
 auto. symmetry. apply eqb_neq. intro. inv H. pose proof (fin_proof x). simpl in H0...
 + rewrite assign_Sn. unfold seq. rewrite IHd.
 replace (Ary FF'[ '[ n] | [S n | E0]] p2 =? Ary FF'[ '[ n] | [S n | E0]] p2) with true by dauto...
 - destruct n as [n E1]. induction n. simpl...
 rewrite !accp_Sn. destruct (exp_des e) as [ve e'] eqn : E2.
 replace e with (exp_con (ve, e')) by (rewrite <- E2; apply exp_con_des).
 rewrite assign_Sn. unfold seq. rewrite !access_Sn. f_equal.
 + destruct n. simpl... specialize IHn with (E1 := leS_le E1). 
 erewrite <- IHn with ve. clear IHn.
 rewrite !access_ary. apply v_optmk_eq. fun_ext. rewrite a_idx_accp.
 rewrite IHd.
 replace (Ary FF'[ '[ S n] | [S (S n) | E1]] p1 =? Ary FF'[ x | [S n | leS_le E1]] p2) with false.
 2 : { symmetry. apply eqb_neq. intro. injection H; intros... } vauto.
 + rewrite IHd.
 replace (Ary FF'[ '[ n] | [S n | E1]] p1 =? Ary FF'[ '[ n] | [S n | E1]] p2) with false. 
 2 : { symmetry. apply eqb_neq. intro. injection H; intros... }
 apply access_assign_aux. 2 : { intros. apply IHd. } dauto.
Qed.


Lemma access_assign : forall d (p1 p2 : path) (e : exp d) (eta : env),
 access ((accp p1 | := e) eta) (accp  p2) = if p1 =? p2 then optexp e else access eta (accp  p2).
Proof with dauto.
 intros d. destruct (optdata_dec d) as [E | E]; unfold optexp, access;
 rewrite E. apply access_assign'. intros...
Qed.

(** 当访问相同赋值路径时 *)
Lemma access_assign_eq' : forall eta d p (e : exp d),
 access_aux (((accp p)| := e) eta) (accp p) = Some e.
Proof. intros. rewrite access_assign'; dauto. Qed.

Lemma access_assign_eq : forall eta d p (e : exp d),
 access (((accp p)| := e) eta) (accp p) = optexp e.
Proof. intros. rewrite access_assign; dauto. Qed.

(** 当访问不相同赋值路径时 *)
Lemma access_assign_neq' : forall eta d p1 p2 (e : exp d),
 p1 <> p2 ->
 access_aux (((@accp d p1)| := e) eta) (@accp d p2) = access_aux eta (accp p2).
Proof. intros. rewrite access_assign'; dauto; dauto. Qed.

Lemma access_assign_neq : forall eta d p1 p2 (e : exp d),
 p1 <> p2 ->
 access (((@accp d p1)| := e) eta) (@accp d p2) = access eta (accp p2).
Proof. intros. rewrite access_assign; dauto; dauto. Qed.

(** 当重复两次赋值时, 若 path1 不等于路径 path2, 则可交换 *)
Lemma assign_assign_comm_aux : forall n m d (p1 p2 : path) {E : S n <= m} 
 (ve : exp (ary [n | leS_le E] d)) (e : exp d),
 (forall (p1' p2' : path) (e1' e2' : exp d),
 accp p1' | := e1' '; accp p2' | := e2' = 
 (if p1' =? p2' then accp p1' | := e2' else accp p2' | := e2' '; accp  p1' | := e1')) ->
 @accp (ary [n | leS_le E] d) p1 | := ve '; @accp d (Ary FF'[ '[ n] | [S n | E]] p2) | := e = 
 accp (Ary FF'[ '[ n] | [S n | E]] p2) | := e '; @accp (ary [n | leS_le E] d) p1 | := ve.
Proof with dauto.
 intros. rewrite !assign_ary. apply comm_seq_comm1...
 + rewrite H. replace (Ary FF'[ i | [n | leS_le E]] p1 =? 
 Ary FF'[ j | [n | leS_le E]] p1) with false... dauto. inv H1...
 + rewrite H. replace (Ary FF'[ i | [n | leS_le E]] p1 =?
 Ary FF'[ fin_lstH (Nat.lt_0_succ n) | [S n | E]] p2) with false... 
 dauto. inv H0. simpl in i. pose proof fin_proof i...
Qed.

Lemma assign_assign_comm : forall d (p1 p2 : path) (e1 e2 : exp d),
 accp p1 | := e1 '; accp p2 | := e2 = 
 if p1 =? p2 then accp p1 | := e2
 else accp p2 | := e2 '; accp p1 | := e1.
Proof with dauto.
 induction d; intros; destruct (p1 =? p2) eqn : E...
 - unfold seq; simpl. fun_ext. rewrite env_update_shadow...
 - unfold seq; simpl. fun_ext. rewrite env_update_permute...
 - destruct n as [n E]. induction n. simpl... 
 destruct (exp_des e1) as [ve1 e1'] eqn : E0. destruct (exp_des e2) as [ve2 e2'] eqn : E1.
 replace e1 with (exp_con (ve1, e1')) by (rewrite <- E0; apply exp_con_des).
 replace e2 with (exp_con (ve2, e2')) by (rewrite <- E1; apply exp_con_des).
 rewrite !accp_Sn. rewrite !assign_Sn. rewrite <- !seq_assoc. 
 rewrite seq_assoc with (c1 := accp (Ary FF'[ '[ n] | [S n | E]] p2) | := e1').
 replace (@accp d (Ary FF'[ '[ n] | [S n | E]] p2) | := e1' '; @accp (ary [n | leS_le E] d) p2 | := ve2) with
 (@accp (ary [n | leS_le E] d) p2 | := ve2 '; @accp d (Ary FF'[ '[ n] | [S n | E]] p2) | := e1') by
 ( apply assign_assign_comm_aux; apply IHd). rewrite <- seq_assoc. rewrite IHd. 
 replace (Ary FF'[ '[ n] | [S n | E]] p2 =? Ary FF'[ '[ n] | [S n | E]] p2) with true by dauto.
 rewrite seq_assoc. f_equal. apply IHn.
 - destruct n as [n E0]. induction n. simpl...
 destruct (exp_des e1) as [ve1 e1'] eqn : E1. destruct (exp_des e2) as [ve2 e2'] eqn : E2.
 replace e1 with (exp_con (ve1, e1')) by (rewrite <- E1; apply exp_con_des).
 replace e2 with (exp_con (ve2, e2')) by (rewrite <- E2; apply exp_con_des).
 rewrite !accp_Sn. rewrite !assign_Sn. rewrite <- !seq_assoc.
 rewrite seq_assoc with (c1 := accp (Ary FF'[ '[ n] | [S n | E0]] p1) | := e1').
 replace (accp (Ary FF'[ '[ n] | [S n | E0]] p1) | := e1' '; accp  p2 | := ve2) with
 (@accp (ary [n | leS_le E0] d) p2 | := ve2 '; accp (Ary FF'[ '[ n] | [S n | E0]] p1) | := e1') by
 (apply assign_assign_comm_aux; apply IHd). rewrite <- seq_assoc. rewrite IHd. 
 replace (Ary FF'[ '[ n] | [S n | E0]] p1 =? Ary FF'[ '[ n] | [S n | E0]] p2) with false.
 2 : { dauto. inv H... } rewrite seq_assoc with (c1 := accp p1 | := ve1).
 rewrite IHn. rewrite <- !seq_assoc. rewrite seq_assoc with (c1 := accp p1 | := ve1).
 replace (accp  p1 | := ve1 '; accp (Ary FF'[ '[ n] | [S n | E0]] p2) | := e2') with
 (accp (Ary FF'[ '[ n] | [S n | E0]] p2) | := e2' '; accp  p1 | := ve1) by
 (symmetry; apply assign_assign_comm_aux; apply IHd). rewrite <- !seq_assoc...
Qed.

(** 赋值两次相同路径取后一次 *)
Lemma assign_assign_comm_eq : forall d p (e1 e2 : exp d),
 accp p | := e1 '; accp p | := e2 = accp p | := e2.
Proof.
 intros. subst. rewrite assign_assign_comm. dauto.
Qed.

(** 两次赋值路径不同时, 可交换 *)
Lemma assign_assign_comm_neq : forall d (p1 p2 : path) (e1 e2 : exp d),
 p1 <> p2 ->
 accp p1 | := e1 '; accp p2 | := e2 = 
 accp p2 | := e2 '; accp p1 | := e1 .
Proof.
 intros. rewrite assign_assign_comm. replace (p1 =? p2) with false; dauto.
Qed.

End Command.

(** ** Tactics *)

(** *** Notation *)

Notation " p1 '; p2 " := (seq p1 p2) (right associativity,at level 65).

Notation " a |:= e " := (assign a e) (at level 60).

Notation "p '!->' e ';' eta" := (env_update eta p e)
 (at level 100, e at next level, right associativity).

Notation "'!' p ';' eta" := (env_remove eta p) (at level 100, right associativity).

(** *** Auto *)
#[export] Hint Rewrite skip_l skip_r If_true If_false If_same comm_seq_Sn comm_seq_0
comm_seq_mul_0_r comm_seq_mul_0_l comm_seq_no_change comm_seq_rev_Sn comm_seq_rev_0
comm_seq_rev_mul_0_r comm_seq_rev_mul_0_l comm_seq_rev_no_change comm_par_Sn
comm_par_0 comm_par_mul_0_r comm_par_mul_0_l comm_par_no_change comm_par_rev_Sn
comm_par_rev_0 comm_par_rev_mul_0_r comm_par_rev_mul_0_l comm_par_rev_no_change
assign_Sn assign_0 vrm_num vrm_ary vrm_Sn vrm_0 vrm_shadow vrm_assign access_Sn  
access_assign' access_assign assign_assign_comm : ocore.

#[export] Hint Resolve comm_eq seq_assoc seq_fold comm_seq_comm1 comm_seq_comm2
assign_num assign_ary assign_eq vrm_comm access_num access_ary access_helper_Sn : ocore.


(* ######################################################################### *)

(** * Utils *)

(** *** Ltac *)

(** 定义 oauto, 包含本所定义的一些引理和定义 *)
Ltac oauto := 
 repeat (quan_simpl; bool_simpl; opt_simpl; pair_simpl; fun_simpl; data_simpl; path_simpl;
 vec_simpl; f_simpl); subst; 
 autorewrite with ocore vcore dcore fcore core; auto with ocore dcore vcore fcore core;
 try lia; try apply proof_irrelevance.
