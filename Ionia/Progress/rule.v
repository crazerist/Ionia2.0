Require Import Coq.Logic.ProofIrrelevance FunctionalExtensionality.
Require Import Classical_Prop.
Require Import Coq.Reals.Exp_prop.
Require Export command.

Set Implicit Arguments.

Open Scope path_scope.

(* ######################################################################### *)
(** * Basic Elemment *)

Section Basic_Elem.

(** ** zero *)

(** *** Definition *)

(** 定义零元 *)
Definition zero : exp num := R0.

(** ** one *)

(** *** Definition *)

(** 定义一 *)
Definition one : exp num := R1.

(** ** E1 *)

(** 定义自然常数 E1 *)
Definition E1 : exp num := Rtrigo_def.exp 1%R.

Parameter rand : exp num.

End Basic_Elem.


(* ######################################################################### *)
(** * Unary Function *)

Section Unary_Fun.

(** ** negate *)

(** *** Definition *)

(** 定义取负数 *)
Definition negate (x: exp num) : exp num := Ropp x.

(** *** Lemma *)

(** 重复 negate 等于本身 *)
Lemma negate_negate : forall x, negate (negate x) = x.
Proof. apply Ropp_involutive. Qed.

(** 通过 negate 判断等价 *)
Lemma negate_eq : forall x y,
  negate x = negate y <-> x = y.
Proof. split. apply Ropp_eq_reg. apply Ropp_eq_compat. Qed.

(** *** Example *)

(** 对一取复等于负一 *)
Example negate_test : negate one = (- R1)%R.
Proof. auto. Qed.

(** *** inv *)

(** *** Definition *)

(** 定义倒数 *)
Definition inv (x : exp num) : exp num := Rinv x.

(** *** Lemma *)

(** 经过两次 inv 两次后等于本身 *)
Lemma inv_inv : forall (x : exp num), inv (inv x) = x.
Proof. apply Rinv_inv. Qed.

(** 通过 inv 判断等价 *)
Lemma inv_eq : forall x y,
  inv x = inv y <-> x = y.
Proof. split. apply Rinv_eq_reg. apply Rinv_eq_compat. Qed.

(** inv zero 等于 zero *)
Lemma inv_0 : inv zero = zero.
Proof. apply Rinv_0. Qed.

(** inv 和 negate 可交换 *)
Lemma inv_negate : forall x, inv (negate x) = negate (inv x).
Proof. apply Rinv_opp. Qed.

(** ** epow *)

(** 定义自然指数 epow *)
Definition epow (x : exp num) : exp num := Rtrigo_def.exp x.

(** *** Example *)

(** 测试 epow one *)
Example epow_test : epow one = E1.
Proof. auto. Qed.

(** ** ln *)

(** 定义自然对数 ln *)
Definition ln (x: exp num) : exp num := ln x.

(** *** Lemma *)

(** 先自然指数， 再自然对数等于本身 *)
Lemma ln_epow : forall (x : exp num),
  ln (epow x) = x.
Proof. apply ln_exp. Qed.

(** 先自然对数， 再自然指数等于本身 *)
Lemma epow_ln : forall (x : exp num),
  (0 < x)%R -> epow (ln x) = x.
Proof. apply exp_ln. Qed.

(** *** Example *)

(** 测试 ln e *)
Example ln_test : ln E1 = one.
Proof. apply ln_exp. Qed.

(** ** sqrt *)

(** *** Definition *)

(** 定义平方根 *)
Definition make_nonnegreal (x : R) : nonnegreal :=
  match Rle_dec 0 x with
  | left proof => mknonnegreal x proof
  | right _ => mknonnegreal 0 (Rle_refl 0)
  end.

Definition sqrt (x:exp num) : exp num := Rsqrt (make_nonnegreal x).


End Unary_Fun.

(** ** Tactics *)

(** *** Auto *)

#[export] Hint Rewrite negate_negate  inv_inv inv_0 inv_negate ln_epow epow_ln: icore.

#[export] Hint Resolve negate_eq inv_eq : icore.

(* ######################################################################### *)
(** * Binary Functions *)

Section Binary_Fun.

(** ** add *)

(** *** Definition *)

Definition add (x y: exp num) : exp num := Rplus x y.

(** *** Lemma *)

(** add 满足交换律 *)
Lemma add_comm : forall x y, add x y = add y x.
Proof. apply Rplus_comm. Qed.

(** add 满足结合律 *)
Lemma add_assoc : forall x y z, add (add x y) z = add x (add y z).
Proof. apply Rplus_assoc. Qed.

(** 简化 add 0 x *)
Lemma add_0_l : forall x, add zero x = x.
Proof. apply Rplus_0_l. Qed.

(** 化简 add x 0 *)
Lemma add_0_r : forall x, add x zero = x.
Proof. apply Rplus_0_r. Qed.

(** *** Example *)

(** 测试add zero one *)
Example add_test : add zero one = one.
Proof. apply add_0_l. Qed.

(** ** sub *)

(** *** Definition *)

(** 定义减法 *)
Definition sub (x y: exp num) : exp num := Rminus x y.

(** *** Lemma *)

(** 减去自身等于零 *)
Lemma sub_diag : forall x, sub x x = zero.
Proof. apply Rminus_diag. Qed.

(** 简化 sub 0 x *)
Lemma sub_0_l : forall x, sub zero x = negate x.
Proof. apply Rminus_0_l. Qed.

(** 简化 sub x 0 *)
Lemma sub_0_r : forall x, sub x zero = x.
Proof. apply Rminus_0_r. Qed.

(** sub 对 negate 满足分布率*)
Lemma negate_sub_distr : forall x y, negate (sub x y) = sub y x.
Proof. apply Ropp_minus_distr. Qed.

(** 化简 x + y - x *)
Lemma add_sub_l : forall x y, sub (add x y) x = y.
Proof. apply Rplus_minus_l. Qed.

(** 化简 x + y - y *)
Lemma add_sub_r : forall x y, sub (add x y) y = x.
Proof. apply Rplus_minus_r. Qed.

(** *** Example *)

(** 测试 one - one *)
Example sub_test : sub one one = zero.
Proof. apply sub_diag. Qed.

(** ** mul *)

(** *** Definition *)

(** 定义乘法 *)
Definition mul (x y: exp num) : exp num := Rmult x y.

(** *** Lemma *)

(** 乘法满足交换律 *)
Lemma mul_comm : forall x y, Rmult x y = Rmult y x.
Proof. apply Rmult_comm. Qed.

(** mul 满足结合律 *)
Lemma mul_assoc : forall x y z, mul (mul x y) z = mul x (mul y z).
Proof. apply Rmult_assoc. Qed.

(** 简化 mul zero x *)
Lemma mul_0_l : forall x, mul zero x = zero.
Proof. apply Rmult_0_l. Qed.

(** 化简 mul x zero *)
Lemma mul_0_r : forall x, mul x zero = zero.
Proof. apply Rmult_0_r. Qed.

(** 化简 mul one x *)
Lemma mul_1_l : forall x, mul one x = x.
Proof. apply Rmult_1_l. Qed.

(** 化简 mul x one *)
Lemma mul_1_r : forall x, mul x one = x.
Proof. apply Rmult_1_r. Qed.

(** *** Example *)

(** 测试 mul one one *)
Example mul_test: mul one one = one.
Proof. apply mul_1_l. Qed.

(** ** scal *)

(** *** Definition *)

(** 定义 scal， 将 R 与 acc num 相乘 *)
Definition scal (r: R) (x: exp num) : exp num := Rmult r x.

(** *** Lemma *)

(** 乘法满足交换律 *)
Lemma scal_comm : forall x y, Rmult x y = Rmult y x.
Proof. apply Rmult_comm. Qed.

(** scal 满足结合律 *)
Lemma scal_assoc : forall x y z, scal (Rmult x y) z = scal x (scal y z).
Proof. apply Rmult_assoc. Qed.

(** 简化 scal R0 x *)
Lemma scal_0_l : forall x, scal R0 x = zero.
Proof. apply Rmult_0_l. Qed.

(** 化简 scal x zero *)
Lemma scal_0_r : forall x, scal x zero = zero.
Proof. apply Rmult_0_r. Qed.

(** 化简 scal R1 x *)
Lemma scal_1_l : forall x, scal R1 x = x.
Proof. apply Rmult_1_l. Qed.

(** 化简 scal x one *)
Lemma scal_1_r : forall x, scal x one = x.
Proof. apply Rmult_1_r. Qed.

(** *** Example *)

(** 测试 scal R1 one *)
Example scal_test : scal R1 one = one.
Proof. apply scal_1_l. Qed.

(** ** div *)

(** *** Definition *)

(** 定义除法 *)
Definition div (x y: exp num) : exp num := Rdiv x y.

(** *** Lemma *)

(** 化简 div zero x *)
Lemma div_0_l : forall x , div zero x = zero.
Proof. apply Rdiv_0_l. Qed.

(** 化简 div x zero *)
Lemma div_0_r : forall x, div x zero = zero.
Proof. apply Rdiv_0_r. Qed.

(** 化简 div one x *)
Lemma div_1_l : forall x , div one x = inv x.
Proof. apply Rdiv_1_l. Qed.

(** 化简 div x one *)
Lemma div_1_r : forall x , div x one = x.
Proof. apply Rdiv_1_r. Qed.

(** 化简 div x (negate y) *)
Lemma div_negate_r : forall x y,
  div x (negate y) = negate (div x y).
Proof. apply Rdiv_opp_r. Qed.

(** 化简 div (negate x) y *)
Lemma div_negate_l: forall x y,
  div (negate x) y = negate (div x y).
Proof. apply Rdiv_opp_l. Qed.

(** 化简 inv (div x y) *)
Lemma inv_div : forall x y, inv (div x y) = div y x.
Proof. apply Rinv_div. Qed.

(** *** Example *)

(** 测试 div one one *)
Lemma div_test : div one one = one.
Proof. apply div_1_r. Qed.

(** divn *)

(** *** Definition *)

(** 定义 div_n, 表示实数和整数的除法 *)
Definition divn(x: exp num) (n :nat)  : exp num := Rdiv x (INR n).

(** *** Lemma *)
(** 化简 divn zero x *)
Lemma divn_0_l : forall x , divn zero x = zero.
Proof. intros; unfold divn. apply Rdiv_0_l. Qed.

(** 化简 divn x zero *)
Lemma divn_0_r : forall x, divn x 0 = zero.
Proof. intros; unfold divn. apply Rdiv_0_r. Qed.

(** 化简 divn one x *)
Lemma divn_1_l : forall x , divn one x = inv (INR x).
Proof. intros; unfold divn. apply Rdiv_1_l. Qed.

(** 化简 divn x one *)
Lemma divn_1_r : forall x , divn x 1 = x.
Proof. apply Rdiv_1_r. Qed.

(** 化简 divn (negate x) y *)
Lemma divn_negate: forall x y,
  divn (negate x) y = negate (divn x y).
Proof. intros; unfold divn. apply Rdiv_opp_l. Qed.

(** *** Example *)

(** 测试 divn one one *)
Lemma divn_test : divn one 1 = one.
Proof. apply divn_1_r. Qed.

(** ** pow *)

(** *** Definition *)

(** 定义 pow,  表示 exp num的整数幂乘 *)
Definition pow (x: exp num) (n :nat) : exp num := powerRZ x (Z.of_nat n).

(** *** Lemma *)

(** 一个数的 0 的幂等于 one *)
Lemma pow_0 : forall x, pow x 0 = one.
Proof. apply powerRZ_O. Qed.

(** 一个数的 1 的幂等于其本身 *)
Lemma pow_1 : forall x, pow x 1 = x.
Proof. apply powerRZ_1. Qed.

(** one 的幂等于 one *)
Lemma pow1 : forall x, pow one x = one.
Proof. intros. apply powerRZ_R1. Qed.

(** 化简 pow (inv x) n *)
Lemma pow_inv : forall x n, pow (inv x) n = inv (pow x n).
Proof. intros. apply powerRZ_inv'. Qed.

(** *** Example *)

(** 测试 pow one 2 *)
Example pow_test : pow one 2 = one.
Proof. apply pow1. Qed.

(** ** leb *)

(** *** Definition *)

(** 定义le， 表示小于等于 *)
Definition leb (x y : exp num) : bool := if Rle_dec x y then true else false.

(** *** Lemma *)

(** leb 与 Rle 等价 *)
Lemma leb_eq : forall (x y : exp num), (x <= y)%R <-> leb x y = true.
Proof with oauto.
  unfold leb; split; intros; destruct (Rle_dec x y); auto. inv H.
Qed.

Lemma leb_eq' : forall (x y : exp num), ~ (x <= y)%R <-> leb x y = false.
Proof with oauto.
  unfold leb; split; intros; destruct (Rle_dec x y); auto. lra. inv H.
Qed.

(** Example *)

(** 测试 leb zero one *)
Example leb_test : leb zero one = true.
Proof. apply leb_eq. assert (R0 <= R1)%R. lra. apply H. Qed.

(** ** gtb *)

(** *** Definition *)

(** 定义le， 表示大于 *)
Definition gtb (x y : exp num) : bool := if Rgt_dec x y then true else false.

(** *** Lemma *)

(** gtb 与 Rgt 等价 *)
Lemma gtb_eq : forall (x y : exp num), (x > y)%R <-> gtb x y = true.
Proof with oauto.
  unfold gtb; split; intros; destruct (Rgt_dec x y); auto. inv H.
Qed.

Lemma gtb_eq' : forall (x y : exp num), ~ (x > y)%R  <-> gtb x y = false.
Proof with oauto.
  unfold gtb; split; intros; destruct (Rgt_dec x y); auto. lra.  inv H.
Qed.

(** ** Example *)

(** 测试 gtb one zero *)
Example gtb_test : gtb one zero = true.
Proof. apply gtb_eq. assert (R1 > R0)%R. lra. apply H. Qed.

End Binary_Fun.

(** ** Tactics *)

#[export] Hint Rewrite add_0_l  add_0_r  sub_diag sub_0_l sub_0_r
negate_sub_distr  add_sub_l add_sub_r  mul_0_l mul_0_r mul_1_l
mul_1_r scal_0_l scal_1_r  div_0_l div_0_r div_1_l div_1_r
div_negate_r div_negate_l inv_div  divn_0_l divn_0_r divn_1_l
divn_1_r divn_negate  pow_0 pow_1 pow1 pow_inv : icore.

#[export] Hint Resolve add_comm add_assoc mul_comm mul_assoc scal_comm
scal_assoc  leb_eq gtb_eq : icore.

(* ######################################################################### *)
(** * Exp Functions *)

Section Exp_Fun.

(** ** reduce *)

(** *** Definition *)

(** 定义 reduce， 表示对一个 f 进行递归 *)
Definition reduce {m n} {E : n <= m} {s t:data}
  (f: exp s -> exp t -> exp t) (init:exp t) (v:exp (ary [n|E] s)) 
  : exp t := v_reduce f init (exp_unfold v).

(** *** Lemma *)

(** 化简 reduce 0 *)
Lemma reduce_0 : forall m {E : 0 <= m} {s t} 
  (f : exp s -> exp t -> exp t) init (v : exp (ary [0 |E] s)),
  reduce f init v = init.
Proof. intros. apply v_reduce_0. Qed.

(** 化简 reduce (S n*)
Lemma reduce_Sn : forall m n {E : S n <= m} {s t}
  (f : exp s -> exp t -> exp t) (init : exp t) (ve : exp (ary [n | leS_le E] s)) e,
    reduce f init (exp_con (ve,e)) = f e (reduce f init ve).
Proof. intros. apply v_reduce_Sn. Qed.

(** *** Example *)

Example _0lt3 : 0 < 3. Proof. lia. Qed.

Example  _1lt3 : 1 < 3. Proof. lia. Qed.

Example _2lt3 : 2 < 3. Proof. lia. Qed.

Example myf (a b : exp (ary '{3} num)) := [add (a |[F[_0lt3]]) (b |[F[_0lt3]]),
   add (a |[F[_1lt3]]) (b |[F[_1lt3]]), add (a |[F[_2lt3]]) (b |[F[_2lt3]])].

(** 测试 reduce *)
Example reduce_test : 
  reduce myf (@exp_default (ary '{3} num)) myexp = [5%R, 7%R, 9%R].
Proof. cbv. repeat (f_equal; try lra). Qed.

(** ** sum *)

(** *** Deinition *)

(** 定义 sum, 表示求和 *)
Definition sum {m n} {E : n <= m} (e : exp (ary [n|E] num)): exp num :=
  reduce add zero e.

(** *** Lemma *)

(** 化简 sum 0 *)
Lemma sum_0 : forall m  {E : 0 <= m} (e : exp(ary [0|E] num)),
  sum e = zero.
Proof. intros. apply reduce_0. Qed.

(** 化简 sum (S n) *)
Lemma sum_Sn : forall m n {E : S n <= m} (ve : exp (ary [n| leS_le E] num)) e,
  sum (exp_con (ve, e)) = add e (sum ve).
Proof. intros. apply reduce_Sn. Qed.

(** *** Example *)

(** 测试 sum *)
Example sum_test : sum ([1,2,3]%R :exp (ary '{3} num))= 6%R.
Proof. cbv. lra. Qed.

(** ** max *)

(** *** Definition *)

(** 定义max, 寻找最大值 *)
Definition max_aux {m n} {E : S n <= m} (e : exp (ary [S n | E] num))
  : exp num := v_max_aux gtb (exp_unfold e).

Definition max {m n} {E : n <= m} (e : exp (ary [n|E] num)) (E' : 0 < n)
  : exp num := v_max gtb (exp_unfold e) E'.

(** *** Lemma *)

(** 化简 max_aux 0 *)
Lemma max_0' : forall m {E : 1 <= m} (e : exp(ary [1|E] num)), max_aux e = e |[fin_0S].
Proof. intros; unfold max_aux, reduce. rewrite v_max_0'; oauto. Qed.

(** 化简 max_1 *)
Lemma max_1 : forall m {E : 1 <= m} (e : exp(ary [1|E] num)),
   max e Nat.lt_0_1 = e |[fin_0H Nat.lt_0_1].
Proof. intros. unfold e_idx,v_idx. destruct e; simpl in *. auto. Qed.

(** 化简 max S n*)
Lemma max_Sn' : forall m n {E : S (S n) <= m} (ve : exp (ary [S n| leS_le E] num)) e,
  max_aux (exp_con (ve, e)) = if (gtb e (max_aux ve)) then e else  max_aux ve.
Proof. 
  intros. unfold max_aux. rewrite exp_unfold_con. rewrite v_max_Sn'; oauto.
Qed.

Lemma max_Sn : forall m n {E : (S n) <= m} (ve : exp (ary [n| leS_le E] num)) e {E' : 0 < n},
  max (exp_con (ve, e)) (Nat.lt_0_succ n) = 
  if (gtb e (max ve E')) then e else  max ve E'.
Proof. 
  intros. unfold max. rewrite exp_unfold_con. rewrite v_max_Sn with (E:=E'); oauto.
Qed.


(** *** Example *)

(** 测试 max_aux *)
Example max_aux_test : max_aux ([1,3,2]%R :exp (ary '{3} num)) = 3%R.
Proof with oauto.
  destruct (exp_des ([1%R, 3%R, 2%R] : exp (ary '{ 3} num))) as [v e] eqn : E.
  replace ([1%R, 3%R, 2%R] : exp (ary '{ 3} num)) with (exp_con (v, e))
  by (rewrite <- E; apply exp_con_des). rewrite max_Sn'. replace (max_aux v) with 3%R.
  replace (gtb e 3%R) with false... apply gtb_eq'. inv E; lra.
  inv E. clear H1; clear E; clear e. rename H0 into E; rewrite E.
  destruct (exp_des v) as [v' e] eqn : E0.
  replace v with (exp_con (v', e)) by (rewrite <- E0; apply exp_con_des).
  rewrite max_Sn'. rewrite <- E in E0. replace (gtb e (max_aux v')) with true.
  inv E0... replace (max_aux v') with 1%R. symmetry; apply gtb_eq; inv E0; lra.
  rewrite max_0'. inv E0...
Qed.

(* Definition seq {n:nat} {d:data} (f:fin n -> acc d -> comm) 
  (out:acc(ary '{n} d)):=
  comm_seq (fun i  => f i out|{i}).
*)
Definition binding {s t} (e: exp s)(f:exp s -> exp t) :=
  f e.


Definition Let{s t}(e:exp s)(f:exp s -> acc t -> comm)(out:acc t) :=
  f e out.

Definition join {n1 n2 : nat} {d} 
 (e : exp (ary '{n1} (ary '{n2} d))) : 
 exp (ary '{n1*n2} d) := v_join (@exp_default d) e.

Lemma join_equiv: forall (n1 n2 : nat) d  
  (e : exp (ary '{n1} (ary '{n2} d))) ,
  join e = seq_make (fun i : fin (n1 * n2) =>
    e|[fst(fin_1to2d i)]|[snd(fin_1to2d i)]).
Proof with oauto.
  intros. unfold join, v_join, seq_make.
  f_equal; fun_ext. destruct (fin_1to2d x) eqn : E. unfold e_idx;
  simpl in *. repeat f_equal; rewrite E...
Qed.

Parameter alwayslt : forall {i1 i2}, i1 < i2.



Definition concat {n1 n2 : nat} {d}
  (e1 : exp (ary '{n1} d)) (e2 : exp (ary '{n2} d)) :
  exp (ary '{n1+n2} d) :=
  v_concat (@exp_default d) e1 e2.

Lemma concat_equiv: forall {n1 n2 : nat} d
  (e1 : exp (ary '{n1} d)) (e2 : exp (ary '{n2} d)),
  concat e1 e2 = seq_make (fun i : fin (n1 + n2) =>
    if i <? n1 then e1|[[fin2nat i|@alwayslt i n1]] else e2|[[(fin2nat i)-n1|@alwayslt (i - n1) n2]]).
Proof with oauto.
  intros. unfold concat, v_concat, seq_make. f_equal.
Qed.


End Exp_Fun.

(** ** Tactics *)

#[export] Hint Rewrite reduce_0 reduce_Sn  sum_0 sum_Sn max_0' max_1 max_Sn max_Sn' : icore.

Notation "'tlet' x ':=' e 'in' y" := (binding e (fun x => y))(at level 81).

(* ######################################################################### *)

(** * Utils *)

(** *** Ltac *)

(** 定义 iauto, 包含本所定义的一些引理和定义 *)
Ltac rauto := 
 repeat (quan_simpl; bool_simpl; opt_simpl; pair_simpl; fun_simpl; data_simpl; path_simpl;
 vec_simpl; f_simpl); subst; 
 autorewrite with icore ocore vcore dcore fcore core; auto with icore ocore dcore vcore fcore core;
 try lia; try apply proof_irrelevance.
