Require Import Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Classical_Prop.
Require Import Coq.Reals.Exp_prop.
Require Export rule.

Set Implicit Arguments.

Open Scope path_scope.

Definition tmp_path := path.

Axiom assign_tmp : forall {d} (tmp : tmp_path) (e : exp d) (c : comm) env,
  c (((accp tmp) |:= e) env) = c env.

Parameter mytmp : tmp_path.

Definition accessd d (eta : env) (a : acc d) :=
  match access eta a with
  | Some val => val
  | None => exp_default
  end.


(* ######################################################################### *)
(** * Functional to Imperative *)

Section Fun2Imp.

(** ** A *)

(** *** Definition *)

(** 定义转换器 A, 输入地址和赋值，输出赋值命令 *)
Definition A {d:data} (val:(acc d)*(exp d)) : comm := 
  fst val |:= snd val.

(** *** Lemma *)

(** 展开 A *)
Lemma Avar : forall (a : acc num) (e : exp num),
  A(a, e) = a |:= e.
Proof. oauto. Qed.

Lemma Aassign : forall n d (a : acc (ary '{n} d)) (e : exp (ary '{n} d)),
  A(a, e) = comm_seq (fun i : fin n => A(a|{i}, e|[i])).
Proof. oauto. Qed.

Lemma Aunfold : forall {d} (a : acc d) (e : exp d),
  A(a, e) = a |:= e.
Proof. oauto. Qed.

Lemma Afold : forall {d} (a : acc d) (e : exp d),
  a |:= e = A(a,e).
Proof. oauto. Qed.



(** *** Example *)

(** 测试转换器 A *)
Example A_test : A (myacc, myexp) = myacc |:= myexp.
Proof. auto. Qed.

(** ** C *)

(** *** Definition *)

(** 定义转化器 C, 输入一个函数和值，输出命令 *)
Definition C {d:data} (val :(exp d)*(exp d -> comm)): comm := 
  (snd val) (fst val).

(** *** Lemma *)

(** 展开 C *)
Lemma Cvar : forall (e : exp num) (f : exp num -> comm),
  C(e, f) = f e.
Proof. auto. Qed.

Lemma Cunfold : forall {d} (e : exp d) (f : exp d -> comm),
  C(e, f) = f e.
Proof. auto. Qed.

Lemma Cfold : forall {d} (e : exp d) (f : exp d -> comm),
  f e = C(e, f).
Proof. oauto. Qed.

(** *** Example *)

(** 测试转换器 C*)
Example C_test : C(myexp, fun e => skip) = skip.
Proof. auto. Qed.

End Fun2Imp.


Lemma Aneg : forall (a:acc num) (e:exp num),
  A(a, negate e) = C(negate e, fun x => a|:=x).
Proof. oauto. Qed.

(** 展开 A（a, inv e) *)
Lemma Ainv : forall (a: acc num) (e: exp num),
  A(a, inv e) = C(inv e, fun x => a|:=x).
Proof. oauto. Qed.


(** 展开 A(a, epow e) *)
Lemma Aepow : forall (a: acc num) (e: exp num),
  A(a, epow e) = C(epow e, fun x => a |:= x).
Proof. oauto. Qed.

(** 展开 A(a, ln e) *)
Lemma Aln : forall (a:acc num) (e:exp num),
  A(a, ln e) = C(e, fun x => a |:= ln x).
Proof. oauto. Qed.


(** 展开 A(a, sqrt e) *)
Lemma Asqrt : forall (a:acc num) (e:exp num),
  A(a, sqrt e) = C(e, fun x => a |:= sqrt x).
Proof. oauto. Qed.

  Lemma Aadd : forall (a:acc num) (x y:exp num),
  A(a, add x y) = C(add x y, fun e => a |:= e).
Proof. oauto. Qed.

(** 化简 A(a, sub x y) *)
Lemma Asub : forall (a:acc num) (x y:exp num),
  A(a, sub x y) = C(sub x y, fun e => a |:= e).
Proof. oauto. Qed.

  (** 化简 A(a, mul x y) *)
Lemma Amul : forall (a:acc num) (x y:exp num),
  A(a, mul x y) = C(mul x y, fun e => a |:= e).
Proof. oauto. Qed.

Lemma Ascal : forall (a:acc num) (x : R) (y:exp num),
  A(a, scal x y) = C(scal x y, fun e => a |:= e).
Proof. oauto. Qed.

Lemma Adiv : forall (a:acc num) (x y:exp num),
  A(a, div x y) = C(div x y, fun e => a |:= e).
Proof. oauto. Qed.

  Lemma Adivn : forall (a:acc num) (x :exp num) (y : nat),
  A(a, divn x y) = C(divn x y, fun e => a |:= e).
Proof. oauto. Qed.


Lemma Apow: forall (a:acc num) (x :exp num) (y : nat),
  A(a, pow x y) = C(pow x y, fun e => a |:= e).
Proof. oauto. Qed.

Definition Max {m n} {E: n <= m} (e : exp (ary [n| E] num))
  (f:exp num -> acc num -> comm) (c : exp num -> comm) (a:path) (E' : 0 < n) :=
  new (fun tmp => 
    A(tmp, e |[fin_0H E']) ';
    comm_seq (fun (i: fin n) eta =>
    (If (gtb e|[i] (accessd num eta tmp)) (f (e|[i]) tmp) (f (accessd num eta tmp) tmp)) eta) ';
    fun eta => (c (accessd num eta tmp) eta)) (accp a).


Lemma Amax_aux :  forall n m {E :n <= m} (e : exp (ary [n | E] num)) 
  (a : path) eta {E': 0 < n},
  accessd num
(comm_seq
(fun (i : fin n) (eta0 : env) =>
If (gtb e |[ i] (accessd num eta0 (accp a)))
(A (accp a, e |[ i]))
(A (accp a, accessd num eta0 (accp a)))
eta0) (A (accp a, e |[ fin_0H E']) eta))
(accp a) = max e E'.
Proof with oauto.
  destruct n. intros; inv E'. induction n; intros.
 - unfold comm_seq. rewrite skip_l. rewrite Aunfold. unfold accessd. rewrite access_assign_eq.
   replace (optexp e |[ fin_0H E']) with (Some e |[ fin_0H E']) by oauto.
   rewrite If_same. rewrite Avar. rewrite access_assign_eq...
 - destruct (exp_des e) as [ve e'] eqn : E0.
    replace e with (exp_con (ve, e')) by (rewrite <- E0; oauto).
    rewrite comm_seq_Sn. unfold seq.
    replace (accessd num
(comm_seq
(fun (i : fin (S n)) (eta0 : env) =>
If
(gtb (exp_con (ve, e')) |[ FS[ i]]
(accessd num eta0 (accp a)))
(A (accp a, (exp_con (ve, e'))
|[ FS[ i]]))
(A (accp a, accessd num eta0 (accp a)))
eta0)
(A (accp a, (exp_con (ve, e')) |[ fin_0H E'])
eta)) (accp a)) with (max ve (Nat.lt_0_succ n)) by (rewrite <- IHn 
      with (a:=a) (eta:=eta); repeat f_equal; oauto).
    replace ((exp_con (ve, e')) |[ '[ S n]]) with e' by oauto. 
    replace E'  with (Nat.lt_0_succ (S n)) at 2 by oauto. 
    rewrite max_Sn with (E' := (Nat.lt_0_succ (n))).
    destruct (gtb e' (max ve (Nat.lt_0_succ n))) eqn : E1; [rewrite If_true | rewrite If_false];
    rewrite Avar; unfold accessd; rewrite access_assign_eq...
Qed.

Lemma Amax_aux' : forall n m {E : n <= m} (e : exp (ary [n | E] num)) 
  (a: path) eta x {E' : 0 < n},
  a <> x ->
  @access_aux num
(comm_seq
(fun (i : fin n) (eta0 : env) =>
If (gtb e |[ i] (accessd num eta0 (accp a)))
(A (accp a, e |[ i]))
(A (accp a, accessd num eta0 (accp a))) eta0)
(A (accp a, e |[ fin_0H E']) eta)) (accp x) = access_aux eta (accp x).
Proof with oauto.
  destruct n. intros; inv E'. induction n; intros.
  - unfold comm_seq. rewrite skip_l. rewrite Aunfold. unfold accessd. rewrite access_assign_eq.
   replace (optexp e |[ fin_0H E']) with (Some e|[fin_0H E']) by (symmetry; apply optexp_Some_eq; oauto).
   rewrite If_same. rewrite Avar. repeat rewrite access_assign_neq'...
  - rewrite comm_seq_Sn. destruct (exp_des e) as [ve e'] eqn : E0.
    replace e with (exp_con (ve, e')) by (rewrite <- E0; oauto). unfold seq.
    replace (accessd num
(comm_seq
(fun (i : fin (S n)) (eta0 : env) =>
If
(gtb (exp_con (ve, e')) |[ FS[ i]]
(accessd num eta0 (accp a)))
(A (accp a, (exp_con (ve, e'))
|[ FS[ i]]))
(A (accp a, accessd num eta0 (accp a)))
eta0)
(A (accp a, (exp_con (ve, e')) |[ fin_0H E'])
eta)) (accp a)) with (max ve (Nat.lt_0_succ n)) 
      by (rewrite <- Amax_aux with (a:=a) (eta:=eta) ; repeat f_equal; oauto).
  specialize IHn with (m:=m) (E:=leS_le E) (e:=ve) (a:=a) (eta:=eta) (x:=x) (E':= (Nat.lt_0_succ n)).
   destruct (gtb (exp_con (ve, e')) |[ '[ S n]] (max ve (Nat.lt_0_succ n))) eqn : E1;
   [rewrite If_true | rewrite If_false]; rewrite Avar; 
   (rewrite access_assign_neq'; [ | oauto]); (rewrite <- IHn; [| oauto]); repeat f_equal...
Qed.

Lemma Amax' : forall n m {E : n <= m} (e : exp (ary [n|E] num)) a {E' : 0 < n},
  A(accp a, max e E') = 
  C(e,fun x => Max x (fun x' => (fun tmp:acc num => A(tmp,x'))) (fun r => A((accp a),r)) a E').
Proof with oauto.
  intros. rewrite Avar. rewrite Cunfold. unfold Max, new.
  unfold seq. fun_ext. rename x into eta. rewrite Avar.
  replace ( accessd num
(comm_seq
(fun (i : fin n) (eta0 : env) =>
If (gtb e |[ i] (accessd num eta0 (accp a)))
(A (accp a, e |[ i]))
(A (accp a, accessd num eta0 (accp a)))
eta0) (A (accp a, e |[ fin_0H E']) eta))
(accp a))
         with  (max e E')  by (symmetry; apply Amax_aux).
    apply access_eq_env; intros.
    rewrite !access_assign'. destruct (a =? x) eqn : E0; path_simpl. oauto.
    symmetry. rewrite Amax_aux'...
Qed.

Lemma Amax : forall n m {E : n <= m} (e : exp (ary [n|E] num)) a {E' : 0 < n},
  A(a, max e E') = 
  C(e,fun x => Max x (fun x' => (fun tmp:acc num => A(tmp,x'))) (fun r => A(a,r)) a E').
Proof. apply Amax'. Qed.



Definition Sum {m n} {E:n <= m} (e : exp (ary [n|E] num))
  (f:exp num -> acc num -> comm) (c : exp num -> comm) (a:path) :=
  new (fun tmp => tmp |:= zero '; 
  comm_seq (fun (i:fin n) eta => f (add (e |[i]) (accessd num eta tmp)) tmp eta) ';
  fun eta => c (accessd num eta tmp) eta) (accp a).

(** *** Lemma *)

(** 化简 sum 0 *)
Lemma sum_0 : forall m  {E : 0 <= m} (e : exp(ary [0|E] num)),
  sum e = zero.
Proof. intros. apply reduce_0. Qed.

(** 化简 sum (S n) *)
Lemma sum_Sn : forall m n {E : S n <= m} (ve : exp (ary [n| leS_le E] num)) e,
  sum (exp_con (ve, e)) = add e (sum ve).
Proof. intros. apply reduce_Sn. Qed.

(** 化简 A(a, sum e) *)
Lemma Asum_aux : forall n m {E : n <= m} (e : exp (ary [n | E] num)) (a: path) eta,
  accessd num (comm_seq
 (fun (i : fin n) (eta0 : env) =>
         A (accp a, add e |[ i] (accessd num eta0 (accp a))) eta0)
        ((accp a |:= zero) eta)) (accp a) = sum e.
Proof with oauto.
  induction n; intros.
  - rewrite comm_seq_0.  unfold skip. unfold accessd. rewrite access_assign_eq...
  - destruct (exp_des e) as [ve e'] eqn : E0.
    replace e with (exp_con (ve, e')) by (rewrite <- E0; apply exp_con_des).
    specialize IHn with (m:=m) (E:= leS_le E) (e:=ve) (a:=a) (eta:=eta).
    rewrite comm_seq_Sn. unfold seq.
  replace (accessd num
           (comm_seq
              (fun (i : fin n) (eta0 : env) =>
               A
                 (accp a,
                  add (exp_con (ve, e')) |[ FS[ i]] (accessd num eta0 (accp a))) eta0)
              ((accp a |:= zero) eta)) (accp a))
    with (sum ve) by( rewrite <- IHn; repeat f_equal; oauto).
  replace (add (exp_con (ve, e')) |[ '[ n]] (sum ve)) with (sum (exp_con (ve, e'))).
  2 :{ rewrite sum_Sn. f_equal. replace (fin_lstH (Nat.lt_0_succ n)) with '[n] by oauto.
  rewrite e_idx_tail... } rewrite Avar. unfold accessd. rewrite access_assign_eq...
Qed.

Lemma Asum_aux' : forall n m {E : n <= m} (x a : path) (e : exp (ary [n | E] num)) (eta : env),
  x <> a -> @access_aux num
  (comm_seq
     (fun (i : fin n) (eta0 : env) =>
      A (accp a, add e |[ i] (accessd num eta0 (accp a))) eta0)
     ((accp a |:= zero) eta)) (accp x) = access_aux eta (accp x).
Proof with oauto.
  induction n. simpl... unfold skip... intros. destruct (exp_des e) as [ve e'] eqn : E0.
  replace e with (exp_con (ve, e')) by (rewrite <- E0; apply exp_con_des).
  rewrite comm_seq_Sn. unfold seq.
  specialize IHn with (m:=m) (E:= (leS_le E)) (x:=x) (a:=a) (e:=ve) (eta:=eta).
  unfold accessd at 1.
  destruct ( access
            (comm_seq
               (fun (i : fin n) (eta0 : env) =>
                A
                  (accp a,
                   add (exp_con (ve, e')) |[ FS[ i]] (accessd num eta0 (accp a))) eta0)
               ((accp a |:= zero) eta)) (accp a));
    (rewrite Avar; (rewrite access_assign_neq'; [ | oauto]);
    (rewrite <- IHn; [ | oauto]); repeat f_equal)...
Qed.

Lemma Asum' : forall n m {E : n <= m} (e : exp (ary [n|E] num)) (a : path),
  A(accp a, sum e) = C(e, fun x => Sum x (fun x' => (fun tmp => A(tmp,x'))) (fun r => A(accp a, r)) a).
Proof with oauto.
  intros. rewrite Avar. rewrite Cunfold. unfold Sum. unfold new. 
  unfold seq. fun_ext. rename x into eta. rewrite Avar.
  replace (accessd num(comm_seq
 (fun (i : fin n) (eta0 : env) =>
         A (accp a, add e |[ i] (accessd num eta0 (accp a))) eta0)
        ((accp a |:= zero) eta)) (accp a))
        with (sum e) by (symmetry; apply Asum_aux).
  apply access_eq_env. intros x. rewrite !access_assign'. 
  destruct (a =? x) eqn : E0; path_simpl. simpl... symmetry. rewrite Asum_aux'...
Qed.

Lemma Asum : forall n m {E : n <= m} (e : exp (ary [n|E] num)) (a : acc num),
  A(a, sum e) = C(e, fun x => Sum x (fun x' => (fun tmp => A(tmp,x'))) (fun r => A(a, r)) a).
Proof with oauto. apply Asum'. Qed.

Lemma Aseq_aux: forall (n : nat) (d : data) (f : fin n -> exp d) a,
   a |:= seq_make f = comm_seq (fun i : fin n => a |{ i} |:= f i).
Proof with oauto.
  destruct n. simpl... intros. unfold assign. fun_ext. f_equal.
   unfold assign. fun_ext. f_equal...
Qed. 

Theorem Aseq: forall (n:nat) (d:data) (f:fin n -> exp d) a, 
  A(a, seq_make f ) = comm_seq (fun i : fin n => A (a |{i}, f i)).
Proof. intros. rewrite Aunfold. apply Aseq_aux. Qed.

Definition Let{s t}(e:exp s)(f:exp s -> acc t -> comm)(out:acc t) :=
  f e out.


Theorem Alet: forall {s t} (e:exp s)(f:exp s -> exp t)(a:acc t),
  A(a,binding e f ) =  C(e,fun x => Let x 
                          (fun x1:exp s => (fun o:acc t => A(o,f x1))) a).
Proof. 
  simpl. unfold Let,binding. auto. 
Qed.

Theorem Aif: forall (n:nat) (d:data) (a:acc(ary '{n} d)) (b:bool) e1 e2 i,
  A(a|{i},if b then e1 else e2) = If b (A(a|{i},e1)) (A(a|{i},e2)).
Proof.
  intros. unfold If. fun_ext; simpl. destruct b; auto.
Qed.


Theorem Aif1: forall(d:data) (a:acc d) (b:bool) e1 e2,
  (a|:= if b then e1 else e2) = If b (a|:= e1) (a|:=e2).
Proof.
  intros. unfold If. fun_ext; simpl. destruct b; auto. 
Qed.



Lemma Aif2 : forall {d} (a : acc d) (i1 i2 : nat) (f: i1 < i2 -> exp d) (e: exp d),
  A (a, (match lt_dec i1 i2 with
   | left P1 => f P1
   | right P2 => e
   end)) = If (i1 <? i2) (A (a,(f alwayslt))) (A (a,e)).
Proof with oauto.
  intros. destruct (lt_dec i1 i2). replace (i1 <? i2) with true by oauto.
  rewrite If_true. rewrite !Aunfold. repeat f_equal...
  replace (i1 <? i2) with false by oauto. rewrite If_false...
Qed.

Axiom Aif3 : forall {d} (a : acc d) (i1 i2 i3 i4 : nat) 
  (f: i1 < i2 -> i3 < i4 -> exp d) (e: exp d),
  A (a, (match (lt_dec i1 i2), (lt_dec i3 i4) with
   | left P1, left P2 => f P1 P2
   | _, _ => e
   end)) = If ((i1 <? i2)%nat && (i3 <? i4) %nat) (A (a,(f alwayslt alwayslt))) (A (a,e)).



(** 展开 C(negate e, f) *)
Lemma Cneg: forall (e:exp num) (f : exp num -> comm) ,
  C(negate e, f) = C(e, fun x => f (negate x)).
Proof. unfold C. auto. Qed.

(** 展开 C(inv e, f) *)
Lemma Cinv : forall (e: exp num) (f: exp num -> comm),
  C(inv e, f) = C(e, fun x => f (inv e)).
Proof. oauto. Qed.

(** 展开 C(epow e, f) *)
Lemma Cepow : forall (e:exp num) (f : exp num -> comm),
  C(epow e, f) = C(e, fun x => f (epow e)).
Proof. oauto. Qed.


(** 展开 C(ln e, f) *)
Lemma Cln : forall (e:exp num) (f : exp num -> comm),
  C(ln e, f) = C(e, fun x => f (ln x)).
Proof. oauto. Qed.

Lemma Csqrt : forall (e:exp num) (f : exp num -> comm),
  C(sqrt e, f) = C(e, fun x => f (sqrt x)).
Proof. oauto. Qed.

(** 化简 C(add x y, f) *)
Lemma Cadd : forall (x y:exp num) (f : exp num -> comm),
  C(add x y, f) = C(x, fun e => (C(y, fun e' => f (add e e')))).
Proof. oauto. Qed.


(** 化简 C(sub x y, f) *)
Lemma Csub : forall (x y:exp num) (f : exp num -> comm),
  C(sub x y, f) = C(x, fun e => (C(y, fun e' => f (sub e e')))).
Proof. oauto. Qed.


(** 化简 C(mul x y, f) *)
Lemma Cmul : forall (x y:exp num) (f : exp num -> comm),
  C(mul x y, f) = C(x, fun e => (C(y, fun e' => f (mul e e')))).
Proof. oauto. Qed.

(** 化简 C(scal x y, f) *)
Lemma Cscal : forall (x : R) (y:exp num) (f : exp num -> comm),
  C(scal x y, f) = C(y, fun e => f (scal x y)).
Proof. oauto. Qed.

(** 化简 C(div x y, f) *)
Lemma Cdiv : forall (x y:exp num) (f : exp num -> comm),
  C(div x y, f) = C(x, fun e => C(y, fun e' => f (div e e'))).
Proof. oauto. Qed.


(** 化简 C(divn x y, f) *)
Lemma Cdivn : forall (x:exp num) (y: nat) (f : exp num -> comm),
  C(divn x y, f) = C(x, fun e => f (divn e y)).
Proof. oauto. Qed.



Axiom Csum : forall n m {E : n <= m} (e : exp (ary [n|E] num)) (c: exp num -> comm),
    C(sum e , c) = 
   C(e, fun x => Sum x (fun x' o' => A(o',x')) c mytmp).



Axiom Cmax: forall n m {E : n <= m} (e:exp (ary [n|E] num)) (E': 0 < n)
   (c: exp num -> comm),
   C(max e E', c) = 
  C(e, fun x  => Max x (fun x' o' => A(o',x')) c mytmp E').




  Lemma new_equiv: forall d (e:exp d)(c: exp d -> comm)(tmp : tmp_path),
  new (fun tmp => tmp |:= e '; 
  fun eta => c (accessd d eta tmp) eta) (accp tmp) = c e.
Proof with oauto.
  intros. fun_ext. unfold new, seq, accessd.
  rewrite access_assign_eq. destruct (optexp e) as [val |] eqn : E.
  assert (e = val)... apply assign_tmp. assert (e = (@exp_default d))...
  apply assign_tmp.
Qed.

Theorem Cseq: forall (n:nat)(d:data) (f:fin n -> exp d)
  (c:exp (ary '{n} d) -> comm),
  C(seq_make f, c) =
  new (fun tmp => A(tmp, seq_make f) ';
  fun eta => c (accessd (ary '{ n} d) eta tmp) eta) (accp mytmp).
Proof. intros. rewrite Cunfold. symmetry; apply new_equiv. Qed.




Lemma join_equiv: forall (n1 n2 : nat) d  
  (e : exp (ary '{n1} (ary '{n2} d))) ,
  join e = seq_make (fun i : fin (n1 * n2) =>
    e|[fst(fin_1to2d i)]|[snd(fin_1to2d i)]).
Proof with oauto.
  intros. unfold join, v_join, seq_make.
  f_equal; fun_ext. destruct (fin_1to2d x) eqn : E. unfold e_idx;
  simpl in *. repeat f_equal; rewrite E...
Qed.



Lemma Cjoin : forall (n1 n2 : nat) d (e : exp (ary '{n1} (ary '{n2} d))) c,
  C(join e, c) = C(seq_make (fun i : fin (n1 * n2) =>
    e|[fst(fin_1to2d i)]|[snd(fin_1to2d i)]),c).
Proof. intros. repeat f_equal. rewrite join_equiv. auto. Qed.





Lemma concat_equiv: forall {n1 n2 : nat} d
  (e1 : exp (ary '{n1} d)) (e2 : exp (ary '{n2} d)),
  concat e1 e2 = seq_make (fun i : fin (n1 + n2) =>
    if i <? n1 then e1|[[fin2nat i|@alwayslt i n1]] else e2|[[(fin2nat i)-n1|@alwayslt (i - n1) n2]]).
Proof with oauto.
  intros. unfold concat, v_concat, seq_make. f_equal.
Qed.


Axiom Clet: forall {s t} (e:exp s)(f: exp s -> exp t)(c: exp t -> comm),
  C(binding e f, c ) = new (fun tmp => A(tmp, binding e f) '; 
    (fun eta => c (accessd t eta tmp) eta)) (accp mytmp).



Axiom Cif: forall (d:data)(b:bool) e1 e2 (c:exp d -> comm),
  C(if b then e1 else e2, c) = If b (C(e1,c)) (C(e2,c)).


