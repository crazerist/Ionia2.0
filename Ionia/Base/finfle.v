Require Export fin fle.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Coq.Logic.Classical_Prop.

Set Implicit Arguments.


(* ######################################################################### *)
(** * Ltac *)

(** ** f_simpl *)

(** 定义 fin 化简:
1. 分析 i: fin 0 的前提
2. 分析 i: fin 1 和 i: fle n 的前提
3. 若目标为 < 或者 <=, 尝试通过 fin 或者 fle 的性质证明
4. 若目标为 =, 尝试通过 fin_eq 进行分析 *)

Ltac f_simpl:=
 repeat match goal with
 | [ x: fin 0 |- _ ] => destruct (fin'_0 x)
 | [ x: fin (?m * 0) |- _ ] => destruct (fin'_0_r x)
 | [ x: fin (0 * ?n) |- _ ] => destruct (fin'_0_l x)
 | [ x: fin 1 |- _ ] => replace x with '[0] by apply fin'_1_unique
 | [ x: fle 0 |- _ ] => replace x with '{0} by apply fle'_0_unique
 | [ |- (fin2nat ?x) < _ ] => try (pose proof (fin_proof ?x); simpl; lia)
 | [ |- (fin2nat ?x) <= _ ] => try (pose proof (fin_proof ?x); simpl; lia)
 | [ x: fin ?n |- _ < ?n ] => try (pose proof (fin_proof x); simpl; lia)
 | [ x: fin ?n |- _ <= ?n ] => try (pose proof (fin_proof x); simpl; lia)
 | [ x: fin ?n |- _ <> ?n ] => try (pose proof (fin_proof x); simpl; lia)
 | [ |- (fle2nat ?x) < _ ] => try (pose proof (fle_proof ?x); simpl; lia)
 | [ |- (fle2nat ?x) <= _ ] => try (pose proof (fle_proof ?x); simpl; lia)
 | [ x: fle ?n |- _ < ?n ] => try (pose proof (fle_proof x); simpl; lia)
 | [ x: fle ?n |- _ <= ?n ] => try (pose proof (fle_proof x); simpl; lia)
 | [ |- _ = _ ] => try (apply fin_eq'; simpl; auto); try (apply fle_eq'; simpl; auto)
 end.

(** 定义 fauto, 包含 finType 和 fleType 所定义的一些引理和定义 *)
Ltac fauto:=
 repeat (quan_simpl; bool_simpl; opt_simpl; pair_simpl; fun_simpl; f_simpl); subst; 
 autorewrite with fcore core ; auto with fcore core; try lia; try apply proof_irrelevance.


(* ######################################################################### *)
(** * Fin Combination *)

Section Fin_Comb.

(** ** fin_fle *)

(** *** Definition *)

(** 定义 fin_fle, 将一个 i : fin (fle2nat (n : fle m)) 转变为 i : fin m*)
Definition fin_fle {m} (n : fle m) (i : fin n) : fin m :=
 F[fin_lt i (fle_proof n)].

(** *** Example *)

(** 将 3 : fin (5 : fle 7) 转变为 3 : fin 7 *)
Example _5le7 : 5 <= 7. Proof. lia. Qed.

Example _3lt5 : 3 < F'[_5le7]. Proof. simpl. lia. Qed.

Goal fin2nat (fin_fle F'[_5le7] F[_3lt5] : fin 7) = 3.
Proof. auto. Qed.

End Fin_Comb.

(** ** Tactics *)

Notation "FF'[ i | n ]" := (fin_fle n i).


(* ######################################################################### *)
(** * Utils *)

Section Utils.

(** ** fin_aux lemma *)

Lemma fin_lem1: forall {m n s} (i : fin ((m-n)/s+1)) (j: fin n),
 n <= m -> i * s + j < m.
Proof with fauto.
 intros. destruct i as [i Hi]. destruct j as [j Hj].
 simpl in *. assert (i <= (m - n) / s)... clear Hi.
 assert (s*i <= s*((m - n) / s)). apply Nat.mul_le_mono_l...
 clear H0. rewrite Nat.mul_comm in H1. assert (i * s <= m - n).
 eapply Nat.le_trans. apply H1. apply Nat.Div0.mul_div_le. clear H1.
 replace m with (m - n + n)...
Qed.

Lemma fin_lem2: forall {n k} (i :fin (n/k)) (j: fin k),
 i * k + j < n.
Proof with fauto.
 intros. destruct i as [i Hi]. destruct j as[j Hj]. simpl.
 assert (E : k <= n). { destruct (classic (k <= n))... 
 assert (n < k)... assert (n/k=0)... apply Nat.div_small... }
 assert (i <= n/k - 1)... clear Hi. assert (k*i <= k*(n/k-1)).
 apply Nat.mul_le_mono_l... clear H. rewrite Nat.mul_comm in H0.
 rewrite Nat.mul_sub_distr_l in H0. rewrite Nat.mul_1_r in H0.
 assert (i*k <= n - k). eapply Nat.le_trans. apply H0. apply Nat.sub_le_mono_r.
 apply Nat.Div0.mul_div_le. replace n with (n - k + k).
 apply Nat.add_le_lt_mono... apply Nat.sub_add...
Qed.

Lemma fin_lem3: forall {n k s} (i: fin ((n-k)/s + 1)) (j: fin k),
 k <= n -> i * s + j < n.
Proof with fauto.
 intros. destruct i as [i Hi]. destruct j as[j Hj]. simpl.
 assert (i <= (n-k)/s)... assert (s*i <= s*((n-k)/s)).
 apply Nat.mul_le_mono_l... clear H0. rewrite Nat.mul_comm in H1.
 assert (i*s<=n-k). eapply Nat.le_trans. apply H1.
 apply Nat.Div0.mul_div_le. replace n with (n - k + k).
 apply Nat.add_le_lt_mono... apply Nat.sub_add...
Qed.

Lemma fin_lem4: forall {n s} (i: fin ((n-1)*s+1)),
  0 < n -> i/s < n.
Proof with fauto.
  intros. destruct i as [i Hi]. simpl.
  destruct n. inv H. destruct s. simpl. lia. simpl in Hi.
  rewrite !Nat.sub_0_r in Hi. apply Nat.Div0.div_lt_upper_bound.
  eapply Nat.lt_le_trans. apply Hi. replace (S s * S n) with (s + (s*n + n + 1)) by lia.
  replace (n * S s + 1) with (0+(s*n + n + 1)) by lia. apply Nat.add_le_mono_r...
Qed.

Lemma fin_lem5 : forall {n m p} (i : fin (m+n-2*p)) (j : fin n),
  1+p<=n -> i + j < m + 1 + 2*(n -1 -p).
Proof with fauto.
  intros. destruct i as [i Hi]. destruct j as[j Hj]. simpl.
  replace (m+1+(n-1-p+(n-1-p+0))) with ((m+n-2*p)+(n-1)) by lia.
  apply Nat.add_lt_le_mono...
Qed.

Lemma fin_lem6: forall {n k} (i : fin (n - k)),
  k <= n -> i + k < n.
Proof. intros. destruct i as [i Hi]. simpl. lia. Qed.

Lemma fin_lem7: forall {n k} (i : fin k) (j : fin (n/k)),
  i * (n/k) + j < n.
Proof with fauto.
  intros. destruct i as [i Hi]. destruct j as[j Hj]. simpl.
  assert (0 < k)... apply Nat.mul_lt_mono_pos_l with (p:=k)...
  replace (k * (i * (n / k) + j)) with (i*(k*(n/k))+j*k) by lia.
  apply Nat.le_lt_trans with (i*n + j*k).
  apply Nat.add_le_mono_r. apply Nat.mul_le_mono_l.
  apply Nat.Div0.mul_div_le. destruct k... assert (i <= k)...
  replace (S k * n) with (k * n + n) by lia. apply Nat.add_le_lt_mono.
  apply Nat.mul_le_mono_r... assert ((S k) * j < (S k) * (n / S k)).
  apply Nat.mul_lt_mono_pos_l... rewrite Nat.mul_comm in H1.
  eapply Nat.lt_le_trans. apply H1. apply Nat.Div0.mul_div_le.
Qed.

Lemma fin_lem8: forall {n k} (i: fin (k*n)),  i/k < n.
Proof. 
  intros. destruct i as [i Hi]. simpl. apply Nat.Div0.div_lt_upper_bound. auto.
Qed.

Lemma fin_lem9: forall {n m} (i: fin (m + n -1)) (j : fin n),
  0 < n -> i + j < m + 2 * (n - 1).
Proof with fauto.
  intros. destruct i as [i Hi]. destruct j as[j Hj].
  replace (m + 2 * (n - 1)) with (m + n - 1 + (n - 1))... simpl.
  apply Nat.add_lt_le_mono...
Qed.

Lemma fin_lem10: forall {n} (i: fin n),
  n - 1 - i < n.
Proof with fauto.
  intros. destruct i as [i Hi]. simpl...
Qed.

Lemma fin_lem11: forall {n m} (i: fin n) (j: fin m),
  i + j < m + n - 1.
Proof with fauto.
  intros. destruct i as [i Hi]. destruct j as[j Hj]; simpl...
Qed.

Lemma fin_lem12 : forall {m s} (i: fin ((m+2*0-1)/s + 1)), 0 < m -> i < m.
Proof with fauto.
  intros. destruct i as [i Hi]. simpl. destruct m...
  simpl in Hi. rewrite Nat.add_sub in Hi. rewrite <- Nat.add_1_r.
  eapply Nat.lt_le_trans. apply Hi. apply Nat.add_le_mono_r.
  destruct s. simpl... apply Nat.Div0.div_le_upper_bound...
Qed.

End Utils.