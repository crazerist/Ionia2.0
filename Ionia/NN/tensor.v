Require Export rule.

Set Implicit Arguments.

(* ********************************Tensor************************* *)

Definition Tensor1 (m       : nat) := exp (ary '{m} num).

Definition Tensor1_unfold {m} (input : Tensor1 m) : exp (ary '{m} num).
Proof. exact input. Defined.
Definition Tensor1_fold {m} (input : exp (ary '{m} num)) : Tensor1 m.
Proof. exact input. Defined.

Definition Tensor2 (m n     : nat) := exp (ary '{m} (ary '{n} num)).

Definition Tensor2_unfold {m n} (input : Tensor2 m n) : exp (ary '{m} (ary '{n} num)).
Proof. exact input. Defined.
Definition Tensor2_fold {m n} (input : exp (ary '{m} (ary '{n} num))) : Tensor2 m n.
Proof. exact input. Defined.


Definition Tensor3 (m n p   : nat) := exp (ary '{m} (ary '{n} (ary '{p} num))).

Definition Tensor3_unfold {m n p} (input : Tensor3 m n p) : exp (ary '{m} (ary '{n} (ary '{p} num))).
Proof. exact input. Defined.
Definition Tensor3_fold {m n p} (input : exp (ary '{m} (ary '{n} (ary '{p} num)))) : Tensor3 m n p.
Proof. exact input. Defined.


Definition Tensor4 (m n p q : nat) := exp (ary '{m} (ary '{n} (ary '{p} (ary '{q} num)))).

Definition Tensor4_unfold {m n p q} (input : Tensor4 m n p q) : exp (ary '{m} (ary '{n} (ary '{p} (ary '{q} num)))).
Proof. exact input. Defined.
Definition Tensor4_fold {m n p q} (input : exp (ary '{m} (ary '{n} (ary '{p} (ary '{q} num))))) : Tensor4 m n p q.
Proof. exact input. Defined.


Definition Default1d (n : nat) : Tensor1 n := exp_default.

Definition Default2d (m n : nat) : Tensor2 m n := exp_default.

Definition Default3d (channel m n : nat) : Tensor3 channel m n := exp_default.

Definition Default4d (batch channel m n : nat) : Tensor4 batch channel m n := exp_default.

Definition Randn1d (n : nat) : Tensor1 n := seq_make (fun i : fin n => rand).

Definition Randn2d (n m : nat) : Tensor2 n m :=
  seq_make (fun i: fin n => seq_make (fun j: fin m => rand)).

Definition Rand3d (channel m n : nat) : Tensor3 channel m n :=
  seq_make (fun c: fin channel => seq_make (fun i: fin m =>
  seq_make (fun j: fin n => rand))).

Definition Rand4d (batch channel m n : nat) : Tensor4 batch channel m n :=
  seq_make (fun b: fin batch => seq_make (fun c: fin channel =>
  seq_make (fun i: fin m => seq_make (fun j: fin n => rand)))).

Definition Fill1d (m : nat) (e: exp num) : Tensor1 m := seq_make (fun i : fin m => e).

Definition Fill2d (n m : nat) (e: exp num) : Tensor2 n m:=
  seq_make (fun i: fin n => seq_make (fun j: fin m => e)).

Definition Fill3d (n m channel : nat) (e: exp num) : Tensor3 channel n m:=
  seq_make (fun c : fin channel => seq_make (fun i: fin n => seq_make (fun j: fin m => e))).

Definition Fill4d (n m batch channel : nat) (e: exp num) : Tensor4 batch channel n m:=
  seq_make (fun b : fin batch => (seq_make (fun c : fin channel => 
  seq_make (fun i: fin n => seq_make (fun j: fin m => e))))).

Ltac Tensor_unfold :=
  unfold Tensor1_unfold, Tensor2_unfold, Tensor3_unfold, Tensor4_unfold.