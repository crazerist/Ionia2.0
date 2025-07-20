Require Export tensor.

Arguments Nat.div : simpl never.

(* Tensor1 n *)
Definition ReLU1d {n} (input: Tensor1 n) :=
  seq_make (fun i:fin n => 
  if (leb (Tensor1_unfold input)|[i] zero) then zero else (Tensor1_unfold input)|[i]).

(* Tensor2 n m *)
Definition ReLU2d {n m} (input: Tensor2 n m) :=
  seq_make (fun i:fin n => seq_make (fun j:fin m => 
  if (leb (Tensor2_unfold input)|[i]|[j] zero) then zero else (Tensor2_unfold input)|[i]|[j])).

(* Tensor3 filernum n m *)
Definition ReLU3d {n m filernum} (input: Tensor3 filernum n m) :=
  seq_make (fun num: fin filernum => seq_make (fun i:fin n => seq_make (fun j:fin m => 
  if (leb (Tensor3_unfold input)|[num]|[i]|[j] zero) then zero else (Tensor3_unfold input)|[num]|[i]|[j]))).

Definition ReLU4d {n m batch filernum} (input: Tensor4 batch filernum n m) : Tensor4 batch filernum n m :=
  seq_make (fun b:fin batch => seq_make (fun num: fin filernum => seq_make (fun i:fin n => seq_make (fun j:fin m => 
  if (leb (Tensor4_unfold input)|[b]|[num]|[i]|[j] zero) then zero else (Tensor4_unfold input)|[b]|[num]|[i]|[j])))).

Definition Softmax1d {m} (input: Tensor1 m) :=
  tlet s := sum (seq_make (fun i:fin m => epow (Tensor1_unfold input)|[i])) in
  seq_make (fun j:fin m => div (epow (Tensor1_unfold input)|[j]) s).

Definition Softmax2d {n batch} (input: Tensor2 batch n) :=
  tlet s := seq_make (fun b:fin batch => sum (seq_make (fun i:fin n => epow (Tensor2_unfold input)|[b]|[i]))) in 
  seq_make (fun b:fin batch => seq_make (fun j:fin n => div (epow (Tensor2_unfold input)|[b]|[j]) s|[b])).

Definition Softmax3d {n m filernum:nat} (input : Tensor3 filernum n m)  :=
  tlet s := sum (seq_make (fun num:fin filernum => sum (seq_make (fun i:fin n =>
    sum (seq_make (fun j:fin m => epow (Tensor3_unfold input)|[num]|[i]|[j])))))) in
  seq_make (fun num:fin filernum => seq_make (fun i:fin n => seq_make (fun j:fin m =>
  div (epow (Tensor3_unfold input)|[num]|[i]|[j]) s))).

Definition Softmax4d {n m batch filernum} (input: Tensor4 batch filernum n m)  :=
  tlet s := seq_make (fun b: fin batch => sum (seq_make (fun num : fin filernum => 
    sum (seq_make (fun i:fin n => sum (seq_make (fun j:fin m => 
    epow (Tensor4_unfold input)|[b]|[num]|[i]|[j]))))))) in 
  seq_make (fun b: fin batch => seq_make (fun num:fin filernum => 
  seq_make (fun i:fin n => seq_make (fun j:fin m => 
  div (epow (Tensor4_unfold input)|[b]|[num]|[i]|[j]) (s|[b]))))).

Definition Sigmoid1d {m} (input : Tensor1 m)  :=
  seq_make (fun i:fin m => div one (add one (epow (negate (Tensor1_unfold input)|[i])))).

Definition Sigmoid2d {n m} (input : Tensor2 n m)  :=
  seq_make (fun i:fin n => seq_make (fun j: fin m =>
  div one (add one (epow (negate (Tensor2_unfold input)|[i]|[j]))))).

Definition Sigmoid3d {channel n m} (input: Tensor3 channel n m)  := 
  seq_make (fun c:fin channel => seq_make (fun i:fin n => seq_make (fun j:fin m => 
  div one (add one (epow (negate (Tensor3_unfold input)|[c]|[i]|[j])))))).

Definition Sigmoid4d {n m batch channel} (input: Tensor4 batch channel n m)  :=
  seq_make (fun b:fin batch => seq_make (fun c: fin channel =>
  seq_make (fun i:fin n => seq_make (fun j: fin m =>
  div one (add one (epow (negate (Tensor4_unfold input)|[b]|[c]|[i]|[j]))))))).

Definition Tanh1d {m} (input: Tensor1 m) :=
  seq_make (fun i: fin m => 
  div (sub (epow (Tensor1_unfold input)|[i])(epow (negate (Tensor1_unfold input)|[i])))
    (add (epow (Tensor1_unfold input)|[i])(epow (negate (Tensor1_unfold input)|[i])))).

Definition Tanh2d {n m} (input: Tensor2 n m) :=
  seq_make (fun i: fin n => seq_make (fun j: fin m =>
  div (sub (epow (Tensor2_unfold input)|[i]|[j])(epow (negate (Tensor2_unfold input)|[i]|[j])))
    (add (epow (Tensor2_unfold input)|[i]|[j])(epow (negate (Tensor2_unfold input)|[i]|[j]))))).

Definition Tanh3d {n m channel} (input: Tensor3 channel n m) :=
  seq_make (fun c : fin channel => seq_make (fun i: fin n => seq_make (fun j: fin m =>
  div (sub (epow (Tensor3_unfold input)|[c]|[i]|[j])(epow (negate (Tensor3_unfold input)|[c]|[i]|[j])))
    (add (epow (Tensor3_unfold input)|[c]|[i]|[j])(epow (negate (Tensor3_unfold input)|[c]|[i]|[j])))))).

Definition Tanh4d {n m batch channel} (input: Tensor4 batch channel n m)  :=
  seq_make (fun b: fin batch => seq_make (fun c: fin channel=> 
  seq_make (fun i: fin n => seq_make (fun j: fin m =>
  div (sub (epow (Tensor4_unfold input)|[b]|[c]|[i]|[j])(epow (negate (Tensor4_unfold input)|[b]|[c]|[i]|[j])))
    (add (epow (Tensor4_unfold input)|[b]|[c]|[i]|[j])(epow (negate (Tensor4_unfold input)|[b]|[c]|[i]|[j]))))))).

Definition LeakyReLU1d {m} (negative_slope: exp num) (input : Tensor1 m)  :=
  seq_make (fun i : fin m => if (gtb (Tensor1_unfold input)|[i] zero)
    then (Tensor1_unfold input)|[i] else mul negative_slope (Tensor1_unfold input)|[i]).

Definition LeakyReLU2d {n m} (negative_slope: exp num) (input : Tensor2 n m) :=
  seq_make (fun i: fin n => seq_make (fun j: fin m => 
  if (gtb (Tensor2_unfold input)|[i]|[j] zero) 
    then (Tensor2_unfold input)|[i]|[j] else mul negative_slope (Tensor2_unfold input)|[i]|[j])).

Definition LeakyReLU3d {n m channel} (negative_slope: exp num) (input : Tensor3 channel n m) :=
  seq_make (fun c: fin channel => seq_make (fun i: fin n => seq_make (fun j: fin m =>
  if (gtb (Tensor3_unfold input)|[c]|[i]|[j] zero) 
    then (Tensor3_unfold input)|[c]|[i]|[j] else mul negative_slope (Tensor3_unfold input)|[c]|[i]|[j]))).

Definition LeakyReLU4d {n m batch channel} (negative_slope: exp num) (input : Tensor4 batch channel n m) :=
  seq_make (fun b: fin batch => seq_make (fun c: fin channel => seq_make (fun i: fin n => seq_make (fun j: fin m =>
  if (gtb (Tensor4_unfold input)|[b]|[c]|[i]|[j] zero) 
    then (Tensor4_unfold input)|[b]|[c]|[i]|[j] else mul negative_slope (Tensor4_unfold input)|[b]|[c]|[i]|[j])))).

Definition Exp1d {m} (input : Tensor1 m)  :=
  seq_make (fun i: fin m =>epow (Tensor1_unfold input)|[i]).

Definition Exp2d {n m} (input : Tensor2 n m)  :=
  seq_make (fun i: fin n => seq_make (fun j: fin m => epow (Tensor2_unfold input)|[i]|[j])).

Definition Exp3d {n m channel} (input : Tensor3 channel n m) :=
  seq_make (fun c : fin channel => seq_make (fun i: fin n => 
  seq_make (fun j: fin m => epow (Tensor3_unfold input)|[c]|[i]|[j]))).

Definition Exp4d {n m batch channel} (input : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i: fin n => 
  seq_make (fun j : fin m => epow (Tensor4_unfold input)|[b]|[c]|[i]|[j])))).

Definition Negate1d {m} (input : Tensor1 m) :=
  seq_make (fun i: fin m => negate (Tensor1_unfold input)|[i]).

Definition Negate2d {n m} (input : Tensor2 n m) : Tensor2 n m :=
  seq_make (fun i: fin n => seq_make (fun j: fin m => negate (Tensor2_unfold input)|[i]|[j])).

Definition Negate3d {n m channel} (input : Tensor3 channel n m) :=
  seq_make (fun c : fin channel => seq_make (fun i: fin n => 
  seq_make (fun j: fin m => negate (Tensor3_unfold input)|[c]|[i]|[j]))).

Definition Negate4d {n m batch channel} (input : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i: fin n => 
  seq_make (fun j : fin m => negate (Tensor4_unfold input)|[b]|[c]|[i]|[j])))).

Definition Addc1d {m} (e : exp num) (input : Tensor1 m) : Tensor1 m :=
  seq_make (fun i : fin m => add (Tensor1_unfold input)|[i] e).

Definition Addc2d {n m} (e : exp num) (input : Tensor2 n m) :=
  seq_make (fun i : fin n => seq_make (fun j : fin m => add (Tensor2_unfold input)|[i]|[j] e)).

Definition Addc3d {n m channel} (e : exp num) (input : Tensor3 channel n m)  :=
  seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => add (Tensor3_unfold input)|[c]|[i]|[j] e))).

Definition Addc4d {n m batch channel} (e : exp num) (input : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => add (Tensor4_unfold input)|[b]|[c]|[i]|[j] e)))).

Definition Add1d {m} (x : Tensor1 m) (y : Tensor1 m)  :=
  seq_make (fun i : fin m => add (Tensor1_unfold x)|[i] (Tensor1_unfold y)|[i]).

Definition Add2d {n m} (x : Tensor2 n m) (y : Tensor2 n m) : Tensor2 n m :=
  seq_make (fun i : fin n => seq_make (fun j : fin m =>
  add (Tensor2_unfold x)|[i]|[j] (Tensor2_unfold y)|[i]|[j])).

Definition Add3d {n m channel} (x : Tensor3 channel n m) (y : Tensor3 channel n m) :=
  seq_make (fun c : fin channel => seq_make (fun i : fin n => seq_make (fun j : fin m =>
  add (Tensor3_unfold x)|[c]|[i]|[j] (Tensor3_unfold y)|[c]|[i]|[j]))).

Definition Add4d {n m batch channel} (x : Tensor4 batch channel n m) (y : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => add (Tensor4_unfold x)|[b]|[c]|[i]|[j] (Tensor4_unfold y)|[b]|[c]|[i]|[j])))).

Definition Subc1d {m} (e : exp num) (input : Tensor1 m) :=
  seq_make (fun i : fin m => sub (Tensor1_unfold input)|[i] e).

Definition Subc2d {n m} (e : exp num) (input : Tensor2 n m)  :=
  seq_make (fun i : fin n => seq_make (fun j : fin m => sub (Tensor2_unfold input)|[i]|[j] e)).

Definition Subc3d {n m channel} (e : exp num) (input : Tensor3 channel n m)  :=
  seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => sub (Tensor3_unfold input)|[c]|[i]|[j] e))).

Definition Subc1d4d {n m batch channel} (e : exp num) (input : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => sub (Tensor4_unfold input)|[b]|[c]|[i]|[j] e)))).

Definition Sub1d {m} (x : Tensor1 m) (y : Tensor1 m)  :=
  seq_make (fun i : fin m => sub (Tensor1_unfold x)|[i] (Tensor1_unfold y)|[i]).

Definition Sub2d {n m} (x : Tensor2 n m) (y : Tensor2 n m)  :=
  seq_make (fun i : fin n => seq_make (fun j : fin m =>
  sub (Tensor2_unfold x)|[i]|[j] (Tensor2_unfold y)|[i]|[j])).

Definition Sub3d {n m channel} (x : Tensor3 channel n m) (y : Tensor3 channel n m) :=
  seq_make (fun c : fin channel => seq_make (fun i : fin n => seq_make (fun j : fin m =>
  sub (Tensor3_unfold x)|[c]|[i]|[j] (Tensor3_unfold y)|[c]|[i]|[j]))).

Definition Sub4d {n m batch channel} (x : Tensor4 batch channel n m) (y : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => sub (Tensor4_unfold x)|[b]|[c]|[i]|[j] (Tensor4_unfold y)|[b]|[c]|[i]|[j])))).

Definition Scal1d {m} (e : exp num) (input : Tensor1 m)  :=
  seq_make (fun i : fin m => scal e (Tensor1_unfold input)|[i]).

Definition Scal2d {n m} (e : exp num) (input : Tensor2 n m)  :=
  seq_make (fun i : fin n => seq_make (fun j : fin m => scal e (Tensor2_unfold input)|[i]|[j])).

Definition Scal3d {n m channel} (e : exp num) (input : Tensor3 channel n m) :=
  seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => scal e (Tensor3_unfold input)|[c]|[i]|[j]))).

Definition Scal4d {n m batch channel} (e : exp num) (input : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => scal e (Tensor4_unfold input)|[b]|[c]|[i]|[j])))).

Definition Mul1d {m} (x : Tensor1 m) (y : Tensor1 m) :=
  seq_make (fun i : fin m => mul (Tensor1_unfold x)|[i] (Tensor1_unfold y)|[i]).

Definition Mul2d {n m} (x : Tensor2 n m) (y : Tensor2 n m) : Tensor2 n m :=
  seq_make (fun i : fin n => seq_make (fun j : fin m =>
  mul (Tensor2_unfold x)|[i]|[j] (Tensor2_unfold y)|[i]|[j])).

Definition Mul3d {n m channel} (x : Tensor3 channel n m) (y : Tensor3 channel n m)  :=
  seq_make (fun c : fin channel => seq_make (fun i : fin n => seq_make (fun j : fin m =>
  mul (Tensor3_unfold x)|[c]|[i]|[j] (Tensor3_unfold y)|[c]|[i]|[j]))).

Definition Mul4d {n m batch channel} (x : Tensor4 batch channel n m) (y : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => mul (Tensor4_unfold x)|[b]|[c]|[i]|[j] (Tensor4_unfold y)|[b]|[c]|[i]|[j])))).

Definition Divn1d {m} (e : exp num) (input : Tensor1 m)  :=
  seq_make (fun i : fin m => div (Tensor1_unfold input)|[i] e).

Definition Divn2d {n m} (e : exp num) (input : Tensor2 n m)  :=
  seq_make (fun i : fin n => seq_make (fun j : fin m => div (Tensor2_unfold input)|[i]|[j] e)).

Definition Divn3d {n m channel} (e : exp num) (input : Tensor3 channel n m)  :=
  seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => div (Tensor3_unfold input)|[c]|[i]|[j] e))).

Definition Divn4d {n m batch channel} (e : exp num) (input : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => div (Tensor4_unfold input)|[b]|[c]|[i]|[j] e)))).

Definition Div1d {m} (x : Tensor1 m) (y : Tensor1 m)  :=
  seq_make (fun i : fin m => div (Tensor1_unfold x)|[i] (Tensor1_unfold y)|[i]).

Definition Div2d {n m} (x : Tensor2 n m) (y : Tensor2 n m)  :=
  seq_make (fun i : fin n => seq_make (fun j : fin m =>
  div (Tensor2_unfold x)|[i]|[j] (Tensor2_unfold y)|[i]|[j])).

Definition Div3d {n m channel} (x : Tensor3 channel n m) (y : Tensor3 channel n m)  :=
  seq_make (fun c : fin channel => seq_make (fun i : fin n => seq_make (fun j : fin m =>
  div (Tensor3_unfold x)|[c]|[i]|[j] (Tensor3_unfold y)|[c]|[i]|[j]))).

Definition Div4d {n m batch channel} (x : Tensor4 batch channel n m) (y : Tensor4 batch channel n m) :=
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => div (Tensor4_unfold x)|[b]|[c]|[i]|[j] (Tensor4_unfold y)|[b]|[c]|[i]|[j])))).

Definition Sum1d {n} (input : Tensor1 n) :=
  sum (seq_make (fun i : fin n => (Tensor1_unfold input)|[i])).

Definition Sum2d {n m} (input : Tensor2 n m)  :=
  sum (seq_make (fun i: fin n => sum (seq_make (fun j: fin m => (Tensor2_unfold input)|[i]|[j])))).

Definition Sum3d {n m channel} (input : Tensor3 channel n m)  :=
  sum (seq_make (fun b: fin channel => sum (seq_make (fun i : fin n => 
  sum (seq_make (fun j : fin m => (Tensor3_unfold input)|[b]|[i]|[j])))))).

Definition Sum4d {n m batch channel} (input : Tensor4 batch channel n m)  :=
  sum (seq_make (fun b : fin batch => sum (seq_make (fun c : fin channel => sum (seq_make (fun i: fin n =>
  sum (seq_make (fun j: fin m => (Tensor4_unfold input)|[b]|[c]|[i]|[j])))))))).

Definition Padding2d {n m} (p : nat) (input : Tensor2 n m)  :=
  seq_make (fun i : fin (n+2*p) => seq_make (fun j : fin (m+2*p) =>
  if (i <? p) || (j <? p) then exp_default else
    match (lt_dec (i-p) n), (lt_dec (j-p) m) with
    | left P1, left P2 => (Tensor2_unfold input)|[[i-p|P1]]|[[j-p|P2]]
    | _, _ => exp_default end)).

Definition Padding3d {n m channel} (p : nat) (input : Tensor3 channel n m)  := 
  seq_make (fun c: fin channel => Padding2d p (Tensor3_unfold input)|[c]).

Definition Padding4d {n m batch channel} (p : nat) (input : Tensor4 batch channel n m) := 
  seq_make (fun b: fin batch => seq_make (fun c : fin channel => Padding2d p (Tensor4_unfold input)|[b]|[c])).


Definition Conv2d {n1 n2 m1 m2} (p s:nat)(w : Tensor2 n1 n2) (input : Tensor2 m1 m2)
  (E1: n1 <= m1 + 2 * p) (E2: n2 <= m2 + 2 * p)  :=
  tlet pad := Padding2d p input in 
  seq_make (fun i1:fin ((m1+2*p-n1)/s+1) => seq_make (fun i2:fin ((m2+2*p-n2)/s + 1) =>
  sum (seq_make (fun j1:fin n1 => sum (seq_make ( fun j2: fin n2 => 
  mul pad|[[i1*s+j1|fin_lem1 i1 j1 E1]]|[[i2*s+j2|fin_lem1 i2 j2 E2]] (Tensor2_unfold w)|[j1]|[j2])))))).

Lemma Conv2d_test_aux : 2 <= 3 + 2 * 1. Proof. cbv; lia. Qed.

Definition input: Tensor2 3 3 := 
  [[1,2,3],[4,5,4],[3,2,1]]%R.

Definition w: Tensor2 2 2 := 
  [[1,0],[0,1]]%R.

Example Conv2d_test : Conv2d 1 1 w input Conv2d_test_aux Conv2d_test_aux =
  [[1,2,3,0],[4,6,6,3],[3,6,6,4],[0,3,2,1]]%R.
Proof. compute. repeat (f_equal; try lra). Qed.

Definition Conv3d {n1 n2 m1 m2 channel filernum} (p s : nat)
  (bias : Tensor1 filernum) (w : Tensor4 filernum channel n1 n2) (input : Tensor3 channel m1 m2)
  (E1: n1 <= m1 + 2 * p) (E2: n2 <= m2 + 2 * p)  :=
  tlet tmp := Padding3d p input in 
  seq_make (fun num: fin filernum => seq_make (fun i1:fin ((m1+2*p-n1)/s+1) => 
  seq_make (fun i2:fin ((m2+2*p-n2)/s + 1) => add (sum (seq_make (fun c:fin channel => 
  sum (seq_make (fun j1: fin n1 => sum (seq_make (fun j2: fin n2 => 
  mul tmp|[c]|[[i1*s+j1|fin_lem1 i1 j1 E1]]|[[i2*s+j2|fin_lem1 i2 j2 E2]] 
    (Tensor4_unfold w)|[num]|[c]|[j1]|[j2]))))))) (Tensor1_unfold bias)|[num]))).

Definition Conv4d {n1 n2 m1 m2 batch channel filernum} (p s : nat)
  (bias : Tensor1 filernum) (w : Tensor4 filernum channel n1 n2) (input : Tensor4 batch channel m1 m2)
  (E1: n1 <= m1 + 2 * p) (E2: n2 <= m2 + 2 * p)  :=
  tlet tmp := Padding4d p input in 
  seq_make (fun b:fin batch => seq_make (fun num: fin filernum => 
  seq_make (fun i1:fin ((m1+2*p-n1)/s+1) => seq_make (fun i2:fin ((m2+2*p-n2)/s+1) => 
  add (sum (seq_make (fun c:fin channel => sum (seq_make (fun j1: fin n1 => sum (seq_make (fun j2: fin n2 => 
  mul tmp|[b]|[c]|[[i1*s+j1|fin_lem1 i1 j1 E1]]|[[i2*s+j2|fin_lem1 i2 j2 E2]]  
    (Tensor4_unfold w)|[num]|[c]|[j1]|[j2]))))))) (Tensor1_unfold bias)|[num])))).

Definition Avgpool2d {n m} (k:nat) (input: Tensor2 n m)  :=
  seq_make (fun i1: fin (n/k) => seq_make (fun j1: fin (m/k) => 
  divn (sum (seq_make (fun i2: fin k => sum (seq_make (fun j2: fin k =>
    (Tensor2_unfold input)|[[i1*k+i2|fin_lem2 i1 i2]]|[[j1*k+j2|fin_lem2 j1 j2]])))))(k*k))).

Definition Avgpool3d {n m filernum} (k:nat) (input: Tensor3 filernum n m)  :=
  seq_make (fun num: fin filernum => seq_make (fun i1: fin (n/k) => seq_make (fun j1: fin (m/k) => 
  divn (sum (seq_make (fun i2:fin k => sum (seq_make (fun j2: fin k => 
    (Tensor3_unfold input)|[num]|[[i1*k+i2|fin_lem2 i1 i2]]|[[j1*k+j2|fin_lem2 j1 j2]])))))(k*k)))).

Definition Avgpool4d {n m batch filernum} (k:nat) (input: Tensor4 batch filernum n m)  :=
  seq_make (fun b: fin batch => seq_make (fun num: fin filernum => 
  seq_make (fun i1: fin (n/k) => seq_make (fun j1: fin (m/k) => 
  divn (sum (seq_make (fun i2: fin k => sum (seq_make (fun j2: fin k => 
    (Tensor4_unfold input)|[b]|[num]|[[i1*k+i2|fin_lem2 i1 i2]]|[[j1*k+j2|fin_lem2 j1 j2]])))))(k*k))))).

Definition Maxpool2d {n m} (k:nat) (input: Tensor2 n m) (Ek : 0 < k)  :=
  seq_make (fun i1: fin (n/k) => seq_make (fun j1:fin (m/k) => 
  max (seq_make (fun i2: fin k => max (seq_make (fun j2: fin k => 
    (Tensor2_unfold input)|[[i1*k+i2|fin_lem2 i1 i2]]|[[j1*k+j2|fin_lem2 j1 j2]]))Ek))Ek)).

Definition Maxpool3d {n m filernum} (k:nat) (input : Tensor3 filernum n m)
  (Ek : 0 < k) :=
  seq_make (fun num: fin filernum =>  seq_make (fun i1: fin (n/k) => seq_make (fun j1: fin (m/k) => 
  max (seq_make (fun i2: fin k => max (seq_make (fun j2: fin k => 
    (Tensor3_unfold input)|[num]|[[i1*k+i2|fin_lem2 i1 i2]]|[[j1*k+j2|fin_lem2 j1 j2]]))Ek))Ek))).

Definition Maxpool4d {n m batch filernum} (k:nat) (input : Tensor4 batch filernum n m)
  (Ek : 0 < k)  :=
  seq_make (fun b: fin batch => seq_make (fun num: fin filernum => 
  seq_make (fun i1: fin (n/k) => seq_make (fun j1: fin (m/k) => 
  max (seq_make (fun i2: fin k => max (seq_make (fun j2: fin k => 
    (Tensor4_unfold input)|[b]|[num]|[[i1*k+i2|fin_lem2 i1 i2]]|[[j1*k+j2|fin_lem2 j1 j2]]))Ek))Ek)))).

Definition AdaptiveAvgPool2d {m1 m2} (n1 n2:nat)
  (input: Tensor2 m1 m2)  :=
  seq_make (fun _: fin n1 => seq_make (fun _: fin n2 =>
  divn (sum (seq_make (fun i: fin m1 => sum (seq_make (fun j: fin m2 =>
    (Tensor2_unfold input)|[i]|[j])))))(n1*n2))).

Definition AdaptiveAvgPool3d {m1 m2 channel} (n1 n2:nat)
  (input: Tensor3 channel m1 m2)  :=
  seq_make (fun c: fin channel => seq_make (fun _: fin n1 => seq_make (fun _: fin n2 =>
  divn (sum (seq_make (fun i: fin m1 => sum (seq_make (fun j: fin m2 =>
    (Tensor3_unfold input)|[c]|[i]|[j])))))(n1*n2)))).

Definition AdaptiveAvgPool4d {m1 m2 batch channel} (n1 n2:nat)
  (input: Tensor4 batch channel m1 m2)  :=
  seq_make (fun b: fin batch => seq_make (fun c: fin channel =>
  seq_make (fun _: fin n1 => seq_make (fun _: fin n2 =>
  divn (sum (seq_make (fun i: fin m1 => sum (seq_make (fun j: fin m2 =>
    (Tensor4_unfold input)|[b]|[c]|[i]|[j])))))(n1*n2))))).

Definition Maxpool2d_pad {n m} (kersize stride padding : nat)
  (input: Tensor2 n m) (Ek:0 < kersize) (E1: kersize <= n+2*padding) (E2:kersize<=m+2*padding) 
   :=
  tlet tmp := Padding2d padding input in
  seq_make (fun i1:fin ((n+2*padding-kersize)/stride+1) => seq_make (fun j1:fin ((m+2*padding-kersize)/stride+1) => 
  max (seq_make (fun i2: fin kersize => max (seq_make (fun j2: fin kersize => 
    (Tensor2_unfold tmp)|[[i1*stride+i2|fin_lem3 i1 i2 E1]]|[[j1*stride+j2|fin_lem3 j1 j2 E2]]))Ek))Ek)).

Definition Maxpool3d_pad {n m filernum} (kersize stride padding : nat)
  (input: Tensor3 filernum n m) (Ek:0 < kersize) (E1: kersize <= n+2*padding) (E2:kersize<=m+2*padding)  :=
  tlet tmp := Padding3d padding input in
  seq_make (fun num: fin filernum => seq_make (fun i1:fin ((n+2*padding-kersize)/stride+1) =>
  seq_make (fun j1:fin ((m+2*padding-kersize)/stride+1) => 
  max (seq_make (fun i2: fin kersize => max (seq_make (fun j2: fin kersize => 
    (Tensor3_unfold tmp)|[num]|[[i1*stride+i2|fin_lem3 i1 i2 E1]]|[[j1*stride+j2|fin_lem3 j1 j2 E2]]))Ek))Ek))).

Definition Maxpool4d_pad {n m batch filernum} (kersize stride padding : nat)
  (input: Tensor4 batch filernum n m)
  (Ek:0 < kersize) (E1: kersize <= n+2*padding) (E2:kersize<=m+2*padding) :=
  tlet tmp := Padding4d padding input in
  seq_make (fun b: fin batch => seq_make (fun num: fin filernum => 
  seq_make (fun i1:fin ((n+2*padding-kersize)/stride+1) => seq_make (fun j1:fin ((m+2*padding-kersize)/stride+1) => 
  max (seq_make (fun i2: fin kersize => max (seq_make (fun j2: fin kersize => 
    (Tensor4_unfold tmp)|[b]|[num]|[[i1*stride+i2|fin_lem3 i1 i2 E1]]|[[j1*stride+j2|fin_lem3 j1 j2 E2]]))Ek))Ek)) )).

Definition Linear1d {n outnum} (w: Tensor2 outnum n)
  (bias: Tensor1 outnum)(input: Tensor1 n) :=
  seq_make (fun out:fin outnum => add (sum (seq_make (fun i:fin n => 
  mul (Tensor1_unfold input)|[i] (Tensor2_unfold w)|[out]|[i]))) (Tensor1_unfold bias)|[out]).

Definition Linear2d {n batch outnum} (w: Tensor2 outnum n)
  (bias: Tensor1 outnum)(input: Tensor2 batch n)  :=
  seq_make (fun b:fin batch => seq_make (fun out:fin outnum => add (sum (seq_make (fun i:fin n => 
  mul (Tensor2_unfold input)|[b]|[i] (Tensor2_unfold w)|[out]|[i]))) (Tensor1_unfold bias)|[out])).

Definition Linear3d {n batch channel outnum} (w: Tensor2 outnum n)
  (bias : Tensor1 outnum)(input: Tensor3 channel batch n) :=
  seq_make (fun c : fin channel => seq_make (fun b:fin batch => 
  seq_make (fun out : fin outnum => add (sum (seq_make (fun i : fin n => 
  mul (Tensor3_unfold input)|[c]|[b]|[i] (Tensor2_unfold w)|[out]|[i]))) (Tensor1_unfold bias)|[out]))).

Definition Linear4d {n batch channel filernum outnum} (w: Tensor2 outnum n)
  (bias : Tensor1 outnum)(input: Tensor4 channel batch filernum n)  :=
  seq_make (fun c : fin channel => seq_make (fun b:fin batch => seq_make (fun num:fin filernum => 
  seq_make (fun out : fin outnum => add (sum (seq_make (fun i : fin n => 
  mul (Tensor4_unfold input)|[c]|[b]|[num]|[i] (Tensor2_unfold w)|[out]|[i]))) (Tensor1_unfold bias)|[out])))).

Definition Matrix_mul {m n p} (x : Tensor2 m p) (y : Tensor2 p n)  :=
  seq_make (fun i:fin m => seq_make (fun j: fin n => 
  sum (seq_make (fun k:fin p => mul (Tensor2_unfold x)|[i]|[k] (Tensor2_unfold y)|[k]|[j])))).

Definition tensordot2d_3d {m h n s} (x : Tensor2 m h) (y : Tensor3 h n s)  :=
  seq_make (fun o : fin m => seq_make (fun i:fin n => seq_make (fun j:fin s => sum (seq_make (fun k:fin h => 
  mul (Tensor2_unfold x)|[o]|[k] (Tensor3_unfold y)|[k]|[i]|[j]))))).

Definition tensordot3d_2d {m h n s} (x : Tensor3 m n h) (y : Tensor2 h s) :=
  seq_make (fun o:fin m => seq_make (fun i:fin n => seq_make (fun j:fin s => sum (seq_make (fun k:fin h =>
  mul (Tensor3_unfold x)|[o]|[i]|[k] (Tensor2_unfold y)|[k]|[j]))))).

Definition mm_mul{n d h} (m1 : Tensor2 n d) (w1 : Tensor2 d h) (m2 : Tensor2 n h)
  (w2 : Tensor2 h h) (b : Tensor1 h) := 
  seq_make (fun i:fin n => seq_make (fun j:fin h => add (add (sum (seq_make (fun k1:fin d =>
  mul (Tensor2_unfold m1)|[i]|[k1] (Tensor2_unfold w1)|[k1]|[j])))(sum (seq_make (fun k2:fin h => 
  mul (Tensor2_unfold m2)|[i]|[k2] (Tensor2_unfold w2)|[k2]|[j])))) (Tensor1_unfold b)|[j])).

Definition Dropout1d {n} (input : Tensor1 n) (dropout_ratio: exp num)  :=
  seq_make (fun i => if (gtb dropout_ratio rand) then zero 
    else div (Tensor1_unfold input)|[i] (sub one dropout_ratio)).

Definition Dropout2d {n m} (input : Tensor2 n m) (dropout_ratio: exp num)  :=
  seq_make (fun i: fin n => seq_make (fun j: fin m => if (gtb dropout_ratio rand)
  then zero  else div (Tensor2_unfold input)|[i]|[j] (sub one dropout_ratio))).

Definition Dropout3d {n m channel} (input : Tensor3 channel n m) (dropout_ratio: exp num) :=
  seq_make (fun c: fin channel => seq_make (fun i: fin n => seq_make (fun j: fin m => 
  if (gtb dropout_ratio rand) then zero else div (Tensor3_unfold input)|[c]|[i]|[j] (sub one dropout_ratio)))).

Definition Dropout4d {n m batch channel} (input : Tensor4 batch channel n m)
  (dropout_ratio: exp num)  :=
  seq_make (fun b: fin batch => seq_make (fun c: fin channel =>
  seq_make (fun i: fin n =>  seq_make (fun j : fin m =>
  if (gtb dropout_ratio rand) then zero else div (Tensor4_unfold input)|[b]|[c]|[i]|[j] (sub one dropout_ratio))))).

Definition BatchNorm2d {batch channel} (x : Tensor2 batch channel)
  (gemma beta: exp num) :=
  tlet mean := divn (Sum2d x) (batch*channel) in
  tlet var := divn (sum (seq_make (fun b:fin batch => sum (seq_make (fun c:fin channel => 
    mul (sub (Tensor2_unfold x)|[b]|[c] mean)(sub (Tensor2_unfold x)|[b]|[c] mean))))))(batch*channel) in
  seq_make (fun b:fin batch => seq_make (fun c:fin channel => 
  add (mul (div (sub (Tensor2_unfold x)|[b]|[c] mean) (sqrt var)) gemma) beta)).

Definition BatchNorm3d {batch channel n} (x : Tensor3 batch channel n)
  (gemma beta: exp num) :=
  tlet mean := divn (Sum3d x) (batch*channel*n) in
  tlet var := divn (sum (seq_make (fun b:fin batch => sum (seq_make (fun c:fin channel => 
    sum (seq_make (fun j : fin n => mul (sub (Tensor3_unfold x)|[b]|[c]|[j] mean)
      (sub (Tensor3_unfold x)|[b]|[c]|[j] mean)))))))) (batch*channel*n) in
  seq_make (fun b: fin batch => seq_make (fun c: fin channel => seq_make (fun i: fin n =>
  add (mul (div (sub (Tensor3_unfold x)|[b]|[c]|[i] mean) (sqrt var)) gemma) beta))).

Definition BatchNorm4d{batch channel n m} (x : Tensor4 batch channel n m) 
  (gemma beta: exp num)  :=
  tlet mean := divn (Sum4d x) (batch*channel*n*m) in
  tlet var := divn (sum (seq_make (fun b: fin batch => sum (seq_make (fun c:fin channel => 
    sum (seq_make (fun i:fin n =>  sum (seq_make (fun j: fin m => 
    mul (sub (Tensor4_unfold x)|[b]|[c]|[i]|[j] mean) 
    (sub (Tensor4_unfold x)|[b]|[c]|[i]|[j] mean)))))))))) (batch*channel*n*m) in
  seq_make (fun b: fin batch => seq_make (fun c: fin channel => 
  seq_make (fun i: fin n => seq_make (fun j: fin m => 
  add (mul (div (sub (Tensor4_unfold x)|[b]|[c]|[i]|[j] mean) (sqrt var)) gemma) beta)))).

Definition Interpolation2d {n m} (s : nat) (input : Tensor2 n m)
  (E:0<n) (E':0<m) :=
  seq_make (fun i: fin ((n-1)*s+1) => seq_make (fun j: fin ((m-1)*s+1) =>
  if (((i mod s) =? 0)%nat && ((j mod s) =? 0))%nat
    then (Tensor2_unfold input)|[[i/s|fin_lem4 i E]]|[[j/s|fin_lem4 j E']] else exp_default)).

Definition Interpolation3d {n m channel} (s : nat) (input : Tensor3 channel n m)
  (E:0<n) (E':0<m)  :=
  seq_make (fun c : fin channel => 
  seq_make (fun i: fin ((n-1)*s + 1) => seq_make (fun j: fin ((m-1)*s + 1) =>
  if (((i mod s) =? 0)%nat && ((j mod s) =? 0))%nat
    then (Tensor3_unfold input)|[c]|[[i/s|fin_lem4 i E]]|[[j/s|fin_lem4 j E']] else exp_default))).

Definition Interpolation4d {n m batch channel} (s : nat) (input : Tensor4 batch channel n m)
  (E:0<n) (E':0<m)  :=
  seq_make (fun b: fin batch => seq_make (fun c: fin channel => 
  seq_make (fun i : fin ((n-1)*s + 1) =>  seq_make (fun j : fin ((m-1)*s + 1) => 
  if (((i mod s) =? 0)%nat && ((j mod s) =? 0))%nat 
    then (Tensor4_unfold input)|[b]|[c]|[[i/s|fin_lem4 i E]]|[[j/s|fin_lem4 j E']] else exp_default)))).

Definition ConvTranspose2d {m1 m2 n1 n2} (p s : nat) (input : Tensor2 m1 m2) (w : Tensor2 n1 n2)
  (E1:0<m1) (E2:0<m2) (E3:1+p<=n1) (E4:1+p<=n2)  :=
  tlet inter := Interpolation2d s input E1 E2 in
  tlet pad := seq_make(fun i: fin ((m1-1)*s+1+2*(n1-1-p)) => seq_make(fun j: fin ((m2-1)*s+1+2*(n2-1-p)) =>
    if (i <? (n1-1-p)) && (j <? (n2-1-p)) then exp_default else 
    match (lt_dec (i-(n1-1-p)) ((m1-1)*s + 1)), (lt_dec (i-(n2-1-p)) ((m2-1)*s+1)) with
      | left P1, left P2 => inter|[[i-(n1-1-p)|P1]]|[[i-(n2-1-p)|P2]]
      | _,_ => exp_default end)) in
  seq_make (fun i1: fin ((m1-1)*s+n1-2*p) => seq_make (fun j1: fin ((m2-1)*s+n2-2*p) => 
  sum (seq_make (fun i2: fin n1 => sum (seq_make (fun j2: fin n2 =>
  mul pad|[[i1 + i2|fin_lem5 i1 i2 E3]]|[[j1 + j2|fin_lem5 j1 j2 E4]] (Tensor2_unfold w)|[i2]|[j2])))))).

Definition ConvTranspose3d {filernum channel m1 m2 n1 n2} (p s : nat) (bias : Tensor1 filernum)
  (w : Tensor4 filernum channel n1 n2) (input : Tensor3 channel m1 m2)
  (E1:0<m1) (E2:0<m2) (E3:1+p<=n1) (E4:1+p<=n2)  :=
  tlet inter := Interpolation3d s input E1 E2 in
  tlet pad := seq_make (fun c:fin channel => seq_make(fun i: fin ((m1-1)*s+1+2*(n1-1-p)) => 
    seq_make(fun j: fin ((m2-1)*s+1+2*(n2-1-p)) => if (i <? (n1-1-p)) && (j <? (n2-1-p)) then exp_default else 
    match (lt_dec (i-(n1-1-p)) ((m1-1)*s + 1)), (lt_dec (i-(n2-1-p)) ((m2-1)*s+1)) with
      | left P1, left P2 => inter|[c]|[[i-(n1-1-p)|P1]]|[[i-(n2-1-p)|P2]]
      | _,_ => exp_default end))) in
  seq_make (fun num: fin filernum => seq_make (fun i1: fin ((m1-1)*s+n1-2*p) => 
  seq_make (fun j1: fin ((m2-1)*s+n2-2*p) => add (sum (seq_make (fun c:fin channel => 
  sum (seq_make ( fun i2:fin n1 => sum (seq_make (fun j2:fin n2 => 
  mul pad|[c]|[[i1 + i2|fin_lem5 i1 i2 E3]]|[[j1 + j2|fin_lem5 j1 j2 E4]] 
    (Tensor4_unfold w)|[num]|[c]|[i2]|[j2]))))))) (Tensor1_unfold bias)|[num]))).

Definition ConvTranspose4d {batch filernum channel m1 m2 n1 n2} (p s : nat) (bias : Tensor1 filernum)
  (w : Tensor4 filernum channel n1 n2) (input : Tensor4 batch channel m1 m2)
  (E1:0<m1) (E2:0<m2) (E3:1+p<=n1) (E4:1+p<=n2)  :=
  tlet inter := Interpolation4d s input E1 E2 in
  tlet pad := seq_make (fun b: fin batch => seq_make (fun c:fin channel => 
    seq_make(fun i: fin ((m1-1)*s+1+2*(n1-1-p)) => seq_make(fun j: fin ((m2-1)*s+1+2*(n2-1-p)) =>
    if (i <? (n1-1-p)) && (j <? (n2-1-p)) then exp_default else 
    match (lt_dec (i-(n1-1-p)) ((m1-1)*s + 1)), (lt_dec (i-(n2-1-p)) ((m2-1)*s+1)) with
      | left P1, left P2 => inter|[b]|[c]|[[i-(n1-1-p)|P1]]|[[i-(n2-1-p)|P2]]
      | _,_ => exp_default end)))) in
  seq_make (fun b : fin batch => seq_make (fun num: fin filernum => 
  seq_make (fun i1: fin ((m1-1)*s+n1-2*p) => seq_make (fun j1: fin ((m2-1)*s+n2-2*p) => 
  add (sum (seq_make (fun c: fin channel => sum (seq_make ( fun i2:fin n1 => sum (seq_make (fun j2:fin n2 => 
  mul pad|[b]|[c]|[[i1 + i2|fin_lem5 i1 i2 E3]]|[[j1 + j2|fin_lem5 j1 j2 E4]] 
    (Tensor4_unfold w)|[num]|[c]|[i2]|[j2]))))))) (Tensor1_unfold bias)|[num])))).

Definition Log_Softmax1d {n} (input: Tensor1 n)  :=
  tlet total := sum (seq_make (fun i: fin n => epow (Tensor1_unfold input)|[i])) in 
  seq_make (fun j: fin n => ln (div (epow (Tensor1_unfold input)|[j]) total)).

Definition Log_Softmax2d {n batch}(input: Tensor2 batch n) :=
  tlet sum := seq_make (fun b : fin batch => sum (seq_make (fun i => 
    epow (Tensor2_unfold input)|[b]|[i]))) in 
  seq_make (fun b:fin batch => seq_make (fun j: fin n => 
  ln (div (epow (Tensor2_unfold input)|[b]|[j]) sum|[b]))).

Definition Log_Softmax3d {n m batch } (input: Tensor3 batch n m)  :=
  tlet sums := seq_make (fun b : fin batch => seq_make (fun i : fin n => 
    sum (seq_make (fun j : fin m => epow (Tensor3_unfold input)|[b]|[i]|[j])))) in 
  seq_make (fun b : fin batch => seq_make (fun i : fin n => seq_make (fun j : fin m => 
  ln (div (epow (Tensor3_unfold input)|[b]|[i]|[j]) sums|[b]|[i])))).

Definition Log_Softmax4d {batch channel n m} (input: Tensor4 batch channel n m)  :=
  tlet sums := seq_make (fun b : fin batch => seq_make (fun c : fin channel => 
    seq_make (fun i : fin n => sum (seq_make (fun j : fin m => 
    epow (Tensor4_unfold input)|[b]|[c]|[i]|[j]))))) in 
  seq_make (fun b : fin batch => seq_make (fun c : fin channel => seq_make (fun i : fin n => 
  seq_make (fun j : fin m => ln (div (epow (Tensor4_unfold input)|[b]|[c]|[i]|[j]) sums|[b]|[c]|[i]))))).

Definition NLLLoss2d {n batch} (input: Tensor2 batch n) (label: list (fin n)) (E : 0 < n) :=
  tlet sum := sum (seq_make (fun b:fin batch => 
    negate ((Tensor2_unfold input)|[b]|[nth b label (fin_0H E)]))) in
  divn sum batch.

Definition NLLLoss3d {n m batch} (input: Tensor3 batch n m) 
  (label: list (list (fin m))) (E : 0 < m):=
  tlet sum := sum (seq_make (fun b:fin batch => sum (seq_make (fun i: fin n => 
    negate ((Tensor3_unfold input)|[b]|[i]|[nth i (nth b label nil) (fin_0H E)]))))) in
  divn sum (batch*m).

Definition NLLLoss4d {n m batch channel} (input: Tensor4 batch channel n m) 
  (label: list (list (list (fin m)))) (E : 0 < m) :=
  tlet sum := sum (seq_make (fun b:fin batch => 
    sum (seq_make (fun c : fin channel => sum (seq_make (fun i: fin n => 
    negate ((Tensor4_unfold input)|[b]|[c]|[i]|[nth i (nth c (nth b label nil) nil) (fin_0H E)]))))))) in
  divn sum (batch*channel*n).

Definition BCELoss2d {n batch} (input: Tensor2 batch n) (label : Tensor2 batch n)  :=
  seq_make (fun b:fin batch => (seq_make (fun i: fin n => 
  negate (add (mul (Tensor2_unfold label)|[b]|[i] (ln (Tensor2_unfold input)|[b]|[i])) 
  (mul (sub one (Tensor2_unfold label)|[b]|[i]) (ln (sub one (Tensor2_unfold input)|[b]|[i]))))))).

Definition BCELoss3d {batch n m} (input: Tensor3 batch n m) (label: Tensor3 batch n m)  :=
  seq_make (fun b: fin batch => seq_make (fun i: fin n => seq_make (fun j: fin m => 
  negate (add  (mul (Tensor3_unfold label)|[b]|[i]|[j] (ln (Tensor3_unfold input)|[b]|[i]|[j])) 
    (mul (sub one (Tensor3_unfold label)|[b]|[i]|[j]) (ln (sub one (Tensor3_unfold input)|[b]|[i]|[j]))))))).

Definition BCELoss4d {batch channel n m} (input: Tensor4 batch channel n m) 
  (label: Tensor4 batch channel n m)  :=
  seq_make (fun b: fin batch =>  seq_make (fun c: fin channel => seq_make (fun i: fin n => 
  seq_make (fun j: fin m => negate (add (mul (Tensor4_unfold label)|[b]|[c]|[i]|[j] 
    (ln (Tensor4_unfold input)|[b]|[c]|[i]|[j])) (mul (sub one (Tensor4_unfold label)|[b]|[c]|[i]|[j]) 
    (ln (sub one (Tensor4_unfold input)|[b]|[c]|[i]|[j])))))))).

Definition MeanBCELoss2d {n batch} (input: Tensor2 batch n) (label : Tensor2 batch n):=
  tlet sum := sum (seq_make (fun b:fin batch =>  sum (seq_make (fun i: fin n => 
    negate (add (mul (Tensor2_unfold label)|[b]|[i] (ln (Tensor2_unfold input)|[b]|[i]) ) 
      (mul (sub one (Tensor2_unfold label)|[b]|[i]) (ln (sub one (Tensor2_unfold input)|[b]|[i])))))))) in
  divn sum (batch*n).

Definition MeanBCELoss3d {batch n m} (input: Tensor3 batch n m) (label: Tensor3 batch n m)  :=
  tlet sum := sum (seq_make (fun b: fin batch => sum (seq_make (fun i: fin n => 
    sum (seq_make (fun j: fin m => negate (add 
      (mul (Tensor3_unfold label)|[b]|[i]|[j] (ln (Tensor3_unfold input)|[b]|[i]|[j])) 
      (mul (sub one (Tensor3_unfold label)|[b]|[i]|[j]) 
      (ln (sub one (Tensor3_unfold input)|[b]|[i]|[j])))))))))) in
  divn sum (batch * n * m).

Definition MeanBCELoss4d {batch channel n m} (input: Tensor4 batch channel n m) 
  (label: Tensor4 batch channel n m)  :=
  tlet sum := sum (seq_make (fun b: fin batch => sum (seq_make (fun c: fin channel => 
    sum (seq_make (fun i: fin n => sum (seq_make (fun j: fin m => 
      negate (add (mul (Tensor4_unfold label)|[b]|[c]|[i]|[j] (ln (Tensor4_unfold input)|[b]|[c]|[i]|[j])) 
        (mul (sub one (Tensor4_unfold label)|[b]|[c]|[i]|[j]) 
        (ln (sub one (Tensor4_unfold input)|[b]|[c]|[i]|[j])))))))))))) in
  divn sum (batch * channel * n * m).

Definition Flatten2d {n m} (input: exp (ary '{n} (ary '{m} num))) := join input.

Definition Flatten3d {n m channel} (input: Tensor3 channel n m)  :=
  join (join (Tensor3_unfold input)).

Definition Flatten4d {n m batch channel} (input : Tensor4 batch channel n m)  :=
  seq_make (fun b : fin batch => Flatten3d ((Tensor4_unfold input) |[b])).

Definition Concat4d {n m batch channel1 channel2} (x : Tensor4 batch channel1 n m)
  (y : Tensor4 batch channel2 n m)  :=
  seq_make (fun b: fin batch => concat (Tensor4_unfold x)|[b] (Tensor4_unfold y)|[b]).

Definition Reshape3d_2d {batch n m} (k:nat) (input : Tensor3 batch n m)  :=
  tlet e' := Flatten3d input in
  seq_make(fun i : fin k => seq_make(fun j : fin ((batch*n*m)/k)=> 
    (Tensor1_unfold e')|[[i*((batch*n*m)/k)+j|fin_lem7 i j]])).

(* Fixpoint ReshapeList2d (l: list (list nat))
  : list nat := 
  match l with
  | [] => []
  | h :: tl => h ++ ReshapeList2d tl
  end. *)

Definition m_nth {channel n m} (input : Tensor3 channel n m) (c: fin channel)  := 
  seq_make (fun i : fin n => seq_make(fun j : fin m => (Tensor3_unfold input)|[c]|[i]|[j])).

Notation " m [ i ] " := (m_nth m i) (at level 2).


(* ============================================================================================ *)

Definition loss {n} (p: Tensor1 n)  :=
  divn (sum (seq_make (fun i=> negate (ln (Tensor1_unfold p)|[i])))) n.

Definition Softmax_loss {n} (p: Tensor1 n) :=
  tlet tmp := Softmax1d (Tensor1_unfold p) in seq_make (fun i: fin n => negate (ln tmp|[i])).

Definition Softmax_Loss {n} (p: Tensor1 n) (label:fin n) :=
  tlet sum := sum (seq_make (fun i:fin n => epow (Tensor1_unfold p)|[i])) in
  negate (ln (div (epow (Tensor1_unfold p)|[label]) sum)).

Definition SparseCateCross_Loss {m n} (p: Tensor2 n m) (label : Tensor2 n m)  :=
  negate (divn (sum (seq_make (fun i: fin n => sum (seq_make (fun j: fin m => 
    mul (Tensor2_unfold p)|[i]|[j] (ln (Tensor2_unfold label)|[i]|[j])))))) n).

Definition MSE_loss {n} (x y: Tensor1 n) :=
  divn (sum (seq_make (fun i: fin n => mul (sub (Tensor1_unfold x)|[i] (Tensor1_unfold y)|[i]) 
    (sub (Tensor1_unfold x)|[i] (Tensor1_unfold y)|[i])))) n.

Definition Relu_grad {n filernum} (input : Tensor3 filernum n n) :=
  seq_make (fun num: fin filernum => seq_make (fun i:fin n => seq_make (fun j:fin n => 
  if (leb (Tensor3_unfold input)|[num]|[i]|[j] zero) then zero else one ))).

Definition relu (e: exp num):= if (leb e zero) then zero else e.

Definition relu_grad (e: exp num):= if (leb e zero) then zero else one. 

Definition output_backward {n} (x y: Tensor1 n)  :=
  seq_make (fun i : fin n => sub (Tensor1_unfold x)|[i] (Tensor1_unfold y)|[i]).

Definition nn_backward{n m} (d_l: Tensor1 n) (w : Tensor2 n m) (z_l_1 : Tensor1 m) :=
  seq_make (fun i:fin m => mul (sum (seq_make (fun j:fin n => 
  mul (Tensor2_unfold w)|[j]|[i] (Tensor1_unfold d_l)|[j])))(relu_grad (Tensor1_unfold z_l_1)|[i])).

Definition average_pool_backward {n k} (dout: Tensor2 n n) (z_l_1 : Tensor2 (k*n) (k*n)) :=
  seq_make (fun i:fin (k*n) => seq_make (fun j:fin (k*n) => 
  mul (Tensor2_unfold dout)|[[i/k|fin_lem8 i]]|[[j/k|fin_lem8 j]] (Tensor2_unfold z_l_1)|[i]|[j])).

Definition averagepool_backward{n} (dout: Tensor2 n n) (k:nat)  :=
  seq_make (fun i:fin (k*n) => seq_make (fun j:fin (k*n) => 
  (Tensor2_unfold dout)|[[i/k|fin_lem8 i]]|[[j/k|fin_lem8 j]])).

Definition average_pool_backward_g {n channel} (dout : Tensor3 channel n n)
  (k : nat) (z_l_1: Tensor3 channel (k*n) (k*n)) :=
  seq_make (fun c:fin channel =>  seq_make (fun i:fin (k*n) => seq_make (fun j:fin (k*n) => 
  mul (Tensor3_unfold dout)|[c]|[[i/k|fin_lem8 i]]|[[j/k|fin_lem8 j]] (Tensor3_unfold z_l_1)|[c]|[i]|[j]))). 

Definition convolution_backward {n m} (dout: Tensor2 m m) (p : Tensor2 (m+n-1) (m+n-1))
  (w : Tensor2 n n) (E: 0 < n)  :=
  tlet dout_pad := Padding2d (n-1) dout in
  seq_make (fun i1:fin (m+n-1) => seq_make (fun j1:fin (m+n-1) => 
  mul (sum (seq_make (fun i2:fin n => sum (seq_make ( fun j2: fin n => 
  mul dout_pad|[[i1 + i2|fin_lem9 i1 i2 E]]|[[j1 + j2|fin_lem9 j1 j2 E]] 
    (Tensor2_unfold w)|[[n-1-i2|fin_lem10 i2]]|[[n-1-j2|fin_lem10 j2]])))))
    (relu_grad (Tensor2_unfold p)|[i1]|[j1]))).

Definition convolution_backward_g {filernum channel m n} (dout : Tensor3 filernum m m)
  (p : Tensor3 channel (m+n-1) (m+n-1)) (w: Tensor4 filernum channel n n)
  (E:0 < n)  :=
  tlet dout_pad := Padding3d (n-1) dout in
  seq_make (fun c:fin channel => seq_make (fun i1:fin (m+n-1) => seq_make (fun j1:fin (m+n-1) => 
  mul (sum (seq_make (fun num :fin filernum => sum (seq_make (fun i2:fin n => 
  sum (seq_make (fun j2: fin n => 
  mul dout_pad|[num]|[[i1 + i2|fin_lem9 i1 i2 E]]|[[j1 + j2|fin_lem9 j1 j2 E]] 
    (Tensor4_unfold w)|[num]|[c]|[[n-1-i2|fin_lem10 i2]]|[[n-1-j2|fin_lem10 j2]])))))))
    (relu_grad (Tensor3_unfold p)|[c]|[i1]|[j1])))).

Definition convolution_backward_w {m n} (dout : Tensor2 m m)
  (p : Tensor2 (m+n-1) (m+n-1)) (E:0<n):=
  seq_make (fun i1:fin n => seq_make (fun j1:fin n => 
  sum (seq_make (fun i2:fin m => sum (seq_make ( fun j2: fin m => 
  mul (Tensor2_unfold p)|[[i1 + i2|fin_lem11 i1 i2]]|[[j1 + j2|fin_lem11 j1 j2]] 
    (Tensor2_unfold dout)|[i2]|[j2])))))).

Definition convolution_backward_b {n} (dout: Tensor2 n n)  :=
  sum (seq_make (fun i:fin n => sum (seq_make (fun j: fin n => (Tensor2_unfold dout)|[i]|[j])))).

Definition convolution_backward_w_g {filernum channel m n} (dout : Tensor3 filernum (m+n-1) (m+n-1))
  (p : Tensor3 channel m m)  :=
  seq_make(fun num:fin filernum => seq_make (fun c:fin channel => seq_make (fun i1:fin n =>
  seq_make (fun j1:fin n => sum (seq_make (fun i2:fin m =>  sum (seq_make ( fun j2: fin m => 
    mul (Tensor3_unfold dout)|[num]|[[i1 + i2|fin_lem11 i1 i2]]|[[j1 + j2|fin_lem11 j1 j2]] (Tensor3_unfold p)|[c]|[i2]|[j2])))))))).

Definition convolution_backward_b_g {filernum m n} 
  (dout : Tensor3 filernum (m+n-1) (m+n-1))  :=
  seq_make(fun num:fin filernum => sum (seq_make (fun i:fin (m+n-1) =>
  sum (seq_make (fun j: fin (m+n-1) => (Tensor3_unfold dout)|[num]|[i]|[j]))))).

Definition nn_backward_w{m n}(dout: Tensor1 n) (a_l_1: Tensor1 m) :=
  seq_make (fun i:fin n => seq_make (fun j:fin m => 
  mul (Tensor1_unfold dout)|[i] (Tensor1_unfold a_l_1)|[j])).

Definition nn_backward_b{n}(dout: Tensor1 n)  :=
  seq_make (fun i:fin n => (Tensor1_unfold dout)|[i]).

Definition convert_in {batch out_channel in_channel m1 m2} (s : nat) (input : Tensor4 batch in_channel m1 m2)
  (Ec: out_channel <= in_channel) (E1:0<m1) (E2:0<m2) :=
  seq_make (fun b:fin batch => seq_make (fun c: fin out_channel => 
  seq_make (fun i: fin ((m1+2*0-1)/s+1)=> seq_make (fun j: fin ((m2+2*0-1)/s+1) => 
    (Tensor4_unfold input)|[b]|[[fin2nat c|fin_lt c Ec]]|[[fin2nat i|fin_lem12 i E1]]|[[fin2nat j|fin_lem12 j E2]])))).

Lemma convert_1_aux : forall n, 0 < n -> (n + 0 - 1)/1 + 1 = n.
Proof. intros. rewrite Nat.div_1_r. lia. Qed.

Definition convert_1{batch channel m1 m2} (input : Tensor4 batch channel ((m1+2*0-1)/1+1) ((m2+2*0-1)/1+1))
  (E1 : 0 < m1) (E2 : 0 < m2) : Tensor4 batch channel m1 m2.
Proof. simpl in *.
  replace ((m1 + 0 - 1) / 1 + 1) with m1 in input by (symmetry; apply convert_1_aux; auto).
  replace ((m2 + 0 - 1) / 1 + 1) with m2 in input by (symmetry; apply convert_1_aux; auto).
  exact input.
Qed.

Lemma convert_2_aux : forall n, 0 < n -> (n + 2 - 3)/1 + 1 = n.
Proof. intros. rewrite Nat.div_1_r. lia. Qed.

Definition convert_2{batch channel m1 m2}(input : Tensor4 batch channel ((m1+2*1-3)/1+1) ((m2+2*1-3)/1+1))
  (E1 : 0 < m1) (E2 : 0 < m2) : Tensor4 batch channel m1 m2.
Proof. simpl in *.
 replace ((m1 + 2 - 3) / 1 + 1) with m1 in input by (symmetry; apply convert_2_aux; auto).
 replace ((m2 + 2 - 3) / 1 + 1) with m2 in input by (symmetry; apply convert_2_aux; auto).
 exact input.
Qed.

Lemma convert_3_aux : forall n, 0 < n -> (n + 4 - 5)/1 + 1 = n.
Proof. intros. rewrite Nat.div_1_r. lia. Qed.

Definition convert_3{batch channel m1 m2}(input : Tensor4 batch channel ((m1+2*2-5)/1+1) ((m2+2*2-5)/1+1))
  (E1 : 0 < m1) (E2 : 0 < m2) : Tensor4 batch channel m1 m2.
Proof. simpl in *.
 replace ((m1 + 4 - 5) / 1 + 1) with m1 in input by (symmetry; apply convert_3_aux; auto).
 replace ((m2 + 4 - 5) / 1 + 1) with m2 in input by (symmetry; apply convert_3_aux; auto).
 exact input.
Qed.

Definition convert_4 {batch channel m1 m2 growth_rate num_layers}
  (input: Tensor4 batch channel m1 m2) (E:num_layers = 0)
  :  Tensor4 batch (channel + growth_rate * num_layers) m1 m2.
Proof. simpl in *.
  rewrite E. rewrite Nat.mul_0_r. rewrite Nat.add_0_r. exact input.
Qed.

Lemma convert_5_aux : forall a b c, a + b * S c = a + b * c + b.
Proof. intros. lia. Qed.

Definition convert_5 {batch channel m1 m2 growth_rate p'}
  (input : Tensor4 batch (channel + growth_rate * p' + growth_rate) m1 m2)
  : Tensor4 batch (channel + growth_rate * (S p')) m1 m2.
Proof. simpl in *. rewrite convert_5_aux. exact input. Qed.