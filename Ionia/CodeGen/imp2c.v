Require Import Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Ascii String Floats.
Require Export fun2imp.

Import ListNotations.

Set Implicit Arguments.

Open Scope path_scope.

Open Scope string_scope.


Lemma append_assoc : forall s1 s2 s3 : string,
  (s1 ++ s2) ++ s3 = s1 ++ s2 ++ s3.
Proof.
  intros.
  (* 对第一个字符串 s1 进行归纳 *)
  induction s1 as [|c s1' IH].
  - (* 基本情况: s1 是空字符串 *)
    simpl. (* 简化表达式 *)
    reflexivity. (* 两边都等于 s2 ++ s3 *)
  - (* 归纳步骤: s1 = String c s1' *)
    simpl. (* 简化左连接操作 *)
    simpl. (* 简化右连接操作 *)
    rewrite IH. (* 应用归纳假设 *)
    reflexivity. (* 两边相等 *)
Qed.

Open Scope path_scope.

(* ######################################################################### *)
(** Rewrite Rules from Nat to String *)

Section Nat2String.

Definition natToDigit (n : nat) : ascii :=
  match n with
    | 1 => "1"
    | 2 => "2"
    | 3 => "3"
    | 4 => "4"
    | 5 => "5"
    | 6 => "6"
    | 7 => "7"
    | 8 => "8"  
    | 9 => "9"
    | _ => "0"
  end.

Fixpoint writeNatAux (time n : nat) (acc : string) : string :=
  let acc' := String (natToDigit (n mod 10)) acc in
  match time with
    | 0 => acc'
    | S time' =>
      match n / 10 with
        | 0 => acc'
        | n' => writeNatAux time' n' acc'
      end
  end.

Definition writeNat (n : nat) : string :=
  writeNatAux n n "".

End Nat2String.

(* ######################################################################### *)
(** Rewrite Rules from Imperative to C *)

Section Imp2C.

Open Scope string_scope.

Parameter myenv : env.

Parameter vrd : forall {d:data}, string -> exp d.

Parameter vwt : forall {d:data}, string -> acc d.


Fixpoint CG_data (d:data) s: string :=
  match d with
   | num => "float "++ s
   | @ary n m d => (CG_data d (s++"["++(writeNat m)++"]") )
  end.

Inductive Vpath := Aidx (i:nat).

Definition pslist := list Vpath.

(* convert a var to be a var of nat type. *)
Parameter str2nat : string -> nat.
Coercion str2nat : string >-> nat.

Parameter CG_comm: comm -> nat -> string.
Parameter CG_acc   : 
  forall {d:data} , pslist -> acc d -> string.
Parameter CG_exp   : 
  forall {d:data} , pslist -> exp d -> string.

Definition vstr (cnt:nat) : string := "v"++(writeNat cnt ).
Definition istr (cnt:nat) : string := "i"++(writeNat cnt ).

Parameter str2fin : forall (n:nat), string -> fin n.


(* 自定义命令的编号 *)
Definition cnt_skip : nat := 0.

Fixpoint applyps (v:string) (ps:pslist) : string :=
  match ps with
   | nil => v
   | (Aidx i)::tl => applyps (v ++"["++(writeNat i)++"]") tl 
  end.

Lemma applyps_nil: forall v,
  applyps v nil = v.
Proof. auto. Qed.

Lemma applyps_Aidx: forall v tl i,
  applyps v ((Aidx i)::tl) = applyps (v ++"["++(writeNat i)++"]") tl.
Proof. auto. Qed.

Parameter writeBool: bool -> string.
Parameter writeR: R -> string.

Axiom CGskip :  forall (cnt:nat), 
  CG_comm skip cnt = "/* skip */".

Axiom CGif: forall b c1 c2 cnt,
  CG_comm (If b c1 c2) cnt = 
"if ("++ writeBool b++")
  { " ++ CG_comm c1 cnt  ++ "}
else
  { " ++ CG_comm c2 cnt ++ "}".

Axiom CGseq  : forall (p1 p2:comm) (cnt:nat),
   CG_comm (p1 '; p2) cnt  = 
  (CG_comm p1 cnt)++"
"++(CG_comm p2 (cnt)).

Axiom CGassign : forall (a:acc num) (e:exp num) (cnt:nat), 
   CG_comm (a |:= e) cnt = 
   (CG_acc nil a) ++" = " ++ (CG_exp nil e)++" ;".

Axiom CGnew : forall (d:data) (p:acc d -> comm)(a:acc d) (cnt:nat), 
  CG_comm (new p a) cnt =
  (CG_data d) (vstr cnt) ++";
" ++ (CG_comm (p(vwt (vstr cnt))) (cnt+1)).

Axiom CGfor : forall (n:nat) (p:fin n -> comm) (cnt:nat),
  CG_comm (comm_seq p) cnt =
"for(int "++(istr cnt)++"=0; "++(istr cnt)++"<"
    ++(writeNat n)++"; "++(istr cnt)++" += 1) 
  { " ++ (CG_comm (p (str2fin n(istr cnt))) (cnt+1)) ++ "}".

Axiom CGparfor : forall (n:nat) (d:data) (a:acc (ary '{n} d))
   (p:fin n -> acc d -> comm) (cnt:nat),
  CG_comm (comm_par a p) cnt =
"#pragma omp parallel for
for (int "++(istr cnt)++"=0; "++(istr cnt)++" < "
    ++(writeNat n)++"; "++(istr cnt)++" += 1) 
  { " ++ (CG_comm 
     (p (str2fin n (istr cnt)) 
    (a|{(str2fin n (istr cnt))})) (cnt+1)) ++ "}".

Axiom CGaccvar : forall (d:data) (a:string) (ps:pslist), 
   @CG_acc d ps (vwt a) = applyps a ps.

Axiom CGidxAcc : forall (d:data) (n:nat) (a:acc (ary '{n} d)) (i:fin n) (ps:pslist),
  CG_acc ps (a |{i}) = CG_acc (Aidx i :: ps) a.

Lemma CGaccp : forall (a : acc num),
  @accp num a = a.
Proof. auto. Qed.

(* r-values. *)

Axiom CGexpvar : forall (d:data) (x:string) (ps:pslist), 
   @CG_exp d ps (vrd x) = applyps x ps.

Axiom CGneg : forall (e:exp num),
  CG_exp nil (negate e) = "(- "++(CG_exp nil e)++")".

Axiom CGadd : forall (e1 e2 : exp num),
  CG_exp nil (add e1 e2) =
  "("++(CG_exp nil e1)++" + "++(CG_exp nil e2)++")".

Axiom CGsub : forall (e1 e2 : exp num),
  CG_exp nil (sub e1 e2) =
  "("++(CG_exp nil e1)++" - "++(CG_exp nil e2)++")".

Axiom CGmul : forall (e1 e2 : exp num),
  CG_exp nil (mul e1 e2) =
  "("++(CG_exp nil e1)++" * "++(CG_exp nil e2)++")".

Axiom CGdiv : forall (e1 e2 : exp num),
  CG_exp nil (div e1 e2) =
  "("++(CG_exp nil e1)++") / ("++(CG_exp nil e2)++")".

Axiom CGdivn : forall (e1 : exp num)(e2:nat),
  CG_exp nil (divn e1 e2) =
  "(("++(CG_exp nil e1)++") / ("++(writeNat e2)++"))".

Axiom CGscal : forall (e1:R)(e2 : exp num),
  CG_exp nil (scal e1 e2) =
  "("++ (writeR e1) ++" * "++(CG_exp nil e2)++")".

Axiom CGepow : forall(e : exp num),
 CG_exp nil (epow e) = "exp("++(CG_exp nil e)++")".

Axiom CGln : forall (e:exp num),
  CG_exp nil (ln e) = "(log("++(CG_exp nil e)++"))".

Axiom wtStrNat : forall (s:string), writeNat (str2nat s) = s.

Axiom CGidx : forall (d:data) (n:nat) (e:exp (ary '{n} d)) 
  (i: fin n) (ps:pslist),
  CG_exp ps (e |[i]) = CG_exp (Aidx i::ps) e.

Axiom exp_default_simpl1: @exp_default num = vrd "0".
Axiom exp_zero: zero = vrd "0".
Axiom exp_one: one = vrd "1".

Lemma exp_default_simpl2: forall n d, 
  @exp_default (ary '{n} d) = seq_make (fun i => exp_default).
Proof.  auto. Qed.

Axiom CGleb: forall (e1 e2 : exp num),
  writeBool (leb e1 e2) =
  (CG_exp nil e1)++" <= "++(CG_exp nil e2).

Axiom CGgtb : forall (e1 e2 : exp num),
  writeBool (gtb e1 e2) =
  (CG_exp nil e1)++" > "++(CG_exp nil e2).



Axiom CGrand :
 CG_exp nil (rand) = "rand()".

(* env带来的翻译规则 *)
Axiom CGaccess: forall{d} (eta:env)(i: nat),
 accessd d eta (vwt (vstr i)) =  @vrd d (vstr i).

Axiom CGenv : forall (c : comm),
CG_comm (fun eta : env => c eta) = CG_comm (c).

Lemma CGenv_eq : forall (c1 c2 : comm),
  c1 = c2 -> CG_comm (fun env => c1 env) = CG_comm (fun env => c2 env).
Proof. intros. subst. auto. Qed.

Parameter Vrd:forall {d}, acc d -> exp d.

Axiom CGVrd: forall (d:data) (a:acc d) ps,
  CG_exp ps (Vrd a) = CG_acc ps a.

Axiom CGVar: forall (d:data) (s:string),
  @accp d (Var s) = vwt s. 


Axiom CGenv_new : forall (d:data) (p:acc d -> comm)(a:acc d) (cnt:nat), 
  CG_comm (fun eta:env => (new p a) eta) cnt =
  (CG_data d) (vstr cnt) ++";
" ++ (CG_comm (p(vwt (vstr cnt))) (cnt+1)).

Axiom CGenv_Sum : forall {n} (a : acc (ary '{n} num)) f c (p: path) cnt,
  CG_comm (fun eta : env => (Sum (accessd (ary '{n} num) eta a)
    f c p) eta) cnt = 
  CG_data (num) (vstr cnt) ++ ";
  " ++
  CG_comm (A (vwt (vstr cnt), zero)) (cnt + 1) ++ ";
  " ++
  CG_comm (comm_seq (fun i : fin n =>  fun eta : env =>
    f (add (Vrd a)|[i] (Vrd (vwt (vstr cnt)))) (vwt (vstr cnt))
     eta)) (cnt + 1) ++ ";
   " ++
   CG_comm (A  (@accp num p, Vrd (vwt (vstr cnt)))) (cnt + 1).

Axiom CGenv_Max : forall {n} (a : acc (ary '{n} num)) f c p (E : 0 < n) cnt,
  CG_comm (fun eta : env => (Max (accessd (ary '{n} num) eta a)
  f c p E) eta) cnt =
  CG_data (num) (vstr cnt) ++ ";
  " ++ 
  CG_comm (A (vwt (vstr cnt), (Vrd a)|[F[E]])) (cnt + 1) ++ ";
  " ++
  CG_comm (comm_seq (fun i : fin n => fun eta : env => 
  (If (gtb (Vrd a)|[i] (Vrd (vwt (vstr cnt)))) (f (Vrd a)|[i] (vwt (vstr cnt))) 
  (f (Vrd (vwt (vstr cnt))) (vwt (vstr cnt))))eta)) (cnt + 1) ++ ";
  " ++ 
   CG_comm (A  (@accp num p, Vrd (vwt (vstr cnt)))) (cnt + 1).


End Imp2C.


(* ######################################################################### *)
(** Rewrite Tactics *)


Open Scope string_scope.

Open Scope nat_scope.

Axiom writeBool_le: forall n i, writeBool (i<=?n) =  writeNat i ++ " <= " ++ writeNat n.

Axiom writeBool_lt: forall n i, writeBool (i<?n) =  writeNat i ++ " < " ++ writeNat n.

Axiom writeBool_eq: forall n i, writeBool (i=?n) =  writeNat i ++ " == " ++ writeNat n.

Axiom writeBool_andb: forall n i, writeBool (i&&n) =  writeBool i ++ " && " ++ writeBool n.

Axiom writeBool_orb: forall n i, writeBool (i||n) =  writeBool i ++ " || " ++ writeBool n.
Axiom writeNat_nat2fin: forall m n {E : n < m}, writeNat F[E] = writeNat n.

Axiom writeNat_fin : forall n, writeNat '{n} = writeNat n.

Axiom writeNat_str2fin: forall n (s:string), writeNat (str2fin n s) = s.

Axiom writeNat_add: forall (m n:nat),writeNat (m+n) 
  = "(" ++ writeNat m ++ ") + (" ++ writeNat n ++")".

Axiom writeNat_sub: forall (m n:nat),writeNat (m-n) 
  = "(" ++ writeNat m ++ ") - (" ++ writeNat n ++")".

Axiom writeNat_mul: forall (m n:nat),writeNat (m*n) 
  = "(" ++ writeNat m ++ ") * (" ++ writeNat n ++ ")".

Axiom writeNat_div: forall (m n:nat),writeNat (m/n) 
  ="(" ++ writeNat m ++ ") / (" ++ writeNat n ++ ")".

Axiom writeNat_mod: forall (m n:nat),writeNat (m mod n) 
  ="(" ++ writeNat m ++ ") % (" ++ writeNat n ++ ")".

Axiom writeBool_leb : forall (e1 e2 : exp num),
  writeBool (leb e1 e2) =
  "(" ++ CG_exp nil e1  ++ ") <= (" ++ CG_exp nil e2 ++")".

Axiom writeBool_gtb : forall (e1 e2 : exp num),
  writeBool (gtb e1 e2) =
  "(" ++ CG_exp nil e1  ++ ") > (" ++ CG_exp nil e2 ++")".

Axiom writeNat_str2fin_nat: forall n m (s:string), writeNat (str2fin n s * m) = s ++ "*m".

Lemma idx_if: forall (b:bool) n d (e1 e2:exp (ary '{n} d)) i,
  (if b then e1 else e2)|[i] = 
  if b then e1|[i] else e2|[i].
Proof. destruct b; auto. Qed.

Lemma add_ifl: forall (b:bool) e1 e2 e3,
  add (if b then e1 else e2) e3 = 
  if b then add e1 e3 else add e2 e3.
Proof. destruct b;auto. Qed.

Lemma add_ifr: forall (b:bool) e1 e2 e3,
  add e1 (if b then e2 else e3) = 
  if b then add e1 e2 else add e1 e3.
Proof. destruct b;auto. Qed.
