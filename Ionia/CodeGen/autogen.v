Require Import Logic.FunctionalExtensionality.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Ascii String.
Require Export imp2c.

Ltac CGenvrw :=
  match goal with
  | [ |- context [CG_comm (fun eta : env => A(_,_) eta)]] => 
      erewrite CGenv_eq;[|fun_ext; rewrite Aunfold; rewrite ?CGaccess; rewrite Afold;reflexivity]; rewrite CGenv
   | [ |- context [CG_comm (fun eta : env => C(if _ then _ else _ , _)eta)]] =>
    erewrite CGenv_eq;[ | fun_ext; rewrite ?CGaccess; reflexivity]; rewrite CGenv
      | [ |- context [CG_comm (fun eta : env => C(_,_) eta)]] => 
      erewrite CGenv_eq;[|fun_ext; rewrite Cunfold; rewrite ?CGaccess; rewrite Cfold;reflexivity]; rewrite CGenv
  | [ |- context [CG_comm (fun eta : env => (assign _ _ ) eta)]] => 
      erewrite CGenv_eq;[|fun_ext; rewrite ?CGaccess; rewrite Afold;reflexivity]; rewrite CGenv
  | [ |- context [CG_comm (fun eta : env => (Sum (accessd (ary '{?n} num) eta _) _ _ _) eta)]]   
      => rewrite CGenv_Sum
  | [ |- context [CG_comm (fun eta : env => (Max (accessd (ary '{?n} num) eta _) _ _ _ _) eta)]]   
      => rewrite CGenv_Max
  | _ => rewrite ?CGenv
  end.

Ltac hypUnfold :=
  repeat match goal with
  | [ H:= vrd _ |- _] => (unfold H;clear H)
  end.

Ltac default_unfold:=
  rewrite ?exp_default_simpl2;
  hypUnfold.

Ltac hypRewrite :=
  repeat match goal with 
  | [ H: writeNat _ = _ |- _] => rewrite ?H ;clear H
  | [ H: writeR _ = _ |- _] => rewrite ?H ;clear H
  end.


Ltac Crw :=
  match goal with
  | |- context [ C( _, fun x => Sum x _ _ _)] => rewrite Cunfold; unfold Sum
    | |- context [ C(seq_make _, _) ] => rewrite Cseq
  | |- context [ C( _, fun x => Max x _ _ _ _)] => rewrite Cunfold; unfold Max
  | |- context [ C(binding _ _, _)] => rewrite Clet
  | |- context [ C(if _ then _ else _, _)] => rewrite Cif
  
  | |- context [ C(add _ _, _) ] => rewrite Cadd; Crw
  | |- context [ C(sub _ _, _) ] => rewrite Csub; Crw
  | |- context [ C(mul _ _, _) ] => rewrite Cmul; Crw
  | |- context [ C(div _ _, _ ) ] => rewrite Cdiv; Crw
  | |- context [ C(divn _ _, _ )] => rewrite Cdivn; Crw
  | |- context [ C(sum _, _)] => rewrite Csum; Crw
  | |- context [ C(max _ _, _ )] => rewrite Cmax; Crw
  | |- context [ C(join _, _ )] => rewrite ?join_equiv; Crw
  | |- context [ C(concat _ _, _ )] => rewrite ?concat_equiv; Crw
     (*  | |- context [ C(reduce _ _ _,_) ] => rewrite Csum;unfold suml *)
  (*  | |- context [ C(mkvPar _,_) ] => rewrite CmkvPar;unfold mkvParl   *) 
  | |- context [ C((seq_make _) |[_], _)] => rewrite ?seq_make_idx
  | |- context [ C( _, _) ] => rewrite Cunfold
  | _ => idtac
  end.

Ltac Arw :=
   match goal with
  | |- context [ A(_,seq_make _) ] => rewrite Aseq
(*   | |- context [ A(_,mkvPar _) ] => rewrite AmkvPar;unfold mkvParl *)
  | |- context [ A(_ ,add _ _) ] => rewrite Aadd; Crw
  | |- context [ A(_, sub _ _) ] => rewrite Asub; Crw
  | |- context [ A(_, mul _ _) ] => rewrite Amul; Crw
  | |- context [ A(_, div _ _) ] => rewrite Adiv; Crw
  | |- context [ A(_, divn _ _)] => rewrite Adivn; Crw
  | |- context [ A(_, sum _) ] => rewrite Asum; Crw
  | |- context [ A(_, max _ _)] => rewrite Amax; Crw
  | |- context [ A(_, join _ )] => rewrite ?join_equiv; Arw
  | |- context [ A(_, concat _ _ )] => rewrite ?concat_equiv; Arw
  | |- context [ A(_,binding _ _) ] => rewrite Alet;unfold Let
  | |- context [ A(_,if _ then _ else _) ] => rewrite ?Aif
  | |- context [ A (_, (match lt_dec _ _ with
   | left P1 => match lt_dec _ _ with
    |left P2 => _
    | right _ => ?e
    end
   | right _ => ?e end))] => rewrite ?Aif3
  | |- context [ A (_, (match lt_dec _ _ with
   | left P1 => _
   | right _ => _ end))] => rewrite ?Aif2
    | |- context [ @A (ary _ _) (_,_) ] => rewrite Aassign
  | |- context [ A(_, (seq_make _) |[_])] => rewrite ?seq_make_idx
  | |- context [ A(_, _) ] => rewrite Aunfold
  | _ => idtac
   end.

Ltac CGrw:=  
  match goal with
  | |- context [ CG_comm (A _) ] => Arw
  | |- context [ CG_comm (C _) ] => Crw
  | |- context [ CG_comm (skip) _ ] => rewrite CGskip
  | |- context [ CG_comm (If _ _ _) ] => rewrite CGif
  | |- context [ CG_comm (seq _) _ ] => rewrite CGseq
  | |- context [ CG_comm (assign _ _ ) _ ] => rewrite CGassign
  | |- context [ CG_comm (new _ _) _ ] => rewrite CGnew
  | |- context [ CG_comm (comm_seq _ ) _ ] => rewrite CGfor
(*   | |- context [ CG_comm (comm_par _ _) _ ] => rewrite CGparfor,?cnt_parfor *)
  | |- context [CG_comm (_ '; _) _] => rewrite CGseq
    | [ |- context [ CG_comm (fun eta : env => _)]] => CGenvrw
  | _ => idtac
  end; rewrite ?seq_make_idx.

Ltac CGrws := repeat CGrw; unfold CG_data; rewrite ?seq_make_idx; f_equal.

Ltac Accrw :=
  match goal with
  | [ |- context [CG_acc _ (_|{_})]] =>  rewrite CGidxAcc
  | [ |- context [CG_acc _ (vwt _)]] => rewrite CGaccvar
  | [ |- context [CG_acc _ (accp (Var _))]] => rewrite CGVar; rewrite CGaccvar
   | [ |- context [CG_acc _ (accp _)]] => rewrite ?CGaccp
  | _ => idtac
  end.

Ltac Accrws := repeat Accrw.

Ltac Exprw :=
  match goal with
  | [ |- context [CG_exp _ (_|[_])]] => rewrite CGidx
  | [ |- context [CG_exp _ (vrd _)]] => rewrite CGexpvar
  | [ |- context [CG_exp _ (Vrd _)]] => rewrite CGVrd; Accrw
  | [ |- context [CG_exp _ (negate _)]] => rewrite CGneg
  | [ |- context [CG_exp _ (add _ _ )]] => rewrite CGadd
  | [ |- context [CG_exp _ (sub _ _ )]] => rewrite CGsub
  | [ |- context [CG_exp _ (mul _ _ )]] => rewrite CGmul
  | [ |- context [CG_exp _ (div _ _ )]] => rewrite CGdiv
  | [ |- context [CG_exp _ (divn _ _ )]] => rewrite CGdivn
  | [ |- context [CG_exp _ (scal _ _ )]] => rewrite CGscal
  | [ |- context [CG_exp _ (epow _)]] => rewrite CGepow
  | [ |- context [CG_exp _ (ln _)]] => rewrite CGln
  | [ |- context [CG_exp _ rand]] => rewrite CGrand
  end.

Ltac Exprws := repeat Exprw.

Ltac AErw :=
  rewrite ?exp_default_simpl1,?exp_zero,?exp_one;
  Accrws; Exprws.

Ltac applypsrw :=
  rewrite ?fin_1to2d_row , ?fin_1to2d_col;
  match goal with
  | [ |- context [applyps _ (Aidx _ :: _ )]] => rewrite applyps_Aidx
  | [ |- context [applyps _ nil]] => applyps_nil
  end.

Ltac applypsrws :=  repeat applypsrw.

Ltac strnat_simpl:=
  simpl fin2nat; rewrite ?writeNat_str2fin; rewrite ?writeNat_fin;
  match goal with
  | |- context [ writeNat (_ + _) ] => rewrite writeNat_add
  | |- context [ writeNat (_ - _) ] => rewrite writeNat_sub
  | |- context [ writeNat (_ * _) ] => rewrite writeNat_mul
  | |- context [ writeNat (_ / _) ] => rewrite writeNat_div
  | |- context [ writeNat (_ mod _) ] => rewrite writeNat_mod
  | |- context [ writeBool ( _ <? _) ] => rewrite writeBool_lt
  | |- context [ writeBool ( _ =? _) ] => rewrite writeBool_eq
  | |- context [ writeBool ( _ <=? _) ] => rewrite writeBool_le
  | |- context [ writeBool ( _ && _) ] => rewrite writeBool_andb
  | |- context [ writeBool ( _ || _) ] => rewrite writeBool_orb
  | |- context [ writeBool (leb _ _ )] => rewrite writeBool_leb; Exprws;applypsrws
  | |- context [ writeBool (gtb _ _ )] => rewrite writeBool_gtb; Exprws; applypsrws
  | _ => idtac
  end. 

Ltac strSimpl:=
  applypsrws;
  repeat strnat_simpl;
  unfold vstr,istr;
  repeat hypRewrite. 

Ltac Translate :=
  default_unfold; CGrws; AErw; strSimpl.

Ltac Translated := Translate; simpl.

(*********************************** Example *******************************************)

Section Examples.

Variables m1 m2 n1 n2 m n p s batch channel filernum:nat. 
Hypothesis wtn:  writeNat n = "n".
Hypothesis wtm:  writeNat m = "m".
Hypothesis wtp:  writeNat p = "p".
Hypothesis wts:  writeNat s = "s".
Hypothesis wtn1:  writeNat n1 = "n1".
Hypothesis wtn2:  writeNat n2 = "n2".
Hypothesis wtm1:  writeNat m1 = "m1".
Hypothesis wtm2:  writeNat m2 = "m2".
Hypothesis wtbatch:  writeNat batch = "batch".
Hypothesis wtchannel:  writeNat channel = "channel".
Hypothesis wtfilernum:  writeNat filernum = "filernum".
Hypothesis Mn: n>0.
Hypothesis Mm: m>0.
Hypothesis Mn1: n1>0.
Hypothesis Mm1: m1>0.
Hypothesis Mn2: n2>0.
Hypothesis Mm2: m2>0.
Hypothesis Mbatch: batch>0.
Hypothesis Mchannel: channel>0.
Hypothesis Mfilernum: filernum>0.

Section vector.

Let xS : exp (ary '{S m} num) := vrd "x".
Let yS : exp (ary '{S m} num) := vrd "y".

Let x : exp (ary '{m} num) := vrd "x".
Let y : exp (ary '{m} num) := vrd "y".


Definition dot {k} (x y: exp (ary '{k} num)) : exp num :=
  sum (seq_make (fun i : fin k => mul x|[i] y|[i] )).

  
  
  
(*   add (accessd (ary '{ m} num) eta (vwt (vstr 0))) |[ i] *)
  
  

    
  
(*   CG_comm (A (vwt (vstr cnt), zero)) (cnt + 1) ++ ";
  " ++
  CG_comm (comm_seq (fun i : fin n =>  
    f (add (accessd eta p1) |[i] (accessd eta (vwt (vstr cnt)))) (vwt (vstr cnt)))) (cnt + 1). *)


Goal exists output,
  CG_comm (A (accp (Var "out"), dot x y)) 0 = output.
Proof.
  unfold dot. Translated.
  exists "float v0;
v0 = 0 ;
for(int i1=0; i1<m; i1 += 1) 
  { v0 = ((x[i1] * y[i1]) + v0) ;}
out = v0 ;". auto.
Qed.

Hypothesis Em : 0 < m.

Goal exists output,
  CG_comm (A (accp (Var "out"), max x Em)) 0 = output.
Proof. Translated.
 exists"float v0;
v0 = x[0] ;
for(int i1=0; i1<m; i1 += 1) 
  { if ((x[i1]) > (v0))
  { v0 = x[i1] ;}
else
  { v0 = v0 ;}}
out = v0 ;". auto.
Qed.

Lemma dot_fin_aux : forall (n: nat) (i : fin (n -1)), (fin2nat i) < n.
Proof. intros. destruct i as [i Hi]. simpl. lia. Qed.

Lemma dot_fin_aux' : forall (n: nat) (i : fin (n-1)), i + 1 < n.
Proof. intros. destruct i as [i Hi]. simpl. lia. Qed.

(* Definition dot_fin {k} (x: exp (ary '{k} num)) (E:k > 0) :=
  seq_make (fun i: fin (k - 1) => add x|[[fin2nat i|dot_fin_aux i]] x|[[i+1|dot_fin_aux' i]]). *)
  





(* Example dot_fin_test : exists output,
  CG_comm (A(accp (Var "out"), dot_fin x y)) 0 = output. *)


(* Goal exists output,
  CG_comm (A(accp (Var "out"), dot x y)) 0 = output.
Proof. 
  unfold dot. rewrite Asum. unfold Sum. rewrite Cvar.
  unfold new. repeat rewrite CGseq. rewrite CGassign. rewrite CGVar.
  rewrite CGaccvar. rewrite exp_zero. rewrite CGexpvar.
  simpl (applyps "out" [] ++ " = " ++ applyps "0" [] ++ " ;").
  rewrite CGfor. unfold istr. simpl(writeNat 0). simpl ("i" ++ writeNat 0)
   rewrite CGexpvar.
  
   rewrite Cseq_make with(a:= Var "out").
  rewrite CGnew. rewrite Aseq_make. unfold seq_makel. rewrite CGseq.
  rewrite CGfor.
  replace (fun eta : env =>
     new
       (fun tmp : acc num =>
        tmp |:= zero
        '; seqfor
             (fun (i : fin m) (eta0 : env) =>
              A (tmp, add (access eta (vwt (vstr 0))) |[ i] (access eta0 tmp)) eta0)
           '; (fun eta0 : env => A (acc' (Var "out"), access eta0 tmp) eta0))
       (acc' (Var "out")) eta) with
  (fun eta : env =>
     new
       (fun tmp : acc num =>
        tmp |:= zero
        '; seqfor
             (fun (i : fin m) (eta0 : env) =>
              A (tmp, add (Vrd (vwt (vstr 0))) |[ i] (access eta0 tmp)) eta0)
           '; (fun eta0 : env => A (acc' (Var "out"), access eta0 tmp) eta0))
       (acc' (Var "out")) eta). rewrite CGenv_new.
  repeat rewrite CGseq. rewrite CGfor. repeat rewrite CGenv_Vrd. rewrite CGenv0.
  unfold A,C. repeat rewrite CGassign. rewrite CGmul. rewrite CGadd. 
  repeat rewrite CGidx. repeat rewrite CGidxAcc. repeat rewrite CGVrd.
  rewrite CGVar.  str_simpl.
  exists "float v0[m];
for(int i1=0; i1<m; i1 += 1) 
  { v0[i1] = (x[i1] * y[i1]) ;}
float v1;
v1 = 0 ;
for(int i2=0; i2<m; i2 += 1) 
  { v1 = (v0[i2] + v1) ;}
out = v1 ;". auto. 
repeat fun_ext;f_equal. fun_ext. repeat f_equal. repeat fun_ext. f_equal. 
rewrite <- CGenv_Vrd3 with(eta:=x0). auto. *)

End vector.
End Examples.




