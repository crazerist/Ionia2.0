Require Import Reals String Nat List Bool Arith.
Require Export operation.
Require Export autogen.
Import ListNotations.
Set Implicit Arguments.

Open Scope path_scope.

Open Scope string_scope.

Set Printing Depth 1000.         (* 极深设置 *)
Unset Printing Compact Contexts.  (* 禁用所有省略 *)

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
Hypothesis n1m1p : n1 <= m1 + 2 * p.
Hypothesis n2m2p : n2 <= m2 + 2 * p.

Section conv.

Let input1d : Tensor1 m := vrd "input".
Let input2d : exp (ary '{m1} (ary '{m2} num)) := vrd "input".
Let input3d : Tensor3 channel '{m1} '{m2} := vrd "input".
Let input4d : Tensor4 batch channel '{m1} '{m2} := vrd "input".

Let kernel2d : exp (ary '{n1} (ary '{n2} num)) := vrd "kernel".
Let kernel3d : Tensor3 channel '{n1} '{n2} := vrd "kernel".
Let kernel4d : Tensor4 filernum channel '{n1} '{n2} := vrd "kernel".

Let bias : Tensor1 filernum := vrd "bias".

(* 开启字符串作用域以确保"++"操作符可用 *)
Open Scope string_scope.


Goal exists output,
  CG_comm (A(vwt "out", Padding2d p input2d)) 0 = output.
Proof.
  unfold Padding2d. Tensor_unfold. Time Translated.
  exists  "for(int i0=0; i0<(m1) + ((2) * (p)); i0 += 1) 
  { for(int i1=0; i1<(m2) + ((2) * (p)); i1 += 1) 
  { if (i0 < p || i1 < p)
  { out[i0][i1] = 0 ;}
else
  { if ((i0) - (p) < m1 && (i1) - (p) < m2)
  { out[i0][i1] = input[(i0) - (p)][(i1) - (p)] ;}
else
  { out[i0][i1] = 0 ;}}}}". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",Padding3d p input3d)) 0 = output.
Proof. 
  unfold Padding3d,Padding2d. Tensor_unfold. Time Translated.
  exists  "for(int i0=0; i0<channel; i0 += 1) 
  { for(int i1=0; i1<(m1) + ((2) * (p)); i1 += 1) 
  { for(int i2=0; i2<(m2) + ((2) * (p)); i2 += 1) 
  { if (i1 < p || i2 < p)
  { out[i0][i1][i2] = 0 ;}
else
  { if ((i1) - (p) < m1 && (i2) - (p) < m2)
  { out[i0][i1][i2] = input[i0][(i1) - (p)][(i2) - (p)] ;}
else
  { out[i0][i1][i2] = 0 ;}}}}}". auto.
Qed.

Example Padding4d_exam : exists output,
  CG_comm (A(vwt "out",Padding4d p input4d)) 0 = output.
Proof. unfold Padding4d, Padding3d, Padding2d. Tensor_unfold. Time Translated.
  exists ("for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<(m1) + ((2) * (p)); i2 += 1) 
  { for(int i3=0; i3<(m2) + ((2) * (p)); i3 += 1) 
  { if (i2 < p || i3 < p)
  { out[i0][i1][i2][i3] = 0 ;}
else
  { if ((i2) - (p) < m1 && (i3) - (p) < m2)
  { out[i0][i1][i2][i3] = input[i0][i1][(i2) - (p)][(i3) - (p)] ;}
else
  { out[i0][i1][i2][i3] = 0 ;}}}}}}"). auto.
Qed.

Let x : Tensor4 batch n1 m1 m2 := vrd "x".
Let y : Tensor4 batch n2 m1 m2 := vrd "y".

Example Conv2d_exam : exists output,
  CG_comm (A(vwt "out",Conv2d p s kernel2d input2d n1m1p n2m2p)) 0 = output.
Proof. unfold Conv2d. unfold Padding2d. Tensor_unfold. Time Translated.
  exists "float v0[(m1) + ((2) * (p))][(m2) + ((2) * (p))];
for(int i1=0; i1<(m1) + ((2) * (p)); i1 += 1) 
  { for(int i2=0; i2<(m2) + ((2) * (p)); i2 += 1) 
  { if (i1 < p || i2 < p)
  { v0[i1][i2] = 0 ;}
else
  { if ((i1) - (p) < m1 && (i2) - (p) < m2)
  { v0[i1][i2] = input[(i1) - (p)][(i2) - (p)] ;}
else
  { v0[i1][i2] = 0 ;}}}}
for(int i1=0; i1<((((m1) + ((2) * (p))) - (n1)) / (s)) + (1); i1 += 1) 
  { for(int i2=0; i2<((((m2) + ((2) * (p))) - (n2)) / (s)) + (1); i2 += 1) 
  { float v3;
v3 = 0 ;
for(int i4=0; i4<n1; i4 += 1) 
  { float v5;
v5 = 0 ;
for(int i6=0; i6<n2; i6 += 1) 
  { v5 = ((v0[((i1) * (s)) + (i4)][((i2) * (s)) + (i6)] * kernel[i4][i6]) + v5) ;}
v3 = (v5 + v3) ;}
out[i1][i2] = v3 ;}}". auto.
Qed.

Example Conv3_exam : exists output,
  CG_comm (A(vwt "out",Conv3d p s bias kernel4d input3d n1m1p n2m2p)) 0 = output.
Proof. unfold Conv3d, Conv2d, Padding3d, Padding2d.
    Tensor_unfold. Time Translated.
  exists "float v0[channel][(m1) + ((2) * (p))][(m2) + ((2) * (p))];
for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<(m1) + ((2) * (p)); i2 += 1) 
  { for(int i3=0; i3<(m2) + ((2) * (p)); i3 += 1) 
  { if (i2 < p || i3 < p)
  { v0[i1][i2][i3] = 0 ;}
else
  { if ((i2) - (p) < m1 && (i3) - (p) < m2)
  { v0[i1][i2][i3] = input[i1][(i2) - (p)][(i3) - (p)] ;}
else
  { v0[i1][i2][i3] = 0 ;}}}}}
for(int i1=0; i1<filernum; i1 += 1) 
  { for(int i2=0; i2<((((m1) + ((2) * (p))) - (n1)) / (s)) + (1); i2 += 1) 
  { for(int i3=0; i3<((((m2) + ((2) * (p))) - (n2)) / (s)) + (1); i3 += 1) 
  { float v4;
v4 = 0 ;
for(int i5=0; i5<channel; i5 += 1) 
  { float v6;
v6 = 0 ;
for(int i7=0; i7<n1; i7 += 1) 
  { float v8;
v8 = 0 ;
for(int i9=0; i9<n2; i9 += 1) 
  { v8 = ((v0[i5][((i2) * (s)) + (i7)][((i3) * (s)) + (i9)] * kernel[i1][i5][i7][i9]) + v8) ;}
v6 = (v8 + v6) ;}
v4 = (v6 + v4) ;}
out[i1][i2][i3] = (v4 + bias[i1]) ;}}}". auto.
Qed.

End conv.

Section relu.

Let input2d : Tensor2 m1 m2 := vrd "input".
Let input3d : Tensor3 channel m1 m2 := vrd "input".
Let input4d : Tensor4 batch channel m1 m2 := vrd "input".

Example ReLU2d_exam : exists output,
   CG_comm (A(vwt "out",ReLU2d input2d)) 0 = output.
Proof.
  unfold ReLU2d. Tensor_unfold. Time Translated.
  exists "for(int i0=0; i0<m1; i0 += 1) 
  { for(int i1=0; i1<m2; i1 += 1) 
  { if ((input[i0][i1]) <= (0))
  { out[i0][i1] = 0 ;}
else
  { out[i0][i1] = input[i0][i1] ;}}}". auto.
Qed.

Example ReLU3d_exam : exists output,
   CG_comm (A(vwt "out",ReLU3d input3d)) 0 = output.
Proof. 
  unfold ReLU3d. Tensor_unfold. Time Translated.
  exists "for(int i0=0; i0<channel; i0 += 1) 
  { for(int i1=0; i1<m1; i1 += 1) 
  { for(int i2=0; i2<m2; i2 += 1) 
  { if ((input[i0][i1][i2]) <= (0))
  { out[i0][i1][i2] = 0 ;}
else
  { out[i0][i1][i2] = input[i0][i1][i2] ;}}}}". auto.
Qed.

Example ReLU4d_exam : exists output,
   CG_comm (A(vwt "out",ReLU4d input4d)) 0 = output.
Proof.
  unfold ReLU4d. Tensor_unfold. Time Translated.
  exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<m1; i2 += 1) 
  { for(int i3=0; i3<m2; i3 += 1) 
  { if ((input[i0][i1][i2][i3]) <= (0))
  { out[i0][i1][i2][i3] = 0 ;}
else
  { out[i0][i1][i2][i3] = input[i0][i1][i2][i3] ;}}}}}". auto.
Qed.

End relu.

Section softmax.

Let input1d : Tensor1 m := vrd "input".
Let input2d : Tensor2 m1 m2 := vrd "input".
Let input3d : Tensor3 channel m1 m2 := vrd "input".
Let input4d : Tensor4 batch channel m1 m2 := vrd "input".

Goal exists output,
  CG_comm (A(vwt "out",Softmax1d input1d)) 0 = output.
Proof. unfold Softmax1d. Tensor_unfold. Time Translated.
exists "float v0;
v0 = 0 ;
for(int i1=0; i1<m; i1 += 1) 
  { v0 = (exp(input[i1]) + v0) ;}
for(int i1=0; i1<m; i1 += 1) 
  { out[i1] = (exp(input[i1])) / (v0) ;}". auto.
Qed.

Example Softmax2d_exam : exists output,
  CG_comm (A(vwt "out",Softmax2d input2d)) 0 = output.
Proof.
    unfold Softmax2d. Tensor_unfold. Time Translated.
  exists "float v0[m1];
for(int i1=0; i1<m1; i1 += 1) 
  { float v2;
v2 = 0 ;
for(int i3=0; i3<m2; i3 += 1) 
  { v2 = (exp(input[i1][i3]) + v2) ;}
v0[i1] = v2 ;}
for(int i1=0; i1<m1; i1 += 1) 
  { for(int i2=0; i2<m2; i2 += 1) 
  { out[i1][i2] = (exp(input[i1][i2])) / (v0[i1]) ;}}". auto.
Qed.

Example Softmax3d_exam : exists output,
  CG_comm (A(vwt "out",Softmax3d input3d)) 0 = output.
Proof.
    unfold Softmax3d. Tensor_unfold. Time Translated.
  exists "float v0;
v0 = 0 ;
for(int i1=0; i1<channel; i1 += 1) 
  { float v2;
v2 = 0 ;
for(int i3=0; i3<m1; i3 += 1) 
  { float v4;
v4 = 0 ;
for(int i5=0; i5<m2; i5 += 1) 
  { v4 = (exp(input[i1][i3][i5]) + v4) ;}
v2 = (v4 + v2) ;}
v0 = (v2 + v0) ;}
for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<m1; i2 += 1) 
  { for(int i3=0; i3<m2; i3 += 1) 
  { out[i1][i2][i3] = (exp(input[i1][i2][i3])) / (v0) ;}}}". auto.
Qed.

End softmax.

(* ==============================Avgpool Operator=================================== *)

Section avgpool.

Let input1d : Tensor1 m := vrd "input".
Let input2d : Tensor2 m1 m2 := vrd "input".
Let input3d : Tensor3 channel m1 m2 := vrd "input".
Let input4d : Tensor4 batch channel m1 m2 := vrd "input".

Example Avgpool2d_exam : exists output,
  CG_comm (A(vwt "out",Avgpool2d n input2d)) 0 = output.
Proof. unfold Avgpool2d. Tensor_unfold. Time Translated.
  exists "for(int i0=0; i0<(m1) / (n); i0 += 1) 
  { for(int i1=0; i1<(m2) / (n); i1 += 1) 
  { float v2;
v2 = 0 ;
for(int i3=0; i3<n; i3 += 1) 
  { float v4;
v4 = 0 ;
for(int i5=0; i5<n; i5 += 1) 
  { v4 = (input[((i0) * (n)) + (i3)][((i1) * (n)) + (i5)] + v4) ;}
v2 = (v4 + v2) ;}
out[i0][i1] = ((v2) / ((n) * (n))) ;}}". auto.
Qed.

Example Avgpool3d_exam : exists output,
  CG_comm (A(vwt "out",Avgpool3d n input3d)) 0 = output.
Proof.  unfold Avgpool3d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<channel; i0 += 1) 
  { for(int i1=0; i1<(m1) / (n); i1 += 1) 
  { for(int i2=0; i2<(m2) / (n); i2 += 1) 
  { float v3;
v3 = 0 ;
for(int i4=0; i4<n; i4 += 1) 
  { float v5;
v5 = 0 ;
for(int i6=0; i6<n; i6 += 1) 
  { v5 = (input[i0][((i1) * (n)) + (i4)][((i2) * (n)) + (i6)] + v5) ;}
v3 = (v5 + v3) ;}
out[i0][i1][i2] = ((v3) / ((n) * (n))) ;}}}". auto.
Qed. 

Example Avgpool4d : exists output,
  CG_comm (A(vwt "out",Avgpool4d n input4d)) 0 = output.
Proof. unfold Avgpool4d. Tensor_unfold. Time Translated.
  exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<(m1) / (n); i2 += 1) 
  { for(int i3=0; i3<(m2) / (n); i3 += 1) 
  { float v4;
v4 = 0 ;
for(int i5=0; i5<n; i5 += 1) 
  { float v6;
v6 = 0 ;
for(int i7=0; i7<n; i7 += 1) 
  { v6 = (input[i0][i1][((i2) * (n)) + (i5)][((i3) * (n)) + (i7)] + v6) ;}
v4 = (v6 + v4) ;}
out[i0][i1][i2][i3] = ((v4) / ((n) * (n))) ;}}}}". auto.
Qed.

End avgpool.

Section maxpool.

Let input1d : Tensor1 m := vrd "input".
Let input2d : Tensor2 m1 m2 := vrd "input".
Let input3d : Tensor3 channel m1 m2 := vrd "input".
Let input4d : Tensor4 batch channel m1 m2 := vrd "input".

Hypothesis En : 0 < n.

Example Maxpool2d_exam : exists output,
  CG_comm (A(vwt "out",Maxpool2d n input2d En)) 0 = output.
Proof. unfold Maxpool2d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<(m1) / (n); i0 += 1) 
  { for(int i1=0; i1<(m2) / (n); i1 += 1) 
  { float v2[n];
for(int i3=0; i3<n; i3 += 1) 
  { float v4[n];
for(int i5=0; i5<n; i5 += 1) 
  { v4[i5] = input[((i0) * (n)) + (i3)][((i1) * (n)) + (i5)] ;}
float v5;
  v5 = v4[0] ;;
  for(int i6=0; i6<n; i6 += 1) 
  { if ((v4[i6]) > (v5))
  { v5 = v4[i6] ;}
else
  { v5 = v5 ;}};
  v2[i3] = v5 ;}
float v3;
  v3 = v2[0] ;;
  for(int i4=0; i4<n; i4 += 1) 
  { if ((v2[i4]) > (v3))
  { v3 = v2[i4] ;}
else
  { v3 = v3 ;}};
  out[i0][i1] = v3 ;}}". auto.
Qed.

Example Maxpool3d_exam : exists output,
  CG_comm (A(vwt "out",Maxpool3d n input3d En)) 0 = output.
Proof. unfold Maxpool3d. Tensor_unfold. Time Translated.
exists
"for(int i0=0; i0<channel; i0 += 1) 
  { for(int i1=0; i1<(m1) / (n); i1 += 1) 
  { for(int i2=0; i2<(m2) / (n); i2 += 1) 
  { float v3[n];
for(int i4=0; i4<n; i4 += 1) 
  { float v5[n];
for(int i6=0; i6<n; i6 += 1) 
  { v5[i6] = input[i0][((i1) * (n)) + (i4)][((i2) * (n)) + (i6)] ;}
float v6;
  v6 = v5[0] ;;
  for(int i7=0; i7<n; i7 += 1) 
  { if ((v5[i7]) > (v6))
  { v6 = v5[i7] ;}
else
  { v6 = v6 ;}};
  v3[i4] = v6 ;}
float v4;
  v4 = v3[0] ;;
  for(int i5=0; i5<n; i5 += 1) 
  { if ((v3[i5]) > (v4))
  { v4 = v3[i5] ;}
else
  { v4 = v4 ;}};
  out[i0][i1][i2] = v4 ;}}}". auto.
Qed.

Example Maxpool4d_exam : exists output,
  CG_comm (A(vwt "out",Maxpool4d n input4d En)) 0 = output.
Proof. unfold Maxpool4d. Tensor_unfold. Time Translated.
exists
"for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<(m1) / (n); i2 += 1) 
  { for(int i3=0; i3<(m2) / (n); i3 += 1) 
  { float v4[n];
for(int i5=0; i5<n; i5 += 1) 
  { float v6[n];
for(int i7=0; i7<n; i7 += 1) 
  { v6[i7] = input[i0][i1][((i2) * (n)) + (i5)][((i3) * (n)) + (i7)] ;}
float v7;
  v7 = v6[0] ;;
  for(int i8=0; i8<n; i8 += 1) 
  { if ((v6[i8]) > (v7))
  { v7 = v6[i8] ;}
else
  { v7 = v7 ;}};
  v4[i5] = v7 ;}
float v5;
  v5 = v4[0] ;;
  for(int i6=0; i6<n; i6 += 1) 
  { if ((v4[i6]) > (v5))
  { v5 = v4[i6] ;}
else
  { v5 = v5 ;}};
  out[i0][i1][i2][i3] = v5 ;}}}}". auto.
Qed.

End maxpool.

(* ==============================Linear Operator=================================== *)

Section linear.

Let input1d : Tensor1 m := vrd "input".
Let input2d : Tensor2 batch m := vrd "input".
Let input3d : Tensor3 batch channel m:= vrd "input".

Let kernel2d : Tensor2 n m := vrd "kernel".

Let bias : Tensor1 n := vrd "bias".

Example Linear_exam : exists output,
  CG_comm (A(vwt "out",Linear1d kernel2d bias input1d )) 0 = output.
Proof. unfold Linear1d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<n; i0 += 1) 
  { float v1;
v1 = 0 ;
for(int i2=0; i2<m; i2 += 1) 
  { v1 = ((input[i2] * kernel[i0][i2]) + v1) ;}
out[i0] = (v1 + bias[i0]) ;}". auto.
Qed.

Example Linear2d_exam : exists  output,
  CG_comm (A(vwt "out",Linear2d kernel2d bias input2d )) 0 = output.
Proof. unfold Linear2d. Tensor_unfold. Time Translated. 
exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<n; i1 += 1) 
  { float v2;
v2 = 0 ;
for(int i3=0; i3<m; i3 += 1) 
  { v2 = ((input[i0][i3] * kernel[i1][i3]) + v2) ;}
out[i0][i1] = (v2 + bias[i1]) ;}}". auto.
Qed.

Example Linear3d_exam : exists  output,
  CG_comm (A(vwt "out",Linear3d kernel2d bias input3d )) 0 = output.
Proof. unfold Linear3d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<n; i2 += 1) 
  { float v3;
v3 = 0 ;
for(int i4=0; i4<m; i4 += 1) 
  { v3 = ((input[i0][i1][i4] * kernel[i2][i4]) + v3) ;}
out[i0][i1][i2] = (v3 + bias[i2]) ;}}}". auto.
Qed.

End linear.

(* ==============================Flatten Operator=================================== *)

Section flatten.

Let input2d : Tensor2 m1 m2 := vrd "input".
Let input3d : Tensor3 channel m1 m2 := vrd "input".
Let input4d : Tensor4 batch channel m1 m2 := vrd "input".

Definition Tensor2_unfold {k1 k2} (input : Tensor2 k1 k2) : 
exp (ary '{k1} (ary '{k2} num)). Proof. exact input. Defined.

Goal exists output,
  CG_comm (A(accp (Var "out"), join (Tensor2_unfold input2d))) 0 = output.
Proof.
   unfold Tensor2_unfold. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<(m1) * (m2); i0 += 1) 
  { out[i0] = input[(i0) / (m2)][(i0) % (m2)] ;}". auto. Qed.

Example Flatten3d_exam : exists output, 
  CG_comm (A(vwt "out",Flatten3d input3d )) 0 = output.
Proof. unfold Flatten3d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<((channel) * (m1)) * (m2); i0 += 1) 
  { out[i0] = input[((i0) / (m2)) / (m1)][((i0) / (m2)) % (m1)][(i0) % (m2)] ;}". auto.
Qed.

Example Flatten4d_exam : exists output, 
  CG_comm (A(vwt "out",Flatten4d input4d )) 0 = output.
Proof. unfold Flatten4d, Flatten3d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<((channel) * (m1)) * (m2); i1 += 1) 
  { out[i0][i1] = input[i0][((i1) / (m2)) / (m1)][((i1) / (m2)) % (m1)][(i1) % (m2)] ;}}". auto.
Qed.

End flatten.

Section concat.

Let x : Tensor4 batch n1 m1 m2 := vrd "x".
Let y : Tensor4 batch n2 m1 m2 := vrd "y".

Goal exists output,
  CG_comm (A(vwt "out",Concat4d x y )) 0 = output.
Proof. 
unfold Concat4d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<(n1) + (n2); i1 += 1) 
  { if (i1 < n1)
  { for(int i2=0; i2<m1; i2 += 1) 
  { for(int i3=0; i3<m2; i3 += 1) 
  { out[i0][i1][i2][i3] = x[i0][i1][i2][i3] ;}}}
else
  { for(int i2=0; i2<m1; i2 += 1) 
  { for(int i3=0; i3<m2; i3 += 1) 
  { out[i0][i1][i2][i3] = y[i0][(i1) - (n1)][i2][i3] ;}}}}}".
auto.
Qed.

End concat.

(* ==============================Truncl Operator=================================== *)
(*
Section truncl.

Let input1d : Tensor1 m := vrd "input".
Let input2d : Tensor2 batch m := vrd "input".

Hypothesis Em : n <= m.



Goal exists output,
  CG_comm (A(vwt "out",Truncl1d n input1d Em)) 0 = output.
Proof. 
unfold Truncl1d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<(m) - (n); i0 += 1) 
  { out[i0] = input[(i0) + (n)] ;}".
auto.
Qed.

Hypothesis Eb : n <= batch.

Goal exists output,
  CG_comm (A(vwt "out",Truncl2d n input2d Eb)) 0 = output.
Proof. 
unfold Truncl2d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<(batch) - (n); i0 += 1) 
  { for(int i1=0; i1<m; i1 += 1) 
  { out[i0][i1] = input[(i0) + (n)][i1] ;}}".
auto.
Qed.

End truncl.
*)
(* ==============================Tensor_element Operator=================================== *)

Section tensor_element.

Let input1d : Tensor1 m := vrd "input".
Let input2d : Tensor2 batch m := vrd "input".

Let e : exp num := vrd "e".

Goal exists output,
  CG_comm (A(vwt "out",Fill2d batch m e )) 0 = output.
Proof. 
unfold Fill2d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<m; i1 += 1) 
  { out[i0][i1] = e ;}}".
auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",Exp2d input2d )) 0 = output.
Proof. 
unfold Exp2d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<m; i1 += 1) 
  { out[i0][i1] = exp(input[i0][i1]) ;}}".
auto.
Qed.

End tensor_element.

(* ==============================Two_tensors Operator=================================== *)

Section two_tensor_element.

Let x : Tensor2 m1 m2 := vrd "x".
Let y : Tensor2 m1 m2 := vrd "y".

Let x3d : Tensor3 channel m1 m2 := vrd "x".
Let y3d : Tensor3 channel m1 m2 := vrd "y".

Let x4d : Tensor4 batch channel m1 m2 := vrd "x".
Let y4d : Tensor4 batch channel m1 m2 := vrd "y".

Goal exists output,
  CG_comm (A(vwt "out",Mul2d x y)) 0 = output.
Proof. 
unfold Mul2d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<m1; i0 += 1) 
  { for(int i1=0; i1<m2; i1 += 1) 
  { out[i0][i1] = (x[i0][i1] * y[i0][i1]) ;}}".
auto. Qed.

Goal exists output,
  CG_comm (A(vwt "out",Sub2d x y)) 0 = output.
Proof.
  unfold Sub2d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<m1; i0 += 1) 
  { for(int i1=0; i1<m2; i1 += 1) 
  { out[i0][i1] = (x[i0][i1] - y[i0][i1]) ;}}".
auto. Qed.

Goal exists output,
  CG_comm (A(vwt "out",Add2d x y)) 0 = output.
Proof. 
unfold Add2d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<m1; i0 += 1) 
  { for(int i1=0; i1<m2; i1 += 1) 
  { out[i0][i1] = (x[i0][i1] + y[i0][i1]) ;}}".
auto. Qed.

Goal exists output,
  CG_comm (A(vwt "out",Add3d x3d y3d)) 0 = output.
Proof. 
unfold Add3d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<channel; i0 += 1) 
  { for(int i1=0; i1<m1; i1 += 1) 
  { for(int i2=0; i2<m2; i2 += 1) 
  { out[i0][i1][i2] = (x[i0][i1][i2] + y[i0][i1][i2]) ;}}}".
auto. Qed.

Goal exists output,
  CG_comm (A(vwt "out",Add4d x4d y4d)) 0 = output.
Proof. 
unfold Add4d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<m1; i2 += 1) 
  { for(int i3=0; i3<m2; i3 += 1) 
  { out[i0][i1][i2][i3] = (x[i0][i1][i2][i3] + y[i0][i1][i2][i3]) ;}}}}".
auto. Qed.

End two_tensor_element.

(* ==============================Sum Operator=================================== *)

Section sum.

Let input : Tensor2 m1 m2 := vrd "input".

Goal exists output,
  CG_comm (A(vwt "out",Sum2d input)) 0 = output.
Proof.  unfold Sum2d. Tensor_unfold. Time Translated.
exists "float v0;
v0 = 0 ;
for(int i1=0; i1<m1; i1 += 1) 
  { float v2;
v2 = 0 ;
for(int i3=0; i3<m2; i3 += 1) 
  { v2 = (input[i1][i3] + v2) ;}
v0 = (v2 + v0) ;}
out = v0 ;".
auto. Qed.

End sum.

(* ==============================AdaptiveAvgPool Operator=================================== *)

Section adaptiveAvgPool.

Let input : Tensor4 batch channel m1 m2 := vrd "input".

Goal exists output,
  CG_comm (A(vwt "out",AdaptiveAvgPool4d n1 n2 input)) 0 = output.
Proof. 
unfold AdaptiveAvgPool4d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<n1; i2 += 1) 
  { for(int i3=0; i3<n2; i3 += 1) 
  { float v4;
v4 = 0 ;
for(int i5=0; i5<m1; i5 += 1) 
  { float v6;
v6 = 0 ;
for(int i7=0; i7<m2; i7 += 1) 
  { v6 = (input[i0][i1][i5][i7] + v6) ;}
v4 = (v6 + v4) ;}
out[i0][i1][i2][i3] = ((v4) / ((n1) * (n2))) ;}}}}".
auto. Qed.

End adaptiveAvgPool.

(* ==============================Maxpool_pad Operator=================================== *)

Section maxpool_pad.

Let input2d : Tensor2 m1 m2 := vrd "input".
Let input3d : Tensor3 channel m1 m2 := vrd "input".
Let input4d : Tensor4 batch channel m1 m2 := vrd "input".

Hypothesis En : 0 < n.
Hypothesis Em1 : n <= m1 + 2 * p.
Hypothesis Em2 : n <= m2 + 2 * p.
Goal exists output,
  CG_comm (A(vwt "out",Maxpool3d_pad n s p input3d En Em1 Em2)) 0 = output.
Proof. 
unfold Maxpool3d_pad, Padding3d,Padding2d. Tensor_unfold. Time Translated .
exists "float v0[channel][(m1) + ((2) * (p))][(m2) + ((2) * (p))];
for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<(m1) + ((2) * (p)); i2 += 1) 
  { for(int i3=0; i3<(m2) + ((2) * (p)); i3 += 1) 
  { if (i2 < p || i3 < p)
  { v0[i1][i2][i3] = 0 ;}
else
  { if ((i2) - (p) < m1 && (i3) - (p) < m2)
  { v0[i1][i2][i3] = input[i1][(i2) - (p)][(i3) - (p)] ;}
else
  { v0[i1][i2][i3] = 0 ;}}}}}
for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<((((m1) + ((2) * (p))) - (n)) / (s)) + (1); i2 += 1) 
  { for(int i3=0; i3<((((m2) + ((2) * (p))) - (n)) / (s)) + (1); i3 += 1) 
  { float v4[n];
for(int i5=0; i5<n; i5 += 1) 
  { float v6[n];
for(int i7=0; i7<n; i7 += 1) 
  { v6[i7] = v0[i1][((i2) * (s)) + (i5)][((i3) * (s)) + (i7)] ;}
float v7;
  v7 = v6[0] ;;
  for(int i8=0; i8<n; i8 += 1) 
  { if ((v6[i8]) > (v7))
  { v7 = v6[i8] ;}
else
  { v7 = v7 ;}};
  v4[i5] = v7 ;}
float v5;
  v5 = v4[0] ;;
  for(int i6=0; i6<n; i6 += 1) 
  { if ((v4[i6]) > (v5))
  { v5 = v4[i6] ;}
else
  { v5 = v5 ;}};
  out[i1][i2][i3] = v5 ;}}}".
auto. Qed.

Goal exists output,
  CG_comm (A(vwt "out",Maxpool4d_pad n s p input4d En Em1 Em2)) 0 = output.
Proof. 
unfold Maxpool4d_pad, Padding4d, Padding3d, Padding2d.
Tensor_unfold. Time Translated.
exists "float v0[batch][channel][(m1) + ((2) * (p))][(m2) + ((2) * (p))];
for(int i1=0; i1<batch; i1 += 1) 
  { for(int i2=0; i2<channel; i2 += 1) 
  { for(int i3=0; i3<(m1) + ((2) * (p)); i3 += 1) 
  { for(int i4=0; i4<(m2) + ((2) * (p)); i4 += 1) 
  { if (i3 < p || i4 < p)
  { v0[i1][i2][i3][i4] = 0 ;}
else
  { if ((i3) - (p) < m1 && (i4) - (p) < m2)
  { v0[i1][i2][i3][i4] = input[i1][i2][(i3) - (p)][(i4) - (p)] ;}
else
  { v0[i1][i2][i3][i4] = 0 ;}}}}}}
for(int i1=0; i1<batch; i1 += 1) 
  { for(int i2=0; i2<channel; i2 += 1) 
  { for(int i3=0; i3<((((m1) + ((2) * (p))) - (n)) / (s)) + (1); i3 += 1) 
  { for(int i4=0; i4<((((m2) + ((2) * (p))) - (n)) / (s)) + (1); i4 += 1) 
  { float v5[n];
for(int i6=0; i6<n; i6 += 1) 
  { float v7[n];
for(int i8=0; i8<n; i8 += 1) 
  { v7[i8] = v0[i1][i2][((i3) * (s)) + (i6)][((i4) * (s)) + (i8)] ;}
float v8;
  v8 = v7[0] ;;
  for(int i9=0; i9<n; i9 += 1) 
  { if ((v7[i9]) > (v8))
  { v8 = v7[i9] ;}
else
  { v8 = v8 ;}};
  v5[i6] = v8 ;}
float v6;
  v6 = v5[0] ;;
  for(int i7=0; i7<n; i7 += 1) 
  { if ((v5[i7]) > (v6))
  { v6 = v5[i7] ;}
else
  { v6 = v6 ;}};
  out[i1][i2][i3][i4] = v6 ;}}}}".
auto. Qed.

End maxpool_pad.

(* ==============================Sigmoid Operator=================================== *)

Section sigmoid.

Let input2d : Tensor2 m1 m2 := vrd "input".
Let input4d : Tensor4 batch channel m1 m2 := vrd "input".

Goal exists output,
  CG_comm (A(vwt "out",Sigmoid2d input2d)) 0 = output.
Proof. 
unfold Sigmoid2d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<m1; i0 += 1) 
  { for(int i1=0; i1<m2; i1 += 1) 
  { out[i0][i1] = (1) / ((1 + exp((- input[i0][i1])))) ;}}".
auto. Qed.

Goal exists output,
  CG_comm (A(vwt "out",Sigmoid4d input4d)) 0 = output.
Proof. 
unfold Sigmoid4d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<m1; i2 += 1) 
  { for(int i3=0; i3<m2; i3 += 1) 
  { out[i0][i1][i2][i3] = (1) / ((1 + exp((- input[i0][i1][i2][i3])))) ;}}}}".
auto. Qed.

End sigmoid.

(* ==============================Randn Operator=================================== *)

Section randn.

Let input2d : Tensor2 m1 m2 := vrd "input".

Goal exists output,
  CG_comm (A(vwt "out", Randn2d m1 m2 )) 0 = output.
Proof. 
  unfold Randn2d. Tensor_unfold. Time Translated.
  exists "for(int i0=0; i0<m1; i0 += 1) 
  { for(int i1=0; i1<m2; i1 += 1) 
  { out[i0][i1] = rand() ;}}". auto.
Qed.

End randn.

(* ==============================Dropout Operator=================================== *)

Section dropout.

Let input2d : Tensor2 m1 m2 := vrd "input".
Let dropout_ratio : exp num := vrd "dropout_ratio".

Goal exists output,
  CG_comm (A(vwt "out", Dropout2d input2d dropout_ratio )) 0 = output.
Proof. 
  unfold Dropout2d. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<m1; i0 += 1) 
  { for(int i1=0; i1<m2; i1 += 1) 
  { if ((dropout_ratio) > (rand()))
  { out[i0][i1] = 0 ;}
else
  { out[i0][i1] = (input[i0][i1]) / ((1 - dropout_ratio)) ;}}}". auto.
Qed.

End dropout.

(* ==============================ConvTranspose Operator=================================== *)

Section convTranspose.

Let input2d : Tensor2 m1 m2 := vrd "input".
Let w : Tensor2 n1 n2 := vrd "kernel".

Hypothesis Em1 : 0 < m1.
Hypothesis Em2 : 0 < m2.

Goal exists output,
  CG_comm (A(vwt "out", Interpolation2d s input2d Em1 Em2)) 0 = output.
Proof. 
  unfold Interpolation2d. Tensor_unfold. Time Translated. 
exists "for(int i0=0; i0<(((m1) - (1)) * (s)) + (1); i0 += 1) 
  { for(int i1=0; i1<(((m2) - (1)) * (s)) + (1); i1 += 1) 
  { if ((i0) % (s) == 0 && (i1) % (s) == 0)
  { out[i0][i1] = input[(i0) / (s)][(i1) / (s)] ;}
else
  { out[i0][i1] = 0 ;}}}". auto.
Qed.

Hypothesis En1 : 1 + p <= n1.
Hypothesis En2 : 1 + p <= n2.

Goal exists output,
  CG_comm (A(vwt "out", ConvTranspose2d p s input2d w Em1 Em2 En1 En2)) 0 = output.
Proof. 
  unfold ConvTranspose2d, Interpolation2d. Tensor_unfold. Time Translated.
  exists "float v0[(((m1) - (1)) * (s)) + (1)][(((m2) - (1)) * (s)) + (1)];
for(int i1=0; i1<(((m1) - (1)) * (s)) + (1); i1 += 1) 
  { for(int i2=0; i2<(((m2) - (1)) * (s)) + (1); i2 += 1) 
  { if ((i1) % (s) == 0 && (i2) % (s) == 0)
  { v0[i1][i2] = input[(i1) / (s)][(i2) / (s)] ;}
else
  { v0[i1][i2] = 0 ;}}}
float v1[((((m1) - (1)) * (s)) + (1)) + ((2) * (((n1) - (1)) - (p)))][((((m2) - (1)) * (s)) + (1)) + ((2) * (((n2) - (1)) - (p)))];
for(int i2=0; i2<((((m1) - (1)) * (s)) + (1)) + ((2) * (((n1) - (1)) - (p))); i2 += 1) 
  { for(int i3=0; i3<((((m2) - (1)) * (s)) + (1)) + ((2) * (((n2) - (1)) - (p))); i3 += 1) 
  { if (i2 < ((n1) - (1)) - (p) && i3 < ((n2) - (1)) - (p))
  { v1[i2][i3] = 0 ;}
else
  { if ((i2) - (((n1) - (1)) - (p)) < (((m1) - (1)) * (s)) + (1) && (i2) - (((n2) - (1)) - (p)) < (((m2) - (1)) * (s)) + (1))
  { v1[i2][i3] = v0[(i2) - (((n1) - (1)) - (p))][(i2) - (((n2) - (1)) - (p))] ;}
else
  { v1[i2][i3] = 0 ;}}}}
for(int i2=0; i2<((((m1) - (1)) * (s)) + (n1)) - ((2) * (p)); i2 += 1) 
  { for(int i3=0; i3<((((m2) - (1)) * (s)) + (n2)) - ((2) * (p)); i3 += 1) 
  { float v4;
v4 = 0 ;
for(int i5=0; i5<n1; i5 += 1) 
  { float v6;
v6 = 0 ;
for(int i7=0; i7<n2; i7 += 1) 
  { v6 = ((v1[(i2) + (i5)][(i3) + (i7)] * kernel[i5][i7]) + v6) ;}
v4 = (v6 + v4) ;}
out[i2][i3] = v4 ;}}". auto.
Qed.

End convTranspose.

(* ==============================Tanh Operator=================================== *)

Section tanh.

Let input4d : Tensor4 batch channel m1 m2 := vrd "input".

Goal exists output,
  CG_comm (A(vwt "out", Tanh4d input4d)) 0 = output.
Proof. 
  unfold Tanh4d.  Tensor_unfold. Time Translated.
  exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<m1; i2 += 1) 
  { for(int i3=0; i3<m2; i3 += 1) 
  { out[i0][i1][i2][i3] = ((exp(input[i0][i1][i2][i3]) - exp((- input[i0][i1][i2][i3])))) / ((exp(input[i0][i1][i2][i3]) + exp((- input[i0][i1][i2][i3])))) ;}}}}". auto.
Qed.

End tanh.

(* ==============================LeakyReLU Operator=================================== *)

Section leakyReLU.

Let input4d : Tensor4 batch channel m1 m2 := vrd "input".
Let negative_slope : exp num := vrd "negative_slope".

Goal exists output,
  CG_comm (A(vwt "out", LeakyReLU4d negative_slope input4d)) 0 = output.
Proof. 
  unfold LeakyReLU4d. Tensor_unfold. Time Translated.

  exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<m1; i2 += 1) 
  { for(int i3=0; i3<m2; i3 += 1) 
  { if ((input[i0][i1][i2][i3]) > (0))
  { out[i0][i1][i2][i3] = input[i0][i1][i2][i3] ;}
else
  { out[i0][i1][i2][i3] = (negative_slope * input[i0][i1][i2][i3]) ;}}}}}". auto.
Qed.

End leakyReLU.

(* ==============================Log_Softmax Operator=================================== *)

Section log_Softmax.

Let input2d : Tensor2 m1 m2 := vrd "input".

Goal exists output,
  CG_comm (A(vwt "out", Log_Softmax2d input2d)) 0 = output.
Proof. 
  unfold Log_Softmax2d. Tensor_unfold. Time Translated.
  exists "float v0[m1];
for(int i1=0; i1<m1; i1 += 1) 
  { float v2;
v2 = 0 ;
for(int i3=0; i3<m2; i3 += 1) 
  { v2 = (exp(input[i1][i3]) + v2) ;}
v0[i1] = v2 ;}
for(int i1=0; i1<m1; i1 += 1) 
  { for(int i2=0; i2<m2; i2 += 1) 
  { out[i1][i2] = (log((exp(input[i1][i2])) / (v0[i1]))) ;}}". auto.
Qed.

End log_Softmax.

(* ==============================BCELoss Operator=================================== *)

Section bceLoss.

Let input2d : Tensor2 batch m := vrd "input".
Let label : Tensor2 batch m := vrd "label".

Goal exists output,
  CG_comm (A(vwt "out", BCELoss2d input2d label)) 0 = output.
Proof. 
  unfold BCELoss2d. Tensor_unfold. Time Translated. 
  exists "for(int i0=0; i0<batch; i0 += 1) 
  { for(int i1=0; i1<m; i1 += 1) 
  { out[i0][i1] = (- ((label[i0][i1] * (log(input[i0][i1]))) + ((1 - label[i0][i1]) * (log((1 - input[i0][i1])))))) ;}}". auto.
Qed.

End bceLoss.

(* ****************************** CNN Backward ****************************** *)

Section backward.

Variables r:R. 
Hypothesis wtr:  writeR r = "s".

Let dout : exp (ary '{m + n - 1} (ary '{m + n - 1} num)) := vrd "dout".
Let dout_aver : exp (ary '{m} (ary '{m} num)) := vrd "dout".
Let z_l_1 : exp (ary '{n*m} (ary '{n*m} num)) := vrd "z_l_1".
Let w_bw : exp (ary '{n} (ary '{n} num)) := vrd "kernel".
Let x_bw : exp (ary '{m} (ary '{m} num)) := vrd "input".
Let y : exp (ary '{n} num) := vrd "y".
Let y' : exp (ary '{n} num) := vrd "y'".

Let w_l_nn : exp (ary '{n} (ary '{m} num)) := vrd "w_l".
Let z_l_1_nn : exp (ary '{m} num) := vrd "z_l_1".
Let d_l_nn : exp (ary '{n} num) := vrd "d_l".

Let d_l_averback : exp (ary '{channel} (ary '{m} (ary '{m} num))) := vrd "d_l".
Let z_l_1_aver : exp (ary '{channel} (ary '{n*m} (ary '{n*m} num))) := vrd "z_l_1".

Let w : exp (ary '{filernum} (ary '{channel} (ary '{n} (ary '{n} num)))) := vrd "kernel".
Let dout_conv : exp (ary '{filernum} (ary '{m} (ary '{m} num))) := vrd "dout".
Let z_conv : exp (ary '{channel} (ary '{m+n-1} (ary '{m+n-1} num))) := vrd "z".

Let dout_conv_l : exp (ary '{filernum} (ary '{m+n-1} (ary '{m+n-1} num))) := vrd "dout".
Let z_conv_l : exp (ary '{channel} (ary '{m} (ary '{m} num))) := vrd "z".

Hypothesis En : 0 < n.
Goal exists output,
  CG_comm (A(vwt "out",Softmax_Loss y F[En])) 0 = output.
Proof.
unfold Softmax_Loss. Tensor_unfold. Time Translated.
exists "float v0;
v0 = 0 ;
for(int i1=0; i1<n; i1 += 1) 
  { v0 = (exp(y[i1]) + v0) ;}
out = (- (log((exp(y[0])) / (v0)))) ;". auto.
Qed.


Goal exists output,
  CG_comm (A(vwt "out",Softmax_loss y)) 0 = output.
Proof.
unfold Softmax_loss, Softmax1d. Tensor_unfold. Time Translate.
exists "float v0[n];
float v1;
v1 = 0 ;
for(int i2=0; i2<n; i2 += 1) 
  { v1 = (exp(y[i2]) + v1) ;}
for(int i2=0; i2<n; i2 += 1) 
  { v0[i2] = (exp(y[i2])) / (v1) ;}
for(int i1=0; i1<n; i1 += 1) 
  { out[i1] = (- (log(v0[i1]))) ;}". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",loss y)) 0 = output.
Proof. unfold loss. Tensor_unfold. Time Translated.
exists "float v0;
v0 = 0 ;
for(int i1=0; i1<n; i1 += 1) 
  { v0 = ((- (log(y[i1]))) + v0) ;}
out = ((v0) / (n)) ;". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out", MSE_loss y y')) 0 = output.
Proof. unfold MSE_loss. Tensor_unfold. Time Translated.
exists "float v0;
v0 = 0 ;
for(int i1=0; i1<n; i1 += 1) 
  { v0 = (((y[i1] - y'[i1]) * (y[i1] - y'[i1])) + v0) ;}
out = ((v0) / (n)) ;". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",average_pool_backward dout_aver z_l_1)) 0 = output.
Proof. unfold average_pool_backward. Tensor_unfold. Time Translated.
  exists "for(int i0=0; i0<(n) * (m); i0 += 1) 
  { for(int i1=0; i1<(n) * (m); i1 += 1) 
  { out[i0][i1] = (dout[(i0) / (n)][(i1) / (n)] * z_l_1[i0][i1]) ;}}". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",average_pool_backward_g d_l_averback n z_l_1_aver)) 0 = output.
Proof. unfold average_pool_backward_g. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<channel; i0 += 1) 
  { for(int i1=0; i1<(n) * (m); i1 += 1) 
  { for(int i2=0; i2<(n) * (m); i2 += 1) 
  { out[i0][i1][i2] = (d_l[i0][(i1) / (n)][(i2) / (n)] * z_l_1[i0][i1][i2]) ;}}}". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",convolution_backward x_bw dout w_bw En)) 0 = output.
Proof. unfold convolution_backward, Padding2d, relu_grad. Tensor_unfold. Time Translated.
exists "float v0[(m) + ((2) * ((n) - (1)))][(m) + ((2) * ((n) - (1)))];
for(int i1=0; i1<(m) + ((2) * ((n) - (1))); i1 += 1) 
  { for(int i2=0; i2<(m) + ((2) * ((n) - (1))); i2 += 1) 
  { if (i1 < (n) - (1) || i2 < (n) - (1))
  { v0[i1][i2] = 0 ;}
else
  { if ((i1) - ((n) - (1)) < m && (i2) - ((n) - (1)) < m)
  { v0[i1][i2] = input[(i1) - ((n) - (1))][(i2) - ((n) - (1))] ;}
else
  { v0[i1][i2] = 0 ;}}}}
for(int i1=0; i1<((m) + (n)) - (1); i1 += 1) 
  { for(int i2=0; i2<((m) + (n)) - (1); i2 += 1) 
  { float v3;
v3 = 0 ;
for(int i4=0; i4<n; i4 += 1) 
  { float v5;
v5 = 0 ;
for(int i6=0; i6<n; i6 += 1) 
  { v5 = ((v0[(i1) + (i4)][(i2) + (i6)] * kernel[((n) - (1)) - (i4)][((n) - (1)) - (i6)]) + v5) ;}
v3 = (v5 + v3) ;}
if ((dout[i1][i2]) <= (0))
  { out[i1][i2] = (v3 * 0) ;}
else
  { out[i1][i2] = (v3 * 1) ;}}}". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",convolution_backward_w x_bw dout En)) 0 = output.
Proof. unfold convolution_backward_w. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<n; i0 += 1) 
  { for(int i1=0; i1<n; i1 += 1) 
  { float v2;
v2 = 0 ;
for(int i3=0; i3<m; i3 += 1) 
  { float v4;
v4 = 0 ;
for(int i5=0; i5<m; i5 += 1) 
  { v4 = ((dout[(i0) + (i3)][(i1) + (i5)] * input[i3][i5]) + v4) ;}
v2 = (v4 + v2) ;}
out[i0][i1] = v2 ;}}". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",convolution_backward_w_g dout_conv_l z_conv_l)) 0 = output.
Proof. unfold convolution_backward_w_g. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<filernum; i0 += 1) 
  { for(int i1=0; i1<channel; i1 += 1) 
  { for(int i2=0; i2<n; i2 += 1) 
  { for(int i3=0; i3<n; i3 += 1) 
  { float v4;
v4 = 0 ;
for(int i5=0; i5<m; i5 += 1) 
  { float v6;
v6 = 0 ;
for(int i7=0; i7<m; i7 += 1) 
  { v6 = ((dout[i0][(i2) + (i5)][(i3) + (i7)] * z[i1][i5][i7]) + v6) ;}
v4 = (v6 + v4) ;}
out[i0][i1][i2][i3] = v4 ;}}}}". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",nn_backward d_l_nn w_l_nn z_l_1_nn)) 0 = output.
Proof. unfold nn_backward,relu_grad. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<m; i0 += 1) 
  { float v1;
v1 = 0 ;
for(int i2=0; i2<n; i2 += 1) 
  { v1 = ((w_l[i2][i0] * d_l[i2]) + v1) ;}
if ((z_l_1[i0]) <= (0))
  { out[i0] = (v1 * 0) ;}
else
  { out[i0] = (v1 * 1) ;}}". auto.
Qed.

Goal exists output,
  CG_comm (A(vwt "out",nn_backward_w d_l_nn z_l_1_nn)) 0 = output.
Proof. unfold nn_backward_w. Tensor_unfold. Time Translated.
exists "for(int i0=0; i0<n; i0 += 1) 
  { for(int i1=0; i1<m; i1 += 1) 
  { out[i0][i1] = (d_l[i0] * z_l_1[i1]) ;}}". auto.
Qed. 

End backward.

End Examples.