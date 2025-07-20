Require Export operation.
Require Import Coq.Program.Basics.

Ltac modelnat_simpls :=
  repeat (try apply Nat.le_add_le_sub_r; repeat apply sub_le_trans; try (apply Nat.div_le_lower_bound;[lia|])).

Section LeNet5.

Variable input : Tensor3 1 32 32.
Variable kernel_c1: Tensor4 6 1 5 5.
Variable bias_c1: Tensor1 6.
Variable kernel_c2: Tensor4 16 6 5 5.
Variable bias_c2: Tensor1 16.
Variable full_c1: Tensor2 120 (16*5*5).
Variable full_b1: Tensor1 120.
Variable full_c2: Tensor2 84 120.
Variable full_b2: Tensor1 84.
Variable full_c3: Tensor2 10 84.
Variable full_b3: Tensor1 10.

Lemma LeN_lem1 : 5 <= 32 + 2 * 0. Proof. lia. Qed.
Lemma LeN_lem2 : 0 < 2. Proof. lia. Qed.
Lemma LeN_lem3 : 5 <= ((32 + 2 * 0 - 5) / 1 + 1) / 2 + 2 * 0. Proof. cbv. lia. Qed.

Definition LeNet_5 :=
  tlet feature_map_1 := Conv3d 0 1 bias_c1 kernel_c1 input LeN_lem1 LeN_lem1 in 
  tlet relu_map_1 := ReLU3d feature_map_1 in
  tlet pool_map_2 := Maxpool3d 2 relu_map_1 LeN_lem2 in
  tlet feature_map_3 := Conv3d 0 1 bias_c2 kernel_c2 pool_map_2 LeN_lem3 LeN_lem3 in
  tlet relu_map_3 := ReLU3d feature_map_3 in
  tlet pool_map_4 := Maxpool3d 2 relu_map_3 LeN_lem2  in
  tlet flatten_map5 := Flatten3d pool_map_4 in
  tlet full_map_5 := Linear1d full_c1 full_b1 flatten_map5 in
  tlet relu_map_5 := ReLU1d full_map_5 in
  tlet full_map_6 := Linear1d full_c2 full_b2 relu_map_5 in
  tlet relu_map_6 := ReLU1d full_map_6 in 
  tlet full_map_7 := Linear1d full_c3 full_b3 relu_map_6 in
  Softmax1d full_map_7.

End LeNet5.

Section Mnist.

Variable input: Tensor4 64 1 28 28.
Variable kernel_c1: Tensor4 32 1 3 3.
Variable bias_c1: Tensor1 32.
Variable kernel_c2: Tensor4 64 32 3 3.
Variable bias_c2: Tensor1 64.
Variable full_c1: Tensor2 128 (64*12*12).
Variable full_b1: Tensor1 128.
Variable full_c2: Tensor2 10 128.
Variable full_b2: Tensor1 10.

Lemma Mnist_lem1 : 3 <= 28 + 2 * 0. Proof. lia. Qed.
Lemma Mnist_lem2 : 3 <= (28 + 2 * 0 - 3) / 1 + 1 + 2 * 0. Proof. cbv; lia. Qed.
Lemma Mnist_lem3 : 0 < 2. Proof. lia. Qed.
Lemma Mnist_lem4 : 0 < 10. Proof. lia. Qed.

Definition mnist :=
  tlet feature_map_1 := Conv4d 0 1 bias_c1 kernel_c1 input Mnist_lem1 Mnist_lem1 in 
  tlet relu_map_1 := ReLU4d feature_map_1 in
  tlet feature_map_2 := Conv4d 0 1 bias_c2 kernel_c2 relu_map_1 Mnist_lem2 Mnist_lem2 in
  tlet relu_map_2 := ReLU4d feature_map_2 in
  tlet pool_map_1 := Maxpool4d 2 relu_map_2 Mnist_lem3 in
  tlet drop_map_1 := Dropout4d pool_map_1 0.25%R in
  tlet flatten_map := Flatten4d drop_map_1 in
  tlet fc_map_1 := Linear2d full_c1 full_b1 flatten_map in
  tlet relu_map_3 := ReLU2d fc_map_1 in
  tlet drop_map_2 := Dropout2d relu_map_3 0.5%R in
  tlet fc_map_2 := Linear2d full_c2 full_b2 drop_map_2 in
  Log_Softmax2d fc_map_2.

End Mnist.

Section AlexNet.

Variable batch channel m1 m2 : nat.
Variable input: Tensor4 batch channel m1 m2.
Variable c1_w: Tensor4 64 channel 11 11.
Variable c1_b: Tensor1 64.
Variable c2_w: Tensor4 192 64 5 5.
Variable c2_b: Tensor1 192.
Variable c3_w: Tensor4 384 192 3 3.
Variable c3_b: Tensor1 384.
Variable c4_w: Tensor4 256 384 3 3.
Variable c4_b: Tensor1 256.
Variable c5_w: Tensor4 256 256 3 3.
Variable c5_b: Tensor1 256.
Variable f1_w: Tensor2 4096 (256*6*6).
Variable f1_b: Tensor1 4096.
Variable f2_w: Tensor2 4096 4096.
Variable f2_b: Tensor1 4096.
Variable f3_w: Tensor2 1000 4096.
Variable f3_b: Tensor1 1000.

Hypothesis AlexN_hyp1 : 63 <= m1.
Hypothesis AlexN_hyp2 : 63 <= m2.

Lemma AlexN_lem1 : 11 <= m1 + 2 * 2. Proof. lia. Qed.
Lemma AlexN_lem2 : 11 <= m2 + 2 * 2. Proof. lia. Qed.
Lemma AlexN_lem3 : 3 <= (m1 + 2 * 2 - 11) / 4 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma AlexN_lem4 : 3 <= (m2 + 2 * 2 - 11) / 4 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma AlexN_lem5 : 3 <=(((m1 + 2 * 2 - 11) / 4 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 2 - 5) /
1 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma AlexN_lem6 : 3 <=(((m2 + 2 * 2 - 11) / 4 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 2 - 5) /
1 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma Alex_lem7 : 3 <= (((((((m1 + 2 * 2 - 11) / 4 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 2 -
5) / 1 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 0.
Proof. modelnat_simpls. lia. Qed.
Lemma Alex_lem8 : 3 <= (((((((m2 + 2 * 2 - 11) / 4 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 2 -
5) / 1 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 0.
Proof. modelnat_simpls. lia. Qed.

Definition AlexNet :=
  tlet conv1 := Conv4d 2 4 c1_b c1_w input AlexN_lem1 AlexN_lem2 in
  tlet conv1_relu := ReLU4d conv1 in
  tlet conv1_pool := Maxpool4d_pad 3 2 0 conv1_relu nat_lem6 AlexN_lem3 AlexN_lem4  in
  tlet conv2 := Conv4d 2 1 c2_b c2_w conv1_pool nat_lem3 nat_lem3 in
  tlet conv2_relu := ReLU4d conv2 in
  tlet conv2_pool := Maxpool4d_pad 3 2 0 conv2_relu nat_lem6 AlexN_lem5 AlexN_lem6  in
  tlet conv3 := Conv4d 1 1 c3_b c3_w conv2_pool nat_lem2 nat_lem2  in
  tlet conv3_relu := ReLU4d conv3 in
  tlet conv4 := Conv4d 1 1 c4_b c4_w conv3_relu nat_lem2 nat_lem2  in
  tlet conv4_relu := ReLU4d conv4 in
  tlet conv5 := Conv4d 1 1 c5_b c5_w conv4_relu nat_lem2 nat_lem2  in
  tlet conv5_relu := ReLU4d conv5 in
  tlet conv5_pool := Maxpool4d_pad 3 2 0 conv5_relu nat_lem6 Alex_lem7 Alex_lem8 in
  tlet avgpool := AdaptiveAvgPool4d 6 6 conv5_pool in
  tlet drop1 := Dropout2d (Flatten4d avgpool) 0.5%R in
  tlet fc1 := Linear2d f1_w f1_b drop1 in
  tlet fc1_relu := ReLU2d fc1 in
  tlet drop2 := Dropout2d fc1_relu 0.5%R in
  tlet fc2 := Linear2d f2_w f2_b drop2 in
  tlet fc2_relu := ReLU2d fc2 in
  Linear2d f3_w f3_b fc2_relu.

End AlexNet.

(* ResNet *)
Section BasicBlock.

Context {batch m1 m2 : nat}.

Variables in_channel out_channel stride:nat.
Variable downsample: bool.
Variables input: Tensor4 batch in_channel m1 m2.

Hypothesis BasB_hyp : downsample = false -> out_channel <= in_channel.
Hypothesis BasB_hyp1 : 0 < m1.
Hypothesis BasB_hyp2 : 0 < m2.

Lemma BasB_lem1 : 3 <= m1 + 2 * 1. Proof. lia. Qed.
Lemma BasB_lem2 : 3 <= m2 + 2 * 1. Proof. lia. Qed.
Lemma BasB_lem3 : 1 <= m1 + 2 * 0. Proof. lia. Qed.
Lemma BasB_lem4 : 1 <= m2 + 2 * 0. Proof. lia. Qed.


Definition BasicBlock :=
  let conv1_w := Default4d out_channel in_channel 3 3 in
  let conv1_b := Default1d out_channel in
  let conv2_w := Default4d out_channel out_channel 3 3 in
  let conv2_b := Default1d out_channel in 
  tlet conv1 := Conv4d 1 stride conv1_b conv1_w input BasB_lem1 BasB_lem2 in
  tlet bn1 := BatchNorm4d conv1 one zero in
  tlet relu1 := ReLU4d bn1 in
  tlet conv2 := convert_2 (Conv4d 1 1 conv2_b conv2_w relu1 nat_lem2 nat_lem2) nat_lem4' nat_lem4' in
  tlet bn2 := BatchNorm4d conv2 one zero in
  match downsample with
  | true => fun _ =>
      let convdown_w := Default4d out_channel in_channel 1 1 in
      let convdown_b := Default1d out_channel in
      tlet identity1 := Conv4d 0 stride convdown_b convdown_w input BasB_lem3 BasB_lem4 in
      BatchNorm4d identity1 one zero
  | false => fun eqd : false = downsample =>
      convert_in stride input (BasB_hyp (eq_sym eqd)) BasB_hyp1 BasB_hyp2
  end eq_refl.

End  BasicBlock.

(* Arguments BasicBlock {batch m1 m2} (in_channel out_channel stride downsample) _ _ _ _ : assert.
*)

Section BottleNeck.

Context {batch m1 m2: nat}.

Variables in_channel out_channel s:nat.
Variable downsample: bool.
Variable input: Tensor4 batch in_channel m1 m2.

Hypothesis BotN_hyp : downsample = false -> out_channel * 4 <= in_channel.
Hypothesis BotN_hyp1 : 0 < m1. 
Hypothesis BotN_hyp2 : 0 < m2.

Lemma BotN_lem1 : 1 <= m1 + 2 * 0. Proof. lia. Qed.
Lemma BotN_lem2 : 1 <= m2 + 2 * 0. Proof. lia. Qed.
Lemma BotN_lem3 : 3 <= m1 + 2 * 1. Proof. lia. Qed.
Lemma BotN_lem4 : 3 <= m2 + 2 * 1. Proof. lia. Qed.

Definition BottleNeck :=
  let conv1_w := Default4d out_channel in_channel 1 1 in
  let conv1_b := Default1d out_channel in
  let conv2_w := Default4d out_channel out_channel 3 3 in
  let conv2_b := Default1d out_channel in 
  let conv3_w := Default4d (out_channel*4) out_channel 1 1 in
  let conv3_b := Default1d (out_channel*4) in 
  tlet conv1 := convert_1 (Conv4d 0 1 conv1_b conv1_w input BotN_lem1 BotN_lem2) BotN_hyp1 BotN_hyp2 in
  tlet bn1 := BatchNorm4d conv1 one zero in
  tlet relu1 := ReLU4d bn1 in
  tlet conv2 := Conv4d 1 s conv2_b conv2_w relu1 BotN_lem3 BotN_lem4 in
  tlet bn2 := BatchNorm4d conv2 one zero in
  tlet relu2 := ReLU4d bn2 in
  tlet conv3 := convert_1 (Conv4d 0 1 conv3_b conv3_w relu2  nat_lem1 nat_lem1) nat_lem4' nat_lem4' in
  tlet bn3 := BatchNorm4d conv3 one zero in
  match downsample with
  | true => fun _ =>
  let convdown_w := Default4d (out_channel*4) in_channel 1 1 in
  let convdown_b := Default1d (out_channel*4) in
  tlet identity1 := Conv4d 0 s convdown_b convdown_w input BotN_lem1 BotN_lem2 in
  BatchNorm4d  identity1 one zero
  | false => fun eqd : false = downsample =>
      convert_in s input (BotN_hyp (eq_sym eqd)) BotN_hyp1 BotN_hyp2
  end eq_refl.

End BottleNeck.

Section MakeLayer.

Fixpoint make_layer {batch m1 m2 in_channel out_channel} (num_block :nat)
  (input : Tensor4 batch in_channel m1 m2) (E : out_channel <= in_channel)
  (E1 : 0 < m1) (E2 : 0 < m2) : Tensor4 batch out_channel m1 m2 :=
  match num_block with
  | O => convert_1 (BasicBlock in_channel out_channel 1 false input (const E) E1 E2) E1 E2
  | S p' => convert_1 (BasicBlock in_channel out_channel 1 false (make_layer p' input  (le_n in_channel) E1 E2) (const E) E1 E2 ) E1 E2
  end.

End MakeLayer.

Section ResNet34.

Context {batch channel m1 m2 : nat}.
Context (input: Tensor4 batch channel m1 m2).

Hypothesis ResN_hyp1 : 0 < m1.
Hypothesis ResN_hyp2 : 0 < m2.

Lemma ResN_lem : forall {P}, true = false -> P. Proof. intros. inv H. Qed.
Lemma ResN_lem1 : 7 <= m1 + 2 * 3. Proof. lia. Qed.
Lemma ResN_lem2 : 7 <= m2 + 2 * 3. Proof. lia. Qed.

Definition ResNet_34 :=
  let b1_cv1_w := Default4d 64 channel 7 7 in
  let b1_cv1_b := Default1d 64 in
  let b6_w := Default2d 10 (512*1*1) in
  let b6_b := Default1d 10 in
  tlet block1_conv := Conv4d 3 2 b1_cv1_b b1_cv1_w input ResN_lem1 ResN_lem2 in
  tlet block1_bn := BatchNorm4d block1_conv one zero in
  tlet block1_relu := ReLU4d block1_bn in
  tlet block1 := Maxpool4d_pad 3 2 1 block1_relu nat_lem6 nat_lem2 nat_lem2 in
  tlet block2 := make_layer 3 block1 (le_n _) nat_lem4' nat_lem4' in
  tlet block3_1 := BasicBlock 64 128 2 true block2 ResN_lem nat_lem4' nat_lem4' in
  tlet block3 := make_layer 3 block3_1 (le_n _) nat_lem4' nat_lem4' in
  tlet block4_1 := BasicBlock 128 256 2 true block3 ResN_lem nat_lem4' nat_lem4' in
  tlet block4 := make_layer 5 block4_1 (le_n _) nat_lem4' nat_lem4' in
  tlet block5_1 := BasicBlock 256 512 2 true block4 ResN_lem nat_lem4' nat_lem4' in
  tlet block5 := make_layer 2 block5_1 (le_n _) nat_lem4' nat_lem4' in
  tlet block6_pool := AdaptiveAvgPool4d 1 1 block5 in (* (4,512,1,1) *)
  tlet block6_flatt := Flatten4d block6_pool in       (* (4,512) *)
  Linear2d b6_w b6_b block6_flatt.

End ResNet34.

Section VGG.

Context {batch : nat}.

Variable input: Tensor4 batch 3 224 224.
Variable c1_w: Tensor4 64 3 3 3.
Variable c1_b: Tensor1 64.
Variable c2_w: Tensor4 64 64 3 3.
Variable c2_b: Tensor1 64.
Variable c3_w: Tensor4 128 64 3 3.
Variable c3_b: Tensor1 128.
Variable c4_w: Tensor4 128 128 3 3.
Variable c4_b: Tensor1 128.
Variable c5_w: Tensor4 256 128 3 3.
Variable c5_b: Tensor1 256.
Variable c6_w: Tensor4 256 256 3 3.
Variable c6_b: Tensor1 256.
Variable c7_w: Tensor4 256 256 3 3.
Variable c7_b: Tensor1 256.
Variable c8_w: Tensor4 512 256 3 3.
Variable c8_b: Tensor1 512.
Variable c9_w: Tensor4 512 512 3 3.
Variable c9_b: Tensor1 512.
Variable c10_w: Tensor4 512 512 3 3.
Variable c10_b: Tensor1 512.
Variable c11_w: Tensor4 512 512 3 3.
Variable c11_b: Tensor1 512.
Variable c12_w: Tensor4 512 512 3 3.
Variable c12_b: Tensor1 512.
Variable c13_w: Tensor4 512 512 3 3.
Variable c13_b: Tensor1 512.
Variable f1_w: Tensor2 4096 (512*7*7).
Variable f1_b: Tensor1 4096.
Variable f2_w: Tensor2 4096 4096.
Variable f2_b: Tensor1 4096.
Variable f3_w: Tensor2 1000 4096.
Variable f3_b: Tensor1 1000.


Lemma VGG_1 : 3 <= 224 + 2 * 1. Proof. cbv; lia. Qed.
Lemma VGG_2 : 3 <= (((224 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1) /
2 + 2 * 1. Proof. cbv; lia. Qed.
Lemma VGG_3 : 3 <= ((((((224 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1) / 2 +
2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1) / 2 + 2 * 1. Proof. cbv; lia. Qed.
Lemma VGG_4 : 3 <= ((((((((((224 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1) /
2 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1) / 2 +
2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) /
1 + 1) / 2 + 2 * 1. Proof. cbv; lia. Qed.
Lemma VGG_5 : 3 <= ((((((((((((((224 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 +
1) / 2 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 +
1) / 2 + 2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 +
1 + 2 * 1 - 3) / 1 + 1) / 2 + 2 * 1 - 3) / 1 + 1 +
2 * 1 - 3) / 1 + 1 + 2 * 1 - 3) / 1 + 1) / 2 + 2 * 1. Proof. cbv; lia. Qed.


Definition VGG_16:= 
  tlet conv1 := Conv4d 1 1 c1_b c1_w input VGG_1 VGG_1 in
  tlet conv1_relu := ReLU4d conv1 in
  tlet conv2 := Conv4d 1 1 c2_b c2_w conv1_relu nat_lem2 nat_lem2 in
  tlet conv2_relu := ReLU4d conv2 in
  tlet pool1 := Maxpool4d 2 conv2_relu nat_lem5  in     (* (batch,64,112,112) *)
  tlet conv3 := Conv4d 1 1 c3_b c3_w pool1 VGG_2 VGG_2 in
  tlet conv3_relu := ReLU4d conv3 in
  tlet conv4 := Conv4d 1 1 c4_b c4_w conv3_relu nat_lem2 nat_lem2 in
  tlet conv4_relu := ReLU4d conv4 in
  tlet pool2 := Maxpool4d 2 conv4_relu nat_lem5 in     (* (batch,128,56,56) *)
  tlet conv5 := Conv4d 1 1 c5_b c5_w pool2 VGG_3 VGG_3 in
  tlet conv5_relu := ReLU4d conv5 in
  tlet conv6 := Conv4d 1 1 c6_b c6_w conv5_relu nat_lem2 nat_lem2 in
  tlet conv6_relu := ReLU4d conv6 in
  tlet conv7 := Conv4d 1 1 c7_b c7_w conv6_relu nat_lem2 nat_lem2 in
  tlet conv7_relu := ReLU4d conv7 in
  tlet pool3 := Maxpool4d 2 conv7_relu nat_lem5 in     (* (batch,256,28,28) *)
  tlet conv8 := Conv4d 1 1 c8_b c8_w pool3 VGG_4 VGG_4 in
  tlet conv8_relu := ReLU4d conv8 in
  tlet conv9 := Conv4d 1 1 c9_b c9_w conv8_relu nat_lem2 nat_lem2 in
  tlet conv9_relu := ReLU4d conv9 in
  tlet conv10 := Conv4d 1 1 c10_b c10_w conv9_relu nat_lem2 nat_lem2 in
  tlet conv10_relu := ReLU4d conv10 in
  tlet pool4 := Maxpool4d 2 conv10_relu nat_lem5 in    (* (batch,512,14,14) *)
  tlet conv11 := Conv4d 1 1 c11_b c11_w pool4 VGG_5 VGG_5 in
  tlet conv11_relu := ReLU4d conv11 in
  tlet conv12 := Conv4d 1 1 c12_b c12_w conv11_relu nat_lem2 nat_lem2 in
  tlet conv12_relu := ReLU4d conv12 in
  tlet conv13 := Conv4d 1 1 c13_b c13_w conv12_relu nat_lem2 nat_lem2 in
  tlet conv13_relu := ReLU4d conv13 in
  tlet pool5 := Maxpool4d 2 conv13_relu nat_lem5 in     (* (batch,512,7,7) *)
  tlet fc1 := Linear2d f1_w f1_b (Flatten4d pool5) in (* (batch,4096) *)
  tlet fc1_relu := ReLU2d fc1 in 
  tlet fc2 := Linear2d f2_w f2_b fc1_relu in          (* (batch,4096) *)
  tlet fc2_relu := ReLU2d fc2 in
  tlet fc3 := Linear2d f3_w f3_b fc2_relu in          (* (batch,1000) *)
  Softmax2d fc3.

End VGG.

Section Inception.

Context {batch channel m1 m2 : nat}.

Variables c1_ch1 c2_ch1 c2_ch3 c3_ch1 c3_ch5 c4_ch1: nat.
Variable input: Tensor4 batch channel m1 m2.

Hypothesis Inc_hyp1 : 0 < m1.
Hypothesis Inc_hyp2 : 0 < m2.

Lemma Inc_lem1 : 1 <= m1 + 2 * 0. Proof. lia. Qed.
Lemma Inc_lem2 : 1 <= m2 + 2 * 0. Proof. lia. Qed.
Lemma Inc_lem3 : 3 <= m1 + 2 * 1. Proof. lia. Qed.
Lemma Inc_lem4 : 3 <= m2 + 2 * 1. Proof. lia. Qed.
Lemma Inc_lem5 : 5 <= m1 + 2 * 2. Proof. lia. Qed.
Lemma Inc_lem6 : 5 <= m2 + 2 * 2. Proof. lia. Qed.

Definition Inception :=
  let c1_w := Default4d c1_ch1 channel 1 1 in
  let c1_b := Default1d c1_ch1 in
  let c2_w1 := Default4d c2_ch1 channel 1 1 in
  let c2_b1 := Default1d c2_ch1 in 
  let c2_w2 := Default4d c2_ch3 c2_ch1 3 3 in
  let c2_b2 := Default1d c2_ch3 in
  let c3_w1 := Default4d c3_ch1 channel 1 1 in
  let c3_b1 := Default1d c3_ch1 in 
  let c3_w2 := Default4d c3_ch5 c3_ch1 5 5 in
  let c3_b2 := Default1d c3_ch5 in
  let c4_w := Default4d c4_ch1 channel 1 1 in
  let c4_b := Default1d c4_ch1 in
  tlet p1_1 := convert_1 (Conv4d 0 1 c1_b c1_w input Inc_lem1 Inc_lem2) Inc_hyp1 Inc_hyp2 in
  tlet p1_2 := ReLU4d p1_1 in
  tlet p2_1 := convert_1 (Conv4d 0 1 c2_b1 c2_w1 input Inc_lem1 Inc_lem2) Inc_hyp1 Inc_hyp2 in
  tlet p2_2 := ReLU4d p2_1 in
  tlet p2_3 := convert_2 (Conv4d 1 1 c2_b2 c2_w2 p2_2 Inc_lem3 Inc_lem4) Inc_hyp1 Inc_hyp2 in
  tlet p2_4 := ReLU4d p2_3 in
  tlet p3_1 := convert_1 (Conv4d 0 1 c3_b1 c3_w1 input Inc_lem1 Inc_lem2) Inc_hyp1 Inc_hyp2 in
  tlet p3_2 := ReLU4d p3_1 in
  tlet p3_3 := convert_3 (Conv4d 2 1 c3_b2 c3_w2 p3_2 Inc_lem5 Inc_lem6) Inc_hyp1 Inc_hyp2 in
  tlet p3_4 := ReLU4d p3_3 in
  tlet p4_1 := convert_2 (Maxpool4d_pad 3 1 1 input _0lt3 Inc_lem3 Inc_lem4) Inc_hyp1 Inc_hyp2 in
  tlet p4_2 := convert_1 (Conv4d 0 1 c4_b c4_w p4_1 Inc_lem1 Inc_lem2) Inc_hyp1 Inc_hyp2 in
  tlet p4_3 := ReLU4d p4_2 in
  Concat4d (Concat4d (Concat4d p1_2 p2_4) p3_4) p4_3.

End Inception.

Section GoogleNet.

Context {batch channel m1 m2 : nat}.

Hypothesis Goo_hyp1 : 45 <= m1.
Hypothesis Goo_hyp2 : 45 <= m2.

Variable input: Tensor4 batch channel m1 m2.

Lemma Goo_lem1 : 7 <= m1 + 2 * 3. Proof. lia. Qed.
Lemma Goo_lem2 : 7 <= m2 + 2 * 3. Proof. lia. Qed.
Lemma Goo_lem3 : 3 <= (m1 + 2 * 3 - 7) / 2 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma Goo_lem4 : 3 <= (m2 + 2 * 3 - 7) / 2 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma Goo_lem5 : 3 <= ((((m1 + 2 * 3 - 7) / 2 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0 -
1) / 1 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma Goo_lem6 : 3 <= ((((m2 + 2 * 3 - 7) / 2 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0 -
1) / 1 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma Goo_lem7 : 3 <= (((((m1 + 2 * 3 - 7) / 2 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0 - 1) /
1 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma Goo_lem8 : 3 <= (((((m2 + 2 * 3 - 7) / 2 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0 - 1) /
1 + 1 + 2 * 1 - 3) / 1 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0. Proof. modelnat_simpls. lia. Qed.
Lemma Goo_lem9 : 0 <(((((((m1 + 2 * 3 - 7) / 2 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0 - 1) / 1 + 1 +
2 * 1 - 3) / 1 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0 - 3) / 2 + 1) / 2. Proof. modelnat_simpls. lia. Qed.
Lemma Goo_lem10 : 0 <(((((((m2 + 2 * 3 - 7) / 2 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0 - 1) / 1 + 1 +
2 * 1 - 3) / 1 + 1 + 2 * 0 - 3) / 2 + 1 + 2 * 0 - 3) / 2 + 1) / 2. Proof. modelnat_simpls. lia. Qed. 

Definition GoogleNet :=
  let b1_w := Default4d 64 channel 7 7 in
  let b1_b := Default1d 64 in
  let b2_w1 := Default4d 64 64 1 1 in
  let b2_b1 := Default1d 64 in
  let b2_w2 := Default4d 192 64 3 3 in
  let b2_b2 := Default1d 192 in
  let f_w := Default2d 1000 1024 in
  let f_b := Default1d 1000 in
  tlet b1_conv := Conv4d 3 2 b1_b b1_w input Goo_lem1 Goo_lem2 in
  tlet b1_relu := ReLU4d b1_conv in
  tlet b1_pool := Maxpool4d_pad 3 2 0 b1_relu _0lt3 Goo_lem3 Goo_lem4  in (* batch,64,56,56 *)
  tlet b2_conv1 := Conv4d 0 1 b2_b1 b2_w1 b1_pool nat_lem1 nat_lem1 in
  tlet b2_relu1 := ReLU4d b2_conv1 in
  tlet b2_conv2 := Conv4d 1 1 b2_b2 b2_w2 b2_relu1 nat_lem2 nat_lem2 in
  tlet b2_relu2 := ReLU4d b2_conv2 in
  tlet b2_pool := Maxpool4d_pad 3 2 0 b2_relu2 _0lt3 Goo_lem5 Goo_lem6   in (* batch,192,28,28 *)
  tlet b3_1 := Inception 64 96 128 16 32 32 b2_pool nat_lem4' nat_lem4' in (* batch,256,28,28 *)
  tlet b3_2 := Inception 128 128 192 32 96 64 b3_1 nat_lem4' nat_lem4' in  (* batch,480,28,28 *)
  tlet b3_pool := Maxpool4d_pad 3 2 0 b3_2 nat_lem6 Goo_lem7 Goo_lem8  in          (* batch,480,14,14 *)
  tlet b4_1 := Inception 192 96 208 16 48 64 b3_pool nat_lem4' nat_lem4' in     (* batch,512,14,14 *)
  tlet b4_2 := Inception 160 112 224 24 64 64 b3_1 nat_lem4' nat_lem4'  in       (* batch,512,14,14 *)
  tlet b4_3 := Inception 128 128 256 24 64 64 b3_pool nat_lem4' nat_lem4' in    (* batch,512,14,14 *)
  tlet b4_4 := Inception 112 144 288 32 64 64 b3_1 nat_lem4' nat_lem4' in       (* batch,528,14,14 *)
  tlet b4_5 := Inception 256 160 320 32 128 128 b3_pool nat_lem4' nat_lem4' in  (* batch,832,14,14 *)
  tlet b4_pool := Maxpool4d 2 b4_5 nat_lem5 in                       (* batch,832,7,7 *)
  tlet b5_1 := Inception 256 160 320 32 128 128 b4_pool Goo_lem9 Goo_lem10 in  (* batch,832,7,7 *)
  tlet b5_2 := Inception 384 192 384 48 128 128 b3_1 nat_lem4' nat_lem4'  in     (* batch,1024,7,7 *)
  tlet b5_3 := AdaptiveAvgPool4d 1 1 b5_2 in                (* batch,1024,1,1 *)
  tlet b6_1 := Flatten4d b5_3  in                           (* batch,1024*1*1 *)
  tlet b6_2 := Dropout2d b6_1 0.2%R in                      (* batch,1024*1*1 *)
  Linear2d f_w f_b b6_2.                                   (* batch,1000 *)

End GoogleNet.

(* DenseNet *)

Section DenseLayer.

Context {batch channel m1 m2 : nat}.

Variables bn_size growth_rate : nat.
Variables drop_rate : exp num.
Variables input : Tensor4 batch channel m1 m2.

Hypothesis denl_hyp1 : 0 < m1.
Hypothesis denl_hyp2 : 0 < m2.

Lemma denl_lem1 : 1 <= m1 + 2 * 0. Proof. lia. Qed.
Lemma denl_lem2 : 1 <= m2 + 2 * 0. Proof. lia. Qed.
Lemma denl_lem3 : 3 <= m1 + 2 * 1. Proof. lia. Qed.
Lemma denl_lem4 : 3 <= m2 + 2 * 1. Proof. lia. Qed.

Definition DenseLayer :=
  let c1_w := Default4d (bn_size * growth_rate) channel 1 1 in
  let c1_b := Default1d (bn_size * growth_rate) in
  let c2_w := Default4d growth_rate (bn_size * growth_rate) 3 3 in
  let c2_b := Default1d growth_rate in
  tlet norm1 := BatchNorm4d input  one zero in
  tlet relu1 := ReLU4d norm1 in
  tlet conv1 := convert_1 (Conv4d 0 1 c1_b c1_w relu1 denl_lem1 denl_lem2) denl_hyp1 denl_hyp2 in
  tlet norm2 := BatchNorm4d conv1  one zero in
  tlet relu2 := ReLU4d norm2 in
  tlet conv2 := convert_2 (Conv4d 1 1 c2_b c2_w relu2 denl_lem3 denl_lem4) denl_hyp1 denl_hyp2 in
  tlet new_features := Dropout4d conv2 drop_rate in
  Concat4d input new_features.

End DenseLayer.

Section DenseBlock.

Context {batch channel m1 m2 : nat}.

Fixpoint DenseBlock {batch channel m1 m2} (bn_size growth_rate num_layers :nat)
  (drop_rate: exp num) (input : Tensor4 batch channel m1 m2) (denb_hyp1 : 0 < m1)
  (denb_hyp2 : 0 < m2) : Tensor4 batch (channel + growth_rate * num_layers) m1 m2 :=
  match num_layers with
  | O => convert_4 input eq_refl
  | S p' => convert_5 (DenseLayer bn_size growth_rate drop_rate 
    (DenseBlock bn_size growth_rate p' drop_rate input denb_hyp1 denb_hyp2) denb_hyp1 denb_hyp2)
  end.

End DenseBlock.

Section Transition.

Context {batch channel m1 m2 : nat}.

Variables out_channel : nat.
Variables input: Tensor4 batch channel m1 m2.

Hypothesis trans_hyp1 : 0 < m1.
Hypothesis trans_hyp2 : 0 < m2.

Lemma trans_lem1 : 1 <= m1 + 2 * 0. Proof. lia. Qed.
Lemma trans_lem2 : 1 <= m2 + 2 * 0. Proof. lia. Qed.

(* Transition *)
Definition Transition :=
  let c1_w := Default4d out_channel channel 1 1 in
  let c1_b := Default1d out_channel in
  tlet norm := BatchNorm4d input one zero in
  tlet relu := ReLU4d norm in
  tlet conv := Conv4d 0 1 c1_b c1_w relu trans_lem1 trans_lem2 in
  Avgpool4d 2 conv.

End Transition.

Section DenseNet_121.

Context {batch channel m1 m2 : nat}.

Variables bn_size growth_rate num_init_features compression_rate : nat.
Variables drop_rate: exp num.
Variables input : Tensor4 batch channel m1 m2.

Hypothesis denn_hyp1 : 29 <= m1.
Hypothesis denn_hyp2 : 29 <= m2.

Lemma denn_lem1 : 7 <= m1 + 2 * 3. Proof. lia. Qed.
Lemma denn_lem2 : 7 <= m2 + 2 * 3. Proof. lia. Qed.
Lemma denn_lem3 : 0 < ((((m1 + 2 * 3 - 7) / 2 + 1 + 2 * 1 - 3) / 2 + 1 + 2 * 0 - 1) / 1 + 1) / 2.
Proof. apply nat_lem7. modelnat_simpls. lia. Qed.
Lemma denn_lem4 : 0 < ((((m2 + 2 * 3 - 7) / 2 + 1 + 2 * 1 - 3) / 2 + 1 + 2 * 0 - 1) / 1 + 1) / 2.
Proof. apply nat_lem7. modelnat_simpls. lia. Qed.
Lemma denn_lem5 : 0 < ((((((m1 + 2 * 3 - 7) / 2 + 1 + 2 * 1 - 3) / 2 + 1 + 2 * 0 -
1) / 1 + 1) / 2 + 2 * 0 - 1) / 1 + 1) / 2. Proof. apply nat_lem7. modelnat_simpls. lia. Qed.
Lemma denn_lem6 : 0 < ((((((m2 + 2 * 3 - 7) / 2 + 1 + 2 * 1 - 3) / 2 + 1 + 2 * 0 -
1) / 1 + 1) / 2 + 2 * 0 - 1) / 1 + 1) / 2. Proof. apply nat_lem7. modelnat_simpls. lia. Qed.
Lemma denn_lem7 : 0 < ((((((((m1 + 2 * 3 - 7) / 2 + 1 + 2 * 1 - 3) / 2 + 1 + 2 * 0 -
1) / 1 + 1) / 2 + 2 * 0 - 1) / 1 + 1) / 2 + 2 * 0 - 1) / 1 + 1) / 2.
Proof. apply nat_lem7. modelnat_simpls. lia. Qed.
Lemma denn_lem8 : 0 < ((((((((m2 + 2 * 3 - 7) / 2 + 1 + 2 * 1 - 3) / 2 + 1 + 2 * 0 -
1) / 1 + 1) / 2 + 2 * 0 - 1) / 1 + 1) / 2 + 2 * 0 - 1) / 1 + 1) / 2.
Proof. apply nat_lem7. modelnat_simpls. lia. Qed.

Definition DenseNet_121 :=
  let c1_w := Default4d 64 channel 7 7 in
  let c1_b := Default1d 64 in
  let f1_w := Default2d 1000 1024 in
  let f1_b := Default1d 1000 in
  tlet conv0 := Conv4d 3 2 c1_b c1_w input denn_lem1 denn_lem2 in
  tlet norm0 := BatchNorm4d conv0 one zero in
  tlet relu0 := ReLU4d norm0 in
  tlet pool0 := Maxpool4d_pad 3 2 1 relu0 nat_lem6 nat_lem2 nat_lem2 in
  tlet db1 := DenseBlock 4 32 6 0%R pool0 nat_lem4' nat_lem4' in
  tlet trans1 := Transition 128 db1 nat_lem4' nat_lem4' in
  tlet db2 := DenseBlock 4 32 12 0%R trans1 denn_lem3 denn_lem4 in
  tlet trans2 := Transition 256 db2 denn_lem3 denn_lem4 in
  tlet db3 := DenseBlock 4 32 24 0%R trans2 denn_lem5 denn_lem6 in
  tlet trans3 := Transition 512 db3 denn_lem5 denn_lem6 in
  tlet db4 := DenseBlock 4 32 16 0%R trans3 denn_lem7 denn_lem8 in
  tlet norm5 := BatchNorm4d db4  one zero in
  tlet relu5 := ReLU4d norm5 in
  tlet pool5 := AdaptiveAvgPool4d 1 1 relu5 in
  tlet flatt := Flatten4d pool5 in
  Linear2d f1_w f1_b flatt.

End DenseNet_121.

Section VAE.


(* vae *)
Definition VAE(input: Tensor4 128 1 28 28)
  (fc1_w: Tensor2 400 784) (fc1_b: Tensor1 400)
  (fc21_w: Tensor2 20 400) (fc21_b: Tensor1 20)
  (fc22_w: Tensor2 20 400) (fc22_b: Tensor1 20)
  (fc3_w: Tensor2 400 20) (fc3_b: Tensor1 400)
  (fc4_w: Tensor2 784 400) (fc4_b: Tensor1 784)
  :=
  (* encode *)
  tlet flatten_map := Flatten4d input in              (* (128,784) *)
  tlet fc1_map := Linear2d fc1_w fc1_b flatten_map in (* (128,400) *)
  tlet relu1_map := ReLU2d fc1_map in                 (* (128,400) *)
  tlet mu := Linear2d fc21_w fc21_b relu1_map in      (* mean: (128,20) *)
  tlet logvar := Linear2d fc22_w fc22_b relu1_map in  (* var:  (128,20) *)
  
  tlet std := Exp2d (Scal2d 0.5%R logvar) in          (* (128,20) *)
  tlet eps := Randn2d 128 20 in                          (* (128,20) *)
  tlet z := Add2d (Mul2d eps std) mu in               (* (128,20) *)
  
  (* decode *)
  tlet fc3_map := Linear2d fc3_w fc3_b z in           (* (128,400) *)
  tlet relu3_map := ReLU2d fc3_map in                 (* (128,400) *)
  tlet fc4_map := Linear2d fc4_w fc4_b relu3_map in   (* (128,784) *)
  tlet output := Sigmoid2d fc4_map in                 (* (128,784) *)

  tlet BCE := BCELoss2d output flatten_map in
  (* 0.5 * sum(1 + log(sigma^2) - mu^2 - sigma^2) *)
  tlet KLD := mul (negate 0.5%R)(Sum2d (Sub2d (Sub2d 
  (Addc2d 1%R logvar) (Mul2d mu mu)) (Exp2d logvar))) in
  Addc2d KLD BCE .

End VAE.

Section GCGAN.

Context {nz ngf nc:nat}.

Variable input: Tensor4 64 nz 1 1.
Variable ct1_w: Tensor4 (ngf*8) nz 4 4.
Variable ct1_b: Tensor1 (ngf*8).
Variable ct2_w: Tensor4 (ngf*4) (ngf*8) 4 4.
Variable ct2_b: Tensor1 (ngf*4).
Variable ct3_w: Tensor4 (ngf*2) (ngf*4) 4 4.
Variable ct3_b: Tensor1 (ngf*2).
Variable ct4_w: Tensor4 ngf (ngf*2) 4 4.
Variable ct4_b: Tensor1 ngf.
Variable ct5_w: Tensor4 nc ngf 4 4.
Variable ct5_b: Tensor1 nc.

Lemma GCCAN_lem1 : 1 + 0 <= 4. Proof. lia. Qed.
Lemma GCCAN_lem2 : 0 < (1 - 1) * 1 + 4 - 2 * 0. Proof. lia. Qed.
Lemma GCCAN_lem3 : 1 + 1 <= 4. Proof. lia. Qed.
Lemma GCCAN_lem4 : 0 < ((1 - 1) * 1 + 4 - 2 * 0 - 1) * 2 + 4 - 2 * 1.
Proof. lia. Qed.
Lemma GCCAN_lem5 : 0 < (((1 - 1) * 1 + 4 - 2 * 0 - 1) * 2 + 4 - 2 * 1 - 1) * 2 +
4 - 2 * 1. Proof. lia. Qed.
Lemma GCCAN_lem6 : 0 <
((((1 - 1) * 1 + 4 - 2 * 0 - 1) * 2 + 4 - 2 * 1 - 1) * 2 +
4 - 2 * 1 - 1) * 2 + 4 - 2 * 1. Proof. lia. Qed.
(* DCGAN *)

Definition Generator :=
  tlet feature_map_1 := ConvTranspose4d 0 1 ct1_b ct1_w input nat_lem4 nat_lem4 GCCAN_lem1 GCCAN_lem1 in      (* (64,ngf*8,4,4) *)
  tlet norm_map_1 := BatchNorm4d feature_map_1 one zero in             (* (64,ngf*8,4,4) *)
  tlet relu_map_1 := ReLU4d norm_map_1 in                             (* (64,ngf*8,4,4) *)
  tlet feature_map_2 := ConvTranspose4d 1 2 ct2_b ct2_w relu_map_1 GCCAN_lem2 GCCAN_lem2 GCCAN_lem3 GCCAN_lem3 in (* (64,ngf*4,8,8) *)
  tlet norm_map_2 := BatchNorm4d feature_map_2  one zero in             (* (64,ngf*4,8,8) *)
  tlet relu_map_2 := ReLU4d norm_map_2 in                             (* (64,ngf*4,8,8) *)
  tlet feature_map_3 := ConvTranspose4d 1 2 ct3_b ct3_w relu_map_2 GCCAN_lem4 GCCAN_lem4 GCCAN_lem3 GCCAN_lem3 in (* (64,ngf*2,16,16) *)
  tlet norm_map_3 := BatchNorm4d feature_map_3 one zero in             (* (64,ngf*2,16,16) *)
  tlet relu_map_3 := ReLU4d norm_map_3 in                             (* (64,ngf*2,16,16) *)
  tlet feature_map_4 := ConvTranspose4d 1 2 ct4_b ct4_w relu_map_3 GCCAN_lem5 GCCAN_lem5 GCCAN_lem3 GCCAN_lem3 in (* (64,ngf,32,32) *)
  tlet norm_map_4 := BatchNorm4d feature_map_4 one zero in                 (* (64,ngf,32,32) *)
  tlet relu_map_4 := ReLU4d norm_map_4 in                             (* (64,ngf,32,32) *)
  tlet feature_map_5 := ConvTranspose4d 1 2 ct5_b ct5_w relu_map_4 GCCAN_lem6 GCCAN_lem6 GCCAN_lem3 GCCAN_lem3 in (* (64,nc,64,64) *)
  Tanh4d feature_map_5.                                                (* (64,nc,64,64) *)

End GCGAN.

Section Discriminator.

Context {ndf nc:nat}.

Variable D_input: Tensor4 64 nc 64 64.
Variable c1_w: Tensor4 ndf nc 4 4.
Variable c1_b: Tensor1 ndf.
Variable c2_w: Tensor4 (ndf*2) ndf 4 4.
Variable c2_b: Tensor1 (ndf*2).
Variable c3_w: Tensor4 (ndf*4) (ndf*2) 4 4.
Variable c3_b: Tensor1 (ndf*4).
Variable c4_w: Tensor4 (ndf*8) (ndf*4) 4 4.
Variable c4_b: Tensor1 (ndf*8).
Variable c5_w: Tensor4 1 (ndf*8) 4 4.
Variable c5_b: Tensor1 1.

Lemma Dis_lem1 : 4 <= 64 + 2 * 1. Proof. lia. Qed.
Lemma Dis_lem2 : 4 <= (64 + 2 * 1 - 4) / 2 + 1 + 2 * 1. Proof. cbv. lia. Qed.
Lemma Dis_lem3 : 4 <= ((64 + 2 * 1 - 4) / 2 + 1 + 2 * 1 - 4) / 2 + 1 + 2 * 1.
Proof. cbv; lia. Qed.
Lemma Dis_lem4 : 4 <=
(((64 + 2 * 1 - 4) / 2 + 1 + 2 * 1 - 4) / 2 + 1 + 2 * 1 - 4) /
2 + 1 + 2 * 1 . Proof. cbv; lia. Qed.
Lemma Dis_lem5 : 4 <=
((((64 + 2 * 1 - 4) / 2 + 1 + 2 * 1 - 4) / 2 + 1 + 2 * 1 -
4) / 2 + 1 + 2 * 1 - 4) / 2 + 1 + 2 * 0.
Proof. cbv; lia. Qed.

Definition Discriminator :=
  tlet feature_1 := Conv4d 1 2 c1_b c1_w D_input Dis_lem1 Dis_lem1 in                   (* (64,ndf,32,32) *)
  tlet relu_1 := LeakyReLU4d 0.2%R feature_1 in                       (* (64,ndf,32,32) *)
  tlet feature_2 := Conv4d 1 2 c2_b c2_w relu_1 Dis_lem2 Dis_lem2 in                    (* (64,ndf*2,16,16) *)
  tlet norm_2 := BatchNorm4d feature_2 one zero in                     (* (64,ndf*2,16,16) *)
  tlet relu_2 := LeakyReLU4d 0.2%R norm_2 in                          (* (64,ndf*2,16,16) *)
  tlet feature_3 := Conv4d 1 2 c3_b c3_w relu_2 Dis_lem3 Dis_lem3 in                    (* (64,ndf*4,8,8) *)
  tlet norm_3 := BatchNorm4d feature_3 one zero in                     (* (64,ndf*4,8,8) *)
  tlet relu_3 := LeakyReLU4d 0.2%R norm_3 in                          (* (64,ndf*4,8,8) *)
  tlet feature_4 := Conv4d 1 2 c4_b c4_w relu_3 Dis_lem4 Dis_lem4 in                    (* (64,ndf*8,4,4) *)
  tlet norm_4 := BatchNorm4d feature_4 one zero in                     (* (64,ndf*8,4,4) *)
  tlet relu_4 := LeakyReLU4d 0.2%R norm_4 in                          (* (64,ndf*8,4,4) *)
  tlet feature_5 := Conv4d 0 1 c5_b c5_w relu_4 Dis_lem5 Dis_lem5 in                    (* (64,1,1,1) *)
  Flatten4d (Sigmoid4d feature_5).                         (* (64,1) *)

End Discriminator.

Section DCGAN.

Context {nz ngf ndf nc:nat}.

Variable G_input: Tensor4 64 nz 1 1.
Variable D_real_input: Tensor4 64 nc 64 64.
Variable ct1_w: Tensor4 (ngf*8) nz 4 4.
Variable ct1_b: Tensor1 (ngf*8).
Variable ct2_w: Tensor4 (ngf*4) (ngf*8) 4 4.
Variable ct2_b: Tensor1 (ngf*4).
Variable ct3_w: Tensor4 (ngf*2) (ngf*4) 4 4.
Variable ct3_b: Tensor1 (ngf*2).
Variable ct4_w: Tensor4 ngf (ngf*2) 4 4.
Variable ct4_b: Tensor1 ngf.
Variable ct5_w: Tensor4 nc ngf 4 4.
Variable ct5_b: Tensor1 nc.
Variable c1_w: Tensor4 ndf nc 4 4.
Variable c1_b: Tensor1 ndf.
Variable c2_w: Tensor4 (ndf*2) ndf 4 4.
Variable c2_b: Tensor1 (ndf*2).
Variable c3_w: Tensor4 (ndf*4) (ndf*2) 4 4.
Variable c3_b: Tensor1 (ndf*4).
Variable c4_w: Tensor4 (ndf*8) (ndf*4) 4 4.
Variable c4_b: Tensor1 (ndf*8).
Variable c5_w: Tensor4 1 (ndf*8) 4 4.
Variable c5_b: Tensor1 1.
Variable real_label: Tensor2 64 1.

Definition DCGAN :=
  tlet D_real_output := Discriminator D_real_input 
    c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b in
  tlet errD_real := BCELoss2d D_real_output real_label in 
  tlet fake := Generator G_input 
    ct1_w ct1_b ct2_w ct2_b ct3_w ct3_b ct4_w ct4_b ct5_w ct5_b in
  tlet D_fake_output := Discriminator fake 
    c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b in
  tlet fake_label := Fill2d _ _ zero  in            
  tlet errD_fake := BCELoss2d D_fake_output fake_label in
  tlet label := Fill2d _ _ one in
  BCELoss2d D_fake_output label.

End DCGAN.


(* RNN -> LSTM

  The LSTM solves the long-term dependency problem of RNNs, 
  and its main components consist of a forget gate, an input gate, 
  an output gate, and a memory cell.
 
  # input gate parameters
  W_xi[d][h]: the weight matrix connecting the input to the input gate of the cell;
  W_hi[h][h]: the weight matrix connecting the output of 
              the previous cell to the input gate of the current cell unit;
  b_i[h]
  # forget gate parameters
  W_xf[d][h]: the weight matrix connecting the input to the forget gate of the cell;
  W_hf[h][h]: the weight matrix connecting the output of the previous cell to 
              the forget gate of the current cell;
  b_f[h]
  # output gate parameters
  W_xo[d][h]: the weight matrix connecting the input to the output gate of the cell;
  W_ho[h][h]: the weight matrix connecting the previous cell to the current cell 
              at the present time step;
  b_o[h]
  # candidate memory cell parameters
  W_xc[d][h]: the weight matrix used to generate new memories;
  W_hc[h][h]: the weight matrix for generating new memories;
  b_c[h]
  
  parameters：
  input：input[sequence_length][n][d]
  hidden state: H[num_layers][n][h]
  memory：C[num_layers][n][h]

  output：[num_layer][n][h] *)

Section LSTM.

Context {seq_length n:nat}.

Variables d h:nat.
Variable input : Tensor3 seq_length n d.
Variables H C : Tensor3 1 n h.

Definition LSTM :=
  let W_xi := Default2d d h in
  let W_hi := Default2d h h in
  let b_i := Default1d h in
  let W_xf := Default2d d h in
  let W_hf := Default2d h h in
  let b_f := Default1d h in
  let W_xo := Default2d d h in
  let W_ho := Default2d h h in
  let b_o := Default1d h in
  let W_xc := Default2d d h in
  let W_hc := Default2d h h in
  let b_c := Default1d h in
  seq_make (fun i:fin seq_length => 
  tlet I := Sigmoid2d (mm_mul input[i] W_xi H[fin_0H nat_lem4] W_hi b_i) in
  tlet F := Sigmoid2d (mm_mul input[i] W_xf H[fin_0H nat_lem4] W_hf b_f) in
  tlet O := Sigmoid2d (mm_mul input[i] W_xo H[fin_0H nat_lem4] W_ho b_o) in
  tlet C_tilda := Sigmoid2d (mm_mul input[i] W_xc H[fin_0H nat_lem4] W_hc b_c) in
  tlet C_t := Add2d (Mul2d F C[fin_0H nat_lem4]) (Mul2d I C_tilda) in
  Mul2d O (Tanh2d C_t)
).

End LSTM.






