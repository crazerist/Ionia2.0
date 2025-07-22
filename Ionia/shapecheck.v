Require Import Reals String Nat List Bool Arith.
Require Export operation.
Import ListNotations.
Set Implicit Arguments.

(* ================================================================================================================ *)

(* *** The Experimental Cases In "A Static Analyzer for Detecting Tensor Shape Errors in Deep Neural Network." ***  *)

(* Fig(a) Error on the network structure

  Problem: The second fully connected operation [120] * [10 x 80] -> ERROR!

  (1)PyTorch error message (can only locate the entire layers, 
     unable to pinpoint a specific layer).
     RuntimeError: mat1 and mat2 shapes cannot be multiplied (3x120 and 80x10)

  (2)Coq's static type-checking mechanism 
    (directly locates the relu_map_2 layer for more precise identification).
     The term "relu_map_2" has type "exp (ary 120 num)" while it is expected to have type "exp (ary 80 num)".
*)

Fail Definition Figure3a_mismatch (input: Tensor1 (1*28*28))
  (f1_w: Tensor2 120 (28*28))(f1_b: Tensor1 120)
  (f2_w: Tensor2 10 80)(f2_b: Tensor1 10)
  :=
  tlet feature_map_1 := Linear1d f1_w f1_b input in
  tlet relu_map_2 := ReLU1d feature_map_1 in
  Linear1d f2_w f2_b relu_map_2.

(* Solution: Modify f2_w -> [10,120] *)
Definition Figure3a_corrected (input: Tensor1 (1*28*28))
  (f1_w: Tensor2 120 (28*28))(f1_b: Tensor1 120)
  (f2_w: Tensor2 10 120)(f2_b: Tensor1 10)
  :=
  tlet feature_map_1 := Linear1d f1_w f1_b input in
  tlet relu_map_2 := ReLU1d feature_map_1 in
  Linear1d f2_w f2_b relu_map_2.

(* EVALUATION -> Network -> mnist

  Problem: At NLL_Loss2d, the output has a batch size of [64, 10], 
  but the provided labels have a size of 63 (excluding the first element), 
  causing a type mismatch.

  (1)Error message provided by PyTorch after execution:
     ValueError(): Expected input batch_size (64) to match target batch_size (63).

  (2)Coq's static type-checking mechanism:
     The term "Truncl1d 1 output_label" has type "Tensor1 (64 - 1)" while 
     it is expected to have type "Tensor1 64". 
*)

Lemma MniCor_lem1 : 3 <= 28 + 2 * 0. Proof. lia. Qed.
Lemma MniCor_lem2 : 3 <= (28 + 2 * 0 - 3) / 1 + 1 + 2 * 0. Proof. cbv. lia. Qed.
Lemma MniCor_lem3 : 0 < 10. Proof. lia. Qed.

Fail Definition mnist_mismatch(input: Tensor4 64 1 28 28)
  (kernel_c1: Tensor4 32 1 3 3)(bias_c1: Tensor1 32)
  (kernel_c2: Tensor4 64 32 3 3) (bias_c2: Tensor1 64)
  (full_c1: Tensor2 128 (64*12*12))(full_b1: Tensor1 128)
  (full_c2: Tensor2 10 128)(full_b2: Tensor1 10)
  (output_label : list nat )
  :=
  (* Forward propagation prediction -> *)
  tlet feature_map_1 := Conv4d 0 1 bias_c1 kernel_c1 input in 
  tlet relu_map_1 := ReLU4d feature_map_1 in
  tlet feature_map_2 := Conv4d 0 1 bias_c2 kernel_c2 relu_map_1 in
  tlet relu_map_2 := ReLU4d feature_map_2 in
  tlet pool_map_1 := Maxpool4d 2 relu_map_2 in
  tlet drop_map_1 := Dropout4d pool_map_1 0.25%R in
  tlet flatten_map := Flatten4d drop_map_1 in
  tlet fc_map_1 := Linear2d full_c1 full_b1 flatten_map in
  tlet relu_map_3 := ReLU2d fc_map_1 in
  tlet drop_map_2 := Dropout2d relu_map_3 0.5%R in
  tlet fc_map_2 := Linear2d full_c2 full_b2 drop_map_2 in
  tlet output := Log_Softmax2d fc_map_2 in
  
  (* Loss function *)
  NLLLoss2d output (Truncl1d 1 output_label) .



(* Solution: Modify Truncl1d 1 output_label to output_label, 
   ensuring that the label size is consistent with the batch size. *)
Definition
 mnist_corrected(input: Tensor4 64 1 28 28)
  (kernel_c1: Tensor4 32 1 3 3)(bias_c1: Tensor1 32)
  (kernel_c2: Tensor4 64 32 3 3) (bias_c2: Tensor1 64)
  (full_c1: Tensor2 128 (64*12*12))(full_b1: Tensor1 128)
  (full_c2: Tensor2 10 128)(full_b2: Tensor1 10)
  (output_label : list (fin 10))
  :=
  (* Forward propagation prediction -> *)
  tlet feature_map_1 := Conv4d 0 1 bias_c1 kernel_c1 input MniCor_lem1 MniCor_lem1 in 
  tlet relu_map_1 := ReLU4d feature_map_1 in
  tlet feature_map_2 := Conv4d 0 1 bias_c2 kernel_c2 relu_map_1 MniCor_lem2 MniCor_lem2 in
  tlet relu_map_2 := ReLU4d feature_map_2 in
  tlet pool_map_1 := Maxpool4d 2 relu_map_2 nat_lem5 in
  tlet drop_map_1 := Dropout4d pool_map_1 0.25%R in
  tlet flatten_map := Flatten4d drop_map_1 in
  tlet fc_map_1 := Linear2d full_c1 full_b1 flatten_map in
  tlet relu_map_3 := ReLU2d fc_map_1 in
  tlet drop_map_2 := Dropout2d relu_map_3 0.5%R in
  tlet fc_map_2 := Linear2d full_c2 full_b2 drop_map_2 in
  tlet output := Log_Softmax2d fc_map_2 in
  
  (* Loss function *)
  NLLLoss2d output output_label MniCor_lem3.


(* EVALUATION -> Network -> vae

  VAE (Variational Autoencoder): An unsupervised learning approach 
  for modeling data distribution. It is a generative model used to 
  generate digits, faces, images, etc.

  Problem: At BCELoss2d, the output has a size of [128, 784], 
  but the provided labels have a size of [127, 784] (excluding the first row), 
  causing a type mismatch.

  (1)Error message provided by PyTorch after running: 
   ValueError: Using a target size (torch.Size([127, 784])) that is different to the input size (torch.Size([128, 784])) 
   is deprecated. Please ensure they have the same size.

  (2)Coq's static type-checking mechanism：
   The term "Truncl2d 1 flatten_map" has type "Tensor2 (128 - 1) (1 * 28 * 28)"
   while it is expected to have type "Tensor2 128 784".
 *)

Fail Definition VAE_mismatch(input: Tensor4 128 1 28 28)
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
  
  (* Reparameterization into a normal distribution *)
  tlet std := Exp2d (Mulc2d 0.5%R logvar) in          (* (128,20) *)
  tlet eps := Randn2d std in                          (* (128,20) *)
  (* Reparameterize by multiplying with the standard deviation of 
     a standard normal distribution and adding the mean, transforming 
     the latent vector into a normal distribution. *)
  tlet z := Add2d (Mul2d eps std) mu in               (* (128,20) *)
  
  (* decode *)
  tlet fc3_map := Linear2d fc3_w fc3_b z in           (* (128,400) *)
  tlet relu3_map := ReLU2d fc3_map in                 (* (128,400) *)
  tlet fc4_map := Linear2d fc4_w fc4_b relu3_map in   (* (128,784) *)
  tlet output := Sigmoid2d fc4_map in                 (* (128,784) *)
  
  (* Loss function *)
  tlet BCE := BCELoss2d output (Truncl2d 1 flatten_map) in
  (* 0.5 * sum(1 + log(sigma^2) - mu^2 - sigma^2) *)
  tlet KLD := mul (negate 0.5%R)(Sum2d (Sub2d (Sub2d (Addc2d 1%R logvar)
  (Mul2d mu mu)) (Exp2d logvar))) in
  Addc2d KLD BCE .

(* Solution: Modify (Truncl2d 1 flatten_map) to flatten_map, 
   ensuring that the label size is consistent with the input size. *)
Definition VAE_corrected(input: Tensor4 128 1 28 28)
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
  
  (* Reparameterization into a normal distribution *)
  tlet std := Exp2d (Scal2d 0.5%R logvar) in          (* (128,20) *)
  tlet eps := Randn2d _ _ in                          (* (128,20) *)
  tlet z := Add2d (Mul2d eps std) mu in               (* (128,20) *)
  
  (* decode *)
  tlet fc3_map := Linear2d fc3_w fc3_b z in           (* (128,400) *)
  tlet relu3_map := ReLU2d fc3_map in                 (* (128,400) *)
  tlet fc4_map := Linear2d fc4_w fc4_b relu3_map in   (* (128,784) *)
  tlet output := Sigmoid2d fc4_map in                 (* (128,784) *)
  
  (* Loss function *)
  tlet BCE := BCELoss2d output flatten_map in
  (* 0.5 * sum(1 + log(sigma^2) - mu^2 - sigma^2) *)
  tlet KLD := mul (negate 0.5%R)(Sum2d (Sub2d (Sub2d (Addc2d 1%R logvar)
  (Mul2d mu mu)) (Exp2d logvar))) in
  Addc2d KLD BCE .


(* EVALUATION -> Network -> dcgan

  Generative Adversarial Network (GAN): 
  Comprises two distinct models, namely the generator and the discriminator. 
  The generator's role is to produce fake images that resemble training images. 
  The discriminator's task is to distinguish whether an image is a real training 
  image or a fake image generated by the generator.

*)

(* Generator: The generator G is used to map a latent space vector z to the data space. 
   Since our data consists of images, mapping z to the data space implies creating 
   an RGB image of the same size as the training images (i.e., 3x64x64). *)
Lemma Gener_lem1 : 1 + 0 <= 4. Proof. lia. Qed.
Lemma Gener_lem2 : 0 < (1 - 1) * 1 + 4 - 2 * 0. Proof. lia. Qed.
Lemma Gener_lem3 : 1 + 1 <= 4. Proof. lia. Qed.
Lemma Gener_lem4 : forall {x}, 0 < x + 4 - 2 * 1. Proof. intros. lia. Qed.

Definition Generator{nz ngf nc:nat}(input: Tensor4 64 nz 1 1)
  (ct1_w: Tensor4 (ngf*8) nz 4 4) (ct1_b: Tensor1 (ngf*8)) (* G: Deconvolution parameters *)
  (ct2_w: Tensor4 (ngf*4) (ngf*8) 4 4) (ct2_b: Tensor1 (ngf*4))
  (ct3_w: Tensor4 (ngf*2) (ngf*4) 4 4) (ct3_b: Tensor1 (ngf*2))
  (ct4_w: Tensor4 ngf (ngf*2) 4 4) (ct4_b: Tensor1 ngf)
  (ct5_w: Tensor4 nc ngf 4 4) (ct5_b: Tensor1 nc)
  :=
  (* Generator *)
  tlet feature_map_1 := ConvTranspose4d 0 1 ct1_b ct1_w input nat_lem4 nat_lem4 Gener_lem1 Gener_lem1 in      (* (64,ngf*8,4,4) *)
  tlet norm_map_1 := BatchNorm4d  feature_map_1 one zero in             (* (64,ngf*8,4,4) *)
  tlet relu_map_1 := ReLU4d norm_map_1 in                             (* (64,ngf*8,4,4) *)
  tlet feature_map_2 := ConvTranspose4d 1 2 ct2_b ct2_w relu_map_1 Gener_lem2 Gener_lem2 Gener_lem3 Gener_lem3 in (* (64,ngf*4,8,8) *)
  tlet norm_map_2 := BatchNorm4d feature_map_2 one zero in             (* (64,ngf*4,8,8) *)
  tlet relu_map_2 := ReLU4d norm_map_2 in                             (* (64,ngf*4,8,8) *)
  tlet feature_map_3 := ConvTranspose4d 1 2 ct3_b ct3_w relu_map_2 Gener_lem4 Gener_lem4 Gener_lem3 Gener_lem3 in (* (64,ngf*2,16,16) *)
  tlet norm_map_3 := BatchNorm4d feature_map_3 one zero in             (* (64,ngf*2,16,16) *)
  tlet relu_map_3 := ReLU4d norm_map_3 in                             (* (64,ngf*2,16,16) *)
  tlet feature_map_4 := ConvTranspose4d 1 2 ct4_b ct4_w relu_map_3 Gener_lem4 Gener_lem4 Gener_lem3 Gener_lem3 in (* (64,ngf,32,32) *)
  tlet norm_map_4 := BatchNorm4d feature_map_4 one zero in                 (* (64,ngf,32,32) *)
  tlet relu_map_4 := ReLU4d norm_map_4 in                             (* (64,ngf,32,32) *)
  tlet feature_map_5 := ConvTranspose4d 1 2 ct5_b ct5_w relu_map_4 Gener_lem4 Gener_lem4 Gener_lem3 Gener_lem3 in (* (64,nc,64,64) *)
  Tanh4d feature_map_5                                                (* (64,nc,64,64) *)
  .

(*  Discriminator: The discriminator D is a binary classification network. 
    This network takes an image as input and outputs a scalar probability indicating 
    whether the image is real (as opposed to fake). *)
Lemma Discri_lem1 : 4 <= 64 + 2 * 1. Proof. lia. Qed.
Lemma Discir_lem2 : 4 <= (64 + 2 * 1 - 4) / 2 + 1 + 2 * 1. Proof. cbv; lia. Qed.
Lemma Discir_lem3 : 4 <= ((64 + 2 * 1 - 4) / 2 + 1 + 2 * 1 - 4) / 2 + 1 + 2 * 1. Proof. cbv; lia. Qed.
Lemma Discir_lem4 : 4 <= (((64 + 2 * 1 - 4) / 2 + 1 + 2 * 1 - 4) / 2 + 1 + 2 * 1 - 4) /
2 + 1 + 2 * 1. Proof. cbv; lia. Qed.
Lemma Discir_lem5 : 4 <= ((((64 + 2 * 1 - 4) / 2 + 1 + 2 * 1 - 4) / 2 + 1 + 2 * 1 -
4) / 2 + 1 + 2 * 1 - 4) / 2 + 1 + 2 * 0. Proof. cbv; lia. Qed.

Definition Discriminator{ndf nc:nat}(D_input: Tensor4 64 nc 64 64)
  (c1_w: Tensor4 ndf nc 4 4) (c1_b: Tensor1 ndf)           (* D: Convolutional parameters *)
  (c2_w: Tensor4 (ndf*2) ndf 4 4) (c2_b: Tensor1 (ndf*2))
  (c3_w: Tensor4 (ndf*4) (ndf*2) 4 4) (c3_b: Tensor1 (ndf*4))
  (c4_w: Tensor4 (ndf*8) (ndf*4) 4 4) (c4_b: Tensor1 (ndf*8) )
  (c5_w: Tensor4 1 (ndf*8) 4 4) (c5_b: Tensor1 1)
  :=
  (* Discriminator *)
  tlet feature_1 := Conv4d 1 2 c1_b c1_w D_input Discri_lem1 Discri_lem1 in                   (* (64,ndf,32,32) *)
  tlet relu_1 := LeakyReLU4d 0.2%R feature_1 in                       (* (64,ndf,32,32) *)
  tlet feature_2 := Conv4d 1 2 c2_b c2_w relu_1 Discir_lem2 Discir_lem2  in                    (* (64,ndf*2,16,16) *)
  tlet norm_2 := BatchNorm4d feature_2 one zero in                     (* (64,ndf*2,16,16) *)
  tlet relu_2 := LeakyReLU4d 0.2%R norm_2 in                          (* (64,ndf*2,16,16) *)
  tlet feature_3 := Conv4d 1 2 c3_b c3_w relu_2 Discir_lem3 Discir_lem3 in                    (* (64,ndf*4,8,8) *)
  tlet norm_3 := BatchNorm4d feature_3 one zero in                     (* (64,ndf*4,8,8) *)
  tlet relu_3 := LeakyReLU4d 0.2%R norm_3 in                          (* (64,ndf*4,8,8) *)
  tlet feature_4 := Conv4d 1 2 c4_b c4_w relu_3 Discir_lem4 Discir_lem4 in                    (* (64,ndf*8,4,4) *)
  tlet norm_4 := BatchNorm4d feature_4 one zero in                     (* (64,ndf*8,4,4) *)
  tlet relu_4 := LeakyReLU4d 0.2%R norm_4 in                          (* (64,ndf*8,4,4) *)
  tlet feature_5 := Conv4d 0 1 c5_b c5_w relu_4 Discir_lem5 Discir_lem5 in                    (* (64,1,1,1) *)
  Flatten4d (Sigmoid4d feature_5)                                     (* (64,1) *)
  .

(* Problem: At the last BCELoss2d, the model computes an output of size [64, 1], 
   while the provided labels have a size of [63, 1] (excluding the first row), 
   causing a type mismatch.

  (1)Error message provided by PyTorch after running:
   ValueError: Using a target size (torch.Size([63])) that is different to the 
   input size (torch.Size([64])) is deprecated. Please ensure they have the same size.

  (2)Coq's static type-checking mechanism:
   The term "Truncl2d 1 label" has type "Tensor2 (64 - 1) 1" while it is expected to have type
   "Tensor2 64
    (1 *
     ((((((64 - 4 + 2 * 1) / 2 + 1 - 4 + 2 * 1) / 2 + 1 - 4 + 2 * 1) / 2 + 1 - 4 + 2 * 1) / 2 + 1 -
       4 + 2 * 0) / 1 + 1) *
     ((((((64 - 4 + 2 * 1) / 2 + 1 - 4 + 2 * 1) / 2 + 1 - 4 + 2 * 1) / 2 + 1 - 4 + 2 * 1) / 2 + 1 -
       4 + 2 * 0) / 1 + 1))". *)
Fail Definition DCGAN_mismatch{nz ngf ndf nc:nat}
  (G_input: Tensor4 64 nz 1 1)(D_real_input: Tensor4 64 nc 64 64)
  (ct1_w: Tensor4 (ngf*8) nz 4 4) (ct1_b: Tensor1 (ngf*8)) (* G: Deconvolution parameters *)
  (ct2_w: Tensor4 (ngf*4) (ngf*8) 4 4) (ct2_b: Tensor1 (ngf*4))
  (ct3_w: Tensor4 (ngf*2) (ngf*4) 4 4) (ct3_b: Tensor1 (ngf*2))
  (ct4_w: Tensor4 ngf (ngf*2) 4 4) (ct4_b: Tensor1 ngf)
  (ct5_w: Tensor4 nc ngf 4 4) (ct5_b: Tensor1 nc)
  (c1_w: Tensor4 ndf nc 4 4) (c1_b: Tensor1 ndf)           (* D: Convolutional parameters *)
  (c2_w: Tensor4 (ndf*2) ndf 4 4) (c2_b: Tensor1 (ndf*2))
  (c3_w: Tensor4 (ndf*4) (ndf*2) 4 4) (c3_b: Tensor1 (ndf*4))
  (c4_w: Tensor4 (ndf*8) (ndf*4) 4 4) (c4_b: Tensor1 (ndf*8) )
  (c5_w: Tensor4 1 (ndf*8) 4 4) (c5_b: Tensor1 1)
  (real_label: Tensor2 64 1) (* Each one is a true data label *)
  :=

  (* The result computed from the real input *)
  tlet D_real_output := Discriminator D_real_input 
    c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b in
  (* Loss function *)
  tlet errD_real := BCELoss2d D_real_output real_label in (* Error of the real data labels *)
  
  (* Fake images generated by the generator *)
  tlet fake := Generator G_input 
    ct1_w ct1_b ct2_w ct2_b ct3_w ct3_b ct4_w ct4_b ct5_w ct5_b in
  tlet D_fake_output := Discriminator fake 
    c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b in
  tlet fake_label := Fill2d zero real_label in            (* Generating fake labels *)
  tlet errD_fake := BCELoss2d D_fake_output fake_label in
  
  tlet label := Fill2d one fake_label in
  BCELoss2d D_fake_output (Truncl2d 1 label) (* BUG INJECTION LOCATION *)
  .
  
(* Solution: Modify (Truncl2d 1 label) to label, ensuring that the label size 
   is consistent with the model's output size. *)
Definition DCGAN_corrected{nz ngf ndf nc:nat}
  (G_input: Tensor4 64 nz 1 1)(D_real_input: Tensor4 64 nc 64 64)
  (ct1_w: Tensor4 (ngf*8) nz 4 4) (ct1_b: Tensor1 (ngf*8)) (* G: Deconvolution parameters *)
  (ct2_w: Tensor4 (ngf*4) (ngf*8) 4 4) (ct2_b: Tensor1 (ngf*4))
  (ct3_w: Tensor4 (ngf*2) (ngf*4) 4 4) (ct3_b: Tensor1 (ngf*2))
  (ct4_w: Tensor4 ngf (ngf*2) 4 4) (ct4_b: Tensor1 ngf)
  (ct5_w: Tensor4 nc ngf 4 4) (ct5_b: Tensor1 nc)
  (c1_w: Tensor4 ndf nc 4 4) (c1_b: Tensor1 ndf)           (* D: Convolutional parameters *)
  (c2_w: Tensor4 (ndf*2) ndf 4 4) (c2_b: Tensor1 (ndf*2))
  (c3_w: Tensor4 (ndf*4) (ndf*2) 4 4) (c3_b: Tensor1 (ndf*4))
  (c4_w: Tensor4 (ndf*8) (ndf*4) 4 4) (c4_b: Tensor1 (ndf*8) )
  (c5_w: Tensor4 1 (ndf*8) 4 4) (c5_b: Tensor1 1)
  (real_label: Tensor2 64 1) (* Each one is a real data label *)
  :=

  (* The result computed from the real input *)
  tlet D_real_output := Discriminator D_real_input 
    c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b in
  (* Loss function *)
  tlet errD_real := BCELoss2d D_real_output real_label in (* Error of the real data labels *)
  
  (* Fake images generated by the generator *)
  tlet fake := Generator G_input 
    ct1_w ct1_b ct2_w ct2_b ct3_w ct3_b ct4_w ct4_b ct5_w ct5_b in
  tlet D_fake_output := Discriminator fake 
    c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b in
  tlet fake_label := Fill2d _ _ zero in            (* Generating fake labels *)
  tlet errD_fake := BCELoss2d D_fake_output fake_label in
  
  tlet label := Fill2d _ _ one in
  BCELoss2d D_fake_output label
  .


(* *****************************************StackOverflow questions********************************************** *)

(* Pytorch matrix multiplication error (shape mismatch)
https://stackoverflow.com/questions/76938435/pytorch-matrix-multiplication-error-shape-mismatch *)

(* The issue arises at flatten_map: 
   the subsequent fully connected layer expects one-dimensional input, 
   while the current flatten_map produces a two-dimensional output, 
   resulting in a mismatch of tensor shapes.
   The term "flatten_map" has type
   "exp
    (ary (64 * ((((110 - 3 + 2 * 0) / 1 + 1 - 3 + 2 * 0) / 1 + 1 - 3 + 2 * 0) / 1 + 1))
       (ary ((((80 - 3 + 2 * 0) / 1 + 1 - 3 + 2 * 0) / 1 + 1 - 3 + 2 * 0) / 1 + 1) num))"
   while it is expected to have type "exp (ary (64 * 104 * 74) num)".

*)

Fail Definition shape_mismatch(input: Tensor3 3 110 80)
  (c1_w: Tensor4 32 3 3 3)  (c1_b: Tensor1 32)
  (c2_w: Tensor4 64 32 3 3) (c2_b: Tensor1 64)
  (c3_w: Tensor4 64 64 3 3) (c3_b: Tensor1 64)
  (f1_w: Tensor2 2 (64 * 104 * 74))(f1_b: Tensor1 2)
  :=
  tlet feature_map_1 := Conv3d 0 1 c1_b c1_w input in 
  tlet relu_map_2 := ReLU3d feature_map_1 in
  tlet feature_map_3 := Conv3d 0 1 c2_b c2_w relu_map_2 in
  tlet relu_map_4 := ReLU3d feature_map_3 in
  tlet feature_map_5 := Conv3d 0 1 c3_b c3_w relu_map_4 in
  tlet relu_map_6 := ReLU3d feature_map_5 in 
  tlet flatten_map := join (relu_map_6) in
  Linear f1_w f1_b flatten_map.

(* Solution:

   1.Flattening operation should convert the three-dimensional tensor to 
    a one-dimensional tensor. Modify join(relu_map_6) to 
    join(join(relu_map_6)).

   2.modify the input to a four-dimensional tensor, 
    representing batch size along with the image dimensions.
*)
Lemma ShaMisCor_lem1 : 3 <= 110 + 2 * 0. Proof. lia. Qed.
Lemma ShaMisCor_lem2 : 3 <= 80 + 2 * 0. Proof. lia. Qed.
Lemma ShaMisCor_lem3 : 3 <= (110 + 2 * 0 - 3) / 1 + 1 + 2 * 0. Proof. cbv;lia. Qed.
Lemma ShaMisCor_lem4 : 3 <= (80 + 2 * 0 - 3) / 1 + 1 + 2 * 0. Proof. cbv;lia. Qed.
Lemma ShaMisCor_lem5 : 3 <= ((110 + 2 * 0 - 3) / 1 + 1 + 2 * 0 - 3) / 1 + 1 + 2 * 0. Proof. cbv; lia. Qed.
Lemma ShaMisCor_lem6 : 3 <= ((80 + 2 * 0 - 3) / 1 + 1 + 2 * 0 - 3) / 1 + 1 + 2 * 0. Proof. cbv; lia. Qed.

Definition shape_mismatch_corrected(input: Tensor3 3 110 80)
  (c1_w: Tensor4 32 3 3 3)  (c1_b: Tensor1 32)
  (c2_w: Tensor4 64 32 3 3) (c2_b: Tensor1 64)
  (c3_w: Tensor4 64 64 3 3) (c3_b: Tensor1 64)
  (f1_w: Tensor2 2 (64 * 104 * 74))(f1_b: Tensor1 2)
  :=
  tlet feature_map_1 := Conv3d 0 1 c1_b c1_w input ShaMisCor_lem1 ShaMisCor_lem2 in 
  tlet relu_map_2 := ReLU3d feature_map_1 in
  tlet feature_map_3 := Conv3d 0 1 c2_b c2_w relu_map_2 ShaMisCor_lem3 ShaMisCor_lem4 in
  tlet relu_map_4 := ReLU3d feature_map_3 in
  tlet feature_map_5 := Conv3d 0 1 c3_b c3_w relu_map_4 ShaMisCor_lem5 ShaMisCor_lem6 in
  tlet relu_map_6 := ReLU3d feature_map_5 in 
  tlet flatten_map := join (join (relu_map_6)) in
  Linear1d f1_w f1_b flatten_map.

 
(* UT1: https://stackoverflow.com/questions/66995380/target-size-and-input-size-not-matching-despite-minibatches-tells-otherwise *)

(* The target size does not match the input size:   
   This is reflected when the size of the dataset cannot be evenly divided by the batch_size. 
   Should the last incomplete batch be discarded? *)

(* ERROR: The last incomplete batch is (32, 784), 
   while the target size in the validation set is (batch, 784), causing a type mismatch.
   The term "label" has type "Tensor2 batch 784"
   while it is expected to have type "exp (ary 32 (ary 784 num))" *)
Fail Definition AEmodel{latent_dim batch:nat}
  (input: Tensor4 32 1 28 28)
  (l1_w: Tensor2 32 784)(l1_b: Tensor1 32)
  (l2_w: Tensor2 16 32)(l2_b: Tensor1 16)
  (l3_w: Tensor2 latent_dim 16)(l3_b: Tensor1 latent_dim)
  
  (l4_w: Tensor2 16 latent_dim)(l4_b: Tensor1 16)
  (l5_w: Tensor2 32 16)(l5_b: Tensor1 32)
  (l6_w: Tensor2 784 32)(l6_b: Tensor1 784)
  (label: Tensor2 batch 784)
  :=
  (* encode *)
  tlet input_reshape := Flatten4d input in
  tlet fc_enc1 := ReLU2d (Linear2d l1_w l1_b input_reshape) in
  tlet fc_enc2 := ReLU2d (Linear2d l2_w l2_b fc_enc1) in
  tlet z := ReLU2d (Linear2d l3_w l3_b fc_enc2) in   (* z:(32,latent_dim) *)

  (* decode *)
  tlet fc_dec1 := ReLU2d (Linear2d l4_w l4_b z) in
  tlet fc_dec2 := ReLU2d (Linear2d l5_w l5_b fc_dec1) in
  tlet xHat := Sigmoid2d (Linear2d l6_w l6_b fc_dec2) in   (* xHat:(32,784) *)

  BCELoss2d xHat label.

(* SOLUTION：Discard the last incomplete batch so that all input sizes are (batch, 784). *)
Definition AEmodel_corrected{latent_dim batch:nat}
  (input: Tensor4 batch 1 28 28)
  (l1_w: Tensor2 32 784)(l1_b: Tensor1 32)
  (l2_w: Tensor2 16 32)(l2_b: Tensor1 16)
  (l3_w: Tensor2 latent_dim 16)(l3_b: Tensor1 latent_dim)
  
  (l4_w: Tensor2 16 latent_dim)(l4_b: Tensor1 16)
  (l5_w: Tensor2 32 16)(l5_b: Tensor1 32)
  (l6_w: Tensor2 784 32)(l6_b: Tensor1 784)
  (label: Tensor2 batch 784)
  :=
  (* encode *)
  tlet input_reshape := Flatten4d input in
  tlet fc_enc1 := ReLU2d (Linear2d l1_w l1_b input_reshape) in
  tlet fc_enc2 := ReLU2d (Linear2d l2_w l2_b fc_enc1) in
  tlet z := ReLU2d (Linear2d l3_w l3_b fc_enc2) in   (* z:(32,latent_dim) *)

  (* decode *)
  tlet fc_dec1 := ReLU2d (Linear2d l4_w l4_b z) in
  tlet fc_dec2 := ReLU2d (Linear2d l5_w l5_b fc_dec1) in
  tlet xHat := Sigmoid2d (Linear2d l6_w l6_b fc_dec2) in   (* xHat:(32,784) *)

  BCELoss2d xHat label.


(* UT2: https://stackoverflow.com/questions/60121107/pytorch-nllloss-function-target-shape-mismatch *)

(* Batch size n, input node number d, and hidden node number h of LSTM.
 
  parameters：
  input：input[sequence_length][n][d]
  hidden state: H[num_layers][n][h]
  memory：C[num_layers][n][h]

  output：[num_layer][n][h]
*)


Definition LSTM{seq_length n:nat}(d h:nat)
  (input: Tensor3 seq_length n d)
  (H: Tensor3 1 n h)
  (C: Tensor3 1 n h) 
  :=
  (* input gate *)
  let W_xi := Default2d d h in
  let W_hi := Default2d h h in
  let b_i := Default1d h in
  (* forget gate *)
  let W_xf := Default2d d h in
  let W_hf := Default2d h h in
  let b_f := Default1d h in
  (* output gate *)
  let W_xo := Default2d d h in
  let W_ho := Default2d h h in
  let b_o := Default1d h in
  (* candidate memory cell *)
  let W_xc := Default2d d h in
  let W_hc := Default2d h h in
  let b_c := Default1d h in

  seq_make(fun i:fin seq_length => 
  tlet I := Sigmoid2d (mm_mul input[i] W_xi H[fin_0H nat_lem4] W_hi b_i) in
  tlet F := Sigmoid2d (mm_mul input[i] W_xf H[fin_0H nat_lem4] W_hf b_f) in
  tlet O := Sigmoid2d (mm_mul input[i] W_xo H[fin_0H nat_lem4] W_ho b_o) in
  tlet C_tilda := Sigmoid2d (mm_mul input[i] W_xc H[fin_0H nat_lem4] W_hc b_c) in
  tlet C_t := Add2d (Mul2d F C[fin_0H nat_lem4]) (Mul2d I C_tilda) in
  Mul2d O (Tanh2d C_t)
).


(* ERROR: The dimension of "out" is three-dimensional (256, 4, 1181), 
   and the dimension of "target" is two-dimensional (256, 4). 
   However, NLLLoss2d requires two-dimensional input, and 
   the target should be one-dimensional, resulting in a tensor shape mismatch error.
   The term "out" has type "exp (ary 256 (ary 4 (ary 1181 num)))"
   while it is expected to have type "exp (ary ?batch (ary ?m num))". *)
Fail Definition LSTM_mismatch
  (input: list (list nat))(target: list (list nat))
  (H: Tensor3 1 4 100) (C: Tensor3 1 4 100)
  (linear_w: Tensor2 1181 100) (linear_b: Tensor1 1181)
  :=
  tlet e := Default2d 1181 100 in
  tlet embeds := Embedding2d 256 4 input e in (* (256,4,100) *)
  tlet lstm_out := LSTM 100 embeds H C in      (* (256,4,100) *)
  tlet out_space := Linear3d lstm_out linear_w linear_b in (* (256,4,1181) *)
  tlet out := mkvSeq (fun i: fin 256 => Log_Softmax2d out_space[i]) in
  NLLLoss2d out target
  .

Fixpoint ReshapeList2d {n} (l: list (list (fin n)))
  : list (fin n) := 
  match l with
  | [] => []
  | h :: tl => h ++ ReshapeList2d tl
  end.

Lemma LSTMCor_lem1 : 0 < 1181. Proof. lia. Qed.
Lemma LSTMCor_lem2 : 0 < 256 * 4 * 1181 / (256 * 4). Proof. cbv;lia. Qed.

(* SOLUTION: Reshape the three-dimensional output tensor to two-dimensional and reshape the nested target list to one-dimensional. *)
Definition LSTM_corrected
  (input: list (list (fin 1181)))(target: list (list (fin (256 * 4 * 1181 / (256 * 4)))))
  (H: Tensor3 1 4 100) (C: Tensor3 1 4 100)
  (linear_w: Tensor2 1181 100) (linear_b: Tensor1 1181)
  :=
  tlet e := Default2d 1181 100 in
  tlet embeds := Embedding2d 256 4 input e LSTMCor_lem1 in (* (256,4,100) *)
  tlet lstm_out := LSTM 100 embeds H C in      (* (256,4,100) *)
  tlet out_space := Linear3d linear_w linear_b lstm_out in (* (256,4,1181) *)
  tlet out := seq_make (fun i: fin 256 => Log_Softmax2d out_space[i]) in
  NLLLoss2d (Reshape3d_2d (256*4) out) (ReshapeList2d target) LSTMCor_lem2
  .


(* https://stackoverflow.com/questions/43067338/tensor-multiplication-in-tensorflow *)

(* Tensor dimensions do not match.:

   Error: A has 2 dimensions while B has 3 dimensions. 
   The matrix_mul operation requires two 2-dimensional tensors to be multiplied, 
   resulting in a mismatch of tensor dimensions. The term "B" has type "Tensor3 2 2 3" 
   while it is expected to have type "exp (ary 2 (ary ?p num))". *)

Fail Definition tensor_mul_mismatch
  (A: Tensor2 5 2)
  (B: Tensor3 2 2 3)
  (C: Tensor2 3 3)
  :=
  tlet p := matrix_mul A B in
  matrix_mul p C.


(* SOLUTION: Utilize tensordot to specify performing the dot product operation 
   at a certain dimension within the tensor. *)
Definition tensor_mul_corrected
  (A: Tensor2 5 2)
  (B: Tensor3 2 2 3)
  (C: Tensor2 3 3)
  :=
  tlet p := tensordot2d_3d A B in
  tensordot3d_2d p C.


(* https://stackoverflow.com/questions/63049638/label-shape-mismatch-in-tensorflow *)

(* ERROR: Label Shape mismatch in Tensorflow.
   The term "label" has type "Tensor2 320 10" while it is expected to have type
   "exp (ary 32 (ary 10 num))". *)

Fail Definition label_mismatch
  (input: Tensor4 32 3 150 150)
  (c1_w: Tensor4 16 3 3 3)(c1_b: Tensor1 16)
  (c2_w: Tensor4 32 16 3 3)(c2_b: Tensor1 32)
  (c3_w: Tensor4 64 32 3 3)(c3_b: Tensor1 64)
  (l1_w: Tensor2 128 (64*17*17))(l1_b: Tensor1 128)
  (l2_w: Tensor2 10 128)(l2_b: Tensor1 10)
  (label: Tensor2 320 10)
  :=
  tlet cov1 := ReLU4d (Conv4d 0 1 c1_b c1_w input) in
  tlet pool1 := Maxpool4d 2 cov1 in
  tlet cov2 := ReLU4d (Conv4d 0 1 c2_b c2_w pool1) in
  tlet pool2 := Maxpool4d 2 cov2 in
  tlet cov3 := ReLU4d (Conv4d 0 1 c3_b c3_w pool2) in
  tlet pool3 := Maxpool4d 2 cov3 in 
  tlet flat := Flatten4d pool3 in
  tlet liner1 := Softmax2d (Linear2d l1_w l1_b flat) in
  tlet liner2 := Linear2d l2_w l2_b liner1 in
  SparseCateCross_Loss liner2 label.

Lemma LabCor_lem1 : 3 <= 150 + 2 * 0. Proof. cbv; lia. Qed.
Lemma LabCor_lem2 : 3 <= ((150 + 2 * 0 - 3) / 1 + 1) / 2 + 2 * 0. Proof. cbv; lia. Qed.
Lemma LabCor_lem3 : 3 <= ((((150 + 2 * 0 - 3) / 1 + 1) / 2 + 2 * 0 - 3) / 1 + 1) /
2 + 2 * 0. Proof. cbv; lia. Qed.

(* SOLUTION: label => (32, 10) *)
Definition label_corrected
  (input: Tensor4 32 3 150 150)
  (c1_w: Tensor4 16 3 3 3)(c1_b: Tensor1 16)
  (c2_w: Tensor4 32 16 3 3)(c2_b: Tensor1 32)
  (c3_w: Tensor4 64 32 3 3)(c3_b: Tensor1 64)
  (l1_w: Tensor2 128 (64*17*17))(l1_b: Tensor1 128)
  (l2_w: Tensor2 10 128)(l2_b: Tensor1 10)
  (label: Tensor2 32 10)
  :=
  tlet cov1 := ReLU4d (Conv4d 0 1 c1_b c1_w input LabCor_lem1 LabCor_lem1) in
  tlet pool1 := Maxpool4d 2 cov1 nat_lem5 in
  tlet cov2 := ReLU4d (Conv4d 0 1 c2_b c2_w pool1 LabCor_lem2 LabCor_lem2) in
  tlet pool2 := Maxpool4d 2 cov2 nat_lem5 in
  tlet cov3 := ReLU4d (Conv4d 0 1 c3_b c3_w pool2 LabCor_lem3 LabCor_lem3) in
  tlet pool3 := Maxpool4d 2 cov3 nat_lem5 in 
  tlet flat := Flatten4d pool3 in
  tlet liner1 := Softmax2d (Linear2d l1_w l1_b flat) in
  tlet liner2 := Linear2d l2_w l2_b liner1 in
  SparseCateCross_Loss liner2 label.











