/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsExt
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Decodes
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::recv`: Extended Hook-Stack (`*Ext`) V1 Ratchet `Ok` Tail

Proves `step_v1_ok_2664_to_ret_ext` (`+2664..+2916 -> +876 -> +1040`) for `spqr::recv` under
`SpqrRecvContractsExt`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec
open CryptoVerification.SpqrV1.Prost.MessageMerge
open CryptoVerification.SpqrV1.Top.StateSize
open CryptoVerification.SpqrV1.Top.DecodeState
open CryptoVerification.SpqrV1.Top.InitInner
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Top.MessageDeserialize
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.FromPb
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.CodeLayout

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

private theorem exists_words27_of_length_216_v1 (bs : List (BitVec 8)) (h : bs.length = 216) :
    ∃ d : Words27, ∀ out : BitVec 64, (out ↦ₛ bs) = words27At out d := by
  have hsplit (k : Nat) (l : List (BitVec 8)) : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 (bs := bs.take 8) (by simp [h])
  obtain ⟨w1, hw1⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 8).take 8) (by simp [h])
  obtain ⟨w2, hw2⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 16).take 8) (by simp [h])
  obtain ⟨w3, hw3⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 24).take 8) (by simp [h])
  obtain ⟨w4, hw4⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 32).take 8) (by simp [h])
  obtain ⟨w5, hw5⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 40).take 8) (by simp [h])
  obtain ⟨w6, hw6⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 48).take 8) (by simp [h])
  obtain ⟨w7, hw7⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 56).take 8) (by simp [h])
  obtain ⟨w8, hw8⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 64).take 8) (by simp [h])
  obtain ⟨w9, hw9⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 72).take 8) (by simp [h])
  obtain ⟨w10, hw10⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 80).take 8) (by simp [h])
  obtain ⟨w11, hw11⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 88).take 8) (by simp [h])
  obtain ⟨w12, hw12⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 96).take 8) (by simp [h])
  obtain ⟨w13, hw13⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 104).take 8) (by simp [h])
  obtain ⟨w14, hw14⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 112).take 8) (by simp [h])
  obtain ⟨w15, hw15⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 120).take 8) (by simp [h])
  obtain ⟨w16, hw16⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 128).take 8) (by simp [h])
  obtain ⟨w17, hw17⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 136).take 8) (by simp [h])
  obtain ⟨w18, hw18⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 144).take 8) (by simp [h])
  obtain ⟨w19, hw19⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 152).take 8) (by simp [h])
  obtain ⟨w20, hw20⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 160).take 8) (by simp [h])
  obtain ⟨w21, hw21⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 168).take 8) (by simp [h])
  obtain ⟨w22, hw22⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 176).take 8) (by simp [h])
  obtain ⟨w23, hw23⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 184).take 8) (by simp [h])
  obtain ⟨w24, hw24⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 192).take 8) (by simp [h])
  obtain ⟨w25, hw25⟩ := exists_unpack64_of_length_8 (bs := (bs.drop 200).take 8) (by simp [h])
  obtain ⟨w26, hw26⟩ := exists_unpack64_of_length_8 (bs := bs.drop 208) (by simp [h])
  refine ⟨⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
           w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26⟩, fun out => ?_⟩
  have hbs : bs =
      unpack64 w0 ++ (unpack64 w1 ++ (unpack64 w2 ++ (unpack64 w3 ++
      (unpack64 w4 ++ (unpack64 w5 ++ (unpack64 w6 ++ (unpack64 w7 ++
      (unpack64 w8 ++ (unpack64 w9 ++ (unpack64 w10 ++ (unpack64 w11 ++
      (unpack64 w12 ++ (unpack64 w13 ++ (unpack64 w14 ++ (unpack64 w15 ++
      (unpack64 w16 ++ (unpack64 w17 ++ (unpack64 w18 ++ (unpack64 w19 ++
      (unpack64 w20 ++ (unpack64 w21 ++ (unpack64 w22 ++ (unpack64 w23 ++
      (unpack64 w24 ++ (unpack64 w25 ++ unpack64 w26))))))))))))))))))))))))) := by
    rw [← hw0, ← hw1, ← hw2, ← hw3, ← hw4, ← hw5, ← hw6, ← hw7, ← hw8,
        ← hw9, ← hw10, ← hw11, ← hw12, ← hw13, ← hw14, ← hw15, ← hw16, ← hw17,
        ← hw18, ← hw19, ← hw20, ← hw21, ← hw22, ← hw23, ← hw24, ← hw25, ← hw26]
    conv_lhs =>
      rw [hsplit 8 bs]
      rw [hsplit 8 (bs.drop 8)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 16)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 24)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 32)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 40)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 48)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 56)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 64)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 72)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 80)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 88)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 96)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 104)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 112)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 120)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 128)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 136)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 144)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 152)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 160)]; simp only [List.drop_drop, Nat.reduceAdd]
      rw [hsplit 8 (bs.drop 168)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 176)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 184)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 192)]; simp only [List.drop_drop, Nat.reduceAdd]; rw [hsplit 8 (bs.drop 200)]; simp only [List.drop_drop, Nat.reduceAdd]
  conv_lhs => rw [hbs]
  dsimp only [words27At]
  simp only [pointsToBytes_append, unpack64_length, ← pointsTo64_eq_pointsToBytes,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, sepConj_assoc]

private theorem bytes224_expose_words28_move_2096_to_2928 (sp0 : BitVec 64) (bs : List (BitVec 8))
    (hlen : bs.length = 224) :
    ((sp0 - 2096#64) ↦ₛ bs) ⊢
      ∃∗ w0 : BitVec 64, ∃∗ d : Words27,
        ⌜((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ⊢ ((sp0 - 2928#64) ↦ₛ bs)⌝ ∗
        ((sp0 - 2096#64) ↦₆₄ w0) ∗ words27SubAt sp0 2096 d := by
  have hsplit : bs = bs.take 8 ++ bs.drop 8 := (List.take_append_drop 8 bs).symm
  have htake : (bs.take 8).length = 8 := by simp [hlen]
  have hdrop : (bs.drop 8).length = 216 := by simp [hlen]
  obtain ⟨w0, hw0⟩ := exists_unpack64_of_length_8 htake
  obtain ⟨d, hd⟩ := exists_words27_of_length_216_v1 (bs.drop 8) hdrop
  have h_at (m : Nat) (h0 : m < 2 ^ 64) (h216 : 216 < m) :
      ((sp0 - BitVec.ofNat 64 m) ↦ₛ bs) = ((sp0 - BitVec.ofNat 64 m) ↦₆₄ w0) ∗ words27SubAt sp0 m d := by
    conv_lhs => rw [hsplit]
    rw [pointsToBytes_append, htake, hw0, ← pointsTo64_eq_pointsToBytes,
        hd ((sp0 - BitVec.ofNat 64 m) + 8#64), words27At_sub_eq sp0 m d h0 h216]
  rw [h_at 2096 (by decide) (by decide)]
  refine Entails.sepExists_right w0 (Entails.sepExists_right d ?_)
  refine Entails.pure_right ?_ (Entails.refl _)
  rw [h_at 2928 (by decide) (by decide)]; exact Entails.refl _

private theorem optProtoInnerStateAt_expose_224 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (h_inner_eq : ∀ a opt, DecodeState.optProtoInnerStateAt H_inner A a opt = Drop.optProtoInnerStateAt A a opt)
    (sp0 : BitVec 64) (opt : Option V1State.InnerState) :
    Drop.optProtoInnerStateAt A (sp0 - 2096#64) opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ d : Words27, ∃∗ P_heap : SepProp,
        ⌜((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ∗ P_heap ⊢
          Drop.optProtoInnerStateAt A (sp0 - 2928#64) opt⌝ ∗
        ((sp0 - 2096#64) ↦₆₄ w0) ∗ words27SubAt sp0 2096 d ∗ P_heap := by
  have hto := (relocOptProtoInnerStateAt H_inner A opt).2.to_bytes (sp0 - 2096#64)
  rw [h_inner_eq] at hto
  refine Entails.trans hto ?_
  apply sepExists_left_entails; intro bs
  refine Entails.pure_left fun hbs => ?_
  refine Entails.trans (sepConj_mono_left (bytes224_expose_words28_move_2096_to_2928 sp0 bs hbs)) ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  apply sepExists_left_entails; intro w0; apply sepExists_left_entails; intro d
  refine Entails.pure_left fun hmove => ?_
  refine Entails.sepExists_right w0 (Entails.sepExists_right d
    (Entails.sepExists_right ((relocOptProtoInnerStateAt H_inner A opt).1 bs) ?_))
  refine Entails.pure_right ?_ (Entails.of_eq (by ac_rfl))
  have hof := (relocOptProtoInnerStateAt H_inner A opt).2.of_bytes (sp0 - 2928#64) bs hbs
  rw [h_inner_eq] at hof
  refine Entails.trans ?_ hof
  refine Entails.trans (Entails.of_eq (show
    ((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ∗ (relocOptProtoInnerStateAt H_inner A opt).1 bs =
    (((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d) ∗ (relocOptProtoInnerStateAt H_inner A opt).1 bs by ac_rfl)) ?_
  exact sepConj_mono_left hmove

private theorem protoPqRatchetState_entails_drop_v1 (A : RustAlloc) (sp0 : BitVec 64)
    (chPb : ChainPB) (pb1 : V1State) :
    ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
      memRegion (sp0 - 3048#64) 40 ∗
      ProtoRepr.chainPBAt A (sp0 - 3008#64) chPb ∗
      Drop.optProtoInnerStateAt A (sp0 - 2928#64) pb1.innerState ⊢
    Drop.protoPqRatchetStateAt A (sp0 - 3056#64)
      { versionNegotiation := none, chain := some chPb, inner := some (.v1 pb1) } := by
  dsimp only [Drop.protoPqRatchetStateAt, optVersionNegotiationPBAt, ProtoRepr.optChainPBAt, Drop.optProtoPqRatchetInnerAt]
  have h8 : (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 := bv_sub_add_lit sp0 3056 8
  have h48 : (sp0 - 3056#64) + 48#64 = sp0 - 3008#64 := bv_sub_add_lit sp0 3056 48
  have h128 : (sp0 - 3056#64) + 128#64 = sp0 - 2928#64 := bv_sub_add_lit sp0 3056 128
  rw [h8, h48, h128]
  exact Entails.of_eq (by ac_rfl)

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_sub_96_sub_136 (sp0 : BitVec 64) :
    (sp0 - 96#64) - 136#64 = sp0 - 232#64 := by bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem hsp_add_544 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem hsp_add_560 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 560#64 = s0.sp - 128#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

@[local simp, local arm64_norm, local wp_norm]
private theorem hsp_add_456 (s0 : State) :
    Kdf.HkdfToSliceProof.hsp s0 + 456#64 = s0.sp - 232#64 := by
  unfold Kdf.HkdfToSliceProof.hsp; bv_omega

private theorem memRegion_2856_split_v1_ok (sp0 : BitVec 64) :
    memRegion (sp0 - 3088#64) 2856 ⊢
      memRegion (sp0 - 3088#64) 32 ∗
      (∃∗ w790 : BitVec 64, (sp0 - 3056#64) ↦₆₄ w790) ∗
      memRegion (sp0 - 3048#64) 40 ∗
      memRegion (sp0 - 3008#64) 80 ∗
      memRegion (sp0 - 2928#64) 224 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) Drop.optProtoInnerStateSize ∗
      memRegion (sp0 - 1872#64) 1640 := by
  unfold Drop.optProtoInnerStateSize
  rw [show (2856 : Nat) = 32 + (8 + (40 + (80 + (224 + (608 + (224 + 1640)))))) by decide,
      memRegion_split (sp0 - 3088#64) 32 (8 + (40 + (80 + (224 + (608 + (224 + 1640)))))) (by decide),
      show (sp0 - 3088#64) + 32#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 8 (40 + (80 + (224 + (608 + (224 + 1640))))) (by decide),
      show (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 by bv_omega,
      memRegion_split (sp0 - 3048#64) 40 (80 + (224 + (608 + (224 + 1640)))) (by decide),
      show (sp0 - 3048#64) + 40#64 = sp0 - 3008#64 by bv_omega,
      memRegion_split (sp0 - 3008#64) 80 (224 + (608 + (224 + 1640))) (by decide),
      show (sp0 - 3008#64) + 80#64 = sp0 - 2928#64 by bv_omega,
      memRegion_split (sp0 - 2928#64) 224 (608 + (224 + 1640)) (by decide),
      show (sp0 - 2928#64) + 224#64 = sp0 - 2704#64 by bv_omega,
      memRegion_split (sp0 - 2704#64) 608 (224 + 1640) (by decide),
      show (sp0 - 2704#64) + 608#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 224 1640 (by decide),
      show (sp0 - 2096#64) + 224#64 = sp0 - 1872#64 by bv_omega,
      ProofLib.memRegion_eight (sp0 - 3056#64)]
  exact Entails.refl _

private theorem memRegion_224_split_24_200_v1 (sp0 : BitVec 64) :
    memRegion (sp0 - 2096#64) 224 ⊢
      memRegion (sp0 - 2096#64) 24 ∗ memRegion (sp0 - 2072#64) 200 := by
  rw [show (224 : Nat) = 24 + 200 by decide,
      memRegion_split (sp0 - 2096#64) 24 200 (by decide),
      show (sp0 - 2096#64) + 24#64 = sp0 - 2072#64 by bv_omega]
  exact Entails.refl _

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_writeVReg128_v1_ext (s : State) (i : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 i v).sp = s.sp := rfl

@[local simp, local arm64_norm, local wp_norm]
private theorem sp_setPState_v1_ext (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := rfl

/-- (`+2688 .. +2820`) under `SpqrRecvContractsExt`: copies `st1.into_pb.innerState` (`224`B)
    from `s0.sp - 2096#64` to `s0.sp - 2928#64`, stores `noneCap` (`-1`) at `s0.sp - 3056#64`,
    calls `<PqRatchetState>::encode_to_vec`, and continues via
    `step_v1_ok_epilogue_2820_to_ret`. -/
theorem step_v1_encodeToVec_2688_to_2820_ext {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (st1 : States spqrPolyApi (spqrAuthApi F))
    (chain2 : Chain) (rawKey : Bytes)
    (w0 w1 w790 cap_rk ptr_rk : BitVec 64)
    (hlen_enc : (PqRatchetState.encodeRaw
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) },
        if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2688#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      ProtoRepr.chainPBAt A (s0.sp - 3008#64) chain2.intoPb ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      Drop.optProtoInnerStateAt A (s0.sp - 2096#64) st1.into_pb.innerState ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      memRegion (s0.sp - 232#64) 88 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have henc_ok := spqrRecv_encodeToVec_ok_ext hC
  subst hP
  apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
    bv% (ls_rel% "spqr::recv" "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2688 132
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken
    (optProtoInnerStateAt_expose_224 H_inner A hC.h_inner_eq s0.sp st1.into_pb.innerState) (by sep_focus) ?_
  wp_pull_exists; rename_i w0_in d_in H_in
  wp_focus_pure; intro hpack_in
  refine SepWP.focus_weaken (memRegion_224_sub_entails_words28 s0.sp 2928) (by sep_focus) ?_
  wp_pull_exists; rename_i u0 uDst
  have hjoin_src :
      ((s0.sp - 2096#64) ↦₆₄ w0_in) ∗ words27SubAt s0.sp 2096 d_in ⊢
      memRegion (s0.sp - 2096#64) 24 ∗ memRegion (s0.sp - 2072#64) 200 :=
    Entails.trans (words27SubAt_to_memRegion_224 s0.sp 2096 w0_in d_in)
      (memRegion_224_split_24_200_v1 s0.sp)
  dsimp only [words27SubAt, Nat.reduceSub, BitVec.ofNat_eq_ofNat] at hpack_in hjoin_src ⊢
  simp only [sepConj_assoc]
  wp_steps 33
  refine SepWP.focus_weaken hpack_in (by sep_focus) ?_
  refine SepWP.focus_weaken hjoin_src (by sep_focus) ?_
  have hpack_pq :
      ((s0.sp - 3056#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        memRegion (s0.sp - 3048#64) 40 ∗
        ProtoRepr.chainPBAt A (s0.sp - 3008#64) chain2.intoPb ∗
        Drop.optProtoInnerStateAt A (s0.sp - 2928#64) st1.into_pb.innerState ⊢
      pqRatchetStatePBAt A (s0.sp - 3056#64)
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) } := by
    rw [← protoPqRatchetStateAt_eq_pqRatchetStatePBAt A (s0.sp - 3056#64)]
    exact protoPqRatchetState_entails_drop_v1 A s0.sp chain2.intoPb st1.into_pb
  refine SepWP.focus_weaken hpack_pq (by sep_focus) ?_
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide))) (by sep_focus) ?_
  refine SepWPpI.call_inImage henc_ok
    ⟨s0.sp - 2096#64, s0.sp - 3056#64,
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }⟩
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm, *]; exact hs0_align)
    (rfl : _ = entry + 2820#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed) (fun _ _ => rfl)
    (by
      dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], hlen_enc⟩
        (by simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
            sp_writeVReg128_v1_ext, sp_setPState_v1_ext, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, _, _, hxfp_c, hvregs_c⟩
  dsimp only [pqRatchetStateEncodeToVecSpecX, pqRatchetStateEncodeToVecSpecOf]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by rw [hspm]; simp only [arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = cap_rk := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = ptr_rk := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = BitVec.ofNat 64 rawKey.length := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = 0xFFFFFFFFFFFFFFFF#64 := by rw [hx25_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_setMem, State.sp_writeReg64,
    sp_writeVReg128_v1_ext, sp_setPState_v1_ext, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) (encodeToVecStackOf doReserveStackX) (by decide)).symm) (by sep_focus) ?_
  exact step_v1_ok_epilogue_2820_to_ret A F K ext hC.base_aligned hC.hdealloc
    st msg ret pre_pb
    { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }
    rawKey w0 w1 cap_rk ptr_rk hok s0 sm _ R hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
    hrunm hspm' htr_sm' hx19_sm hx21_sm hx22_sm hx23_sm hx24_sm hx25_sm hx26_sm hx29_sm (by ac_rfl)

/-- (`+2676 .. +2688`) under `SpqrRecvContractsExt`: calls `<Chain>::into_pb` on `chain2` at
    `s0.sp - 232#64`, writing `chain2.intoPb` to `s0.sp - 3008#64`, joins `memRegion (s0.sp -
    232#64) 88`, and continues via `step_v1_encodeToVec_2688_to_2820_ext`. -/
theorem step_v1_chainIntoPb_2676_to_2688_ext {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb : PqRatchetState) (st1 : States spqrPolyApi (spqrAuthApi F))
    (G : ChainProofs.ChainGhost) (chain2 : Chain) (rawKey : Bytes)
    (w0 w1 w790 cap_rk ptr_rk : BitVec 64)
    (hlen_enc : (PqRatchetState.encodeRaw
      { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) }).length < 2 ^ 63)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw
        { versionNegotiation := none, chain := some chain2.intoPb, inner := some (.v1 st1.into_pb) },
        if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2676#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = s0.sp - 3056#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      ((s0.sp - 3056#64) ↦₆₄ w790) ∗
      memRegion (s0.sp - 3048#64) 40 ∗
      memRegion (s0.sp - 3008#64) 80 ∗
      memRegion (s0.sp - 2928#64) 224 ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      Drop.optProtoInnerStateAt A (s0.sp - 2096#64) st1.into_pb.innerState ∗
      memRegion (s0.sp - 1872#64) 1640 ∗
      ChainProofs.chainAt A (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hchain_into := spqrRecv_chainIntoPb_ok_ext hC
  subst hP
  apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
    bv% (ls_rel% "spqr::recv" "<spqr::chain::Chain>::into_pb"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2676 12
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  wp_steps 3
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide))) (by sep_focus) ?_
  refine SepWPpI.call_inImage hchain_into ⟨s0.sp - 3008#64, s0.sp - 232#64, G, chain2⟩
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; exact sp_sub_4992_aligned s0 hs0_align)
    (rfl : _ = entry + 2688#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed) (fun _ _ => rfl)
    (by
      dsimp only [chainIntoPbSpecX]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩
        (by simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, _, hx26_c, _, _, hxfp_c, hvregs_c⟩
  dsimp only [chainIntoPbSpecX]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = cap_rk := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = ptr_rk := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = BitVec.ofNat 64 rawKey.length := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) chainIntoPbStackX (by decide)).symm) (by sep_focus) ?_
  exact step_v1_encodeToVec_2688_to_2820_ext hC st msg ret pre_pb st1 chain2 rawKey
    w0 w1 w790 cap_rk ptr_rk hlen_enc hok s0 sm _ R hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
    hrunm hspm' htr_sm' hx19_sm hx21_sm hx22_sm hx23_sm hx24_sm hx26_sm hx29_sm (by ac_rfl)

/-- Combined V1 ratchet `Ok` tail (`+2664 .. +2916 -> +876 -> +1040 -> ret`) under
    `SpqrRecvContractsExt`. -/
theorem step_v1_ok_2664_to_ret_ext {H_inner : V1InnerHeapPred} {img : Obj.Image}
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvContractsExt H_inner img A F K ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre : MsgPreamble) (pre_pb : PqRatchetState) (pb : V1State)
    (sckaMsg : Message spqrPolyApi)
    (st0 st1 : States spqrPolyApi (spqrAuthApi F))
    (key : Option EpochSecret) (chain0 chain1 chain2 : Chain)
    (G : ChainProofs.ChainGhost) (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (hst_len : st.bytes.length < 2 ^ 32)
    (hpre : msgPreamble msg.bytes = .ok pre)
    (hdec : Proto.spqrDecodeState st.bytes = .ok pre_pb)
    (hinner : pre_pb.inner = some (.v1 pb))
    (hmv : pre.version = 1#8)
    (hmin : ∀ vn, pre_pb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8))
    (hmsg : Message.deserialize spqrPolyApi pre.epoch pre.remaining = .ok sckaMsg)
    (hst0 : States.from_pb spqrPolyApi (spqrAuthApi F) pb = .ok st0)
    (hrecv : States.recv K st0 sckaMsg = .ok ⟨key, st1⟩)
    (hep_ne : (pre.epoch == 0#64) = false)
    (hcf : chainFrom (spqrHkdfWith F) pre_pb.chain pre_pb.versionNegotiation = .ok chain0)
    (hadd : (match key with
      | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch (spqrHkdfWith F) epochSecret)
      | none => .ok chain0) = .ok chain1)
    (hrk : chain1.recvKey (spqrHkdfWith F) (pre.epoch - 1#64) pre.index = .ok (chain2, rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName + 2664#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = s0.sp - 3056#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoAt img.base ∗ st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ A.pool ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      chunkedStatesAt A (s0.sp - 4016#64) st1 ∗
      memRegion (s0.sp - 3088#64) 2856 ∗
      ChainProofs.chainAt A (s0.sp - 232#64) G chain2 ∗
      memRegion (s0.sp - 144#64) 48 ∗
      RustHeap.vecU8Buf A cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpI img (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s P
      (spqrRecvPost A img.base (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hentry : spqrRecvEntry img.base ext =
      (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" := rfl
  have hstates_into := spqrRecv_statesIntoPb_ok_ext hC
  have hok := spqrV1Recv_v1_ratchet_ok hpre hdec hinner hmv hmin hmsg hst0 hrecv hep_ne hcf hadd hrk
  have hlen_enc := encodeRaw_len_lt_of_recv_ok hst_len hok
  subst hP
  apply SepWPpI.of_sepWP (mid := (tripleRatchetProgAtExt img.base ext).fnAddr spqrRecvName +
    bv% (ls_rel% "spqr::recv" "<spqr::v1::chunked::states::States>::into_pb"))
  dsimp only [tripleRatchetProgAtExt, spqrRecvName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  spqr_recv_fetches_range img.base (Rust.withPanics ext) 2664 12
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "spqr::recv" = entry
  examples_hide_fetches
  refine SepWP.focus_weaken (memRegion_2856_split_v1_ok s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w790
  refine SepWP.focus_weaken (spqrRecvRoAt_expose_statesIntoPb img.base) (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_into
  wp_focus_pure; intro hP_ro_into
  wp_steps 3
  apply ProofLib.SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesIntoPbStackX (by decide))) (by sep_focus) ?_
  refine SepWPpI.call_inImage hstates_into ⟨s0.sp - 2096#64, s0.sp - 4016#64, st1⟩
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; exact sp_sub_4992_aligned s0 hs0_align)
    (rfl : _ = entry + 2676#64)
    (by simp only [arm64_norm, htr]; exact List.prefix_refl s0.trace)
    (fun _ => onPanic_of_allocFailed) (fun _ _ => rfl)
    (by
      dsimp only [statesIntoPbSpecX, statesIntoPbSpec]
      have hmem_eq : memRegion (s0.sp - 2096#64) Drop.optProtoInnerStateSize =
          memRegion (s0.sp - 2096#64) DecodeState.optProtoInnerStateSize := rfl
      rw [hmem_eq]
      refine frame_pure_pre
        ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *], hC.base_aligned⟩
        (by simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]; sep_focus))
    ?_
  intro sm hpcm hrunm hspm hcsm
  rcases hcsm with ⟨hx19_c, _, hx21_c, hx22_c, hx23_c, hx24_c, hx25_c, hx26_c, _, _, hxfp_c, hvregs_c⟩
  dsimp only [statesIntoPbSpecX, statesIntoPbSpec]
  refine SepWPpI.focus_pure (by sep_focus) ?_; intro htr_sm
  have htr_sm' : TraceVRegs sm s0 := ⟨by rw [htr_sm]; simp only [arm64_norm, *], by rw [hvregs_c]; simp only [arm64_norm, *]⟩
  have hspm' : sm.sp = s0.sp - 4992#64 := by
    rw [hspm]; simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, arm64_norm, *]
  have hx19_sm : sm.readReg64 .x19 = ret := by rw [hx19_c]; simp only [arm64_norm, *]
  have hx21_sm : sm.readReg64 .x21 = cap_rk := by rw [hx21_c]; simp only [arm64_norm, *]
  have hx22_sm : sm.readReg64 .x22 = ptr_rk := by rw [hx22_c]; simp only [arm64_norm, *]
  have hx23_sm : sm.readReg64 .x23 = w0 := by rw [hx23_c]; simp only [arm64_norm, *]
  have hx24_sm : sm.readReg64 .x24 = BitVec.ofNat 64 rawKey.length := by rw [hx24_c]; simp only [arm64_norm, *]
  have hx25_sm : sm.readReg64 .x25 = s0.sp - 3056#64 := by rw [hx25_c]; simp only [arm64_norm, *]
  have hx26_sm : sm.readReg64 .x26 = 0#64 := by rw [hx26_c]; simp only [arm64_norm, *]
  have hx29_sm : sm.readReg64 .x29 = s0.sp - 96#64 := by
    change sm.readReg64 Reg.fp = s0.sp - 96#64; rw [hxfp_c]; simp only [arm64_norm, *]
  simp only [State.sp_setPC, State.sp_writeReg64, reduceCtorEq, ↓reduceIte, hsp]
  refine SepWPpI.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) statesIntoPbStackX (by decide)).symm) (by sep_focus) ?_
  refine SepWPpI.focus_weaken hP_ro_into (by sep_focus) ?_
  exact step_v1_chainIntoPb_2676_to_2688_ext hC st msg ret pre_pb st1 G chain2 rawKey
    w0 w1 w790 cap_rk ptr_rk hlen_enc hok s0 sm _ R hs0_align
    (by rw [spqrRecvEntry_eq, hentry]; exact hpcm)
    hrunm hspm' htr_sm' hx19_sm hx21_sm hx22_sm hx23_sm hx24_sm hx25_sm hx26_sm hx29_sm (by ac_rfl)

end CryptoVerification.SpqrV1.Top.Recv
