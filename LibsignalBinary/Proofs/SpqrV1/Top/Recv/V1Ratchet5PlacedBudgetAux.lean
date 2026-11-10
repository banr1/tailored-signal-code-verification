/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5
public import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5Placed
import LibsignalBinary.Proofs.Placed.ElfLsRetAddr
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part3Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part5Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part6Placed
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.Pure
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet1
import ProofLib.SepLogic.WPp
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep

/-!
# Budget-Threaded Relocatable V1 `Ok` Result & Drop Epilogue (`+2820 -> ret`)

Stack relocation, `recvResultExactKeyAt` folding, and budget-threaded drop/return steppers
(`+2820..+2916 -> +876 -> +1040`) for `spqr::recv` (Block `329`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5PlacedBudgetAux

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
  (LibsignalCodeLoaded LibsignalPlacement lsmpl lsρ sepWP_seq_lscl withMemEq)
open CryptoVerification.LibsignalSpqrV1
  (Bytes ChainPB MlKem PqRatchetState SpqrRecvModel V1State optKeyBytesAt
   recvResultExactKeyAt spqrV1Recv)
open CryptoVerification.LibsignalTripleRatchet (VecArg)
open CryptoVerification.LibsignalTripleRatchetRepr (noneCap)
open CryptoVerification.RustHeap
  (RustAlloc allocHookStack vecHeader vecU8 vecU8At_eq_header_sep_buf vecU8Buf)
open CryptoVerification.SpqrV1.Drop
  (cap_ne_zero_lt_one_false cap_ne_zero_slt_one_false chunkedStatesSize dropStack96
   optProtoInnerStateAt optProtoInnerStateJumpTablePlacedAt optProtoInnerStateSize
   optProtoPqRatchetInnerAt protoPqRatchetStateAt protoPqRatchetStateSize vecCapPtrDealloc)
open CryptoVerification.SpqrV1.Prost.EncodeToVec
  (extractLsb_hi_append64 extractLsb_lo_append64 pqRatchetStatePBAt)
open CryptoVerification.SpqrV1.Prost.MessageMerge
  (v1StateJumpTablesPlacedAt v1StateMergeJumpTablePlacedExpanded)
open CryptoVerification.SpqrV1.ProtoRepr (chainPBAt optChainPBAt optVersionNegotiationPBAt)
open CryptoVerification.SpqrV1.States.IntoPb (StatesIntoPbGhost)
open CryptoVerification.SpqrV1.States.Recv (StatesRecvGhost)
open CryptoVerification.SpqrV1.Top.DecodeState
  (DecodeStateGhost TraceVRegs V1InnerHeapPred optVersionNegotiationPBTailAt
   relocOptProtoInnerStateAt)
open CryptoVerification.SpqrV1.Top.InitInner (InitInnerGhost)
open CryptoVerification.SpqrV1.Top.Recv
  (SepWPpLS Words27 cap_ne_zero_one_sle_true memRegion_24_words3
   protoPqRatchetStateAt_eq_pqRatchetStatePBAt ret_48_split sepExists_left_entails
   sp_sub_4992_aligned spqrRecvCalleeStackX spqrRecvPlacedEntry spqrRecvPlacedProg
   spqrRecvRoPlacedAt spqrRecvSavedRegs spqrV1Recv_noPanic_of_recv_ok
   stackAt_spqrRecvCallee_split statesFromPbJumpTablePlacedAt
   statesIntoPbJumpTablePlacedAt statesRecvRoPlacedAt
   subroutine_ok_withMemEq_of_lscl vnHeader_sub4640_entails_memRegion_48
   vnTail_sub4640_some_entails_dealloc words27At words27At_sub_eq words27SubAt
   words3_to_memRegion_24)
open CryptoVerification.SpqrV1.Top.Recv.Placed (blkPC_329 blkPl_329)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FreeOnlyEvs RustCliAllocBudget VmPreserved
   rustCliDeallocBudgetSpec rustDeallocEvents)
open LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTopBudget (dropProtoPqRatchetStatePlacedSpec)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.DefsPlacedBudget
  (SpqrRecvPlacedContracts SpqrRecvPlacedContractsOfEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part1PlacedBudget
  (SpqrRecvEnv sepWP_spqrRecvPlacedPostOfEnv_of_post0 spqrRecvBudgetPanicPost
   spqrRecvPlacedPost spqrRecvPlacedPost0 spqrRecvPlacedPost0OfEnv
   spqrRecvPlacedPostOfEnv step_epilogue_placed_ofEnv)
open LibsignalBinary.Proofs.SpqrV1.Top.Recv.Part2PlacedBudget
  (SpqrRecvDropContractsBudget SpqrRecvEnv.append_freeOnly deallocFreeOnlySpec
   freeOnlyWitness seq_vm_clean seq_vm_lscl subroutine_ok_deallocFreeOnly)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff Obj.lookup
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
  RustCliAllocBudget.pool_setPC RustCliAllocBudget.pool_advancePC
  RustCliAllocBudget.pool_setPState RustCliAllocBudget.pool_writeReg64
  RustCliAllocBudget.pool_writeReg32 RustCliAllocBudget.pool_writeReg
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  extractLsb_lo_append64 extractLsb_hi_append64

theorem toDropContractsBudget {MC : AllocCostModel} {H_inner : V1InnerHeapPred}
    {A : RustCliAllocBudget MC} {lim : BudgetLimits} {F : ShaCompress} {K : MlKem}
    {DecodePreEnv DecodePostEnv : DecodeStateGhost → List AllocEvent → Prop}
    {InitEnv : InitInnerGhost → List AllocEvent → Prop}
    {FromPbEnv : V1State → List AllocEvent → Prop}
    {RecvEnv : StatesRecvGhost F → List AllocEvent → Prop}
    {IntoPbEnv : StatesIntoPbGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hC : SpqrRecvPlacedContractsOfEnv H_inner A lim F K
      DecodePreEnv DecodePostEnv InitEnv FromPbEnv RecvEnv IntoPbEnv ext) :
    SpqrRecvDropContractsBudget A lim F ext :=
  { dealloc_ok := hC.dealloc_ok
    dropEpochSlice_ok := hC.dropEpochSlice_ok
    dropOptProtoInnerState_ok := hC.dropOptProtoInnerState_ok
    dropOptProtoChain_ok := hC.dropOptProtoChain_ok
    dropChain_ok := hC.dropChain_ok
    dropPqRatchetState_ok := hC.dropPqRatchetState_ok
    dropStates_ok := hC.dropStates_ok }

theorem frame_pure_pre {Q : Prop} {P R F : SepProp} (hQ : Q) (heq : P = R ∗ F) :
    P ⊢ (⌜Q⌝ ∗ R) ∗ F := by
  rw [heq, sepConj_assoc]; exact Entails.pure_right hQ (Entails.refl _)

theorem onPanic_false_budget {M : SpqrRecvModel} {st msg : VecArg} (s sm : State) :
    (⌜False⌝ : SepProp) ⊢ ⌜M.recvPanics st.bytes msg.bytes ∧ s.trace <+: sm.trace⌝ ∗ anyHeap :=
  Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm)
    (Entails.pure_left fun h => False.elim h)

/-! ## 1. 224-Byte `Option<Inner>` Relocation (`s0.sp - 2096#64 -> s0.sp - 2928#64`) -/

omit [LibsignalPlacement] in
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

omit [LibsignalPlacement] in
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

omit [LibsignalPlacement] in
theorem optProtoInnerStateAt_expose_224 (H_inner : V1InnerHeapPred) (A : RustAlloc)
    (h_inner_eq : ∀ a opt,
      CryptoVerification.SpqrV1.Top.DecodeState.optProtoInnerStateAt H_inner A a opt =
        optProtoInnerStateAt A a opt)
    (sp0 : BitVec 64) (opt : Option V1State.InnerState) :
    optProtoInnerStateAt A (sp0 - 2096#64) opt ⊢
      ∃∗ w0 : BitVec 64, ∃∗ d : Words27, ∃∗ P_heap : SepProp,
        ⌜((sp0 - 2928#64) ↦₆₄ w0) ∗ words27SubAt sp0 2928 d ∗ P_heap ⊢
          optProtoInnerStateAt A (sp0 - 2928#64) opt⌝ ∗
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

/-! ## 2. Result Writing & `PqRatchetState` Drop Helpers (`+2820 .. +2916`) -/

omit [LibsignalPlacement] in
private theorem vecU8_sub_entails_header_payload_v1 (A : RustAlloc) (sp0 : BitVec 64) (m : Nat)
    (bs : List (BitVec 8)) (h0 : m < 2 ^ 64 := by decide) (h16 : 16 < m := by decide) :
    vecU8 A (sp0 - BitVec.ofNat 64 m) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp0 - BitVec.ofNat 64 m) ↦₆₄ cap) ∗
        ((sp0 - BitVec.ofNat 64 (m - 8)) ↦₆₄ ptr) ∗
        ((sp0 - BitVec.ofNat 64 (m - 16)) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  unfold vecU8
  apply sepExists_left_entails; intro cap
  apply sepExists_left_entails; intro ptr
  rw [vecU8At_eq_header_sep_buf A (sp0 - BitVec.ofNat 64 m) cap ptr bs]
  dsimp only [vecHeader]
  have h8 : (sp0 - BitVec.ofNat 64 m) + 8#64 = sp0 - BitVec.ofNat 64 (m - 8) :=
    bv_sub_add_lit sp0 m 8 (by omega) h0
  have h16_eq : (sp0 - BitVec.ofNat 64 m) + 16#64 = sp0 - BitVec.ofNat 64 (m - 16) :=
    bv_sub_add_lit sp0 m 16 (by omega) h0
  rw [h8, h16_eq]
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  exact Entails.of_eq (by ac_rfl)

omit [LibsignalPlacement] in
private theorem vecU8_of_header_buf_v1 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      vecU8Buf A cap ptr bs ⊢
    vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_header_sep_buf A a cap ptr bs]
  dsimp only [vecHeader]
  exact Entails.of_eq (by ac_rfl)

omit [LibsignalPlacement] in
private theorem ret_48_split_6_v1 (ret : BitVec 64) :
    memRegion ret 48 ⊢
      ∃∗ r0 : BitVec 64, ∃∗ r1 : BitVec 64, ∃∗ r2 : BitVec 64,
      ∃∗ r3 : BitVec 64, ∃∗ r4 : BitVec 64, ∃∗ r5 : BitVec 64,
        (ret ↦₆₄ r0) ∗ ((ret + 8#64) ↦₆₄ r1) ∗ ((ret + 16#64) ↦₆₄ r2) ∗
        ((ret + 24#64) ↦₆₄ r3) ∗ ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) := by
  rw [ret_48_split ret,
      ProofLib.memRegion_split' (b := ret + 32#64) (n := 8) (k := 8)
        (b' := ret + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (ret + 32#64),
      ProofLib.memRegion_eight (ret + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepExists_left_entails; intro r5
  apply sepExists_left_entails; intro r4
  apply sepExists_left_entails; intro r3
  apply sepExists_left_entails; intro r2
  apply sepExists_left_entails; intro r1
  apply sepExists_left_entails; intro r0
  refine Entails.sepExists_right r0 (Entails.sepExists_right r1 (Entails.sepExists_right r2
    (Entails.sepExists_right r3 (Entails.sepExists_right r4 (Entails.sepExists_right r5 ?_)))))
  exact Entails.refl _

omit [LibsignalPlacement] in
private theorem recv_ok_some_foldX_v1 (A : RustAlloc) (ret : BitVec 64)
    (cap_st ptr_st cap_rk ptr_rk : BitVec 64) (stBytes rawKey : List (BitVec 8)) :
    (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
      ((ret + 24#64) ↦₆₄ cap_rk) ∗ ((ret + 32#64) ↦₆₄ ptr_rk) ∗
      ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
      vecU8Buf A cap_st ptr_st stBytes ∗
      vecU8Buf A cap_rk ptr_rk rawKey ⊢
    recvResultExactKeyAt A ret (.ok (stBytes, some rawKey)) := by
  dsimp only [recvResultExactKeyAt, optKeyBytesAt]
  have hst := vecU8_of_header_buf_v1 A ret cap_st ptr_st stBytes
  have hrk := vecU8_of_header_buf_v1 A (ret + 24#64) cap_rk ptr_rk rawKey
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrk
  refine Entails.trans
    (Entails.of_eq (show
      (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        ((ret + 24#64) ↦₆₄ cap_rk) ∗ ((ret + 32#64) ↦₆₄ ptr_rk) ∗
        ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
        vecU8Buf A cap_st ptr_st stBytes ∗
        vecU8Buf A cap_rk ptr_rk rawKey =
      ((ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        vecU8Buf A cap_st ptr_st stBytes) ∗
      (((ret + 24#64) ↦₆₄ cap_rk) ∗ ((ret + 32#64) ↦₆₄ ptr_rk) ∗
        ((ret + 40#64) ↦₆₄ BitVec.ofNat 64 rawKey.length) ∗
        vecU8Buf A cap_rk ptr_rk rawKey) by ac_rfl)) ?_
  exact sepConj_mono hst hrk

omit [LibsignalPlacement] in
private theorem recv_ok_none_foldX_v1 (A : RustAlloc) (ret : BitVec 64)
    (cap_st ptr_st r4 r5 : BitVec 64) (stBytes : List (BitVec 8)) :
    (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
      ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
      ((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
      ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ∗
      vecU8Buf A cap_st ptr_st stBytes ⊢
    recvResultExactKeyAt A ret (.ok (stBytes, none)) := by
  dsimp only [recvResultExactKeyAt, optKeyBytesAt, noneCap]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have hst := vecU8_of_header_buf_v1 A ret cap_st ptr_st stBytes
  have h16 : ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ⊢ memRegion (ret + 32#64) 16 := by
    rw [ProofLib.memRegion_split' (b := ret + 32#64) (n := 8) (k := 8)
          (b' := ret + 40#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight (ret + 32#64),
        ProofLib.memRegion_eight (ret + 40#64)]
    exact sepConj_mono (Entails.sepExists_right r4 (Entails.refl _))
      (Entails.sepExists_right r5 (Entails.refl _))
  refine Entails.trans
    (Entails.of_eq (show
      (ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        ((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        ((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5) ∗
        vecU8Buf A cap_st ptr_st stBytes =
      ((ret ↦₆₄ cap_st) ∗ ((ret + 8#64) ↦₆₄ ptr_st) ∗
        ((ret + 16#64) ↦₆₄ BitVec.ofNat 64 stBytes.length) ∗
        vecU8Buf A cap_st ptr_st stBytes) ∗
      (((ret + 24#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗
        (((ret + 32#64) ↦₆₄ r4) ∗ ((ret + 40#64) ↦₆₄ r5))) by ac_rfl)) ?_
  exact sepConj_mono hst (sepConj_mono_right h16)

omit [LibsignalPlacement] in
theorem protoPqRatchetState_entails_drop_v1 (A : RustAlloc) (sp0 : BitVec 64)
    (chPb : ChainPB) (pb1 : V1State) :
    ((sp0 - 3056#64) ↦₆₄ noneCap) ∗
      memRegion (sp0 - 3048#64) 40 ∗
      chainPBAt A (sp0 - 3008#64) chPb ∗
      optProtoInnerStateAt A (sp0 - 2928#64) pb1.innerState ⊢
    protoPqRatchetStateAt A (sp0 - 3056#64)
      { versionNegotiation := none, chain := some chPb, inner := some (.v1 pb1) } := by
  dsimp only [protoPqRatchetStateAt, optVersionNegotiationPBAt, optChainPBAt, optProtoPqRatchetInnerAt]
  have h8 : (sp0 - 3056#64) + 8#64 = sp0 - 3048#64 := bv_sub_add_lit sp0 3056 8
  have h48 : (sp0 - 3056#64) + 48#64 = sp0 - 3008#64 := bv_sub_add_lit sp0 3056 48
  have h128 : (sp0 - 3056#64) + 128#64 = sp0 - 2928#64 := bv_sub_add_lit sp0 3056 128
  rw [h8, h48, h128]
  exact Entails.of_eq (by ac_rfl)

/-! ## 3. Stack Frame Splits and Reassembly for `+2664 .. +2916` -/

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem sp_sub_96_sub_136 (sp0 : BitVec 64) :
    (sp0 - 96#64) - 136#64 = sp0 - 232#64 := by bv_omega

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_544 (s0 : State) :
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s0 + 544#64 = s0.sp - 144#64 := by
  unfold CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp; bv_omega

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_560 (s0 : State) :
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s0 + 560#64 = s0.sp - 128#64 := by
  unfold CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp; bv_omega

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem hsp_add_456 (s0 : State) :
    CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp s0 + 456#64 = s0.sp - 232#64 := by
  unfold CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp; bv_omega

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem sp_writeVReg128_v1 (s : State) (r : BitVec 5) (v : BitVec 128) :
    (s.writeVReg128 r v).sp = s.sp := rfl

omit [LibsignalPlacement] in
@[local simp, local arm64_norm, local wp_norm]
theorem sp_setPState_v1 (s : State) (p : PState) :
    (s.setPState p).sp = s.sp := rfl

omit [LibsignalPlacement] in
theorem memRegion_2856_split_v1_ok (sp0 : BitVec 64) :
    memRegion (sp0 - 3088#64) 2856 ⊢
      memRegion (sp0 - 3088#64) 32 ∗
      (∃∗ w790 : BitVec 64, (sp0 - 3056#64) ↦₆₄ w790) ∗
      memRegion (sp0 - 3048#64) 40 ∗
      memRegion (sp0 - 3008#64) 80 ∗
      memRegion (sp0 - 2928#64) 224 ∗
      memRegion (sp0 - 2704#64) 608 ∗
      memRegion (sp0 - 2096#64) optProtoInnerStateSize ∗
      memRegion (sp0 - 1872#64) 1640 := by
  unfold optProtoInnerStateSize
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

omit [LibsignalPlacement] in
theorem memRegion_224_split_24_200_v1 (sp0 : BitVec 64) :
    memRegion (sp0 - 2096#64) 224 ⊢
      memRegion (sp0 - 2096#64) 24 ∗ memRegion (sp0 - 2072#64) 200 := by
  rw [show (224 : Nat) = 24 + 200 by decide,
      memRegion_split (sp0 - 2096#64) 24 200 (by decide),
      show (sp0 - 2096#64) + 24#64 = sp0 - 2072#64 by bv_omega]
  exact Entails.refl _

omit [LibsignalPlacement] in
private theorem memRegion_48_split_144_v1 (sp0 : BitVec 64) :
    memRegion (sp0 - 144#64) 48 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp0 - 144#64) ↦₆₄ w0) ∗ ((sp0 - 136#64) ↦₆₄ w1) ∗
        ((sp0 - 128#64) ↦₆₄ w2) ∗ memRegion (sp0 - 120#64) 24 := by
  rw [show (48 : Nat) = 24 + 24 by decide,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega,
      memRegion_24_words3 (sp0 - 144#64),
      show (sp0 - 144#64) + 8#64 = sp0 - 136#64 by bv_omega,
      show (sp0 - 144#64) + 16#64 = sp0 - 128#64 by bv_omega]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  apply sepExists_left_entails; intro w2; apply sepExists_left_entails; intro w1; apply sepExists_left_entails; intro w0
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.refl _)))

omit [LibsignalPlacement] in
private theorem ownFrame_join_v1_ok_2892 (sp0 w0_st w1_st w2_st w0_144 w1_144 w2_144 : BitVec 64) :
    memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 48 ∗ memRegion (sp0 - 4592#64) 576 ∗
      memRegion (sp0 - 4016#64) chunkedStatesSize ∗ memRegion (sp0 - 3088#64) 32 ∗
      memRegion (sp0 - 3056#64) 352 ∗ memRegion (sp0 - 2704#64) 608 ∗
      ((sp0 - 2096#64) ↦₆₄ w0_st) ∗ ((sp0 - 2088#64) ↦₆₄ w1_st) ∗ ((sp0 - 2080#64) ↦₆₄ w2_st) ∗
      memRegion (sp0 - 2072#64) 200 ∗ memRegion (sp0 - 1872#64) 1640 ∗ memRegion (sp0 - 232#64) 88 ∗
      ((sp0 - 144#64) ↦₆₄ w0_144) ∗ ((sp0 - 136#64) ↦₆₄ w1_144) ∗ ((sp0 - 128#64) ↦₆₄ w2_144) ∗
      memRegion (sp0 - 120#64) 24 ⊢
    memRegion (sp0 - 4992#64) 0x1320 := by
  unfold chunkedStatesSize
  have h24_st := words3_to_memRegion_24 (sp0 - 2096#64) w0_st w1_st w2_st
  rw [show (sp0 - 2096#64) + 8#64 = sp0 - 2088#64 by bv_omega,
      show (sp0 - 2096#64) + 16#64 = sp0 - 2080#64 by bv_omega] at h24_st
  have h24_144 := words3_to_memRegion_24 (sp0 - 144#64) w0_144 w1_144 w2_144
  rw [show (sp0 - 144#64) + 8#64 = sp0 - 136#64 by bv_omega,
      show (sp0 - 144#64) + 16#64 = sp0 - 128#64 by bv_omega] at h24_144
  rw [show (0x1320 : Nat) = 352 + (48 + (576 + (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))))))) by decide,
      memRegion_split (sp0 - 4992#64) 352 (48 + (576 + (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))))))) (by decide),
      show (sp0 - 4992#64) + 352#64 = sp0 - 4640#64 by bv_omega,
      memRegion_split (sp0 - 4640#64) 48 (576 + (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24)))))))))) (by decide),
      show (sp0 - 4640#64) + 48#64 = sp0 - 4592#64 by bv_omega,
      memRegion_split (sp0 - 4592#64) 576 (928 + (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))))) (by decide),
      show (sp0 - 4592#64) + 576#64 = sp0 - 4016#64 by bv_omega,
      memRegion_split (sp0 - 4016#64) 928 (32 + (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24)))))))) (by decide),
      show (sp0 - 4016#64) + 928#64 = sp0 - 3088#64 by bv_omega,
      memRegion_split (sp0 - 3088#64) 32 (352 + (608 + (24 + (200 + (1640 + (88 + (24 + 24))))))) (by decide),
      show (sp0 - 3088#64) + 32#64 = sp0 - 3056#64 by bv_omega,
      memRegion_split (sp0 - 3056#64) 352 (608 + (24 + (200 + (1640 + (88 + (24 + 24)))))) (by decide),
      show (sp0 - 3056#64) + 352#64 = sp0 - 2704#64 by bv_omega,
      memRegion_split (sp0 - 2704#64) 608 (24 + (200 + (1640 + (88 + (24 + 24))))) (by decide),
      show (sp0 - 2704#64) + 608#64 = sp0 - 2096#64 by bv_omega,
      memRegion_split (sp0 - 2096#64) 24 (200 + (1640 + (88 + (24 + 24)))) (by decide),
      show (sp0 - 2096#64) + 24#64 = sp0 - 2072#64 by bv_omega,
      memRegion_split (sp0 - 2072#64) 200 (1640 + (88 + (24 + 24))) (by decide),
      show (sp0 - 2072#64) + 200#64 = sp0 - 1872#64 by bv_omega,
      memRegion_split (sp0 - 1872#64) 1640 (88 + (24 + 24)) (by decide),
      show (sp0 - 1872#64) + 1640#64 = sp0 - 232#64 by bv_omega,
      memRegion_split (sp0 - 232#64) 88 (24 + 24) (by decide),
      show (sp0 - 232#64) + 88#64 = sp0 - 144#64 by bv_omega,
      memRegion_split (sp0 - 144#64) 24 24 (by decide),
      show (sp0 - 144#64) + 24#64 = sp0 - 120#64 by bv_omega]
  refine Entails.trans
    (Entails.of_eq (show
      memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 48 ∗ memRegion (sp0 - 4592#64) 576 ∗
        memRegion (sp0 - 4016#64) 928 ∗ memRegion (sp0 - 3088#64) 32 ∗ memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗ ((sp0 - 2096#64) ↦₆₄ w0_st) ∗ ((sp0 - 2088#64) ↦₆₄ w1_st) ∗
        ((sp0 - 2080#64) ↦₆₄ w2_st) ∗ memRegion (sp0 - 2072#64) 200 ∗ memRegion (sp0 - 1872#64) 1640 ∗
        memRegion (sp0 - 232#64) 88 ∗ ((sp0 - 144#64) ↦₆₄ w0_144) ∗ ((sp0 - 136#64) ↦₆₄ w1_144) ∗
        ((sp0 - 128#64) ↦₆₄ w2_144) ∗ memRegion (sp0 - 120#64) 24 =
      memRegion (sp0 - 4992#64) 352 ∗ memRegion (sp0 - 4640#64) 48 ∗ memRegion (sp0 - 4592#64) 576 ∗
        memRegion (sp0 - 4016#64) 928 ∗ memRegion (sp0 - 3088#64) 32 ∗ memRegion (sp0 - 3056#64) 352 ∗
        memRegion (sp0 - 2704#64) 608 ∗
        (((sp0 - 2096#64) ↦₆₄ w0_st) ∗ ((sp0 - 2088#64) ↦₆₄ w1_st) ∗ ((sp0 - 2080#64) ↦₆₄ w2_st)) ∗
        memRegion (sp0 - 2072#64) 200 ∗ memRegion (sp0 - 1872#64) 1640 ∗ memRegion (sp0 - 232#64) 88 ∗
        (((sp0 - 144#64) ↦₆₄ w0_144) ∗ ((sp0 - 136#64) ↦₆₄ w1_144) ∗ ((sp0 - 128#64) ↦₆₄ w2_144)) ∗
        memRegion (sp0 - 120#64) 24 by ac_rfl)) ?_
  exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono h24_st
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h24_144)))))))))))

/-! ## 4. Result Epilogue & Drop Cleanup (`+2820 .. +2916 -> +876 -> +1040 -> ret`) -/

omit [LibsignalPlacement] in
private theorem vecU8Buf_expose_len_lt (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8Buf A cap ptr bs ⊢
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ vecU8Buf A cap ptr bs := by
  unfold vecU8Buf
  exact Entails.pure_left fun h => Entails.pure_right h (Entails.pure_right h (Entails.refl _))

omit [LibsignalPlacement] in
private theorem vecU8Buf_nil_entails_dealloc (A : RustAlloc) (cap ptr : BitVec 64) :
    vecU8Buf A cap ptr [] ⊢
      ⌜cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      if cap = 0#64 then emp
      else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat := by
  unfold vecU8Buf
  apply Entails.pure_left; rintro ⟨_, hcap, hptr⟩
  refine Entails.pure_right ⟨hcap, hptr⟩ ?_
  by_cases hc : cap = 0#64
  · simp only [hc, ↓reduceIte]; exact Entails.refl _
  · simp only [hc, ↓reduceIte, List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.add_zero, Nat.sub_zero,
      pointsToBytes_nil, emp_sepConj]; exact Entails.refl _

omit [LibsignalPlacement] in
private theorem ofNat64_beq_zero_false_of_ne_nil {bs : List (BitVec 8)}
    (hne : bs.isEmpty = false) (hlt : bs.length < 2 ^ 63) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  have hpos : 0 < bs.length := by
    cases bs with
    | nil => contradiction
    | cons _ _ => exact Nat.succ_pos _
  rw [beq_eq_false_iff_ne]; intro h0
  have h0n := congrArg BitVec.toNat h0
  simp only [BitVec.toNat_ofNat, BitVec.toNat_zero] at h0n; omega

private theorem spqrRecvRoPlacedAt_expose_dropJumpTable :
    spqrRecvRoPlacedAt ⊢
      ∃∗ P_ro_drop, ⌜optProtoInnerStateJumpTablePlacedAt ∗ P_ro_drop ⊢ spqrRecvRoPlacedAt⌝ ∗
        optProtoInnerStateJumpTablePlacedAt ∗ P_ro_drop := by
  refine Entails.sepExists_right
    (v1StateMergeJumpTablePlacedExpanded ∗
      statesFromPbJumpTablePlacedAt ∗
      statesRecvRoPlacedAt ∗
      statesIntoPbJumpTablePlacedAt) ?_
  refine Entails.pure_right ?_ ?_
  · unfold spqrRecvRoPlacedAt v1StateJumpTablesPlacedAt
    exact Entails.of_eq (by ac_rfl)
  · unfold spqrRecvRoPlacedAt v1StateJumpTablesPlacedAt
    exact Entails.of_eq (by ac_rfl)

/-- Envelope-parametric shared cleanup at `+2884 .. +2916 -> +876 -> +1040`: calls
    `drop_in_place<PqRatchetState>` on `newPb` at `s0.sp - 3056#64`, drops
    `pre_pb.versionNegotiation` at `s0.sp - 4640#64` (`x23 = w0`), jumps to `+876` (`cbz w26,
    +1040`), joins the stack frame, and returns via `step_epilogue_placed_ofEnv`. -/
theorem step_v1_drop_newPb_and_vn_2884_placed_ofEnv {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb newPb : PqRatchetState)
    (w0 w1 w0_st w1_st w2_st w0_144 w1_144 w2_144 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0OfEnv A lim st_cost Env M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2884#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ w0_st) ∗ ((s0.sp - 2088#64) ↦₆₄ w1_st) ∗ ((s0.sp - 2080#64) ↦₆₄ w2_st) ∗
      memRegion (s0.sp - 2072#64) 200 ∗ memRegion (s0.sp - 1872#64) 1640 ∗ memRegion (s0.sp - 232#64) 88 ∗
      ((s0.sp - 144#64) ↦₆₄ w0_144) ∗ ((s0.sp - 136#64) ↦₆₄ w1_144) ∗ ((s0.sp - 128#64) ↦₆₄ w2_144) ∗
      memRegion (s0.sp - 120#64) 24 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hC.dealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  rw [← protoPqRatchetStateAt_eq_pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb]
  refine SepWP.focus_weaken spqrRecvRoPlacedAt_expose_dropJumpTable (by sep_focus) ?_
  wp_pull_exists; rename_i P_ro_drop
  wp_focus_pure; intro hP_ro_drop
  apply sepWP_seq_lscl hcl
  wp_steps 2
  refine ProofLib.SepWP.done (by simp only [arm64_norm]; rfl) (by simp only [arm64_norm, *]) fun hcl1 => ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide))) (by sep_focus) ?_
  have hdrop_pq := subroutine_ok_withMemEq_of_lscl hC.dropPqRatchetState_ok hcl1
  simp only [withMemEq, dropProtoPqRatchetStatePlacedSpec] at hdrop_pq
  dsimp only [spqrRecvPlacedProg, protoPqRatchetStateSize, BitVec.ofNat_eq_ofNat] at hdrop_pq
  wp_call hdrop_pq (⟨s0.sp - 3056#64, newPb⟩, MC.stepEvents evs0 st_cost)
  have hevs_pq := ‹FreeOnlyEvs _›
  have hsp_eq : stackAt s.sp dropStack96 = stackAt (s0.sp - 4992#64) dropStack96 := by rw [hsp]
  refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) dropStack96 (by decide)).symm) (by sep_focus) ?_
  refine SepWP.focus_weaken hP_ro_drop (by sep_focus) ?_
  cases hvn : pre_pb.versionNegotiation with
  | none =>
    dsimp only [optVersionNegotiationPBTailAt]
    wp_focus_pure; intro hw0; subst hw0
    have hsle : (1#64).sle noneCap = false := rfl
    wp_steps 3
    refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp noneCap w1) (by sep_focus) ?_
    refine SepWP.focus_weaken
      (ownFrame_join_v1_ok_2892 s0.sp w0_st w1_st w2_st w0_144 w1_144 w2_144) (by sep_focus) ?_
    exact step_epilogue_placed_ofEnv A lim st_cost Env
      (evs0 ++ freeOnlyWitness hevs_pq) (hevs_free _ hevs_pq)
      M ext st msg ret s0 _ _ R post hpost
      (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
      (by simp only [arm64_norm, *])
      (by
        rw [MC.stepEvents_append]
        simp only [freeOnlyWitness, wp_norm, arm64_norm, *]
        sep_ac_rfl)
  | some vn =>
    refine SepWP.focus_weaken (vnTail_sub4640_some_entails_dealloc A.repAlloc s0.sp w0 w1 vn) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc, LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc0 : (w0 == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hw0 : w0 = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hw0
      wp_steps 3
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp 0#64 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (ownFrame_join_v1_ok_2892 s0.sp w0_st w1_st w2_st w0_144 w1_144 w2_144) (by sep_focus) ?_
      exact step_epilogue_placed_ofEnv A lim st_cost Env
        (evs0 ++ freeOnlyWitness hevs_pq) (hevs_free _ hevs_pq)
        M ext st msg ret s0 _ _ R post hpost
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
        (by simp only [arm64_norm, *])
        (by
          rw [MC.stepEvents_append]
          simp only [freeOnlyWitness, wp_norm, arm64_norm, *]
          sep_ac_rfl)
    · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
      have hsle := cap_ne_zero_one_sle_true hcap_lt hc0
      have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide))) (by sep_focus) ?_
      wp_steps 6
      wp_call hdealloc_fo (w1, w0.toNat, 1, MC.stepEvents (freeOnlyWitness hevs_pq) (MC.stepEvents evs0 st_cost))
      wp_conv_pre => simp only [arm64_norm, *]
      refine SepWP.focus_weaken
        (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm) (by sep_focus) ?_
      wp_steps 2
      refine SepWP.focus_weaken (vnHeader_sub4640_entails_memRegion_48 s0.sp w0 w1) (by sep_focus) ?_
      refine SepWP.focus_weaken
        (ownFrame_join_v1_ok_2892 s0.sp w0_st w1_st w2_st w0_144 w1_144 w2_144) (by sep_focus) ?_
      exact step_epilogue_placed_ofEnv A lim st_cost Env
        (evs0 ++ (freeOnlyWitness hevs_pq ++ rustDeallocEvents w0.toNat 1))
        (hevs_free _ (hevs_pq.append (FreeOnlyEvs.singleton 1 w0.toNat)))
        M ext st msg ret s0 _ _ R post hpost
        (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hs0_align
        (by simp only [arm64_norm, *])
        (by
          rw [MC.stepEvents_append, MC.stepEvents_append]
          simp only [freeOnlyWitness, wp_norm, arm64_norm, *]
          sep_ac_rfl)

theorem step_v1_drop_newPb_and_vn_2884_placed {MC : AllocCostModel} {F : ShaCompress}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (M : SpqrRecvModel) (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb newPb : PqRatchetState)
    (w0 w1 w0_st w1_st w2_st w0_144 w1_144 w2_144 : BitVec 64)
    (s0 s : State) (P R : SepProp) (post : State → SepProp → Prop)
    (hpost : post = spqrRecvPlacedPost0 A lim st_cost M st msg ret s0 R)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2884#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx23 : s.readReg64 .x23 = w0)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
      recvResultExactKeyAt A.repAlloc ret (M.recv st.bytes msg.bytes) ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      ((s0.sp - 2096#64) ↦₆₄ w0_st) ∗ ((s0.sp - 2088#64) ↦₆₄ w1_st) ∗ ((s0.sp - 2080#64) ↦₆₄ w2_st) ∗
      memRegion (s0.sp - 2072#64) 200 ∗ memRegion (s0.sp - 1872#64) 1640 ∗ memRegion (s0.sp - 232#64) 88 ∗
      ((s0.sp - 144#64) ↦₆₄ w0_144) ∗ ((s0.sp - 136#64) ↦₆₄ w1_144) ∗ ((s0.sp - 128#64) ↦₆₄ w2_144) ∗
      memRegion (s0.sp - 120#64) 24 ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0)
    (hcl : LibsignalCodeLoaded lsmpl s.mem) :
    SepWP (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P post :=
  step_v1_drop_newPb_and_vn_2884_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    M ext hC st msg ret pre_pb newPb w0 w1 w0_st w1_st w2_st w0_144 w1_144 w2_144
    s0 s P R post hpost hs0_align hpc hrun hsp htr hx23 hx26 hP hcl

/-- Envelope-parametric (`+2820 .. +2916 -> +876 -> +1040 -> ret`): writes
    `Ok((PqRatchetState.encodeRaw newPb, if rawKey.isEmpty then none else some rawKey))` at
    `ret`, drops `newPb` and `pre_pb.versionNegotiation`, and returns via
    `step_epilogue_placed_ofEnv`. -/
theorem step_v1_ok_epilogue_2820_to_ret_placed_ofEnv {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (Env : List AllocEvent → Prop) (evs0 : List AllocEvent)
    (hevs_free : ∀ evs_d, FreeOnlyEvs evs_d → Env (evs0 ++ evs_d))
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (pre_pb newPb : PqRatchetState)
    (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw newPb, if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = 0xFFFFFFFFFFFFFFFF#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      vecU8 A.repAlloc (s0.sp - 2096#64) (PqRatchetState.encodeRaw newPb) ∗
      memRegion (s0.sp - 2072#64) 200 ∗ memRegion (s0.sp - 1872#64) 1640 ∗
      memRegion (s0.sp - 232#64) 88 ∗ memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPostOfEnv A lim st_cost Env (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) := by
  have hdealloc_fo := subroutine_ok_deallocFreeOnly hC.dealloc_ok
  simp only [deallocFreeOnlySpec, rustCliDeallocBudgetSpec] at hdealloc_fo
  have hfsp_align : ((s0.sp - 4992#64) &&& 15#64 == 0#64) = true := sp_sub_4992_aligned s0 hs0_align
  apply SepWPpLS.of_sepWP_ret_lscl; intro hcl
  subst hP
  dsimp only [spqrRecvPlacedProg, spqrRecvPlacedEntry,
    LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live,
    BitVec.ofNat_eq_ofNat] at hdealloc_fo hpc ⊢
  refine SepWP.focus_weaken
    (vecU8_sub_entails_header_payload_v1 A.repAlloc s0.sp 2096 (PqRatchetState.encodeRaw newPb)) (by sep_focus) ?_
  wp_pull_exists; rename_i cap_st ptr_st
  dsimp only [Nat.reduceSub, BitVec.ofNat_eq_ofNat]
  refine SepWP.focus_weaken (ret_48_split_6_v1 ret) (by sep_focus) ?_
  wp_pull_exists; rename_i r0 r1 r2 r3 r4 r5
  refine SepWP.focus_weaken (memRegion_48_split_144_v1 s0.sp) (by sep_focus) ?_
  wp_pull_exists; rename_i w0_144 w1_144 w2_144
  refine SepWP.focus_weaken (vecU8Buf_expose_len_lt A.repAlloc cap_rk ptr_rk rawKey) (by sep_focus) ?_
  wp_focus_pure; rintro ⟨hrk_le, hcap_rk_lt, hptr_rk_ne⟩
  let len_st := BitVec.ofNat 64 (PqRatchetState.encodeRaw newPb).length
  cases hrk_empty : rawKey.isEmpty with
  | true =>
    have hrk_nil : rawKey = [] := List.isEmpty_iff.mp hrk_empty
    subst hrk_nil
    simp only [List.length_nil, BitVec.ofNat_eq_ofNat] at hx24
    have hok' : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok (PqRatchetState.encodeRaw newPb, none) := by
      simpa [hrk_empty] using hok
    have hfold_none := recv_ok_none_foldX_v1 A.repAlloc ret cap_st ptr_st r4 r5 (PqRatchetState.encodeRaw newPb)
    rw [← hok'] at hfold_none
    refine SepWP.focus_weaken (vecU8Buf_nil_entails_dealloc A.repAlloc cap_rk ptr_rk) (by sep_focus) ?_
    wp_focus_pure; rintro ⟨_, _⟩
    dsimp only [LibsignalBinary.Heap.RustCliAllocBudget.repAlloc_live]
    by_cases hc_rk : cap_rk = 0#64
    · subst hc_rk
      simp only [↓reduceIte, emp_sepConj, sepConj_emp]
      refine seq_vm_lscl hcl (mid := (blkPl_329).base + 2884#64)
        (P_mid :=
          spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
          recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents evs0 st_cost) s ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          memRegion (s0.sp - 4992#64) 352 ∗
          ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
          memRegion (s0.sp - 4592#64) 576 ∗
          memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
          memRegion (s0.sp - 3088#64) 32 ∗
          pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb ∗
          memRegion (s0.sp - 2704#64) 608 ∗
          ((s0.sp - 2096#64) ↦₆₄ cap_st) ∗ ((s0.sp - 2088#64) ↦₆₄ ptr_st) ∗ ((s0.sp - 2080#64) ↦₆₄ len_st) ∗
          memRegion (s0.sp - 2072#64) 200 ∗ memRegion (s0.sp - 1872#64) 1640 ∗ memRegion (s0.sp - 232#64) 88 ∗
          ((s0.sp - 144#64) ↦₆₄ cap_st) ∗ ((s0.sp - 136#64) ↦₆₄ ptr_st) ∗ ((s0.sp - 128#64) ↦₆₄ len_st) ∗
          memRegion (s0.sp - 120#64) 24 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun s1 =>
          s1.sp = s0.sp - 4992#64 ∧ TraceVRegs s1 s0 ∧
          s1.readReg64 .x23 = w0 ∧ s1.readReg64 .x26 = 0#64)
        ?_ ?_
      · by_vm_steps (
          wp_steps 9
          refine SepWP.focus_weaken hfold_none (by sep_focus) ?_
          refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm],
             Entails.of_eq (by dsimp only [len_st]; sep_ac_rfl), ?_⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
        )
      · intro s1 hpc1 hrun1 hcl1 hvm1 ⟨hsp1, htr1, hx23_1, hx26_1⟩
        rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
        refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
        exact step_v1_drop_newPb_and_vn_2884_placed_ofEnv A lim st_cost Env evs0 hevs_free
          (spqrV1Recv F K) ext hC st msg ret pre_pb newPb
          w0 w1 cap_st ptr_st len_st cap_st ptr_st len_st
          s0 s1 _ R _ rfl hs0_align hpc1 hrun1 hsp1 htr1 hx23_1 hx26_1 (by sep_ac_rfl) hcl1
    · have hc_beq : (cap_rk == 0#64) = false := beq_eq_false_iff_ne.mpr hc_rk
      simp only [hc_rk, ↓reduceIte]
      refine seq_vm_lscl hcl (mid := lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
        (P_mid :=
          A.live ptr_rk cap_rk.toNat 1 ∗ memRegion ptr_rk cap_rk.toNat ∗
          stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
          spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
          recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
          A.pool lim (MC.stepEvents evs0 st_cost) s ∗
          memRegion (s0.sp - 4992#64) 352 ∗
          ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
          optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
          memRegion (s0.sp - 4592#64) 576 ∗
          memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
          memRegion (s0.sp - 3088#64) 32 ∗
          pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb ∗
          memRegion (s0.sp - 2704#64) 608 ∗
          ((s0.sp - 2096#64) ↦₆₄ cap_st) ∗ ((s0.sp - 2088#64) ↦₆₄ ptr_st) ∗ ((s0.sp - 2080#64) ↦₆₄ len_st) ∗
          memRegion (s0.sp - 2072#64) 200 ∗ memRegion (s0.sp - 1872#64) 1640 ∗ memRegion (s0.sp - 232#64) 88 ∗
          ((s0.sp - 144#64) ↦₆₄ cap_st) ∗ ((s0.sp - 136#64) ↦₆₄ ptr_st) ∗ ((s0.sp - 128#64) ↦₆₄ len_st) ∗
          memRegion (s0.sp - 120#64) 24 ∗
          spqrRecvSavedRegs (s0.sp - 4992#64) s0)
        (Q := fun s1 =>
          s1.sp = s0.sp - 4992#64 ∧ TraceVRegs s1 s0 ∧
          s1.readReg64 .x0 = ptr_rk ∧ s1.readReg64 .x1 = cap_rk ∧ s1.readReg64 .x2 = 1#64 ∧
          s1.readReg64 .x23 = w0 ∧ s1.readReg64 .x26 = 0#64 ∧
          s1.readReg64 .x30 = (blkPl_329).base + 2884#64)
        ?_ ?_
      · by_vm_steps (
          wp_steps 13
          refine SepWP.focus_weaken hfold_none (by sep_focus) ?_
          refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
            (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm],
             Entails.of_eq (by dsimp only [len_st]; sep_ac_rfl), ?_⟩
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
        )
      · intro s1 hpc1 hrun1 hcl1 hvm1
          ⟨hsp1, htr1, hx0_1, hx1_1, hx2_1, hx23_1, hx26_1, hx30_1⟩
        rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
        have hs1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hfsp_align
        refine SepWP.focus_weaken
          (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide))) (by sep_focus) ?_
        apply sepWP_seq_lscl hcl1 (mid := (blkPl_329).base + 2884#64)
        wp_call hdealloc_fo (ptr_rk, cap_rk.toNat, 1, MC.stepEvents evs0 st_cost)
        refine ProofLib.SepWP.done (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
          (by simp only [arm64_norm, *]) fun hcl2 => ?_
        have hsp_eq : stackAt s1.sp allocHookStack = stackAt (s0.sp - 4992#64) allocHookStack := by rw [hsp1]
        refine SepWP.focus_weaken (Entails.of_eq hsp_eq) (by sep_focus) ?_
        refine SepWP.focus_weaken
          (Entails.of_eq (stackAt_spqrRecvCallee_split (s0.sp - 4992#64) allocHookStack (by decide)).symm)
          (by sep_focus) ?_
        refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
        exact step_v1_drop_newPb_and_vn_2884_placed_ofEnv A lim st_cost Env
          (evs0 ++ rustDeallocEvents cap_rk.toNat 1)
          (fun evs_d hd => by
            rw [List.append_assoc]
            exact hevs_free _ ((FreeOnlyEvs.singleton 1 cap_rk.toNat).append hd))
          (spqrV1Recv F K) ext hC st msg ret pre_pb newPb
          w0 w1 cap_st ptr_st len_st cap_st ptr_st len_st
          s0 _ _ R _ rfl hs0_align
          (by simp only [spqrRecvPlacedEntry, arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
          (by simp only [arm64_norm, *])
          (by
            rw [MC.stepEvents_append]
            simp only [wp_norm, arm64_norm, *]
            sep_ac_rfl)
          hcl2
  | false =>
    have hrk_len_lt : rawKey.length < 2 ^ 63 := Nat.lt_of_le_of_lt hrk_le hcap_rk_lt
    have hrk_ne0 : (BitVec.ofNat 64 rawKey.length == 0#64) = false :=
      ofNat64_beq_zero_false_of_ne_nil hrk_empty hrk_len_lt
    have hok' : (spqrV1Recv F K).recv st.bytes msg.bytes = .ok (PqRatchetState.encodeRaw newPb, some rawKey) := by
      simpa [hrk_empty] using hok
    have hfold_some := recv_ok_some_foldX_v1 A.repAlloc ret cap_st ptr_st cap_rk ptr_rk
      (PqRatchetState.encodeRaw newPb) rawKey
    rw [← hok'] at hfold_some
    refine seq_vm_lscl hcl (mid := (blkPl_329).base + 2884#64)
      (P_mid :=
        spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗
        recvResultExactKeyAt A.repAlloc ret ((spqrV1Recv F K).recv st.bytes msg.bytes) ∗
        A.pool lim (MC.stepEvents evs0 st_cost) s ∗
        stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
        memRegion (s0.sp - 4992#64) 352 ∗
        ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
        optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
        memRegion (s0.sp - 4592#64) 576 ∗
        memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
        memRegion (s0.sp - 3088#64) 32 ∗
        pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb ∗
        memRegion (s0.sp - 2704#64) 608 ∗
        ((s0.sp - 2096#64) ↦₆₄ cap_st) ∗ ((s0.sp - 2088#64) ↦₆₄ ptr_st) ∗ ((s0.sp - 2080#64) ↦₆₄ len_st) ∗
        memRegion (s0.sp - 2072#64) 200 ∗ memRegion (s0.sp - 1872#64) 1640 ∗ memRegion (s0.sp - 232#64) 88 ∗
        ((s0.sp - 144#64) ↦₆₄ cap_st) ∗ ((s0.sp - 136#64) ↦₆₄ ptr_st) ∗ ((s0.sp - 128#64) ↦₆₄ len_st) ∗
        memRegion (s0.sp - 120#64) 24 ∗
        spqrRecvSavedRegs (s0.sp - 4992#64) s0)
      (Q := fun s1 =>
        s1.sp = s0.sp - 4992#64 ∧ TraceVRegs s1 s0 ∧
        s1.readReg64 .x23 = w0 ∧ s1.readReg64 .x26 = 0#64)
      ?_ ?_
    · by_vm_steps (
        wp_steps 10
        refine SepWP.focus_weaken hfold_some (by sep_focus) ?_
        refine ProofLib.SepWP.done (by simp only [wp_norm, arm64_norm, *]; try rfl)
          (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm],
           Entails.of_eq (by dsimp only [len_st]; sep_ac_rfl), ?_⟩
        refine ⟨?_, ?_, ?_, ?_⟩
        all_goals first | rfl | simp only [wp_norm, arm64_norm, *]
      )
    · intro s1 hpc1 hrun1 hcl1 hvm1 ⟨hsp1, htr1, hx23_1, hx26_1⟩
      rw [← A.pool_transport lim (MC.stepEvents evs0 st_cost) s s1 hvm1]
      refine sepWP_spqrRecvPlacedPostOfEnv_of_post0 (spqrV1Recv_noPanic_of_recv_ok hok) ?_
      exact step_v1_drop_newPb_and_vn_2884_placed_ofEnv A lim st_cost Env evs0 hevs_free
        (spqrV1Recv F K) ext hC st msg ret pre_pb newPb
        w0 w1 cap_st ptr_st len_st cap_st ptr_st len_st
        s0 s1 _ R _ rfl hs0_align hpc1 hrun1 hsp1 htr1 hx23_1 hx26_1 (by sep_ac_rfl) hcl1

theorem step_v1_ok_epilogue_2820_to_ret_placed {MC : AllocCostModel}
    (A : RustCliAllocBudget MC) (lim : BudgetLimits) (st_cost : MC.σ)
    (F : ShaCompress) (K : MlKem)
    (ext : String → Option (State → State))
    (hC : SpqrRecvDropContractsBudget A lim F ext)
    (st msg : VecArg) (ret : BitVec 64)
    (evs0 : List AllocEvent) (hevs0 : SpqrRecvEnv st msg evs0)
    (pre_pb newPb : PqRatchetState)
    (rawKey : Bytes)
    (w0 w1 cap_rk ptr_rk : BitVec 64)
    (hok : (spqrV1Recv F K).recv st.bytes msg.bytes =
      .ok (PqRatchetState.encodeRaw newPb, if rawKey.isEmpty then none else some rawKey))
    (s0 s : State) (P R : SepProp)
    (hs0_align : s0.spAligned = true)
    (hpc : s.pc = spqrRecvPlacedEntry + 2820#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 4992#64)
    (htr : TraceVRegs s s0)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = cap_rk)
    (hx22 : s.readReg64 .x22 = ptr_rk)
    (hx23 : s.readReg64 .x23 = w0)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 rawKey.length)
    (hx25 : s.readReg64 .x25 = 0xFFFFFFFFFFFFFFFF#64)
    (hx26 : s.readReg64 .x26 = 0#64)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hP : P =
      spqrRecvRoPlacedAt ∗ st.at A.repAlloc ∗ msg.at A.repAlloc ∗ memRegion ret 48 ∗
      A.pool lim (MC.stepEvents evs0 st_cost) s ∗
      stackAt (s0.sp - 4992#64) spqrRecvCalleeStackX ∗
      memRegion (s0.sp - 4992#64) 352 ∗
      ((s0.sp - 4640#64) ↦₆₄ w0) ∗ ((s0.sp - 4632#64) ↦₆₄ w1) ∗
      optVersionNegotiationPBTailAt A.repAlloc w0 w1 (s0.sp - 4624#64) pre_pb.versionNegotiation ∗
      memRegion (s0.sp - 4592#64) 576 ∗
      memRegion (s0.sp - 4016#64) chunkedStatesSize ∗
      memRegion (s0.sp - 3088#64) 32 ∗
      pqRatchetStatePBAt A.repAlloc (s0.sp - 3056#64) newPb ∗
      memRegion (s0.sp - 2704#64) 608 ∗
      vecU8 A.repAlloc (s0.sp - 2096#64) (PqRatchetState.encodeRaw newPb) ∗
      memRegion (s0.sp - 2072#64) 200 ∗ memRegion (s0.sp - 1872#64) 1640 ∗
      memRegion (s0.sp - 232#64) 88 ∗ memRegion (s0.sp - 144#64) 48 ∗
      vecU8Buf A.repAlloc cap_rk ptr_rk rawKey ∗
      spqrRecvSavedRegs (s0.sp - 4992#64) s0) :
    SepWPpLS (spqrRecvPlacedProg ext) (s0.readReg64 .x30) s P
      (spqrRecvPlacedPost A lim st_cost (spqrV1Recv F K) st msg ret s0 R)
      (spqrRecvBudgetPanicPost (spqrV1Recv F K) st msg s0 R) :=
  step_v1_ok_epilogue_2820_to_ret_placed_ofEnv A lim st_cost (SpqrRecvEnv st msg) evs0
    (fun _ hd => SpqrRecvEnv.append_freeOnly hevs0 hd)
    F K ext hC st msg ret pre_pb newPb rawKey w0 w1 cap_rk ptr_rk hok
    s0 s P R hs0_align hpc hrun hsp htr hx19 hx21 hx22 hx23 hx24 hx25 hx26 hx29 hP

end LibsignalBinary.Proofs.SpqrV1.Top.Recv.V1Ratchet5PlacedBudgetAux
