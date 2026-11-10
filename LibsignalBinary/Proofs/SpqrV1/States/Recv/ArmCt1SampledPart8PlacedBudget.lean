/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3PlacedBudgetAux
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart5PlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8Placed
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlacedBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 8 (Budget-Threaded)

Budget-threaded `[LibsignalPlacement]` Path 4b (`outMsg = none, ack = true`), `outMsg = some
decoded` `<Ct1Sent>::recv_ek` call (`+11496 -> +11528`), Path 5a (`recv_ek = .error`), and
Path 5b prefix helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Poly.DecodedMessage
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.CodeLayout
open Obj.MultiPlacedLib
open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEnv FreeOnlyEvs
  RustCliAllocBudget VmPreserved rustCliDeallocBudgetSpec
)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget (
  UnchunkedCt1SentRecvEkPostEnv UnchunkedCt1SentRecvEkPreEnv
  unchunkedCt1SentRecvEkSpecOfEnv unchunkedCt1SentRecvEkSpecOfPrePostEnv
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local irreducible] addChunkTotal decodedMessageTotal
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero lsmpl_base_332_eq

/-- State-indexed `LibsignalCodeLoaded`-preserving `SepWP` sequencing combinator. -/
theorem ct1Sampled_seq_state_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P : SepProp} {post1 post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P post1)
    (h2 : ∀ sm Pm, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → post1 sm Pm →
      SepWP prog target sm Pm post) :
    SepWP prog target s P post :=
  CryptoVerification.sepWP_seq_lscl hcl
    (SepWP.mono h1 fun sm Pm hpc hrun hp1 hcl' => h2 sm Pm hpc hrun hcl' hp1)

/-! ## 1. Path 4b (`outMsg = none, ack = true`: `+11496 -> s0.x30`) -/

set_option maxHeartbeats 2400000 in
/-- Budget-threaded Path 4b from `+11496 -> s0.x30` (`outMsg = none, ack = true`):
    deallocates `st.sending_ct1` (`FreeOnlyEvs evs`) and returns
    `Ok { key := none, state := .ct1Acknowledged { uc := st.uc, receiving_ek := dec' } }`. -/
theorem ct1Sampled_path_none_ack_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym (withVmPreserved sessionMemcpySpec))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder) (c_uc : Words16) (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx22 : s_in.readReg64 .x22 = 1#64)
    (hx28 : s_in.readReg64 .x28 = fsp + 3272#64)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) none ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗
        statesRecvRoPlacedAt ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA
              (.ok { key := none, state := .ct1Acknowledged { uc := st.uc, receiving_ek := dec' } }) ∗
            memRegion selfA chunkedStatesSize ∗
            statesRecvRoPlacedAt ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX ∗
            Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  refine ArmCt1SampledPart1PlacedBudget.ct1Sampled_seq_vm_lscl hcl
    (ArmCt1SampledPart3PlacedBudget.ct1Sampled_recv_ek_decode_branch_none_placed
      (A := A.repAlloc) s_in fsp _ hfsp_align hpc hrun hsp) ?_
  intro s1 hpc1 hrun1 hcl1 hvm01 ⟨hsp1, hx19_1, _, _, hx22_1, _, _, hx28_1, _, htr1⟩
  refine SepWP.seq
    (ArmCt1SampledPart4PlacedBudget.ct1Sampled_none_branch_ack_placed
      s1 _ hpc1 hrun1 (hx22_1.trans hx22)) ?_
  intro s2 P2 hpc2 hrun2 ⟨hvm12, hP2, hs2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hcl2 : LibsignalCodeLoaded lsmpl s2.mem := by rw [hs2]; exact hcl1
  have hsp2 : s2.sp = fsp := by rw [hs2]; exact hsp1
  have hx19_2 : s2.readReg64 .x19 = outA := by rw [hs2, State.readReg64_setPC, hx19_1, hx19]
  have hx28_2 : s2.readReg64 .x28 = fsp + 3272#64 := by
    rw [hs2, State.readReg64_setPC, hx28_1, hx28]
  have htr2 : TraceCalleeSaved s2 s0 := by rw [hs2]; exact htr1.trans htr
  have hpool02 : A.pool lim st_cost s_in = A.pool lim st_cost s2 :=
    (A.pool_transport lim st_cost s_in s2 (hvm01.trans hvm12)).symm
  have hpre2 :
      memRegion (fsp + 3832#64) 24 ∗ polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗ A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest ⊢
      ∃∗ vecs : List (List GF16), ∃∗ c_dec : Words50,
      ∃∗ v576 : BitVec 64, ∃∗ v584 : BitVec 64, ∃∗ v592 : BitVec 64,
      ∃∗ bs352_576 : List (BitVec 8),
      ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64,
      ∃∗ bs352_976 : List (BitVec 8),
      ∃∗ c_1352 : Words5, ∃∗ vc90 : BitVec 64, ∃∗ vc98 : BitVec 64, ∃∗ c_ca0 : Words5,
      ∃∗ vf10 : BitVec 64, ∃∗ vf18 : BitVec 64,
        ⌜vecs.length = NUM_POLYS⌝ ∗ ⌜bs352_576.length = 352⌝ ∗ ⌜bs352_976.length = 352⌝ ∗
        vecGF16ListOf A.repAlloc (selfA + 8#64) vecs ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ words50At (fsp + 2752#64) c_dec ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗ ((fsp + 984#64) ↦₆₄ v984) ∗ ((fsp + 992#64) ↦₆₄ v992) ∗
        ((fsp + 3216#64) ↦₆₄ vc90) ∗ ((fsp + 3224#64) ↦₆₄ vc98) ∗
        A.pool lim st_cost s2 ∗ stackAt fsp statesRecvCalleeStackX ∗
        (((fsp + 1000#64) ↦ₛ bs352_976) ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗
          mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
          ((fsp + 3856#64) ↦₆₄ vf10) ∗ ((fsp + 3864#64) ↦₆₄ vf18) ∗
          statesRecvRoPlacedAt ∗
          ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 392#64) 8 ∗
            memRegion (selfA + 528#64) 400 ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
              (wordsBytes c_uc.toList) ∗
            relocatedHeap (fun a => polyDecoderAt A.repAlloc a dec') c_dec.toBytes ∗
            memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
            (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
              memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
              memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
              memRegion (fsp + 3872#64) 272) ∗
            memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest)) := by
    rw [hpool02, polyEncoderAt_eq_tag_body A.repAlloc selfA st.sending_ct1]
    refine Entails.trans (Entails.of_eq (show _ =
        polyEncoderBodyAt A.repAlloc (selfA + 8#64) st.sending_ct1 ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        (wordsAt (fsp + 3696#64) c_uc.toList ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 1776 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3856#64) 288) ∗
        ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
            (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
          epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗ memRegion outA v1RecvSize ∗
          statesRecvRoPlacedAt ∗ A.pool lim st_cost s2 ∗ stackAt fsp statesRecvCalleeStackX ∗
          statesRecvSavedCells s0 ∗ Rest) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono
      (polyEncoderBodyAt_entails_vecs_tail A.repAlloc selfA st.sending_ct1)
      (sepConj_mono
        (Relocatable.extract_400 (Relocatable.of_polyDecoderAt A.repAlloc dec') (fsp + 2752#64))
        (sepConj_mono_left (memRegion_none_ack_split fsp c_uc)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Arm64.Entails.sepExists_elim; intro v576
    apply Arm64.Entails.sepExists_elim; intro v584
    apply Arm64.Entails.sepExists_elim; intro v592
    apply Arm64.Entails.sepExists_elim; intro bs352_576
    apply Arm64.Entails.sepExists_elim; intro v976
    apply Arm64.Entails.sepExists_elim; intro v984
    apply Arm64.Entails.sepExists_elim; intro v992
    apply Arm64.Entails.sepExists_elim; intro bs352_976
    apply Arm64.Entails.sepExists_elim; intro c_1352
    apply Arm64.Entails.sepExists_elim; intro vc90
    apply Arm64.Entails.sepExists_elim; intro vc98
    apply Arm64.Entails.sepExists_elim; intro c_ca0
    apply Arm64.Entails.sepExists_elim; intro vf10
    apply Arm64.Entails.sepExists_elim; intro vf18
    apply Arm64.Entails.sepExists_elim; intro c_dec
    apply Arm64.Entails.sepExists_elim; intro vecs
    refine Arm64.Entails.sepExists_right vecs (Arm64.Entails.sepExists_right c_dec
      (Arm64.Entails.sepExists_right v576 (Arm64.Entails.sepExists_right v584
        (Arm64.Entails.sepExists_right v592 (Arm64.Entails.sepExists_right bs352_576
          (Arm64.Entails.sepExists_right v976 (Arm64.Entails.sepExists_right v984
            (Arm64.Entails.sepExists_right v992 (Arm64.Entails.sepExists_right bs352_976
              (Arm64.Entails.sepExists_right c_1352 (Arm64.Entails.sepExists_right vc90
                (Arm64.Entails.sepExists_right vc98 (Arm64.Entails.sepExists_right c_ca0
                  (Arm64.Entails.sepExists_right vf10
                    (Arm64.Entails.sepExists_right vf18 ?_)))))))))))))))
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre2 ?_
  apply ProofLib.SepWP.exists_left; intro vecs; apply ProofLib.SepWP.exists_left; intro c_dec
  apply ProofLib.SepWP.exists_left; intro v576; apply ProofLib.SepWP.exists_left; intro v584
  apply ProofLib.SepWP.exists_left; intro v592; apply ProofLib.SepWP.exists_left; intro bs352_576
  apply ProofLib.SepWP.exists_left; intro v976; apply ProofLib.SepWP.exists_left; intro v984
  apply ProofLib.SepWP.exists_left; intro v992; apply ProofLib.SepWP.exists_left; intro bs352_976
  apply ProofLib.SepWP.exists_left; intro c_1352; apply ProofLib.SepWP.exists_left; intro vc90
  apply ProofLib.SepWP.exists_left; intro vc98; apply ProofLib.SepWP.exists_left; intro c_ca0
  apply ProofLib.SepWP.exists_left; intro vf10; apply ProofLib.SepWP.exists_left; intro vf18
  wp_focus_pure; intro hvecs_len
  wp_focus_pure; intro hbs576
  wp_focus_pure; intro hbs976
  refine SepWP.seq
    (ArmCt1SampledPart4PlacedBudget.ct1Sampled_copy_none_ack_part1_placed
      hdealloc st_cost s2 fsp selfA vecs hvecs_len
      c_uc c_dec bs352_576 k.tail sc k v976 v984 v992 vc90 vc98 _
      hcl2 hfsp_align hpc2 hrun2 hsp2) ?_
  rintro s3 P3 hpc3 hrun3 ⟨evs, hevs, hP3, hsp3, _hacp23, hx19_3, hx23_3, _, hx28_3, _, htr3⟩
  let d := mkSplit928Ct1Acknowledged c_uc c_dec bs352_576 k.tail
  have hP3' : P3 ⊢
      mid376At (fsp + 976#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
      wordsAt (fsp + 1352#64) c_1352.toList ∗
      wordsAt (fsp + 3232#64) c_ca0.toList ∗
      memRegion (fsp + 3272#64) 376 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp
          { (epilogueStackOfSplit928 d selfA k.w200 k.w208) with
            we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
        ((fsp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗ ((fsp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
        ((fsp + 3856#64) ↦₆₄ vf10) ∗ ((fsp + 3864#64) ↦₆₄ vf18) ∗
        statesRecvRoPlacedAt ∗
        (memRegion (selfA + 8#64) 384 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (fsp + 2752#64) 400 ∗ A.pool lim (M.stepEvents evs st_cost) s3 ∗
          (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 392#64) 8 ∗
          memRegion (selfA + 528#64) 400 ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
            (wordsBytes c_uc.toList) ∗
          relocatedHeap (fun a => polyDecoderAt A.repAlloc a dec') c_dec.toBytes ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
            memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 3872#64) 272) ∗
          memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest)) := by
    refine Entails.trans hP3 ?_
    dsimp only [mid376At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hP3' ?_
  refine SepWP.seq
    (ArmCt1SampledPart4PlacedBudget.ct1Sampled_copy_none_ack_part2a_placed
      hmemcpy s3 fsp c_dec.c2.w15 c_dec.w48 c_dec.w49
      bs352_976 c_1352 c_ca0 _ hbs976 hfsp_align hpc3 hrun3 hsp3 hx23_3
      (hx28_3.trans hx28_2)) ?_
  rintro s4 P4 hpc4 hrun4 ⟨hvm34, hP4, hsp4, hx19_4, hx28_4, _, htr4⟩
  have hP4' : P4 ⊢
      copyScratchStackAt fsp (copyFullScratch sc d) ∗
      epilogueStoreStackPart1At fsp
        { (epilogueStackOfSplit928 d selfA k.w200 k.w208) with
          we0 := k.we0, w3c0 := k.w3c0, w3c8 := k.w3c8 } ∗
      ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
      wordsAt (fsp + 528#64) k.tail.toList ∗
      mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
      mid376At (fsp + 976#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
      ((fsp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗ ((fsp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
      mid376At (fsp + 3272#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
      ((fsp + 3856#64) ↦₆₄ vf10) ∗ ((fsp + 3864#64) ↦₆₄ vf18) ∗
      statesRecvRoPlacedAt ∗
      (wordsAt (fsp + 1352#64) c_1352.toList ∗
        wordsAt (fsp + 3232#64) c_1352.toList ∗
        memRegion (selfA + 8#64) 384 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        memRegion (fsp + 2752#64) 400 ∗ A.pool lim (M.stepEvents evs st_cost) s3 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 392#64) 8 ∗
        memRegion (selfA + 528#64) 400 ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
          (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A.repAlloc a dec') c_dec.toBytes ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
          memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3872#64) 272) ∗
        memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest) :=
    Entails.trans hP4 (Entails.of_eq (by sep_ac_rfl))
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq
    (ArmCt1SampledPart4PlacedBudget.ct1Sampled_copy_none_ack_part2b_placed
      s4 fsp selfA outA c_uc c_dec bs352_976 bs352_576
      sc k v576 v584 v592 vf10 vf18 _ hfsp_align hpc4 hrun4 hsp4
      (hx19_4.trans (hx19_3.trans hx19_2)) hx28_4) ?_
  rintro s5 P5 hpc5 hrun5 ⟨hvm45, hP5, hregs5, hsp5, hx19_5, _, htr5⟩
  let k' := epilogueStackOfSplit928 d noneCap k.w200 k.w208
  have hmid' : k'.mid.length = 376 := by
    dsimp only [k', epilogueStackOfSplit928, d]
    exact mkSplit928Ct1Acknowledged_mid_length c_uc c_dec k.tail hbs576
  have hP5' : P5 ⊢
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 3168 ∗ memRegion selfA chunkedStatesSize ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
          (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A.repAlloc a dec') c_dec.toBytes ∗
        statesRecvRoPlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) s3 ∗
        statesRecvSavedCells s0 ∗ Rest) := by
    refine Entails.trans hP5 ?_
    simp only [memRegion_out_960_split_states_key]
    have hself :
        (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 8#64) 384 ∗
          memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400 ⊢
        memRegion selfA chunkedStatesSize :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (words16_entails_memRegion_128 (selfA + 400#64) c_uc)))))
        (tag_384_8_128_400_entails_memRegion_928 selfA (polyEncoderTagVal st.sending_ct1))
    have hstk3168 := memRegion_none_ack_join fsp c_dec.c2.w15 c_dec.w48 c_dec.w49
      c_dec.c2.w12 c_dec.c2.w13 c_dec.c2.w12 c_dec.c2.w13 hbs976 c_1352 c_1352
    refine Entails.trans (Entails.of_eq (show _ =
      epilogueStoreStackPart1At fsp k' ∗ epilogueStoreStackPart2At fsp k' ∗
      memRegion outA chunkedStatesSize ∗ memRegion (outA + 928#64) 32 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (mid376At (fsp + 976#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
          wordsAt (fsp + 1352#64) c_1352.toList ∗ memRegion (fsp + 2752#64) 400 ∗
          ((fsp + 3216#64) ↦₆₄ c_dec.c2.w12) ∗ ((fsp + 3224#64) ↦₆₄ c_dec.c2.w13) ∗
          wordsAt (fsp + 3232#64) c_1352.toList ∗
          mid376At (fsp + 3272#64) c_dec.c2.w15 c_dec.w48 c_dec.w49 bs352_976 ∗
          ((fsp + 3856#64) ↦₆₄ c_dec.c2.w12) ∗ ((fsp + 3864#64) ↦₆₄ c_dec.c2.w13) ∗
          (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
            memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 3872#64) 272)) ∗
        ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 8#64) 384 ∗
          memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400) ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
          (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A.repAlloc a dec') c_dec.toBytes ∗
        statesRecvRoPlacedAt ∗ A.pool lim (M.stepEvents evs st_cost) s3 ∗
        statesRecvSavedCells s0 ∗ Rest) by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hstk3168 (sepConj_mono_left hself)))))))))
  refine SepWP.weaken_pre hP5' ?_
  refine SepWP.seq
    (ArmCt1SampledPart3PlacedBudgetAux.ct1Sampled_epilogue_store_placed
      hmemcpy s5 fsp outA k' _ hmid' hfsp_align hpc5 hrun5 hsp5 hx19_5) ?_
  rintro s6 P6 hpc6 hrun6 ⟨hvm56, hP6, hsp6, htr6⟩
  have heq_split : epilogueSplit928 s5 k' = d :=
    epilogueSplit928_of_eq s5 d noneCap k.w200 k.w208 hregs5
  have hP6' : P6 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A.repAlloc (F := F) outA
          (.ok { key := none, state := .ct1Acknowledged { uc := st.uc, receiving_ek := dec' } }) ∗
        memRegion selfA chunkedStatesSize ∗ statesRecvRoPlacedAt ∗
        A.pool lim (M.stepEvents evs st_cost) s3 ∗ Rest) := by
    refine Entails.trans hP6 ?_
    simp only [heq_split]
    have hstk := copyScratch_and_epilogueStack_entails_memRegion_4144
      fsp (copyFullScratch sc d) k' hmid'
    have hst_out := split928At_reconstruct_ct1Acknowledged
      (A := A.repAlloc) (F := F) outA st.uc dec' c_uc c_dec bs352_576 k.tail hbs576
    have hkey := optEpochSecretAt_none_of_words4
      A.repAlloc (outA + 928#64) (s5.readReg64 .x20) k.w200 k.w208
    dsimp only [resultV1RecvAt, v1RecvAt, k', epilogueStackOfSplit928] at hstk hkey ⊢
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hkey
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (copyScratchStackAt fsp (copyFullScratch sc d) ∗
        epilogueStoreStackPart1At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        epilogueStoreStackPart2At fsp (epilogueStackOfSplit928 d noneCap k.w200 k.w208) ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 976#64) 3168) ∗
      statesRecvSavedCells s0 ∗
      (((split928At outA d ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc)
            (wordsBytes c_uc.toList) ∗
          relocatedHeap (fun a => polyDecoderAt A.repAlloc a dec') c_dec.toBytes) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s5.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗ ((outA + 952#64) ↦₆₄ k.w208))) ∗
        memRegion selfA chunkedStatesSize ∗ statesRecvRoPlacedAt ∗
        A.pool lim (M.stepEvents evs st_cost) s3 ∗ Rest) by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono hst_out hkey))))
  subst hfsp
  refine SepWP.weaken_pre hP6' ?_
  refine SepWP.mono
    (ArmCt1SampledPart1PlacedBudget.ct1Sampled_epilogue_19324_placed
      s0 s6 _ hsp0_align hpc6 hrun6 hsp6
      (htr6.trans (htr5.trans (htr4.trans (htr3.trans htr2))))) ?_
  rintro sf Pf _ _ ⟨hvm6f, hPf, hsp_f, hcs_f, htr_f⟩
  have hpool3f : A.pool lim (M.stepEvents evs st_cost) s3 =
      A.pool lim (M.stepEvents evs st_cost) sf :=
    (A.pool_transport lim (M.stepEvents evs st_cost) s3 sf
      (hvm34.trans (hvm45.trans (hvm56.trans hvm6f)))).symm
  exact ⟨evs, hevs,
    Entails.trans hPf (Entails.of_eq (by rw [hpool3f]; sep_ac_rfl)),
    hsp_f, hcs_f, htr_f⟩

/-! ## 2. `outMsg = some decoded` Common Call (`+11496 -> +11528`) & Path 5a (`recv_ek = .error`) -/

/-- Two-envelope (`PreEnv` / `PostEnv`) budget-threaded common `outMsg = some decoded` call
    (`+11496 -> +11528`) into `<Unchunked.SendCt.Ct1Sent>::recv_ek` (`Block 338`). -/
theorem ct1Sampled_some_to_11528_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K PreEnv PostEnv)))
    (st_cost : M.σ)
    (s_in : State) (fsp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c_uc : Words16) (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfits : FitsEnv M lim st_cost
      (PreEnv ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, uc, decoded, res⟩))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx20 : s_in.readReg64 .x20 = uc.epoch) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11528#64) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a uc) (wordsBytes c_uc.toList) ∗
        memRegion (fsp + 976#64) 1776 ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          PostEnv ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, uc, decoded, res⟩ evs ∧
          (Pf ⊢
            unchunkedCt1SentRecvEkResAt A.repAlloc (fsp + 1856#64) res ∗
            memRegion (fsp + 976#64) 880 ∗
            memRegion (fsp + 1984#64) 768 ∗
            memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3832#64) 24 ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX ∗
            Rest) ∧
          sf.sp = fsp ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
          sf.readReg64 .x20 = uc.epoch ∧
          sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
          sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
          sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
          sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
          sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
          TraceCalleeSaved sf s_in) := by
  refine ArmCt1SampledPart1PlacedBudget.ct1Sampled_seq_vm_lscl hcl
    (ArmCt1SampledPart3PlacedBudget.ct1Sampled_recv_ek_decode_branch_some_placed
      (A := A.repAlloc) s_in fsp decoded _ hfsp_align hpc hrun hsp) ?_
  intro s1 hpc1 hrun1 hcl1 hvm01
    ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hx29_1, htr1⟩
  have hpool01 : A.pool lim st_cost s_in = A.pool lim st_cost s1 :=
    (A.pool_transport lim st_cost s_in s1 hvm01).symm
  have hpre1 :
      vecU8 A.repAlloc (fsp + 3832#64) decoded ∗
        (wordsAt (fsp + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a uc) (wordsBytes c_uc.toList) ∗
          memRegion (fsp + 976#64) 1776 ∗ A.pool lim st_cost s_in ∗
          stackAt fsp statesRecvCalleeStackX ∗ Rest) ⊢
      memRegion (fsp + 1856#64) 128 ∗
        unchunkedCt1SentAt A.repAlloc (fsp + 3696#64) uc ∗
        vecU8 A.repAlloc (fsp + 3832#64) decoded ∗
        A.pool lim st_cost s1 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗ Rest) := by
    rw [hpool01]
    have huc := Relocatable.reconstruct_128
      (fun a => unchunkedCt1SentAt A.repAlloc a uc) (fsp + 3696#64) c_uc
    rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 880) (k := 896)
          (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 128) (k := 768)
          (b' := fsp + 1984#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 1856#64) 128 ∗
      (wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a uc) (wordsBytes c_uc.toList)) ∗
      vecU8 A.repAlloc (fsp + 3832#64) decoded ∗ A.pool lim st_cost s1 ∗
      stackAt fsp statesRecvCalleeStackX ∗
      (memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗ Rest) by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left huc)
  refine SepWP.weaken_pre hpre1 ?_
  refine SepWP.mono
    (ArmCt1SampledPart5PlacedBudget.ct1Sampled_call_recv_ek_placed_ofPrePostEnv
      hrecv_ek st_cost s1 fsp uc decoded res _
      hcl1 hres hfits hfsp_align hpc1 hrun1 hsp1 (hx20_1.trans hx20)) ?_
  rintro sf Pf _ _
    ⟨evs, hevs, hPf, hsp_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx28_f, hx29_f,
      htr_f⟩
  exact ⟨evs, hevs, Entails.trans hPf (Entails.of_eq (by sep_ac_rfl)), hsp_f,
    hx19_f.trans hx19_1, hx20_f, hx21_f.trans hx21_1, hx22_f.trans hx22_1,
    hx23_f.trans hx23_1, hx24_f.trans hx24_1, hx28_f.trans hx28_1, hx29_f.trans hx29_1,
    htr_f.trans htr1⟩

theorem ct1Sampled_some_to_11528_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {Env : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpecOfEnv M A lim F K Env)))
    (st_cost : M.σ)
    (s_in : State) (fsp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c_uc : Words16) (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfits : FitsEnv M lim st_cost
      (Env ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, uc, decoded, res⟩))
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx20 : s_in.readReg64 .x20 = uc.epoch) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11528#64) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a uc) (wordsBytes c_uc.toList) ∗
        memRegion (fsp + 976#64) 1776 ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          Env ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, uc, decoded, res⟩ evs ∧
          (Pf ⊢
            unchunkedCt1SentRecvEkResAt A.repAlloc (fsp + 1856#64) res ∗
            memRegion (fsp + 976#64) 880 ∗
            memRegion (fsp + 1984#64) 768 ∗
            memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3832#64) 24 ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX ∗
            Rest) ∧
          sf.sp = fsp ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
          sf.readReg64 .x20 = uc.epoch ∧
          sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
          sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
          sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
          sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
          sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
          TraceCalleeSaved sf s_in) :=
  ct1Sampled_some_to_11528_placed_ofPrePostEnv
    hrecv_ek st_cost s_in fsp uc c_uc decoded res Rest
    hcl hres hfits hfsp_align hpc hrun hsp hx20

theorem ct1Sampled_some_to_11528_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget.unchunkedCt1SentRecvEkSpec
          M A lim F K)))
    (st_cost : M.σ)
    (s_in : State) (fsp : BitVec 64)
    (uc : Unchunked.SendCt.Ct1Sent (spqrAuthApi F))
    (c_uc : Words16) (decoded : Bytes)
    (res : Except Error (Unchunked.SendCt.Ct1SentEkReceived (spqrAuthApi F)))
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : uc.recv_ek K uc.epoch decoded = StatesResult.ofError res)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx20 : s_in.readReg64 .x20 = uc.epoch) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11528#64) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a uc) (wordsBytes c_uc.toList) ∗
        memRegion (fsp + 976#64) 1776 ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            unchunkedCt1SentRecvEkResAt A.repAlloc (fsp + 1856#64) res ∗
            memRegion (fsp + 976#64) 880 ∗
            memRegion (fsp + 1984#64) 768 ∗
            memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3832#64) 24 ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt fsp statesRecvCalleeStackX ∗
            Rest) ∧
          sf.sp = fsp ∧
          sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
          sf.readReg64 .x20 = uc.epoch ∧
          sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
          sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
          sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
          sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
          sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
          sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
          TraceCalleeSaved sf s_in) :=
  ct1Sampled_some_to_11528_placed_ofPrePostEnv
    hrecv_ek st_cost s_in fsp uc c_uc decoded res Rest
    hcl hres (fun _ h => by cases h; trivial) hfsp_align hpc hrun hsp hx20

set_option maxHeartbeats 2400000 in
/-- Two-envelope (`PreEnv` / `PostEnv`) budget-threaded Path 5a from `+11496 -> s0.x30`
    (`outMsg = some decoded`, `recv_ek = .error (.err err)`): returns `Err(err)`. -/
theorem ct1Sampled_path_some_err_placed_ofPrePostEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {PreEnv PostEnv : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl
        (unchunkedCt1SentRecvEkSpecOfPrePostEnv M A lim F K PreEnv PostEnv)))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder) (c_uc : Words16) (decoded : Bytes) (err : Error)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : st.uc.recv_ek K st.uc.epoch decoded = .error (.err err))
    (hfits : FitsEnv M lim st_cost
      (PreEnv ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, st.uc, decoded, .error err⟩))
    (herr_val : err = .erroneousDataReceived)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        ∃ evsRek evsDrop : List AllocEvent,
          PostEnv ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, st.uc, decoded, .error err⟩ evsRek ∧
          FreeOnlyEvs evsDrop ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err err)) ∗
            memRegion selfA chunkedStatesSize ∗
            A.pool lim (M.stepEvents (evsRek ++ evsDrop) st_cost) sf ∗
            stackAt s0.sp statesRecvStackX ∗
            Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) := by
  have hpre0 :
      optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ A.pool lim st_cost s_in ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ Rest ⊢
      optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (fsp + 976#64) 1776 ∗ A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
          polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗
          ((fsp + 520#64) ↦₆₄ k.w208) ∗ wordsAt (fsp + 528#64) k.tail.toList ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 3152#64) 544 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest) :=
    Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre hpre0 ?_
  refine ct1Sampled_seq_state_lscl hcl
    (ct1Sampled_some_to_11528_placed_ofPrePostEnv
      hrecv_ek st_cost s_in fsp st.uc c_uc decoded (.error err) _
      hcl hres hfits hfsp_align hpc hrun hsp hx20) ?_
  rintro s1 P1 hpc1 hrun1 hcl1 ⟨evsRek, hevsRek, hP1, hsp1, hx19_1, _, _, _, _, _, _, _, htr1⟩
  have hpre1 :
      unchunkedCt1SentRecvEkResAt A.repAlloc (F := F) (fsp + 1856#64) (.error err) ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
        A.pool lim (M.stepEvents evsRek st_cost) s1 ∗ stackAt fsp statesRecvCalleeStackX ∗
        (polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
          polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗
          ((fsp + 520#64) ↦₆₄ k.w208) ∗ wordsAt (fsp + 528#64) k.tail.toList ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 3152#64) 544 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest) ⊢
      ∃∗ vecs : List (List GF16),
        ⌜vecs.length = NUM_POLYS⌝ ∗
        unchunkedCt1SentRecvEkResAt A.repAlloc (F := F) (fsp + 1856#64) (.error err) ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        vecGF16ListOf A.repAlloc (selfA + 8#64) vecs ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        memRegion outA v1RecvSize ∗
        A.pool lim (M.stepEvents evsRek st_cost) s1 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 392#64) 8 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3856#64) 288 ∗ statesRecvSavedCells s0 ∗ Rest) := by
    rw [polyEncoderAt_eq_tag_body A.repAlloc selfA st.sending_ct1]
    refine Entails.trans (Entails.of_eq (show _ =
      polyEncoderBodyAt A.repAlloc (selfA + 8#64) st.sending_ct1 ∗
      (unchunkedCt1SentRecvEkResAt A.repAlloc (F := F) (fsp + 1856#64) (.error err) ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        memRegion outA v1RecvSize ∗ A.pool lim (M.stepEvents evsRek st_cost) s1 ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3856#64) 288 ∗ statesRecvSavedCells s0 ∗ Rest) by sep_ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left
      (polyEncoderBodyAt_entails_vecs_tail A.repAlloc selfA st.sending_ct1)) ?_
    rw [sepExists_sepConj_left]
    apply Arm64.Entails.sepExists_elim; intro vecs
    refine Arm64.Entails.sepExists_right vecs ?_
    exact Entails.of_eq (by sep_ac_rfl)
  refine SepWP.weaken_pre (Entails.trans hP1 hpre1) ?_
  apply ProofLib.SepWP.exists_left; intro vecs
  wp_focus_pure; intro hvecs_len
  refine SepWP.seq
    (ArmCt1SampledPart5PlacedBudget.ct1Sampled_recv_ek_err_to_19324_placed
      (F := F) hdealloc (M.stepEvents evsRek st_cost) s1 fsp selfA outA vecs hvecs_len
      dec' err _ hcl1 herr_val hfsp_align hpc1 hrun1 hsp1 (hx19_1.trans hx19)) ?_
  rintro s2 P2 hpc2 hrun2 ⟨evsDrop, hevsDrop, hP2, hsp2, _hacp12, _, htr2⟩
  have hP2' : P2 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err err)) ∗
        memRegion selfA chunkedStatesSize ∗
        A.pool lim (M.stepEvents evsDrop (M.stepEvents evsRek st_cost)) s2 ∗ Rest) := by
    refine Entails.trans hP2 ?_
    have hself :
        (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 8#64) 384 ∗
          memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400 ⊢
        memRegion selfA chunkedStatesSize :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (words16_entails_memRegion_128 (selfA + 400#64) c_uc)))))
        (tag_384_8_128_400_entails_memRegion_928 selfA (polyEncoderTagVal st.sending_ct1))
    have hstk3168 :
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 128 ∗
          memRegion (fsp + 1984#64) 768 ∗ memRegion (fsp + 2752#64) 400 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3856#64) 288 ⊢
        memRegion (fsp + 976#64) 3168 := by
      rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 880) (k := 2288)
            (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 128) (k := 2160)
            (b' := fsp + 1984#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 1984#64) (n := 768) (k := 1392)
            (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 400) (k := 992)
            (b' := fsp + 3152#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 544) (k := 448)
            (b' := fsp + 3696#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 3696#64) (n := 128) (k := 320)
            (b' := fsp + 3824#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 3824#64) (n := 8) (k := 312)
            (b' := fsp + 3832#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 3832#64) (n := 24) (k := 288)
            (b' := fsp + 3856#64) rfl (by bv_omega) (by decide)]
      exact Entails.of_eq (by sep_ac_rfl)
    have hstk4144 :
        memRegion (fsp + 576#64) 376 ∗ copyScratchStackAt fsp sc ∗
          epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗
          (memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 128 ∗
            memRegion (fsp + 1984#64) 768 ∗ memRegion (fsp + 2752#64) 400 ∗
            memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 3856#64) 288) ⊢
        memRegion fsp 4144 :=
      Entails.trans
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right hstk3168)))))))))
        (copyScratch_part1_and_mem576_entails_memRegion_4144 fsp selfA sc k)
    refine Entails.trans (Entails.of_eq (show _ =
      stackAt fsp statesRecvCalleeStackX ∗
      (memRegion (fsp + 576#64) 376 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1856#64) 128 ∗
          memRegion (fsp + 1984#64) 768 ∗ memRegion (fsp + 2752#64) 400 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3856#64) 288)) ∗
      statesRecvSavedCells s0 ∗
      (resultV1RecvAt A.repAlloc (F := F) outA (.error (.err err)) ∗
        ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 8#64) 384 ∗
          memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400) ∗
        A.pool lim (M.stepEvents evsDrop (M.stepEvents evsRek st_cost)) s2 ∗
        Rest) by sep_ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk4144
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hself))))
  subst hfsp
  refine SepWP.weaken_pre hP2' ?_
  refine SepWP.mono
    (ArmCt1SampledPart1PlacedBudget.ct1Sampled_epilogue_19324_placed
      s0 s2 _ hsp0_align hpc2 hrun2 hsp2
      (htr2.trans (htr1.trans htr))) ?_
  rintro sf Pf _ _ ⟨hvm2f, hPf, hsp_f, hcs_f, htr_f⟩
  have hpool2f :
      A.pool lim (M.stepEvents evsDrop (M.stepEvents evsRek st_cost)) s2 =
        A.pool lim (M.stepEvents (evsRek ++ evsDrop) st_cost) sf := by
    rw [← M.stepEvents_append]
    exact (A.pool_transport lim (M.stepEvents (evsRek ++ evsDrop) st_cost) s2 sf hvm2f).symm
  exact ⟨evsRek, evsDrop, hevsRek, hevsDrop,
    Entails.trans hPf (Entails.of_eq (by rw [hpool2f]; sep_ac_rfl)),
    hsp_f, hcs_f, htr_f⟩

theorem ct1Sampled_path_some_err_placed_ofEnv [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {Env : UnchunkedCt1SentRecvEkGhost F → List AllocEvent → Prop}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpecOfEnv M A lim F K Env)))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder) (c_uc : Words16) (decoded : Bytes) (err : Error)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : st.uc.recv_ek K st.uc.epoch decoded = .error (.err err))
    (hfits : FitsEnv M lim st_cost
      (Env ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, st.uc, decoded, .error err⟩))
    (herr_val : err = .erroneousDataReceived)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        ∃ evsRek evsDrop : List AllocEvent,
          Env ⟨fsp + 1856#64, fsp + 3696#64, fsp + 3832#64, st.uc, decoded, .error err⟩ evsRek ∧
          FreeOnlyEvs evsDrop ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err err)) ∗
            memRegion selfA chunkedStatesSize ∗
            A.pool lim (M.stepEvents (evsRek ++ evsDrop) st_cost) sf ∗
            stackAt s0.sp statesRecvStackX ∗
            Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  ct1Sampled_path_some_err_placed_ofPrePostEnv
    hdealloc hrecv_ek st_cost s0 s_in fsp selfA outA st dec' c_uc decoded err sc k Rest
    hcl hres hfits herr_val hfsp_align hsp0_align hfsp hpc hrun hsp hx19 hx20 htr

theorem ct1Sampled_path_some_err_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustCliDeallocBudgetSpec M A lim))
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl
        (LibsignalBinary.Proofs.SpqrV1.States.Leaves.Batch2DefsPlacedBudget.unchunkedCt1SentRecvEkSpec
          M A lim F K)))
    (st_cost : M.σ)
    (s0 s_in : State) (fsp selfA outA : BitVec 64)
    (st : Chunked.SendCt.Ct1Sampled spqrPolyApi (spqrAuthApi F))
    (dec' : PolyDecoder) (c_uc : Words16) (decoded : Bytes) (err : Error)
    (sc : CopyScratchStack) (k : EpilogueStoreStack)
    (Rest : SepProp)
    (hcl : LibsignalCodeLoaded lsmpl s_in.mem)
    (hres : st.uc.recv_ek K st.uc.epoch decoded = .error (.err err))
    (herr_val : err = .erroneousDataReceived)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hfsp : fsp = s0.sp - 4240#64)
    (hpc : s_in.pc = (blkPl_332).base + 11496#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp)
    (hx19 : s_in.readReg64 .x19 = outA)
    (hx20 : s_in.readReg64 .x20 = st.uc.epoch)
    (htr : TraceCalleeSaved s_in s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s_in
      (optVecU8At A.repAlloc (fsp + 3832#64) (some decoded) ∗
        polyDecoderAt A.repAlloc (fsp + 2752#64) dec' ∗
        polyEncoderAt A.repAlloc selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A.repAlloc a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗
        ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗
        memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗
        memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗
        memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗
        memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗
        A.pool lim st_cost s_in ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        ∃ evs : List AllocEvent,
          FreeOnlyEvs evs ∧
          (Pf ⊢
            resultV1RecvAt A.repAlloc (F := F) outA (.error (.err err)) ∗
            memRegion selfA chunkedStatesSize ∗
            A.pool lim (M.stepEvents evs st_cost) sf ∗
            stackAt s0.sp statesRecvStackX ∗
            Rest) ∧
          sf.sp = s0.sp ∧
          CalleeSavedPreserved s0 sf ∧
          sf.trace = s0.trace) :=
  SepWP.mono
    (ct1Sampled_path_some_err_placed_ofPrePostEnv
      hdealloc hrecv_ek st_cost s0 s_in fsp selfA outA st dec' c_uc decoded err sc k Rest
      hcl hres (fun _ h => by cases h; trivial)
      herr_val hfsp_align hsp0_align hfsp hpc hrun hsp hx19 hx20 htr)
    fun _ _ _ _ ⟨evsRek, evsDrop, hevsRek, hevsDrop, hPf, hsp_f, hcs_f, htr_f⟩ =>
      ⟨evsRek ++ evsDrop, hevsRek.append hevsDrop, hPf, hsp_f, hcs_f, htr_f⟩

/-! ## 3. Path 5b Prefix Helpers (`+11528 -> +11620 -> +15760`) -/

/-- `VmPreserved`-preserving stack copy for `recv_ek = .ok uc_ek` (`+11528 -> +11620`). -/
theorem ct1Sampled_recv_ek_ok_copy_sc_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (fsp : BitVec 64) (sc : CopyScratchStack) (c_ek : Words16) (Rest : SepProp)
    (hw0 : c_ek.w0.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11528#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11620#64) s_in
      (wordsAt (fsp + 1856#64) c_ek.toList ∗
        memRegion (fsp + 3856#64) 128 ∗
        copyScratchStackAt fsp sc ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          wordsAt (fsp + 1856#64) c_ek.toList ∗
          wordsAt (fsp + 3856#64) c_ek.toList ∗
          copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x8 = c_ek.w0 ∧
        sf.readReg64 .x9 = c_ek.w2 ∧
        sf.readReg64 .x10 = c_ek.w3 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = c_ek.w1 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) :=
  ArmCt1SampledPart5PlacedBudget.ct1Sampled_recv_ek_ok_copy_sc_placed
    s_in fsp sc c_ek Rest hw0 hfsp_align hpc hrun hsp

theorem ct1Sampled_recv_ek_ok_copy_sc_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ)
    (s_in : State) (fsp : BitVec 64) (sc : CopyScratchStack) (c_ek : Words16) (Rest : SepProp)
    (hw0 : c_ek.w0.toNat < 2 ^ 63)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s_in.pc = (blkPl_332).base + 11528#64)
    (hrun : s_in.status = .Running)
    (hsp : s_in.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 11620#64) s_in
      (wordsAt (fsp + 1856#64) c_ek.toList ∗
        memRegion (fsp + 3856#64) 128 ∗
        copyScratchStackAt fsp sc ∗
        A.pool lim st_cost s_in ∗
        Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢
          wordsAt (fsp + 1856#64) c_ek.toList ∗
          wordsAt (fsp + 3856#64) c_ek.toList ∗
          copyScratchStackAt fsp { sc with wb0 := c_ek.w1 } ∗
          A.pool lim st_cost sf ∗
          Rest) ∧
        sf.sp = fsp ∧
        sf.readReg64 .x8 = c_ek.w0 ∧
        sf.readReg64 .x9 = c_ek.w2 ∧
        sf.readReg64 .x10 = c_ek.w3 ∧
        sf.readReg64 .x19 = s_in.readReg64 .x19 ∧
        sf.readReg64 .x20 = s_in.readReg64 .x20 ∧
        sf.readReg64 .x21 = s_in.readReg64 .x21 ∧
        sf.readReg64 .x22 = s_in.readReg64 .x22 ∧
        sf.readReg64 .x23 = s_in.readReg64 .x23 ∧
        sf.readReg64 .x24 = s_in.readReg64 .x24 ∧
        sf.readReg64 .x25 = c_ek.w1 ∧
        sf.readReg64 .x28 = s_in.readReg64 .x28 ∧
        sf.readReg64 .x29 = s_in.readReg64 .x29 ∧
        TraceCalleeSaved sf s_in) := by
  refine SepWP.weaken_pre ?_
    (SepWP.mono
      (ct1Sampled_recv_ek_ok_copy_sc_placed
        s_in fsp sc c_ek (A.pool lim st_cost s_in ∗ Rest) hw0 hfsp_align hpc hrun hsp) ?_)
  · exact Entails.of_eq (by sep_ac_rfl)
  · rintro sf Pf _ _ ⟨hvm, hPf, hq⟩
    exact ⟨hvm,
      Entails.trans hPf
        (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm])),
      hq⟩

/-- `VmPreserved`-preserving `ack = false` branch at `+11620 -> +15760`. -/
theorem ct1Sampled_ok_branch_no_ack_eq_placed [LibsignalPlacement]
    {ext : String → Option (State → State)}
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 11620#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 0#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 15760#64) s_in
      Rest
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ Rest) ∧
        sf = s_in.setPC ((blkPl_332).base + 15760#64)) :=
  ArmCt1SampledPart5PlacedBudget.ct1Sampled_ok_branch_no_ack_eq_placed s_in Rest hpc hrun hx22

theorem ct1Sampled_ok_branch_no_ack_eq_pool_placed [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ext : String → Option (State → State)}
    (st_cost : M.σ)
    (s_in : State) (Rest : SepProp)
    (hpc : s_in.pc = (blkPl_332).base + 11620#64)
    (hrun : s_in.status = .Running)
    (hx22 : s_in.readReg64 .x22 = 0#64) :
    SepWP (lsProg_332 (Rust.withPanics ext))
      ((blkPl_332).base + 15760#64) s_in
      (A.pool lim st_cost s_in ∗ Rest)
      (fun sf Pf =>
        VmPreserved s_in sf ∧
        (Pf ⊢ A.pool lim st_cost sf ∗ Rest) ∧
        sf = s_in.setPC ((blkPl_332).base + 15760#64)) :=
  SepWP.mono
    (ct1Sampled_ok_branch_no_ack_eq_placed s_in (A.pool lim st_cost s_in ∗ Rest) hpc hrun hx22)
    fun sf Pf _ _ ⟨hvm, hPf, hsf⟩ =>
      ⟨hvm,
        Entails.trans hPf
          (Entails.of_eq (by rw [A.pool_transport lim st_cost s_in sf hvm])),
        hsf⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8PlacedBudget
