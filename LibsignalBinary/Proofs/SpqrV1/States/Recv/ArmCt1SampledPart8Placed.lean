/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart2Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart4Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart5Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart7
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmCt1SampledPart8
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch3Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`) — `.ct1Sampled` Arm, Part 8 (Relocatable)

Relocatable `[LibsignalPlacement]` Path 4b (`outMsg = none, ack = true`), `outMsg = some decoded`
`<Ct1Sent>::recv_ek` call (`+11496 -> +11528`), Path 5a (`recv_ek = .error`), and Path 5b
prefix helpers.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

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

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrPolyApi spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local irreducible] addChunkTotal decodedMessageTotal
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero lsmpl_base_332_eq

/-! ## 1. Path 4b (`outMsg = none, ack = true`: `+11496 -> s0.x30`) -/

set_option maxHeartbeats 2000000 in
/-- Path 4b from `+11496 -> s0.x30` (`outMsg = none, ack = true`):
    returns `Ok { key := none, state := .ct1Acknowledged { uc := st.uc, receiving_ek := dec' } }`. -/
theorem ct1Sampled_path_none_ack_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
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
      (optVecU8At A (fsp + 3832#64) none ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
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
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Acknowledged { uc := st.uc, receiving_ek := dec' } }) ∗
          memRegion selfA chunkedStatesSize ∗
          statesRecvRoPlacedAt ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  refine ct1Sampled_seq_clean_lscl hcl
    (ct1Sampled_recv_ek_decode_branch_none_placed s_in fsp _ hfsp_align hpc hrun hsp) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx19_1, _, _, hx22_1, _, _, hx28_1, _, htr1⟩
  refine SepWP.seq
    (ct1Sampled_none_branch_ack_placed s1 _ hpc1 hrun1 (hx22_1.trans hx22)) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hs2⟩
  refine SepWP.weaken_pre hP2 ?_
  have hcl2 : LibsignalCodeLoaded lsmpl s2.mem := by rw [hs2]; exact hcl1
  have hsp2 : s2.sp = fsp := by rw [hs2]; exact hsp1
  have hx19_2 : s2.readReg64 .x19 = outA := by rw [hs2, State.readReg64_setPC, hx19_1, hx19]
  have hx28_2 : s2.readReg64 .x28 = fsp + 3272#64 := by rw [hs2, State.readReg64_setPC, hx28_1, hx28]
  have htr2 : TraceCalleeSaved s2 s0 := by rw [hs2]; exact htr1.trans htr
  have hpre2 :
      memRegion (fsp + 3832#64) 24 ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ statesRecvRoPlacedAt ∗ A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗ statesRecvSavedCells s0 ∗ Rest ⊢
      ∃∗ vecs : List (List GF16), ∃∗ c_dec : Words50,
      ∃∗ v576 : BitVec 64, ∃∗ v584 : BitVec 64, ∃∗ v592 : BitVec 64, ∃∗ bs352_576 : List (BitVec 8),
      ∃∗ v976 : BitVec 64, ∃∗ v984 : BitVec 64, ∃∗ v992 : BitVec 64, ∃∗ bs352_976 : List (BitVec 8),
      ∃∗ c_1352 : Words5, ∃∗ vc90 : BitVec 64, ∃∗ vc98 : BitVec 64, ∃∗ c_ca0 : Words5,
      ∃∗ vf10 : BitVec 64, ∃∗ vf18 : BitVec 64,
        ⌜vecs.length = NUM_POLYS⌝ ∗ ⌜bs352_576.length = 352⌝ ∗ ⌜bs352_976.length = 352⌝ ∗
        vecGF16ListOf A (selfA + 8#64) vecs ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ words50At (fsp + 2752#64) c_dec ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 976#64) ↦₆₄ v976) ∗ ((fsp + 984#64) ↦₆₄ v984) ∗ ((fsp + 992#64) ↦₆₄ v992) ∗
        ((fsp + 3216#64) ↦₆₄ vc90) ∗ ((fsp + 3224#64) ↦₆₄ vc98) ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        (((fsp + 1000#64) ↦ₛ bs352_976) ∗ wordsAt (fsp + 1352#64) c_1352.toList ∗
          wordsAt (fsp + 3232#64) c_ca0.toList ∗ memRegion (fsp + 3272#64) 376 ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗
          mid376At (fsp + 576#64) v576 v584 v592 bs352_576 ∗
          ((fsp + 3856#64) ↦₆₄ vf10) ∗ ((fsp + 3864#64) ↦₆₄ vf18) ∗
          statesRecvRoPlacedAt ∗
          ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 392#64) 8 ∗
            memRegion (selfA + 528#64) 400 ∗
            relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
            relocatedHeap (fun a => polyDecoderAt A a dec') c_dec.toBytes ∗
            memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
            (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
              memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
              memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
              memRegion (fsp + 3872#64) 272) ∗
            memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest)) := by
    rw [polyEncoderAt_eq_tag_body A selfA st.sending_ct1]
    refine Entails.trans (Entails.of_eq (show _ =
        polyEncoderBodyAt A (selfA + 8#64) st.sending_ct1 ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗
        (wordsAt (fsp + 3696#64) c_uc.toList ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 976#64) 1776 ∗
          memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3824#64) 8 ∗
          memRegion (fsp + 3856#64) 288) ∗
        ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
          epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
          ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
          wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗ memRegion outA v1RecvSize ∗
          statesRecvRoPlacedAt ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
          statesRecvSavedCells s0 ∗ Rest) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono (polyEncoderBodyAt_entails_vecs_tail A selfA st.sending_ct1)
      (sepConj_mono (Relocatable.extract_400 (Relocatable.of_polyDecoderAt A dec') (fsp + 2752#64))
        (sepConj_mono_left (memRegion_none_ack_split fsp c_uc)))) ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro v576; apply Entails.sepExists_elim; intro v584
    apply Entails.sepExists_elim; intro v592; apply Entails.sepExists_elim; intro bs352_576
    apply Entails.sepExists_elim; intro v976; apply Entails.sepExists_elim; intro v984
    apply Entails.sepExists_elim; intro v992; apply Entails.sepExists_elim; intro bs352_976
    apply Entails.sepExists_elim; intro c_1352; apply Entails.sepExists_elim; intro vc90
    apply Entails.sepExists_elim; intro vc98; apply Entails.sepExists_elim; intro c_ca0
    apply Entails.sepExists_elim; intro vf10; apply Entails.sepExists_elim; intro vf18
    apply Entails.sepExists_elim; intro c_dec; apply Entails.sepExists_elim; intro vecs
    refine Entails.sepExists_right vecs (Entails.sepExists_right c_dec
      (Entails.sepExists_right v576 (Entails.sepExists_right v584
        (Entails.sepExists_right v592 (Entails.sepExists_right bs352_576
          (Entails.sepExists_right v976 (Entails.sepExists_right v984
            (Entails.sepExists_right v992 (Entails.sepExists_right bs352_976
              (Entails.sepExists_right c_1352 (Entails.sepExists_right vc90
                (Entails.sepExists_right vc98 (Entails.sepExists_right c_ca0
                  (Entails.sepExists_right vf10 (Entails.sepExists_right vf18 ?_)))))))))))))))
    exact Entails.of_eq (by ac_rfl)
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
    (ct1Sampled_copy_none_ack_part1_placed hdealloc s2 fsp selfA vecs hvecs_len
      c_uc c_dec bs352_576 k.tail sc k v976 v984 v992 vc90 vc98 _
      hcl2 hfsp_align hpc2 hrun2 hsp2) ?_
  intro s3 P3 hpc3 hrun3 ⟨hP3, hsp3, hx19_3, hx23_3, _, hx28_3, _, htr3⟩
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
          memRegion (fsp + 2752#64) 400 ∗ A.pool ∗
          (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 392#64) 8 ∗
          memRegion (selfA + 528#64) 400 ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          relocatedHeap (fun a => polyDecoderAt A a dec') c_dec.toBytes ∗
          memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
          (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
            memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
            memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
            memRegion (fsp + 3872#64) 272) ∗
          memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest)) := by
    refine Entails.trans hP3 ?_
    dsimp only [mid376At]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hP3' ?_
  refine SepWP.seq
    (ct1Sampled_copy_none_ack_part2a_placed hmemcpy s3 fsp c_dec.c2.w15 c_dec.w48 c_dec.w49
      bs352_976 c_1352 c_ca0 _ hbs976 hfsp_align hpc3 hrun3 hsp3 hx23_3 (hx28_3.trans hx28_2)) ?_
  intro s4 P4 hpc4 hrun4 ⟨hP4, hsp4, hx19_4, hx28_4, _, htr4⟩
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
        memRegion (fsp + 2752#64) 400 ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 392#64) 8 ∗
        memRegion (selfA + 528#64) 400 ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') c_dec.toBytes ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        (memRegion (fsp + 1392#64) 1360 ∗ memRegion (fsp + 3152#64) 64 ∗
          memRegion (fsp + 3648#64) 48 ∗ memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
          memRegion (fsp + 3872#64) 272) ∗
        memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest) :=
    Entails.trans hP4 (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hP4' ?_
  refine SepWP.seq
    (ct1Sampled_copy_none_ack_part2b_placed s4 fsp selfA outA c_uc c_dec bs352_976 bs352_576
      sc k v576 v584 v592 vf10 vf18 _ hfsp_align hpc4 hrun4 hsp4
      (hx19_4.trans (hx19_3.trans hx19_2)) hx28_4) ?_
  intro s5 P5 hpc5 hrun5 ⟨hP5, hregs5, hsp5, hx19_5, _, htr5⟩
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
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') c_dec.toBytes ∗
        statesRecvRoPlacedAt ∗ A.pool ∗
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
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        relocatedHeap (fun a => polyDecoderAt A a dec') c_dec.toBytes ∗
        statesRecvRoPlacedAt ∗ A.pool ∗
        statesRecvSavedCells s0 ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono hstk3168 (sepConj_mono_left hself)))))))))
  refine SepWP.weaken_pre hP5' ?_
  refine SepWP.seq
    (ct1Sampled_epilogue_store_placed hmemcpy s5 fsp outA k' _ hmid' hfsp_align hpc5 hrun5 hsp5 hx19_5) ?_
  intro s6 P6 hpc6 hrun6 ⟨hP6, hsp6, htr6⟩
  have heq_split : epilogueSplit928 s5 k' = d :=
    epilogueSplit928_of_eq s5 d noneCap k.w200 k.w208 hregs5
  have hP6' : P6 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.ok { key := none, state := .ct1Acknowledged { uc := st.uc, receiving_ek := dec' } }) ∗
        memRegion selfA chunkedStatesSize ∗ statesRecvRoPlacedAt ∗ A.pool ∗ Rest) := by
    refine Entails.trans hP6 ?_
    simp only [heq_split]
    have hstk := copyScratch_and_epilogueStack_entails_memRegion_4144 fsp (copyFullScratch sc d) k' hmid'
    have hst_out := split928At_reconstruct_ct1Acknowledged (A := A) (F := F) outA st.uc dec' c_uc c_dec bs352_576 k.tail hbs576
    have hkey := optEpochSecretAt_none_of_words4 A (outA + 928#64) (s5.readReg64 .x20) k.w200 k.w208
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
          relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
          relocatedHeap (fun a => polyDecoderAt A a dec') c_dec.toBytes) ∗
        (((outA + 928#64) ↦₆₄ noneCap) ∗ ((outA + 936#64) ↦₆₄ s5.readReg64 .x20) ∗
          ((outA + 944#64) ↦₆₄ k.w200) ∗ ((outA + 952#64) ↦₆₄ k.w208))) ∗
        memRegion selfA chunkedStatesSize ∗ statesRecvRoPlacedAt ∗ A.pool ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk
      (sepConj_mono_right (sepConj_mono_left (sepConj_mono hst_out hkey))))
  subst hfsp
  refine SepWP.weaken_pre hP6' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_19324_placed s0 s6 _ hsp0_align hpc6 hrun6 hsp6
      (htr6.trans (htr5.trans (htr4.trans (htr3.trans htr2))))) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-! ## 2. `outMsg = some decoded` Common Call (`+11496 -> +11528`) & Path 5a (`recv_ek = .error`) -/

theorem ct1Sampled_some_to_11528_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K)))
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
      (optVecU8At A (fsp + 3832#64) (some decoded) ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a uc) (wordsBytes c_uc.toList) ∗
        memRegion (fsp + 976#64) 1776 ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          unchunkedCt1SentRecvEkResAt A (fsp + 1856#64) res ∗
          memRegion (fsp + 976#64) 880 ∗
          memRegion (fsp + 1984#64) 768 ∗
          memRegion (fsp + 3696#64) 128 ∗
          memRegion (fsp + 3832#64) 24 ∗
          A.pool ∗
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
  refine ct1Sampled_seq_clean_lscl hcl
    (ct1Sampled_recv_ek_decode_branch_some_placed s_in fsp decoded _ hfsp_align hpc hrun hsp) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx28_1, hx29_1, htr1⟩
  have hpre1 :
      vecU8 A (fsp + 3832#64) decoded ∗
        (wordsAt (fsp + 3696#64) c_uc.toList ∗
          relocatedHeap (fun a => unchunkedCt1SentAt A a uc) (wordsBytes c_uc.toList) ∗
          memRegion (fsp + 976#64) 1776 ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗ Rest) ⊢
      memRegion (fsp + 1856#64) 128 ∗
        unchunkedCt1SentAt A (fsp + 3696#64) uc ∗
        vecU8 A (fsp + 3832#64) decoded ∗
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        (memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗ Rest) := by
    have huc := Relocatable.reconstruct_128 (fun a => unchunkedCt1SentAt A a uc) (fsp + 3696#64) c_uc
    rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 880) (k := 896) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 128) (k := 768) (b' := fsp + 1984#64) rfl (by bv_omega) (by decide)]
    refine Entails.trans (Entails.of_eq (show _ =
      memRegion (fsp + 1856#64) 128 ∗
      (wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a uc) (wordsBytes c_uc.toList)) ∗
      vecU8 A (fsp + 3832#64) decoded ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
      (memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono_left huc)
  refine SepWP.weaken_pre hpre1 ?_
  refine SepWP.mono
    (ct1Sampled_call_recv_ek_placed hrecv_ek s1 fsp uc decoded res _
      hcl1 hres hfsp_align hpc1 hrun1 hsp1 (hx20_1.trans hx20)) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hx19_f, hx20_f, hx21_f, hx22_f, hx23_f, hx24_f, hx28_f, hx29_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f,
    hx19_f.trans hx19_1, hx20_f, hx21_f.trans hx21_1, hx22_f.trans hx22_1,
    hx23_f.trans hx23_1, hx24_f.trans hx24_1, hx28_f.trans hx28_1, hx29_f.trans hx29_1,
    htr_f.trans htr1⟩

set_option maxHeartbeats 2000000 in
/-- Path 5a from `+11496 -> s0.x30` (`outMsg = some decoded`, `recv_ek = .error (.err err)`):
    returns `Err(err)`. -/
theorem ct1Sampled_path_some_err_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem}
    {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (hrecv_ek : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 338)
      (withLsCodeLoaded lsmpl (unchunkedCt1SentRecvEkSpec A F K)))
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
      (optVecU8At A (fsp + 3832#64) (some decoded) ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
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
        A.pool ∗
        stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗
        Rest)
      (fun sf Pf =>
        (Pf ⊢
          resultV1RecvAt A (F := F) outA (.error (.err err)) ∗
          memRegion selfA chunkedStatesSize ∗
          A.pool ∗
          stackAt s0.sp statesRecvStackX ∗
          Rest) ∧
        sf.sp = s0.sp ∧
        CalleeSavedPreserved s0 sf ∧
        sf.trace = s0.trace) := by
  have hpre0 :
      optVecU8At A (fsp + 3832#64) (some decoded) ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
        polyEncoderAt A selfA st.sending_ct1 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (selfA + 528#64) 400 ∗ copyScratchStackAt fsp sc ∗
        epilogueStoreStackPart1At fsp k ∗ ((fsp + 232#64) ↦₆₄ selfA) ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 1776 ∗ memRegion (fsp + 3152#64) 544 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
        memRegion outA v1RecvSize ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        statesRecvSavedCells s0 ∗ Rest ⊢
      optVecU8At A (fsp + 3832#64) (some decoded) ∗
        wordsAt (fsp + 3696#64) c_uc.toList ∗
        relocatedHeap (fun a => unchunkedCt1SentAt A a st.uc) (wordsBytes c_uc.toList) ∗
        memRegion (fsp + 976#64) 1776 ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
          wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
          copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
          ((fsp + 232#64) ↦₆₄ selfA) ∗ ((fsp + 512#64) ↦₆₄ k.w200) ∗
          ((fsp + 520#64) ↦₆₄ k.w208) ∗ wordsAt (fsp + 528#64) k.tail.toList ∗
          memRegion (fsp + 576#64) 376 ∗ memRegion (fsp + 568#64) 8 ∗
          memRegion (fsp + 952#64) 8 ∗ memRegion (fsp + 3152#64) 544 ∗
          memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3856#64) 288 ∗
          memRegion outA v1RecvSize ∗ statesRecvSavedCells s0 ∗ Rest) :=
    Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre0 ?_
  refine ct1Sampled_seq_clean_lscl hcl
    (ct1Sampled_some_to_11528_placed hrecv_ek s_in fsp st.uc c_uc decoded (.error err) _
      hcl hres hfsp_align hpc hrun hsp hx20) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx19_1, _, _, _, _, _, _, _, htr1⟩
  have hpre1 :
      unchunkedCt1SentRecvEkResAt A (F := F) (fsp + 1856#64) (.error err) ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3696#64) 128 ∗ memRegion (fsp + 3832#64) 24 ∗
        A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        (polyDecoderAt A (fsp + 2752#64) dec' ∗ polyEncoderAt A selfA st.sending_ct1 ∗
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
        unchunkedCt1SentRecvEkResAt A (F := F) (fsp + 1856#64) (.error err) ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗
        vecGF16ListOf A (selfA + 8#64) vecs ∗
        polyDecoderAt A (fsp + 2752#64) dec' ∗
        memRegion outA v1RecvSize ∗
        A.pool ∗
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
    rw [polyEncoderAt_eq_tag_body A selfA st.sending_ct1]
    refine Entails.trans (Entails.of_eq (show _ =
      polyEncoderBodyAt A (selfA + 8#64) st.sending_ct1 ∗
      (unchunkedCt1SentRecvEkResAt A (F := F) (fsp + 1856#64) (.error err) ∗
        ((fsp + 232#64) ↦₆₄ selfA) ∗ polyDecoderAt A (fsp + 2752#64) dec' ∗
        memRegion outA v1RecvSize ∗ A.pool ∗ stackAt fsp statesRecvCalleeStackX ∗
        (selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗
        wordsAt (selfA + 400#64) c_uc.toList ∗ memRegion (selfA + 528#64) 400 ∗
        copyScratchStackAt fsp sc ∗ epilogueStoreStackPart1At fsp k ∗
        ((fsp + 512#64) ↦₆₄ k.w200) ∗ ((fsp + 520#64) ↦₆₄ k.w208) ∗
        wordsAt (fsp + 528#64) k.tail.toList ∗ memRegion (fsp + 576#64) 376 ∗
        memRegion (fsp + 568#64) 8 ∗ memRegion (fsp + 952#64) 8 ∗
        memRegion (fsp + 976#64) 880 ∗ memRegion (fsp + 1984#64) 768 ∗
        memRegion (fsp + 3152#64) 544 ∗ memRegion (fsp + 3696#64) 128 ∗
        memRegion (fsp + 3824#64) 8 ∗ memRegion (fsp + 3832#64) 24 ∗
        memRegion (fsp + 3856#64) 288 ∗ statesRecvSavedCells s0 ∗ Rest) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (polyEncoderBodyAt_entails_vecs_tail A selfA st.sending_ct1)) ?_
    rw [sepExists_sepConj_left]
    apply Entails.sepExists_elim; intro vecs
    refine Entails.sepExists_right vecs ?_
    exact Entails.of_eq (by ac_rfl)
  refine SepWP.weaken_pre hpre1 ?_
  apply ProofLib.SepWP.exists_left; intro vecs
  wp_focus_pure; intro hvecs_len
  refine SepWP.seq
    (ct1Sampled_recv_ek_err_to_19324_placed (F := F) hdealloc s1 fsp selfA outA vecs hvecs_len
      dec' err _ hcl1 herr_val hfsp_align hpc1 hrun1 hsp1 (hx19_1.trans hx19)) ?_
  intro s2 P2 hpc2 hrun2 ⟨hP2, hsp2, _, htr2⟩
  have hP2' : P2 ⊢
      stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 4144 ∗ statesRecvSavedCells s0 ∗
      (resultV1RecvAt A (F := F) outA (.error (.err err)) ∗
        memRegion selfA chunkedStatesSize ∗ A.pool ∗ Rest) := by
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
      rw [ProofLib.memRegion_split' (b := fsp + 976#64) (n := 880) (k := 2288) (b' := fsp + 1856#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 1856#64) (n := 128) (k := 2160) (b' := fsp + 1984#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 1984#64) (n := 768) (k := 1392) (b' := fsp + 2752#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 2752#64) (n := 400) (k := 992) (b' := fsp + 3152#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 3152#64) (n := 544) (k := 448) (b' := fsp + 3696#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 3696#64) (n := 128) (k := 320) (b' := fsp + 3824#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 3824#64) (n := 8) (k := 312) (b' := fsp + 3832#64) rfl (by bv_omega) (by decide),
          ProofLib.memRegion_split' (b := fsp + 3832#64) (n := 24) (k := 288) (b' := fsp + 3856#64) rfl (by bv_omega) (by decide)]
      exact Entails.of_eq (by ac_rfl)
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
      (resultV1RecvAt A (F := F) outA (.error (.err err)) ∗
        ((selfA ↦₆₄ polyEncoderTagVal st.sending_ct1) ∗ memRegion (selfA + 8#64) 384 ∗
          memRegion (selfA + 392#64) 8 ∗ wordsAt (selfA + 400#64) c_uc.toList ∗
          memRegion (selfA + 528#64) 400) ∗
        A.pool ∗ Rest) by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono hstk4144
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hself))))
  subst hfsp
  refine SepWP.weaken_pre hP2' ?_
  refine SepWP.mono
    (ct1Sampled_epilogue_19324_placed s0 s2 _ hsp0_align hpc2 hrun2 hsp2
      (htr2.trans (htr1.trans htr))) ?_
  intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by ac_rfl)), hsp_f, hcs_f, htr_f⟩

/-! ## 3. Path 5b (`outMsg = some decoded, recv_ek = .ok uc_ek, ack = false`: `+11496 -> s0.x30`) -/

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
        TraceCalleeSaved sf s_in) := by
  rw [copyScratchStackAt_eq_wb0 fsp sc]
  refine SepWP.weaken_pre (Entails.of_eq (show _ =
    wordsAt (fsp + 1856#64) c_ek.toList ∗ memRegion (fsp + 3856#64) 128 ∗
    ((fsp + 176#64) ↦₆₄ sc.wb0) ∗ (copyScratchStackWithoutWb0At fsp sc ∗ Rest) by ac_rfl)) ?_
  refine SepWP.mono
    (ct1Sampled_recv_ek_ok_copy_placed s_in fsp sc.wb0 c_ek _ hw0 hfsp_align hpc hrun hsp) ?_
  intro sf Pf _ _ ⟨hPf, hrest⟩
  refine ⟨Entails.trans hPf ?_, hrest⟩
  rw [← copyScratchStackAt_wb0_reconstruct fsp sc c_ek.w1]
  exact Entails.of_eq (by ac_rfl)

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
        (Pf ⊢ Rest) ∧
        sf = s_in.setPC ((blkPl_332).base + 15760#64)) := by
  dsimp only [lsProg_332, BitVec.ofNat_eq_ofNat] at hpc ⊢
  wp_step
  refine SepWP.done (by simp only [arm64_norm]) (by simpa only [arm64_norm] using hrun) ?_
  exact ⟨Entails.refl _, rfl⟩

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  ct1Sampled_path_none_ack_placed
  ct1Sampled_some_to_11528_placed
  ct1Sampled_path_some_err_placed
  ct1Sampled_recv_ek_ok_copy_sc_placed
  ct1Sampled_ok_branch_no_ack_eq_placed
)

end CryptoVerification.SpqrV1.States.Recv
