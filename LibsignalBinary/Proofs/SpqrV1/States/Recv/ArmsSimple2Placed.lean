/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple2
public import LibsignalBinary.Proofs.SpqrV1.States.Recv.DefsPlaced
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.States.FromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.States.Recv.ArmsSimple1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch0Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.CodeSymFetch1Placed
import LibsignalBinary.Proofs.SpqrV1.States.Recv.DispatchPlaced
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<States>::recv` (Block `332`): Relocatable `HeaderReceived` Arm

Relocatable `[LibsignalPlacement]` proof of the `States.headerReceived` arm (`tag = 8#64`, `+2268`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace LibsignalBinary.Proofs.SpqrV1.States.Recv

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.GF.UnacceleratedMul
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.Poly.AddChunk
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Top
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.States.Leaves.RecvHdrChunk
open CryptoVerification.SpqrV1.States.RecvCt2Chunk
open CryptoVerification.SpqrV1.States.Recv
open CryptoVerification.CodeLayout

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff CryptoVerification.blkPC_332
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

theorem simple_seq_clean_lscl [LibsignalPlacement] {prog : Program} {mid target : BitVec 64}
    {s : State} {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem → Q sm → SepWP prog target sm P_mid post) :
    SepWP prog target s P post :=
  CryptoVerification.sepWP_seq_lscl hcl (SepWP.mono h1 fun sm Pm hpc hrun ⟨hPm, hQ⟩ hcl' =>
    SepWP.weaken_pre hPm (h2 sm hpc hrun hcl' hQ))

/-! ## `States.headerReceived` (`tag = 8#64`, `+2268` / `0x55d30`) -/

theorem headerReceived_memcpy_2268_2284_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s : State) (fsp selfA : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2268#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx1 : s.readReg64 .x1 = selfA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 2284#64) s
      (stackAt fsp allocHookStack ∗ memRegion (fsp + 1856#64) 480 ∗ chunkedHeaderReceivedAt A (selfA + 8#64) st ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ stackAt fsp allocHookStack ∗ chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗
              memRegion (selfA + 8#64) 480 ∗ Frame) ∧
        sm.sp = fsp ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x24 = s.readReg64 .x24 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧ TraceCalleeSaved sm s) := by
  subst hsp hx1
  have hpre : stackAt s.sp allocHookStack ∗ memRegion (s.sp + 1856#64) 480 ∗
      chunkedHeaderReceivedAt A (s.readReg64 .x1 + 8#64) st ∗ Frame ⊢
      ((∃∗ bs : List (BitVec 8), ⌜bs.length = 480⌝ ∗
          (((s.readReg64 .x1 + 8#64) ↦ₛ bs) ∗ relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs)) ∗
       stackAt s.sp allocHookStack) ∗ (memRegion (s.sp + 1856#64) 480 ∗ Frame) :=
    Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (Relocatable.of_chunkedHeaderReceivedAt A st (s.readReg64 .x1 + 8#64)))))
      (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre ?_; apply sepWP_intro_ex_pure; intro bs hbs
  have hmemcpy_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrMemcpySym) sessionMemcpySpec :=
    spqr_hook_ok_of_mem (sym := spqrMemcpySym) hmemcpy
  simp only [sessionMemcpySpec, allocHookStack] at hmemcpy_raw ⊢; rw [← hbs]
  dsimp only [lsProg_332, lsρ, spqrMemcpySym] at hmemcpy_raw ⊢
  wp_steps; wp_call hmemcpy_raw (s.sp + 1856#64, s.readReg64 .x1 + 8#64, bs)
  have hpost : stackAt s.sp 4096 ∗ ((s.sp + 1856#64) ↦ₛ bs) ∗ ((s.readReg64 .x1 + 8#64) ↦ₛ bs) ∗
      relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs ∗ Frame ⊢
      stackAt s.sp 4096 ∗ chunkedHeaderReceivedAt A (s.sp + 1856#64) st ∗
        memRegion (s.readReg64 .x1 + 8#64) bs.length ∗ Frame := by
    refine Entails.trans (Entails.of_eq (show _ = stackAt s.sp 4096 ∗
      (((s.sp + 1856#64) ↦ₛ bs) ∗ relocatedHeap (fun a => chunkedHeaderReceivedAt A a st) bs) ∗
      ((s.readReg64 .x1 + 8#64) ↦ₛ bs) ∗ Frame by ac_rfl)) ?_
    exact sepConj_mono_right (sepConj_mono
      (relocatedHeap_recompose (fun a => chunkedHeaderReceivedAt A a st) bs (s.sp + 1856#64))
      (sepConj_mono_left (pointsToBytes_entails_memRegion (s.readReg64 .x1 + 8#64) bs)))
  refine align_pre (Entails.trans (Entails.of_eq (by ac_rfl)) hpost) ?_; wp_done

set_option maxHeartbeats 1600000 in
theorem headerReceived_ok_step_2284_18996_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} (s : State) (fsp msgA : BitVec 64)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch msg_epoch : BitVec 64)
    (w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 : BitVec 64)
    (w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 : BitVec 64)
    (w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 : BitVec 64)
    (u224 u232 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504 : BitVec 64)
    (u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488 : BitVec 64)
    (Frame : SepProp) (hle : ¬ (msg_epoch > st_epoch)) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 18996#64) s
      (headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
       (msgA ↦₆₄ msg_epoch) ∗
       epilogueRecvStackPartA488 fsp u224 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504 ∗
       ((fsp + 232#64) ↦₆₄ u232) ∗
       epilogueRecvStackPartB fsp u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488 ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ headerReceivedStackWords fsp w0 w1 w2 w3 w4 w5 w6 w7 w8 st_epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
          (msgA ↦₆₄ msg_epoch) ∗
          epilogueRecvStackPartA488 fsp 8#64 w7 w13 w12 w10 w5 w4 w11 st_epoch w8 w3 w2 w6 ∗
          ((fsp + 232#64) ↦₆₄ noneCap) ∗
          epilogueRecvStackPartB fsp w58 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56 ∗ Frame) ∧
        sm.sp = fsp ∧
        sm.readReg64 .x0 = w39 ∧ sm.readReg64 .x1 = w0 ∧ sm.readReg64 .x2 = w57 ∧ sm.readReg64 .x3 = w29 ∧
        sm.readReg64 .x4 = w49 ∧ sm.readReg64 .x5 = w48 ∧ sm.readReg64 .x6 = w40 ∧ sm.readReg64 .x7 = w38 ∧
        sm.readReg64 .x8 = w1 ∧ sm.readReg64 .x9 = w43 ∧ sm.readReg64 .x10 = w35 ∧ sm.readReg64 .x11 = w34 ∧
        sm.readReg64 .x12 = w33 ∧ sm.readReg64 .x13 = w52 ∧ sm.readReg64 .x14 = w53 ∧ sm.readReg64 .x15 = w36 ∧
        sm.readReg64 .x16 = w55 ∧ sm.readReg64 .x17 = w45 ∧ sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = w59 ∧ sm.readReg64 .x21 = w42 ∧ sm.readReg64 .x22 = w51 ∧ sm.readReg64 .x23 = w15 ∧
        sm.readReg64 .x24 = w31 ∧ sm.readReg64 .x25 = w32 ∧ sm.readReg64 .x26 = w47 ∧ sm.readReg64 .x27 = w16 ∧
        sm.readReg64 .x28 = w37 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧ sm.readReg64 .x30 = w41 ∧
        TraceCalleeSaved sm s) := by
  have hule : BitVec.ule msg_epoch st_epoch = true := ule_true_of_not_gt hle
  dsimp only [lsProg_332, headerReceivedStackWords,
    wordsAtOff, epilogueRecvStackPartA488, epilogueRecvStackPartB, noneCap, Nat.reduceAdd, BitVec.ofNat_eq_ofNat] at hpc ⊢
  subst hsp hx24; wp_steps; wp_done

set_option maxHeartbeats 1600000 in
theorem states_recv_headerReceived_ok_2284_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hmemcpy : HookSat (Rust.withPanics ext) spqrMemcpySym sessionMemcpySpec)
    (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hle : ¬ (msg.epoch > st.uc.epoch)) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 1856 ∗
       chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.headerReceived st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.headerReceived st).recv K msg = .ok ⟨none, .headerReceived st⟩ := by
    simp only [States.recv, Chunked.SendCt.HeaderReceived.epoch, Unchunked.SendCt.HeaderReceived.epoch, hle, ↓reduceIte]
  rw [hrecv, memRegion_1856_split_224_288 fsp]
  have hpre : stackAt fsp statesRecvCalleeStackX ∗
      (memRegion fsp 224 ∗ existsWordsAtOff fsp 36 224 ∗ memRegion (fsp + 512#64) 1344) ∗
      chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
      statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool ⊢
      (existsWordsWithBytesAtOff fsp (relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek)) 50 1936 ∗
       ((∃∗ g : ThreeVecWords, wordsAtOff fsp (ekSentWordsList g st.uc.epoch) 1856 ∗
           relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch))) ∗
        existsWordsAtOff fsp 36 224)) ∗
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ memRegion (fsp + 512#64) 1344 ∗
       memRegion (fsp + 2336#64) 1808 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) := by
    refine Entails.trans (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (chunkedHeaderReceivedAt_extract_1856 A fsp st)))) (Entails.of_eq (by ac_rfl))
  refine SepWP.weaken_pre hpre ?_
  dsimp only [existsWordsWithBytesAtOff, existsWordsAtOff, wordsBytes, HAppend.hAppend, Append.append, List.append,
    Nat.reduceAdd, BitVec.ofNat_eq_ofNat]
  apply sepWP_intro_ex_nest; intro w10; apply sepWP_intro_ex_nest; intro w11; apply sepWP_intro_ex_nest; intro w12; apply sepWP_intro_ex_nest; intro w13; apply sepWP_intro_ex_nest; intro w14; apply sepWP_intro_ex_nest; intro w15
  apply sepWP_intro_ex_nest; intro w16; apply sepWP_intro_ex_nest; intro w17; apply sepWP_intro_ex_nest; intro w18; apply sepWP_intro_ex_nest; intro w19; apply sepWP_intro_ex_nest; intro w20; apply sepWP_intro_ex_nest; intro w21
  apply sepWP_intro_ex_nest; intro w22; apply sepWP_intro_ex_nest; intro w23; apply sepWP_intro_ex_nest; intro w24; apply sepWP_intro_ex_nest; intro w25; apply sepWP_intro_ex_nest; intro w26; apply sepWP_intro_ex_nest; intro w27
  apply sepWP_intro_ex_nest; intro w28; apply sepWP_intro_ex_nest; intro w29; apply sepWP_intro_ex_nest; intro w30; apply sepWP_intro_ex_nest; intro w31; apply sepWP_intro_ex_nest; intro w32; apply sepWP_intro_ex_nest; intro w33
  apply sepWP_intro_ex_nest; intro w34; apply sepWP_intro_ex_nest; intro w35; apply sepWP_intro_ex_nest; intro w36; apply sepWP_intro_ex_nest; intro w37; apply sepWP_intro_ex_nest; intro w38; apply sepWP_intro_ex_nest; intro w39
  apply sepWP_intro_ex_nest; intro w40; apply sepWP_intro_ex_nest; intro w41; apply sepWP_intro_ex_nest; intro w42; apply sepWP_intro_ex_nest; intro w43; apply sepWP_intro_ex_nest; intro w44; apply sepWP_intro_ex_nest; intro w45
  apply sepWP_intro_ex_nest; intro w46; apply sepWP_intro_ex_nest; intro w47; apply sepWP_intro_ex_nest; intro w48; apply sepWP_intro_ex_nest; intro w49; apply sepWP_intro_ex_nest; intro w50; apply sepWP_intro_ex_nest; intro w51
  apply sepWP_intro_ex_nest; intro w52; apply sepWP_intro_ex_nest; intro w53; apply sepWP_intro_ex_nest; intro w54; apply sepWP_intro_ex_nest; intro w55; apply sepWP_intro_ex_nest; intro w56; apply sepWP_intro_ex_nest; intro w57
  apply sepWP_intro_ex_nest; intro w58; apply sepWP_intro_ex_nest; intro w59
  rw [sepConj_assoc (relocatedHeap _ _), sepConj_left_comm (relocatedHeap _ _)]
  apply sepWP_intro_ex; intro g
  apply sepWP_intro_ex; intro u224; apply sepWP_intro_ex; intro u232; apply sepWP_intro_ex; intro u240; apply sepWP_intro_ex; intro u248; apply sepWP_intro_ex; intro u256; apply sepWP_intro_ex; intro u264
  apply sepWP_intro_ex; intro u272; apply sepWP_intro_ex; intro u280; apply sepWP_intro_ex; intro u288; apply sepWP_intro_ex; intro u296; apply sepWP_intro_ex; intro u304; apply sepWP_intro_ex; intro u312
  apply sepWP_intro_ex; intro u320; apply sepWP_intro_ex; intro u328; apply sepWP_intro_ex; intro u336; apply sepWP_intro_ex; intro u344; apply sepWP_intro_ex; intro u352; apply sepWP_intro_ex; intro u360
  apply sepWP_intro_ex; intro u368; apply sepWP_intro_ex; intro u376; apply sepWP_intro_ex; intro u384; apply sepWP_intro_ex; intro u392; apply sepWP_intro_ex; intro u400; apply sepWP_intro_ex; intro u408
  apply sepWP_intro_ex; intro u416; apply sepWP_intro_ex; intro u424; apply sepWP_intro_ex; intro u432; apply sepWP_intro_ex; intro u440; apply sepWP_intro_ex; intro u448; apply sepWP_intro_ex; intro u456
  apply sepWP_intro_ex; intro u464; apply sepWP_intro_ex; intro u472; apply sepWP_intro_ex; intro u480; apply sepWP_intro_ex; intro u488; apply sepWP_intro_ex; intro u496; apply sepWP_intro_ex; intro u504
  rw [emp_sepConj]; unfold messageAt
  have hstep1 := headerReceived_ok_step_2284_18996_placed (ext := ext) s fsp msgA
    g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0 g.auth.v2.w1 g.auth.v2.w2
    st.uc.epoch msg.epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
    u224 u232 u288 u296 u336 u352 u368 u376 u384 u408 u432 u456 u496 u504
    u248 u256 u264 u272 u280 u304 u312 u320 u328 u344 u360 u392 u400 u416 u424 u440 u448 u464 u472 u480 u488
    (((fsp + 240#64) ↦₆₄ u240) ∗
     relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
     relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗
     stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗ memRegion (fsp + 512#64) 1344 ∗
     memRegion (fsp + 2336#64) 1808 ∗ statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
     memRegion selfA chunkedStatesSize ∗ statesRecvRoPlacedAt ∗ A.pool)
    hle hfsp_align hpc hrun hsp hx24
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (SepWP.weaken_pre (Entails.of_eq ?_) hstep1) ?_
  · dsimp only [headerReceivedStackWords, words50List, ekSentWordsList, vecWordsList, ct2SentWordsList, authWordsList,
      wordsBytes, HAppend.hAppend, Append.append, List.append, wordsAtOff, epilogueRecvStackPartA488, epilogueRecvStackPartB,
      Nat.reduceAdd, BitVec.ofNat_eq_ofNat]; ac_rfl
  · intro s1 hpc1 hrun1 ⟨hsp1, hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx8_1, hx9_1,
      hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx19_1, hx20_1, hx21_1, hx22_1,
      hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, _, hx30_1, htr1⟩
    rw [hx19] at hx19_1
    have htr10 : TraceCalleeSaved s1 s0 := htr1.trans htr
    have hsp10 : s1.sp = s0.sp - 4240#64 := by rw [hsp1, hfsp_eq]
    have hexit := epilogue_18996_exit_none_488_placed (A := A) hmemcpy s0 s1 outA
      8#64 u240 g.auth.v2.w1 w13 w12 w10 g.auth.v1.w2 g.auth.v1.w1 w11 st.uc.epoch g.auth.v2.w2 g.auth.v1.w0 g.v1.w2 g.auth.v2.w0
      w58 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56
      (relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
       relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ∗
       memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
      hsp0_align hpc1 hrun1 hsp10 hx19_1 htr10
    dsimp only at hexit; rw [← hfsp_eq] at hexit
    refine SepWP.mono (SepWP.weaken_pre ?_ hexit) ?_
    · have hstk3632 := headerReceived_stack_entails_3632 fsp
        g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0 g.auth.v2.w1 g.auth.v2.w2
        st.uc.epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
      unfold messageAt
      refine Entails.trans (Entails.of_eq (show _ =
        (memRegion (fsp + 512#64) 1344 ∗
         headerReceivedStackWords fsp g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0 g.auth.v2.w1 g.auth.v2.w2 st.uc.epoch w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59 ∗
         memRegion (fsp + 2336#64) 1808) ∗
        (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 224 ∗
         epilogueRecvStackPartA488 fsp 8#64 g.auth.v2.w1 w13 w12 w10 g.auth.v1.w2 g.auth.v1.w1 w11 st.uc.epoch g.auth.v2.w2 g.auth.v1.w0 g.v1.w2 g.auth.v2.w0 ∗
         ((fsp + 232#64) ↦₆₄ noneCap) ∗ ((fsp + 240#64) ↦₆₄ u240) ∗
         epilogueRecvStackPartB fsp w58 u256 w18 w21 w27 w25 w30 w28 w26 w19 w22 w20 w23 w44 w14 w17 w50 w24 w46 w54 w56 ∗
         statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
         (relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
          relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59)) ∗
          memRegion selfA chunkedStatesSize ∗
          ((msgA ↦₆₄ msg.epoch) ∗ messagePayloadAt spqrPolyApi msgA msg.payload) ∗
          statesRecvRoPlacedAt ∗ A.pool)) by ac_rfl))
        (Entails.trans (sepConj_mono_left hstk3632) (Entails.of_eq (by ac_rfl)))
    · intro sf Pf _ _ ⟨hPf, hsp_f, hcs_f, htr_f⟩
      rw [hx0_1, hx1_1, hx2_1, hx3_1, hx4_1, hx5_1, hx6_1, hx7_1, hx8_1, hx9_1,
          hx10_1, hx11_1, hx12_1, hx13_1, hx14_1, hx15_1, hx16_1, hx17_1, hx20_1, hx21_1,
          hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hx30_1] at hPf
      have hrec := headerReceived_out_recompose A outA st g w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59
      refine ⟨Entails.trans hPf (Entails.trans (Entails.of_eq (show _ =
        (epilogueRecvOutPartA outA 8#64 g.v1.w0 g.v1.w1 g.v1.w2 g.auth.v1.w0 g.auth.v1.w1 g.auth.v1.w2 g.auth.v2.w0
           g.auth.v2.w1 g.auth.v2.w2 st.uc.epoch w10 w11 w12 w13
           w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w48 w49 w52 w53 ∗
         epilogueRecvOutPartB488 outA w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31
           w44 w45 w46 w47 w50 w51 w54 w55 w56 w57 w58 w59 ∗
         memRegion (outA + 488#64) 440 ∗ optEpochSecretAt A (outA + 928#64) none ∗
         relocatedHeap (fun dst => unchunkedHeaderReceivedAt A dst st.uc) (wordsBytes (ekSentWordsList g st.uc.epoch)) ∗
         relocatedHeap (fun dst => polyDecoderAt A dst st.receiving_ek) (wordsBytes (words50List w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 w25 w26 w27 w28 w29 w30 w31 w32 w33 w34 w35 w36 w37 w38 w39 w40 w41 w42 w43 w44 w45 w46 w47 w48 w49 w50 w51 w52 w53 w54 w55 w56 w57 w58 w59))) ∗
        (memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
         statesRecvRoPlacedAt ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) by ac_rfl))
        (sepConj_mono_left hrec)), hsp_f, hcs_f, htr_f⟩

theorem headerReceived_err_step_2284_2340_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s : State) (fsp outA msgA st_epoch msg_epoch c1 p1 v_out0 v_out16 : BitVec 64) (b_out8 : BitVec 8)
    (Frame : SepProp) (hgt : msg_epoch > st_epoch) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 2340#64) s
      (((outA ↦₆₄ v_out0) ∗ ((outA + 8#64) ↦₈ b_out8) ∗ ((outA + 16#64) ↦₆₄ v_out16)) ∗
       ((fsp + 1856#64) ↦₆₄ c1) ∗ ((fsp + 1864#64) ↦₆₄ p1) ∗ ((fsp + 1928#64) ↦₆₄ st_epoch) ∗
       vecCapPtrDealloc A c1 p1 ∗ (msgA ↦₆₄ msg_epoch) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((outA ↦₆₄ noneCap) ∗ ((outA + 8#64) ↦₈ 4#8) ∗ ((outA + 16#64) ↦₆₄ msg_epoch)) ∗
          ((fsp + 1856#64) ↦₆₄ c1) ∗ ((fsp + 1864#64) ↦₆₄ p1) ∗ ((fsp + 1928#64) ↦₆₄ st_epoch) ∗
          (msgA ↦₆₄ msg_epoch) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc
  simp only [rustDeallocSpec, allocHookStack] at hdealloc_raw ⊢
  have hule : BitVec.ule msg_epoch st_epoch = false := ule_false_of_gt hgt
  dsimp only [lsProg_332, lsρ, spqrDeallocSym, vecCapPtrDealloc, noneCap, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  subst hsp hx19 hx24
  by_cases hc1 : (c1 == 0#64) = true <;> simp only [hc1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
  · wp_steps; wp_apply; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

theorem headerReceived_err_step_2340_2360_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s : State) (fsp c2 p2 : BitVec 64) (Frame : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2340#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 2360#64) s
      (((fsp + 1880#64) ↦₆₄ c2) ∗ ((fsp + 1888#64) ↦₆₄ p2) ∗
       vecCapPtrDealloc A c2 p2 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1880#64) ↦₆₄ c2) ∗ ((fsp + 1888#64) ↦₆₄ p2) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc
  simp only [rustDeallocSpec, allocHookStack] at hdealloc_raw ⊢
  dsimp only [lsProg_332, lsρ, spqrDeallocSym, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  subst hsp
  by_cases hc2 : (c2 == 0#64) = true <;> simp only [hc2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
  · wp_steps; wp_apply; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

theorem headerReceived_err_step_2360_2380_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (s : State) (fsp c3 p3 : BitVec 64) (Frame : SepProp) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2360#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 2380#64) s
      (((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
       vecCapPtrDealloc A c3 p3 ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ A.pool ∗ stackAt fsp allocHookStack ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  have hdealloc_raw : subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsρ spqrDeallocSym) (rustDeallocSpec A) :=
    spqr_hook_ok_of_mem (sym := spqrDeallocSym) hdealloc
  simp only [rustDeallocSpec, allocHookStack] at hdealloc_raw ⊢
  dsimp only [lsProg_332, lsρ, spqrDeallocSym, vecCapPtrDealloc, BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw ⊢
  subst hsp
  by_cases hc3 : (c3 == 0#64) = true <;> simp only [hc3, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
  · wp_steps; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done
  · wp_steps; wp_apply; refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

theorem headerReceived_err_step_2380_19324_placed [LibsignalPlacement]
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
    (s : State) (fsp : BitVec 64) (vecs : List (List Pt)) (hvecs : vecs.length = NUM_POLYS)
    (Frame : SepProp) (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2380#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp) :
    SepWP (lsProg_332 (Rust.withPanics ext)) ((blkPl_332).base + 19324#64) s
      (vecPtListOf A (fsp + 1936#64) vecs ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame)
      (fun sm Pm =>
        (Pm ⊢ memRegion (fsp + 1936#64) polyArrayBytes ∗ A.pool ∗ stackAt fsp dropGluePoly16Stack ∗ Frame) ∧
        sm.sp = fsp ∧ TraceCalleeSaved sm s) := by
  dsimp only [lsProg_332] at hdrop ⊢
  subst hsp
  refine CryptoVerification.sepWP_seq_lscl hcl (mid := lsmpl.base 264) ?_
  wp_steps
  refine SepWP.done rfl hrun (fun hcl1 => ?_)
  have hdrop_raw := subroutine_ok_withMemEq_of_withLsCodeLoaded hdrop hcl1
  dsimp only [withMemEq, dropGlueSortedSetPt16Spec] at hdrop_raw
  wp_call hdrop_raw ⟨s.sp + 1936#64, vecs⟩
  wp_steps
  refine align_pre (Entails.of_eq (by ac_rfl)) ?_; wp_done

set_option maxHeartbeats 1200000 in
theorem states_recv_headerReceived_err_2284_placed [LibsignalPlacement]
    {A : RustAlloc} {F : ShaCompress} {K : MlKem} {ext : String → Option (State → State)}
    (hdealloc : HookSat (Rust.withPanics ext) spqrDeallocSym (rustDeallocSpec A))
    (hdrop : subroutine_ok (lsProg_332 (Rust.withPanics ext)) (lsmpl.base 264)
      (withLsCodeLoaded lsmpl (dropGlueSortedSetPt16Spec A)))
    (s0 s : State) (fsp outA selfA msgA : BitVec 64)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hgt : msg.epoch > st.uc.epoch) (hfsp_eq : fsp = s0.sp - 4240#64)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true) (hfsp_align : (fsp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_332).base + 2284#64)
    (hrun : s.status = .Running) (hsp : s.sp = fsp)
    (hx19 : s.readReg64 .x19 = outA) (hx24 : s.readReg64 .x24 = msgA) (htr : TraceCalleeSaved s s0) :
    SepWP (lsProg_332 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (stackAt fsp statesRecvCalleeStackX ∗ memRegion fsp 1856 ∗
       chunkedHeaderReceivedAt A (fsp + 1856#64) st ∗ memRegion (fsp + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
      (fun sf Pf =>
        (Pf ⊢ resultV1RecvAt A (F := F) outA ((States.headerReceived st).recv K msg) ∗
          memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗
          statesRecvRoPlacedAt ∗ A.pool ∗ stackAt s0.sp statesRecvStackX) ∧
        sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧ sf.trace = s0.trace) := by
  have hrecv : (States.headerReceived st).recv K msg = .error (.err (.epochOutOfRange msg.epoch)) := by
    simp only [States.recv, Chunked.SendCt.HeaderReceived.epoch, Unchunked.SendCt.HeaderReceived.epoch, hgt, ↓reduceIte]
  rw [hrecv, memRegion_out_960_split_err outA, stackAt_statesRecvCallee_eq_allocHook fsp]
  refine SepWP.fold (chunkedHeaderReceivedAt_1856_entails_err A fsp st) (by sep_focus) ?_
  unfold messageAt; wp_pull_exists; rename_i v_out16 b_out8 v_out0 g12 c3 p3 vecs
  wp_focus_pure; intro hvecs
  have hstep1 := headerReceived_err_step_2284_2340_placed hdealloc s fsp outA msgA st.uc.epoch msg.epoch
    g12.v1.cap g12.v1.ptr v_out0 v_out16 b_out8
    (memRegion (outA + 9#64) 7 ∗ memRegion (outA + 24#64) 936 ∗ memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 1856 ∗
     memRegion (fsp + 1872#64) 8 ∗ ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
     memRegion (fsp + 1896#64) 8 ∗ ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
     memRegion (fsp + 1920#64) 8 ∗ vecCapPtrDealloc A g12.v2.cap g12.v2.ptr ∗ vecCapPtrDealloc A c3 p3 ∗
     vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
     statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt)
    hgt hfsp_align hpc hrun hsp hx19 hx24
  refine simple_seq_clean_lscl hcl (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep1) ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, htr1⟩
  refine SepWP.fold (err_epochOutOfRange_entails_resultV1RecvAt A (F := F) outA msg.epoch) (by sep_focus) ?_
  have hstep2 := headerReceived_err_step_2340_2360_placed hdealloc s1 fsp g12.v2.cap g12.v2.ptr
    (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
     ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
     (msgA ↦₆₄ msg.epoch) ∗ memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 1856 ∗
     memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗
     ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗ memRegion (fsp + 1920#64) 8 ∗
     vecCapPtrDealloc A c3 p3 ∗ vecPtListOf A (fsp + 1936#64) vecs ∗
     memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
     statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt)
    hfsp_align hpc1 hrun1 hsp1
  refine simple_seq_clean_lscl hcl1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep2) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, htr2⟩
  have hstep3 := headerReceived_err_step_2360_2380_placed hdealloc s2 fsp c3 p3
    (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
     ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
     ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
     (msgA ↦₆₄ msg.epoch) ∗ memRegion (fsp - 19552#64) 15456 ∗ memRegion fsp 1856 ∗
     memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗ memRegion (fsp + 1920#64) 8 ∗
     vecPtListOf A (fsp + 1936#64) vecs ∗ memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
     statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt)
    hfsp_align hpc2 hrun2 hsp2
  refine simple_seq_clean_lscl hcl2 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep3) ?_
  intro s3 hpc3 hrun3 hcl3 ⟨hsp3, htr3⟩
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_allocHook fsp).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_dropGluePoly16 fsp)) (by sep_focus) ?_
  have hstep4 := headerReceived_err_step_2380_19324_placed hdrop s3 fsp vecs hvecs.1
    (memRegion (fsp - 19552#64) 15424 ∗
     resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
     ((fsp + 1856#64) ↦₆₄ g12.v1.cap) ∗ ((fsp + 1864#64) ↦₆₄ g12.v1.ptr) ∗ ((fsp + 1928#64) ↦₆₄ st.uc.epoch) ∗
     ((fsp + 1880#64) ↦₆₄ g12.v2.cap) ∗ ((fsp + 1888#64) ↦₆₄ g12.v2.ptr) ∗
     ((fsp + 1904#64) ↦₆₄ c3) ∗ ((fsp + 1912#64) ↦₆₄ p3) ∗
     (msgA ↦₆₄ msg.epoch) ∗ memRegion fsp 1856 ∗
     memRegion (fsp + 1872#64) 8 ∗ memRegion (fsp + 1896#64) 8 ∗ memRegion (fsp + 1920#64) 8 ∗
     memRegion (fsp + 2320#64) 16 ∗ memRegion (fsp + 2336#64) 1808 ∗
     statesRecvSavedCells s0 ∗ memRegion selfA chunkedStatesSize ∗
     messagePayloadAt spqrPolyApi msgA msg.payload ∗ statesRecvRoPlacedAt)
    hcl3 hfsp_align hpc3 hrun3 hsp3
  refine CryptoVerification.SpqrV1.States.Recv.seq_clean (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hstep4) ?_
  intro s4 hpc4 hrun4 ⟨hsp4, htr4⟩
  refine SepWP.fold (Entails.of_eq (stackAt_statesRecvCallee_eq_dropGluePoly16 fsp).symm) (by sep_focus) ?_
  refine SepWP.fold (headerReceived_err_stack_combine fsp g12 c3 p3 st.uc.epoch) (by sep_focus) ?_
  have htr40 : TraceCalleeSaved s4 s0 := htr4.trans (htr3.trans (htr2.trans (htr1.trans htr)))
  have hsp40 : s4.sp = s0.sp - 4240#64 := by rw [hsp4, hfsp_eq]
  have hepil := states_recv_epilogue_19324_placed (ext := ext) s0 s4
    (resultV1RecvAt A (F := F) outA (.error (.err (.epochOutOfRange msg.epoch))) ∗
     memRegion selfA chunkedStatesSize ∗ messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool)
    hsp0_align (by rwa [lsmpl_base_332_eq]) hrun4 hsp40 htr40
  rw [← hfsp_eq] at hepil
  refine SepWP.mono (SepWP.weaken_pre (Entails.of_eq (by unfold messageAt; ac_rfl)) hepil) ?_
  intro sf Pf _ _ ⟨hPf, hspf, hcs, htrf⟩
  exact ⟨Entails.trans hPf (Entails.of_eq (by unfold messageAt; ac_rfl)), hspf, hcs, htrf⟩

theorem states_recv_headerReceived_placed_ok_ext [LibsignalPlacement]
    (A : RustAlloc) (F : ShaCompress) (K : MlKem) (ext : String → Option (State → State))
    (hC : StatesRecvPlacedContracts A F K ext)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F))
    (msg : Message spqrPolyApi) :
    subroutine_ok (lsProg_332 (Rust.withPanics ext))
      (lsmpl.base 332)
      (withLsCodeLoaded lsmpl (statesRecvVariantPlacedSpec A F K (.headerReceived st) msg)) := by
  refine subroutine_ok_statesRecvVariantPlacedSpec_of_sepWP (.headerReceived st) msg ?_
  intro outA selfA msgA s0 hcl hpc0 hrun0 hsp0_align hx0 hx1 hx2 _
  have hfsp_align : ((s0.sp - 4240#64) &&& 15#64 == 0#64) = true := spAligned_sub s0.sp 4240#64 hsp0_align (by decide)
  have hpro := states_recv_prologue_placed (ext := ext) s0
    (memRegion outA v1RecvSize ∗ chunkedStatesAt A selfA (.headerReceived st) ∗
     messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) hsp0_align hpc0 hrun0
  refine simple_seq_clean_lscl hcl hpro ?_
  intro s1 hpc1 hrun1 hcl1 ⟨hsp1, hx0_1, hx1_1, hx2_1, _, hx29_1, htr1⟩
  rw [hx0] at hx0_1; rw [hx1] at hx1_1; rw [hx2] at hx2_1; rw [chunkedStatesAt_headerReceived_unfold]
  have hdisp := states_recv_dispatch_placed (ext := ext) s1 (s0.sp - 4240#64) selfA 8#64
    (chunkedHeaderReceivedAt A (selfA + 8#64) st ∗ memRegion (selfA + 488#64) 440 ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 4144 ∗ statesRecvSavedCells s0)
    (by unfold ValidStatesTag; decide) hpc1 hrun1 hsp1 hx1_1
  dsimp only [statesRecvArmOffset] at hdisp
  refine simple_seq_clean_lscl hcl1 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hdisp) ?_
  intro s2 hpc2 hrun2 hcl2 ⟨hsp2, _, hx1_2, _, _, _, _, hx19_2, _, hx24_2, _, _, htr2⟩
  rw [hx0_1] at hx19_2; rw [hx2_1] at hx24_2
  rw [lsmpl_base_332_eq] at hpc2
  rw [memRegion_4144_split_1856_480 (s0.sp - 4240#64), stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
  have hmc := headerReceived_memcpy_2268_2284_placed (A := A) hC.hmemcpy_sat s2 (s0.sp - 4240#64) selfA st
    ((selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 488#64) 440 ∗ statesRecvRoPlacedAt ∗
     memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
     memRegion ((s0.sp - 4240#64) - 19552#64) 15456 ∗ memRegion (s0.sp - 4240#64) 1856 ∗
     memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗ statesRecvSavedCells s0)
    hfsp_align hpc2 hrun2 hsp2 hx1_2
  refine simple_seq_clean_lscl hcl2 (SepWP.weaken_pre (Entails.of_eq (by ac_rfl)) hmc) ?_
  intro s3 hpc3 hrun3 hcl3 ⟨hsp3, hx19_3, hx24_3, _, htr3⟩
  rw [hx19_2] at hx19_3; rw [hx24_2] at hx24_3
  have htr30 : TraceCalleeSaved s3 s0 := htr3.trans (htr2.trans htr1)
  have hself2 :
      stackAt (s0.sp - 4240#64) allocHookStack ∗ chunkedHeaderReceivedAt A (s0.sp - 4240#64 + 1856#64) st ∗
      memRegion (selfA + 8#64) 480 ∗ (selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 488#64) 440 ∗
      statesRecvRoPlacedAt ∗ memRegion outA v1RecvSize ∗ messageAt spqrPolyApi msgA msg ∗ A.pool ∗
      memRegion ((s0.sp - 4240#64) - 19552#64) 15456 ∗
      memRegion (s0.sp - 4240#64) 1856 ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗ statesRecvSavedCells s0 ⊢
      stackAt (s0.sp - 4240#64) statesRecvCalleeStackX ∗ memRegion (s0.sp - 4240#64) 1856 ∗
      chunkedHeaderReceivedAt A (s0.sp - 4240#64 + 1856#64) st ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗
      statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗ memRegion selfA chunkedStatesSize ∗
      messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool := by
    rw [stackAt_statesRecvCallee_eq_allocHook (s0.sp - 4240#64)]
    refine Entails.trans (Entails.of_eq (show _ =
      ((selfA ↦₆₄ 8#64) ∗ memRegion (selfA + 8#64) 480 ∗ memRegion (selfA + 488#64) 440) ∗
      (memRegion ((s0.sp - 4240#64) - 19552#64) 15456 ∗ stackAt (s0.sp - 4240#64) allocHookStack ∗
       memRegion (s0.sp - 4240#64) 1856 ∗
       chunkedHeaderReceivedAt A (s0.sp - 4240#64 + 1856#64) st ∗ memRegion ((s0.sp - 4240#64) + 2336#64) 1808 ∗
       statesRecvSavedCells s0 ∗ memRegion outA v1RecvSize ∗
       messageAt spqrPolyApi msgA msg ∗ statesRecvRoPlacedAt ∗ A.pool) by ac_rfl))
      (Entails.trans (sepConj_mono_left (selfA_headerReceived_entails_memRegion_928 selfA)) (Entails.of_eq (by ac_rfl)))
  refine SepWP.weaken_pre hself2 ?_
  by_cases hgt : msg.epoch > st.uc.epoch
  · exact states_recv_headerReceived_err_2284_placed hC.hdealloc_sat hC.hdrop_pt16 s0 s3 (s0.sp - 4240#64) outA selfA msgA st msg
      hcl3 hgt rfl hsp0_align hfsp_align hpc3 hrun3 hsp3 hx19_3 hx24_3 htr30
  · exact states_recv_headerReceived_ok_2284_placed hC.hmemcpy_sat s0 s3 (s0.sp - 4240#64) outA selfA msgA st msg
      hgt rfl hsp0_align hfsp_align hpc3 hrun3 hsp3 hx19_3 hx24_3 htr30

end LibsignalBinary.Proofs.SpqrV1.States.Recv

namespace CryptoVerification.SpqrV1.States.Recv

export LibsignalBinary.Proofs.SpqrV1.States.Recv (
  simple_seq_clean_lscl
  headerReceived_memcpy_2268_2284_placed
  headerReceived_ok_step_2284_18996_placed
  states_recv_headerReceived_ok_2284_placed
  headerReceived_err_step_2284_2340_placed
  headerReceived_err_step_2340_2360_placed
  headerReceived_err_step_2360_2380_placed
  headerReceived_err_step_2380_19324_placed
  states_recv_headerReceived_err_2284_placed
  states_recv_headerReceived_placed_ok_ext
)

end CryptoVerification.SpqrV1.States.Recv
