/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendDispatch
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived1Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlaced
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves1Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1StepsPlaced
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendHeaderReceived2Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled3Placed
import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendLeaves2Placed
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import ProofLib.SepLogic.WPp

/-!
# Relocatable `<States>::send` Post-Arm Reassembly & Unified 11-Arm Dispatch (Block `427`)

Proves post-arm stack reassembly (`+3068 -> +3196`) and unified 11-arm `<States>::send`
dispatch (`statesSendArmOffset st0 -> +3196`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace CryptoVerification.Cli.SpqrV1.Top.Send

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1
open CryptoVerification.SpqrV1.Top.Send
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [-arm64_norm]
  Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp
  Kdf.HkdfToSliceProof.hsp_add_688_sub_688
  Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-- Shared relocatable post-`States::send` reassembly epilogue (`spqrSendPlacedEntry + 3068#64 -> spqrSendPlacedEntry + 3196#64`). -/
theorem step_send_post_arm_3068_to_3196_placed {F : ShaCompress}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext) {s0 s : State} (sp : BitVec 64)
    (chain : Option ChainPB) (msg : Message spqrPolyApi) (key : Option EpochSecret)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (hvalid : validSendPayload msg.payload)
    (hjoin : SpqrSendJoinStatePlaced sp ext s0 s msg st1)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {ret : BitVec 64} {P Frame : SepProp} {post panicPost : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hP : P = (ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      spqrSendPayloadSlotAt sp ((s.readReg64 .x24).setWidth 8) msg.payload ∗
      spqrSendKeySlotAt A sp (s.readReg64 .x21) (s.readReg64 .x27) key ∗
      chunkedStatesTail920At A (sp + 0x590#64) st1 ∗
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = spqrSendPlacedEntry + 3196#64 →
      sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      sf.readReg64 .x19 = s0.readReg64 .x19 → sf.readReg64 .x20 = chunkedStatesWord0 st1 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = msg.epoch →
      sf.readReg64 .x25 = sp + 0x550#64 → sf.readReg64 .x26 = sp + 0x1260#64 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s0.readReg64 .x28 →
      (sf.readReg64 .x23 = noneCap ↔ chain = none) →
      sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64 →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
          chunkedStatesAt A (sp + 0x190#64) st1 ∗
          memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
          memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
          optEpochSecretRegSlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) key ∗
          messageAt spqrPolyApi (sp + 0x1d70#64) msg) ∗ Frame) post panicPost) :
    SepWPp (spqrSendPlacedProg ext) ret s P post panicPost := by
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  rcases hjoin with ⟨hpc, hrun, hsp, htr, hx19, hx20, hx22, hx25, hx26, hx28, hvregs⟩
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat] at hpc hmemcpy ⊢
  subst hP
  apply of_sepWP_lscro (mid := (blkPl_427).base + 3196#64) hinv
  rw [CryptoVerification.SpqrV1.Top.ChainFrom.optChainPBAt_protoRepr_eq_exists A (sp + 0x60#64) chain]
  simp only [sepExists_sepConj_left]; apply SepWP.exists_elim; intro gChain
  rw [optChainPBAt_eq_word0_rest A gChain (sp + 0x60#64) chain]
  refine SepWP.focus_weaken (optChainPBRestAt_expose_word0_inv A gChain (sp + 0x60#64) chain) (by sep_focus) ?_
  wp_focus_pure; intro hchain_iff
  refine SepWP.focus_weaken (chunkedStatesTail920At_590_entails_reloc A sp st1) (by sep_focus) ?_
  wp_pull_exists; rename_i bs920 sw1 sw2 sw3 bs896
  wp_focus_pure; rintro ⟨hbs920, hlen896⟩
  refine SepWP.focus_weaken (spqrSendPayloadSlotAt_entails_words sp ((s.readReg64 .x24).setWidth 8) msg.payload) (by sep_focus) ?_
  wp_pull_exists; rename_i pw0 pw1 pw2 pw3 pw4 pad32
  wp_focus_pure; rintro ⟨hw24, hpay_rec⟩
  refine SepWP.focus_weaken (spqrSendKeySlotAt_entails_words A sp (s.readReg64 .x21) (s.readReg64 .x27) key) (by sep_focus) ?_
  wp_pull_exists; rename_i kw0 kw1
  rw [memRegion_190_928_split sp, memRegion_530_24_split sp,
      memRegion_1bc0_16_eq_words2 sp, memRegion_1d70_48_split sp]
  wp_pull_exists; wp_steps
  refine call_memcpy_bytes hmemcpy (sp + 0x1b0#64) (sp + 0x5a8#64) hlen896
    (s0 := s0) (sp_call := sp)
    (Frame := ((sp + 0x60#64) ↦₆₄ optChainPBWord0 gChain chain) ∗
      optChainPBRestAt A gChain (sp + 0x60#64) chain ∗
      ((sp + 0x190#64) ↦₆₄ _) ∗ ((sp + 0x198#64) ↦₆₄ _) ∗ ((sp + 0x1a0#64) ↦₆₄ _) ∗ ((sp + 0x1a8#64) ↦₆₄ _) ∗
      ((sp + 0x530#64) ↦₆₄ sw1) ∗ ((sp + 0x538#64) ↦₆₄ sw2) ∗ ((sp + 0x540#64) ↦₆₄ sw3) ∗
      ((sp + 0x550#64) ↦₆₄ pw0) ∗ ((sp + 0x558#64) ↦₆₄ pw1) ∗ ((sp + 0x560#64) ↦₆₄ pw2) ∗ ((sp + 0x568#64) ↦₆₄ pw3) ∗
      ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) ∗ ((sp + 0x580#64) ↦₆₄ kw0) ∗ ((sp + 0x588#64) ↦₆₄ kw1) ∗
      keyWordsDetached A (s.readReg64 .x21) (s.readReg64 .x27) key kw0 kw1 ∗
      ((sp + 0x590#64) ↦₆₄ sw1) ∗ ((sp + 0x598#64) ↦₆₄ sw2) ∗ ((sp + 0x5a0#64) ↦₆₄ sw3) ∗
      relocatedHeap (fun dst => chunkedStatesTail920At A dst st1) bs920 ∗
      ((sp + 0x1bc0#64) ↦₆₄ _) ∗ ((sp + 0x1bc8#64) ↦₆₄ _) ∗ ((sp + 0x1d70#64) ↦₆₄ _) ∗ ((sp + 0x1d78#64) ↦₈ _) ∗
      ((sp + 0x1d79#64) ↦₈ _) ∗ ((sp + 0x1d7a#64) ↦₆₄ _) ∗ ((sp + 0x1d82#64) ↦₆₄ _) ∗ ((sp + 0x1d8a#64) ↦₆₄ _) ∗
      ((sp + 0x1d92#64) ↦₆₄ _) ∗ ((sp + 0x1d9a#64) ↦₁₆ _) ∗ ((sp + 0x1d9c#64) ↦₃₂ _) ∗ Frame)
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    hsp_align (ret_pc := (blkPl_427).base + 3108#64) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm]) (by ac_rfl) ?_
  intro sm hpc_m hrun_m hsp_m htr_m hx19_m hx20_m hx21_m hx22_m _ hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  simp only [arm64_norm, *] at hx19_m hx20_m hx21_m hx22_m hx24_m hx25_m hx26_m hx27_m hx28_m hvregs_m
  wp_steps
  have h568_to_B :
      ((sp + 0x568#64) ↦₆₄ pw3) ∗ ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) ⊢
      ((sp + 0x568#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x56c#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x56e#64) ↦₆₄ (pad32 ++ pw4 ++ pw3.extractLsb' 48 16)) := by
    have h := tail14_formA_eq_formB (sp + 0x568#64) pw3 pw4 pad32
    rw [sp_add_568_add_4 sp, sp_add_568_add_6 sp, sp_add_568_add_8 sp, sp_add_568_add_10 sp] at h
    exact Entails.of_eq h
  refine SepWP.focus_weaken h568_to_B (by sep_focus) ?_; wp_steps
  have h1d92_to_B (dw4 : BitVec 16) (dpad32 : BitVec 32) :
      ((sp + 0x1d92#64) ↦₆₄ pw3) ∗ ((sp + 0x1d9a#64) ↦₁₆ dw4) ∗ ((sp + 0x1d9c#64) ↦₃₂ dpad32) ⊢
      ((sp + 0x1d92#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x1d96#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x1d98#64) ↦₆₄ (dpad32 ++ dw4 ++ pw3.extractLsb' 48 16)) := by
    have h := tail14_formA_eq_formB (sp + 0x1d92#64) pw3 dw4 dpad32
    rw [sp_add_1d92_add_4 sp, sp_add_1d92_add_6 sp, sp_add_1d92_add_8 sp, sp_add_1d92_add_10 sp] at h
    exact Entails.of_eq h
  refine SepWP.focus_weaken (h1d92_to_B _ _) (by sep_focus) ?_; wp_steps
  have h568_to_A :
      ((sp + 0x568#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x56c#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x56e#64) ↦₆₄ (pad32 ++ pw4 ++ pw3.extractLsb' 48 16)) ⊢
      ((sp + 0x568#64) ↦₆₄ pw3) ∗ ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) := by
    have h := (tail14_formA_eq_formB (sp + 0x568#64) pw3 pw4 pad32).symm
    rw [sp_add_568_add_4 sp, sp_add_568_add_6 sp, sp_add_568_add_8 sp, sp_add_568_add_10 sp] at h
    exact Entails.of_eq h
  have h1d92_to_A :
      ((sp + 0x1d92#64) ↦₃₂ pw3.extractLsb' 0 32) ∗
      ((sp + 0x1d96#64) ↦₁₆ pw3.extractLsb' 32 16) ∗
      ((sp + 0x1d98#64) ↦₆₄ (pad32 ++ pw4 ++ pw3.extractLsb' 48 16)) ⊢
      ((sp + 0x1d92#64) ↦₆₄ pw3) ∗ ((sp + 0x1d9a#64) ↦₁₆ pw4) ∗ ((sp + 0x1d9c#64) ↦₃₂ pad32) := by
    have h := (tail14_formA_eq_formB (sp + 0x1d92#64) pw3 pw4 pad32).symm
    rw [sp_add_1d92_add_4 sp, sp_add_1d92_add_6 sp, sp_add_1d92_add_8 sp, sp_add_1d92_add_10 sp] at h
    exact Entails.of_eq h
  refine SepWP.focus_weaken h568_to_A (by sep_focus) ?_
  refine SepWP.focus_weaken h1d92_to_A (by sep_focus) ?_
  have h550_38 :
      ((sp + 0x550#64) ↦₆₄ pw0) ∗ ((sp + 0x558#64) ↦₆₄ pw1) ∗
      ((sp + 0x560#64) ↦₆₄ pw2) ∗ ((sp + 0x568#64) ↦₆₄ pw3) ∗
      ((sp + 0x570#64) ↦₁₆ pw4) ∗ ((sp + 0x572#64) ↦₃₂ pad32) ⊢
      memRegion (sp + 0x550#64) 38 := by
    have h := words_to_memRegion_38 (sp + 0x550#64) pw0 pw1 pw2 pw3 pw4 pad32
    rwa [sp_add_550_add_8 sp,
         show (sp + 0x550#64) + 16#64 = sp + 0x560#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x550#64) + 24#64 = sp + 0x568#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x550#64) + 32#64 = sp + 0x570#64 by rw [BitVec.add_assoc]; rfl,
         show (sp + 0x550#64) + 34#64 = sp + 0x572#64 by rw [BitVec.add_assoc]; rfl] at h
  have hchain_recompose :
      ((sp + 0x60#64) ↦₆₄ optChainPBWord0 gChain chain) ∗
      optChainPBRestAt A gChain (sp + 0x60#64) chain ⊢
      ProtoRepr.optChainPBAt A (sp + 0x60#64) chain := by
    rw [← optChainPBAt_eq_word0_rest A gChain (sp + 0x60#64) chain]
    exact CryptoVerification.SpqrV1.Top.ChainFrom.optChainPBAt_entails_protoRepr A gChain (sp + 0x60#64) chain
  refine SepWP.focus_weaken hchain_recompose (by sep_focus) ?_
  refine SepWP.focus_weaken (reassemble_chunkedStatesAt_190 A sp st1 sw1 sw2 sw3 hbs920) (by sep_focus) ?_
  refine SepWP.focus_weaken (words3_to_memRegion_530_24 sp sw1 sw2 sw3) (by sep_focus) ?_
  refine SepWP.focus_weaken h550_38 (by sep_focus) ?_
  refine SepWP.focus_weaken (words2_to_memRegion_580_16 sp kw0 kw1) (by sep_focus) ?_
  refine SepWP.focus_weaken (reassemble_590_after_memcpy sp sw1 sw2 sw3 hlen896) (by sep_focus) ?_
  refine SepWP.focus_weaken
    (words_keyWordsDetached_entails_optEpochSecretRegSlotAt A sp (s.readReg64 .x21) (s.readReg64 .x27) key kw0 kw1)
    (by sep_focus) ?_
  refine SepWP.focus_weaken (words_entails_messageAt_1d70 sp msg pw0 pw1 pw2 pw3 pw4 pad32 hvalid hpay_rec) (by sep_focus) ?_
  refine finish_sepWP_lscro (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (fun hinv_f => ?_) (Entails.refl _)
  refine SepWPp.mono_pre' ?_ (hnext _ hinv_f
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]))
  simp only [arm64_norm, *]; exact Entails.of_eq (by ac_rfl)

/-! ## Unified 11-Arm `<States>::send` + Post-Arm Reassembly (`statesSendArmOffset st0 -> +3196`) -/

private theorem spqrCoinsAtPlaced_entails_after_same (a cur : BitVec 64) (tape : List (BitVec 8)) :
    spqrCoinsAtPlaced a cur tape ⊢ spqrCoinsAfterPlaced a cur tape (tape.length - tape.length) := by
  rw [Nat.sub_self]; exact spqrCoinsAtPlaced_entails_after_zero a cur tape

omit [LibsignalPlacement] in
private theorem memRegion_190_928_eq (sp : BitVec 64) :
    memRegion (sp + 0x190#64) 928 = memRegion (sp + 400#64) 920 ∗ memRegion (sp + 1320#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 400#64) (n := 920) (k := 8)
    (b' := sp + 1320#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
private theorem memRegion_4080_104_eq (sp : BitVec 64) :
    memRegion (sp + 4080#64) 104 = memRegion (sp + 4080#64) 48 ∗ memRegion (sp + 4128#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 4080#64) (n := 48) (k := 56)
    (b' := sp + 4128#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
private theorem memRegion_4192_504_eq (sp : BitVec 64) :
    memRegion (sp + 4192#64) 504 = memRegion (sp + 4192#64) 448 ∗ memRegion (sp + 4640#64) 56 :=
  ProofLib.memRegion_split' (b := sp + 4192#64) (n := 448) (k := 56)
    (b' := sp + 4640#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
private theorem memRegion_1260_2400_split (sp : BitVec 64) (sz : Nat) (hsz : sz + chunkSize ≤ 2400 := by decide) :
    memRegion (sp + 0x1260#64) 2400 =
      memRegion (sp + 0x1260#64) (sz + chunkSize) ∗
      memRegion (sp + 0x1260#64 + BitVec.ofNat 64 (sz + chunkSize)) (2400 - (sz + chunkSize)) :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := sz + chunkSize) (k := 2400 - (sz + chunkSize))
    (b' := sp + 0x1260#64 + BitVec.ofNat 64 (sz + chunkSize))
    (by change 2400 = sz + 34 + (2400 - (sz + 34)); have : sz + 34 ≤ 2400 := hsz; omega) rfl (by omega)

omit [LibsignalPlacement] in
private theorem memRegion_7104_24_eq (sp : BitVec 64) :
    memRegion (sp + 7104#64) 24 = memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 7120#64) 8 :=
  ProofLib.memRegion_split' (b := sp + 0x1bc0#64) (n := 16) (k := 8)
    (b' := sp + 7120#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
private theorem memRegion_7536_400_eq (sp : BitVec 64) :
    memRegion (sp + 7536#64) 400 = memRegion (sp + 0x1d70#64) 48 ∗ memRegion (sp + 7584#64) 352 :=
  ProofLib.memRegion_split' (b := sp + 0x1d70#64) (n := 48) (k := 352)
    (b' := sp + 7584#64) rfl (by rw [BitVec.add_assoc]; rfl) (by decide)

omit [LibsignalPlacement] in
private theorem statesSendPreArmScratch_eq_post (sp : BitVec 64) :
    statesSendPreArmScratch sp =
      memRegion (sp + 0x1bc0#64) 16 ∗ memRegion (sp + 0x1d70#64) 48 ∗ statesSendPostArmScratch sp := by
  unfold statesSendPreArmScratch statesSendPostArmScratch
  rw [memRegion_7104_24_eq sp, memRegion_7536_400_eq sp]; ac_rfl

private def statesSendLeafScratchRest (sp : BitVec 64) (sz : Nat) : SepProp :=
  memRegion (sp + 32#64) 16 ∗ memRegion (sp + 3552#64) 504 ∗
  memRegion (sp + 4056#64) 8 ∗ memRegion (sp + 4064#64) 16 ∗
  memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 4192#64) 504 ∗
  memRegion (sp + 0x1260#64 + BitVec.ofNat 64 (sz + chunkSize)) (2400 - (sz + chunkSize)) ∗
  memRegion (sp + 7104#64) 24 ∗ memRegion (sp + 7136#64) 400 ∗ memRegion (sp + 7536#64) 400

omit [LibsignalPlacement] in
private theorem statesSendPreArmScratch_eq_leaf (sp : BitVec 64) (sz : Nat)
    (hsz : sz + chunkSize ≤ 2400 := by decide) :
    statesSendPreArmScratch sp =
      memRegion (sp + 0x1260#64) (sz + chunkSize) ∗ statesSendLeafScratchRest sp sz := by
  unfold statesSendPreArmScratch statesSendLeafScratchRest
  rw [memRegion_1260_2400_split sp sz hsz]; ac_rfl

private def statesSendLeafFrame {ctl : BitVec 64} (A : RustAlloc) (sp cur : BitVec 64)
    (tape : List (BitVec 8)) (chain : Option ChainPB) (sz : Nat) (Frame : SepProp) : SepProp :=
  spqrLogLevelZeroPlacedAt ∗ spqrCoinsAtPlaced ctl cur tape ∗
  ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
  memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
  statesSendLeafScratchRest sp sz ∗ Frame

private def statesSendImmFrame {ctl : BitVec 64} (A : RustAlloc) (sp cur : BitVec 64)
    (tape : List (BitVec 8)) (chain : Option ChainPB) (Frame : SepProp) : SepProp :=
  stackAt sp spqrSendCalleeStack ∗ A.pool ∗
  tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
  spqrCoinsAtPlaced ctl cur tape ∗ ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
  memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
  statesSendPreArmScratch sp ∗ Frame

/-- Relocatable continuation contract at `spqrSendPlacedEntry + 3196#64` after `<States>::send` and post-arm reassembly. -/
abbrev SpqrSendAt3196Placed {F : ShaCompress} {ctl : BitVec 64}
    (A : RustAlloc) (ext : String → Option (State → State))
    (s0 : State) (sp cur : BitVec 64) (tape tape' : List (BitVec 8))
    (chain : Option ChainPB) (key : Option EpochSecret)
    (msg : Message spqrPolyApi) (st1 : States spqrPolyApi (spqrAuthApi F))
    (ret : BitVec 64) (Frame Fr : SepProp) (post : State → SepProp → Prop) : Prop :=
  ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
    sf.pc = spqrSendPlacedEntry + 3196#64 →
    sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
    sf.readReg64 .x19 = s0.readReg64 .x19 → sf.readReg64 .x20 = chunkedStatesWord0 st1 →
    sf.readReg64 .x22 = msg.epoch → sf.readReg64 .x25 = sp + 0x550#64 →
    sf.readReg64 .x26 = sp + 0x1260#64 → sf.readReg64 .x28 = s0.readReg64 .x28 →
    (sf.readReg64 .x23 = noneCap ↔ chain = none) →
    sf.pstate = addsPState64 (sf.readReg64 .x23) 1#64 →
    calleeSavedVRegs sf = calleeSavedVRegs s0 →
    SepWPp (spqrSendPlacedProg ext) ret sf
      ((ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
        chunkedStatesAt A (sp + 0x190#64) st1 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 0x550#64) 38 ∗
        memRegion (sp + 0x580#64) 16 ∗ memRegion (sp + 0x590#64) 920 ∗
        memRegion (sp + 0x950#64) 928 ∗
        optEpochSecretRegSlotAt A sp (sf.readReg64 .x21) (sf.readReg64 .x27) key ∗
        messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗
        statesSendPostArmScratch sp ∗
        spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        spqrLogLevelZeroPlacedAt ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr))

/-- Shared relocatable continuation from `spqrSendPlacedEntry + 3068#64` to `spqrSendPlacedEntry + 3196#64` after any of the 11 arms. -/
theorem step_send_post_arm_cont_placed {F : ShaCompress} {ctl : BitVec 64}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    {s0 s1 : State} (sp cur : BitVec 64) (tape tape' : List (BitVec 8))
    (chain : Option ChainPB) (key : Option EpochSecret)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinStatePlaced sp ext s0 s1 msg st1)
    (hvalid : validSendPayload msg.payload)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {ret : BitVec 64} {P0 Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hinv1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hP0 : P0 ⊢
      (stackAt sp spqrSendCalleeStack ∗ A.pool ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
        spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
        ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
        memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
        memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A sp (s1.readReg64 .x21) (s1.readReg64 .x27) key ∗
        chunkedStatesTail920At A (sp + 0x590#64) st1 ∗
        statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196Placed (ctl := ctl) A ext s0 sp cur tape tape' chain key msg st1 ret Frame Fr post) :
    SepWPp (spqrSendPlacedProg ext) ret s1 P0 post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine SepWPp.mono_pre' hP0 ?_
  rw [statesSendPreArmScratch_eq_post sp]
  refine step_send_post_arm_3068_to_3196_placed A ext hA sp chain msg key st1 hvalid hjoin1 hsp_align hinv1
    (Frame := memRegion (sp + 0x950#64) 928 ∗ statesSendPostArmScratch sp ∗
      spqrCoinsAfterPlaced ctl cur tape (tape.length - tape'.length) ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
      spqrLogLevelZeroPlacedAt ∗ A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
    (by ac_rfl) ?_
  intro sf hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f _ hx22_f hx25_f hx26_f _ hx28_f hx23_none hz_f hvregs_f
  refine SepWPp.mono_pre' ?_
    (hnext sf hinv_f hpc_f hrun_f hsp_f htr_f hx19_f hx20_f hx22_f hx25_f hx26_f hx28_f hx23_none hz_f hvregs_f)
  exact Entails.of_eq (by ac_rfl)

/-- Specialization of `step_send_post_arm_cont_placed` for the 6 leaf-call arms (`tape' = tape`, `key = none`). -/
private theorem step_send_post_arm_cont_leaf_placed {F : ShaCompress} {ctl : BitVec 64}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext) {s0 s1 : State} (sp cur : BitVec 64) (tape : List (BitVec 8))
    (chain : Option ChainPB) (sz : Nat) (hsz : sz + chunkSize ≤ 2400 := by decide)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinStatePlaced sp ext s0 s1 msg st1)
    (hvalid : validSendPayload msg.payload) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {ret : BitVec 64} {Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hinv1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hnext : SpqrSendAt3196Placed (ctl := ctl) A ext s0 sp cur tape tape chain none msg st1 ret Frame Fr post) :
    SepWPp (spqrSendPlacedProg ext) ret s1
      ((stackAt sp spqrSendCalleeStack ∗ A.pool ∗
        tokenInitPlacedAt ∗ reduceTablePlacedAt ∗
        memRegion (sp + 0x950#64) 928 ∗ memRegion (sp + 0x1260#64) (sz + chunkSize) ∗
        spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A sp (s1.readReg64 .x21) (s1.readReg64 .x27) none ∗
        chunkedStatesTail920At A (sp + 0x590#64) st1) ∗
       statesSendLeafFrame (ctl := ctl) A sp cur tape chain sz Frame) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine step_send_post_arm_cont_placed (ctl := ctl) A ext hA sp cur tape tape chain none hjoin1 hvalid hsp_align hinv1 ?_ hnext
  unfold statesSendLeafFrame; rw [statesSendPreArmScratch_eq_leaf sp sz hsz]
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (spqrCoinsAtPlaced_entails_after_same _ _ _))))
    (Entails.of_eq (by ac_rfl))

/-- Specialization of `step_send_post_arm_cont_placed` for the 3 immediate arms (`tape' = tape`, `key = none`). -/
private theorem step_send_post_arm_cont_imm_placed {F : ShaCompress} {ctl : BitVec 64}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    {s0 s1 : State} (sp cur : BitVec 64) (tape : List (BitVec 8))
    (chain : Option ChainPB)
    {msg : Message spqrPolyApi} {st1 : States spqrPolyApi (spqrAuthApi F)}
    (hjoin1 : SpqrSendJoinStatePlaced sp ext s0 s1 msg st1)
    (hvalid : validSendPayload msg.payload)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    {ret : BitVec 64} {Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hinv1 : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hnext : SpqrSendAt3196Placed (ctl := ctl) A ext s0 sp cur tape tape chain none msg st1 ret Frame Fr post) :
    SepWPp (spqrSendPlacedProg ext) ret s1
      ((memRegion (sp + 0x950#64) 928 ∗
        spqrSendPayloadSlotAt sp ((s1.readReg64 .x24).setWidth 8) msg.payload ∗
        spqrSendKeySlotAt A sp (s1.readReg64 .x21) (s1.readReg64 .x27) none ∗
        chunkedStatesTail920At A (sp + 0x590#64) st1) ∗
       statesSendImmFrame (ctl := ctl) A sp cur tape chain Frame) post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  refine step_send_post_arm_cont_placed (ctl := ctl) A ext hA sp cur tape tape chain none hjoin1 hvalid hsp_align hinv1 ?_ hnext
  unfold statesSendImmFrame
  exact Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (spqrCoinsAtPlaced_entails_after_same _ _ _))))))))
    (Entails.of_eq (by ac_rfl))

omit [LibsignalPlacement] in
private theorem states_send_ok_elim {F : ShaCompress} {α : Type}
    {r : Except StatesPanic α} {f : α → V1Send spqrPolyApi (spqrAuthApi F) × Bytes}
    {sOut : V1Send spqrPolyApi (spqrAuthApi F)} {tape' : Bytes}
    (h : (StatesResult.ofPanic r >>= fun x => Except.ok (f x)) = Except.ok (sOut, tape')) :
    ∃ x, r = Except.ok x ∧ f x = (sOut, tape') := by
  cases r with
  | error p => contradiction
  | ok x => exact ⟨x, rfl, Except.ok.inj h⟩

set_option maxHeartbeats 800000 in
/-- Unified relocatable 11-arm `<States>::send` + post-arm reassembly (`statesSendArmOffset st0 -> +3196`)
    when `st0.send K tape = .ok (sOut, tape')`. -/
theorem step_send_statesSend_placed {F : ShaCompress} {K : MlKem} {ctl : BitVec 64}
    (A : RustAlloc) (ext : String → Option (State → State))
    (hA : AllocContractsPlaced A ext)
    (hZero : HookSat (Rust.withPanics ext) spqrRustAllocZeroedSym (rustAllocZeroedSpec A))
    (hcoinsFill : CoinsFillPlacedOkX ext)
    (hseed : HookSat (Rust.withPanics ext) spqrMlkemFromSeedSym (mlkemFromSeedSpec K))
    (hpk1 : HookSat (Rust.withPanics ext) spqrMlkemPk1Sym mlkemPk1Spec)
    (hpk2 : HookSat (Rust.withPanics ext) spqrMlkemPk2Sym mlkemPk2Spec)
    (henc1 : HookSat (Rust.withPanics ext) spqrMlkemEncaps1Sym (mlkemEncaps1Spec K))
    (hpk1_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 2304).take 64 = (K.fromSeed s).1.toList)
    (hpk2_slice : ∀ s : List.Vector (BitVec 8) 64,
      ((K.fromSeed s).2.2.toList.drop 1152).take 1152 = (K.fromSeed s).2.1.toList)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F A ext) (hres_call : DoReserve2PlacedOkX A ext)
    (henc_call : EncodeBytesPlacedOkX A ext) (hnc_call : PolyNextChunkPlacedOkX A ext)
    (hhkdf : HkdfToVecPlacedOkX A (spqrHkdfWith F) ext) (hupd : AuthUpdatePlacedOkX F A ext)
    (hhs_call : HeaderSentSendEkChunkPlacedOkX A F ext)
    (hct1r_call : Ct1ReceivedSendEkChunkPlacedOkX A F ext)
    (hct1s_call : Ct1SampledSendCt1ChunkPlacedOkX A F ext)
    (hct2s_call : Ct2SampledSendCt2ChunkPlacedOkX A F ext)
    (hekct1s_call : EkReceivedCt1SampledSendCt1ChunkPlacedOkX A F ext)
    {s0 s : State} (sp cur : BitVec 64) (tape tape' : Bytes)
    (chain : Option ChainPB) (st0 : States spqrPolyApi (spqrAuthApi F))
    (sOut : V1Send spqrPolyApi (spqrAuthApi F))
    (hroot_len : ∀ st, st0 = .headerReceived st → st.uc.auth.rootKey.length + 32 < 2 ^ 63)
    (hsend : st0.send K tape = .ok (sOut, tape'))
    {ret : BitVec 64} {P Frame Fr : SepProp} {post : State → SepProp → Prop}
    (hinv : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = spqrSendPlacedEntry + statesSendArmOffset st0)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (htr : s.trace = s0.trace) (hx19 : s.readReg64 .x19 = s0.readReg64 .x19)
    (hx20 : s.readReg64 .x20 = chunkedStatesWord0 st0)
    (hx24 : s.readReg64 .x24 = sp + 0x950#64) (hx25 : s.readReg64 .x25 = sp + 0x550#64)
    (hx26 : s.readReg64 .x26 = sp + 0x1260#64) (hx28 : s.readReg64 .x28 = sp + 0x1060#64)
    (hx28_0 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ A.pool ∗
      tokenInitPlacedAt ∗ reduceTablePlacedAt ∗ spqrLogLevelZeroPlacedAt ∗
      spqrCoinsAtPlaced ctl cur tape ∗
      ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗
      memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 0x530#64) 24 ∗
      memRegion (sp + 0x550#64) 38 ∗ memRegion (sp + 0x580#64) 16 ∗
      memRegion (sp + 0x590#64) 920 ∗
      chunkedStatesAt A (sp + 0x950#64) st0 ∗
      statesSendPreArmScratch sp) ∗ Frame)
    (hnext : SpqrSendAt3196Placed (ctl := ctl) A ext s0 sp cur tape tape' chain sOut.key sOut.msg sOut.state ret Frame Fr post) :
    SepWPp (spqrSendPlacedProg ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  subst hP; cases st0 with
  | keysUnsampled st =>
    obtain ⟨⟨outSt, chunk, tape1⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2.symm with ⟨rfl, rfl⟩; unfold statesSendPreArmScratch
    refine step_send_arm_keysUnsampled_placed A ext hA hcoinsFill hseed hpk1 hpk2
      hmac_call hres_call henc_call hnc_call hpk1_slice hpk2_slice sp cur tape tape' st outSt chunk h1
      (Frame := ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗ memRegion (sp + 0x190#64) 928 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 32#64) 16 ∗ memRegion (sp + 4064#64) 16 ∗ Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx26 hx28_0 hvregs
      (by rw [show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    have hjoin1' : SpqrSendJoinStatePlaced sp ext s0 s1 _ _ :=
      ⟨hjoin1.1, hjoin1.2, hjoin1.3, hjoin1.4, hjoin1.5, hjoin1.6, hjoin1.7, hjoin1.8, hjoin1.9, hjoin1.10, hjoin1.11⟩
    refine step_send_post_arm_cont_placed A ext hA sp cur tape tape' chain none hjoin1' trivial hsp_align hinv1 ?_ hnext
    unfold statesSendPreArmScratch
    rw [show (sp + 0x1260#64 : BitVec 64) = sp + 4704#64 from rfl]
    exact Entails.of_eq (by ac_rfl)
  | keysSampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 504]
    refine step_send_arm_keysSampled_placed A ext hA hct1r_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) A sp cur tape chain 504 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf_placed A ext hA sp cur tape chain 504 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | headerSent st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 880]
    refine step_send_arm_headerSent_placed A ext hA hhs_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) A sp cur tape chain 880 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf_placed A ext hA sp cur tape chain 880 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ct1Received st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 504]
    refine step_send_arm_ct1Received_placed A ext hA hct1r_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) A sp cur tape chain 504 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf_placed A ext hA sp cur tape chain 504 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ekSentCt1Received st =>
    rcases Prod.mk.inj (Except.ok.inj hsend) with ⟨rfl, rfl⟩
    apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_ekSentCt1Received_placed A ext hA sp st
      (Frame := statesSendImmFrame (ctl := ctl) A sp cur tape chain Frame)
      hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendImmFrame; ac_rfl) fun s1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro hinv1
    exact step_send_post_arm_cont_imm_placed A ext hA sp cur tape chain hjoin1 rfl hsp_align hinv1 hnext
  | noHeaderReceived st =>
    rcases Prod.mk.inj (Except.ok.inj hsend) with ⟨rfl, rfl⟩
    apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_noHeaderReceived_placed A ext hA sp st
      (Frame := statesSendImmFrame (ctl := ctl) A sp cur tape chain Frame)
      hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendImmFrame; ac_rfl) fun s1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro hinv1
    exact step_send_post_arm_cont_imm_placed A ext hA sp cur tape chain hjoin1 trivial hsp_align hinv1 hnext
  | headerReceived st =>
    obtain ⟨⟨outSt, chunk, ek, tape1⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2.symm with ⟨rfl, rfl⟩; unfold statesSendPreArmScratch
    rw [memRegion_190_928_eq sp, memRegion_4080_104_eq sp, memRegion_4192_504_eq sp]
    refine step_send_arm_headerReceived_placed A ext hA hZero hcoinsFill henc1
      hhkdf hupd henc_call hnc_call sp cur tape tape' st outSt chunk ek (hroot_len st rfl) h1
      (Frame := ProtoRepr.optChainPBAt A (sp + 0x60#64) chain ∗ memRegion (sp + 1320#64) 8 ∗
        memRegion (sp + 0x530#64) 24 ∗ memRegion (sp + 3552#64) 504 ∗
        memRegion (sp + 4128#64) 56 ∗ memRegion (sp + 4640#64) 56 ∗ Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx26 hx28 hx28_0 hvregs (by ac_rfl) fun s1 hinv1 hjoin1 => ?_
    have hjoin1' : SpqrSendJoinStatePlaced sp ext s0 s1 _ _ :=
      ⟨hjoin1.1, hjoin1.2, hjoin1.3, hjoin1.4, hjoin1.5, hjoin1.6, hjoin1.7, hjoin1.8, hjoin1.9, hjoin1.10, hjoin1.11⟩
    refine step_send_post_arm_cont_placed A ext hA sp cur tape tape' chain (some ek) hjoin1' trivial hsp_align hinv1 ?_ hnext
    unfold statesSendPreArmScratch
    rw [memRegion_190_928_eq sp, memRegion_4080_104_eq sp, memRegion_4192_504_eq sp]
    exact Entails.of_eq (by ac_rfl)
  | ct1Sampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 928]
    refine step_send_arm_ct1Sampled_placed A ext hA hct1s_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) A sp cur tape chain 928 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf_placed A ext hA sp cur tape chain 928 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ekReceivedCt1Sampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 528]
    refine step_send_arm_ekReceivedCt1Sampled_placed A ext hA hekct1s_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) A sp cur tape chain 528 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf_placed A ext hA sp cur tape chain 528 (by decide) hjoin1 trivial hsp_align hinv1 hnext
  | ct1Acknowledged st =>
    rcases Prod.mk.inj (Except.ok.inj hsend) with ⟨rfl, rfl⟩
    apply of_sepWP_lscro (mid := spqrSendPlacedEntry + 3068#64) hinv
    refine step_send_arm_ct1Acknowledged_placed A ext hA sp st
      (Frame := statesSendImmFrame (ctl := ctl) A sp cur tape chain Frame)
      hpc hrun hsp hsp_align htr hx19 hx20 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendImmFrame; ac_rfl) fun s1 hjoin1 => ?_
    apply SepWP.done hjoin1.pc hjoin1.run; intro hinv1
    exact step_send_post_arm_cont_imm_placed A ext hA sp cur tape chain hjoin1 trivial hsp_align hinv1 hnext
  | ct2Sampled st =>
    obtain ⟨⟨outSt, chunk⟩, h1, h2⟩ := states_send_ok_elim hsend
    rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
    rw [statesSendPreArmScratch_eq_leaf sp 456]
    refine step_send_arm_ct2Sampled_placed A ext hA hct2s_call sp st outSt chunk h1
      (Frame := statesSendLeafFrame (ctl := ctl) A sp cur tape chain 456 Frame)
      hinv hpc hrun hsp hsp_align htr hx19 hx24 hx25 hx26 hx28_0 hvregs
      (by unfold statesSendLeafFrame; ac_rfl) fun s1 hinv1 hjoin1 => ?_
    exact step_send_post_arm_cont_leaf_placed A ext hA sp cur tape chain 456 (by decide) hjoin1 trivial hsp_align hinv1 hnext

end CryptoVerification.Cli.SpqrV1.Top.Send
