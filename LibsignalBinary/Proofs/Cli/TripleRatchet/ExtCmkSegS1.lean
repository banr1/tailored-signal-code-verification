/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSeams
public import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Loop
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSegS1Remove
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Core
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturn
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Remove
import ProofLib.SepLogic.WPp

/-!
# `SP2Ext` Segment S1 (`s1_ok_x`) for `consume_message_key`

Proves the past-counter take path (`CmkS1SpecX`) of `RatchetState::consume_message_key` on
`SP2Ext img.base ext` under `AllocContractsX` and `FindIndexOkX`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

namespace Proofs.libsignal.Stage1X.CmkX

open Arm64 ProofLib ProofLib.SepSolver ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSession.TakePath
open CryptoVerification.SessionModel
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)
open Proofs.libsignal.Stage1X

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_SegS1 : True := trivial

@[local simp] private theorem bv_add_48_8 (x : BitVec 64) : x + 48#64 + 8#64 = x + 56#64 := by bv_omega
@[local simp] private theorem bv_add_48_16 (x : BitVec 64) : x + 48#64 + 16#64 = x + 64#64 := by bv_omega
@[local simp] private theorem bv_add_56_40 (x : BitVec 64) : x + 56#64 + 40#64 = x + 96#64 := by bv_omega

@[local simp] private theorem truncate_32_zeroExtend_64 (x : BitVec 32) :
    (x.zeroExtend 64).truncate 32 = x := by
  ext i hi; simp

@[local simp] private theorem sub32_not_add_one (a b : BitVec 32) :
    a + (~~~b + 1#32) = a - b := by
  have := @BitVec.toNat_not 32 b; bv_omega

@[local simp] private theorem sub32_add_not_add_one (a b : BitVec 32) :
    a + ~~~b + 1#32 = a - b := by
  have := @BitVec.toNat_not 32 b; bv_omega

@[local simp] private theorem bv_sub_104_add_104 (x : BitVec 64) : x - 104#64 + 104#64 = x := by bv_omega

@[local simp] private theorem bv_add_neg104_add_104 (x : BitVec 64) :
    x + bv% (2 ^ 64 - 104) + 104#64 = x := by bv_omega

/-! ## Shared Epilogue and `DuplicatedMessage` Return -/

set_option maxHeartbeats 1600000 in
theorem cmk_epilogue_77c_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkSym + 1916#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP (SP2Ext b ext) (s0.readReg64 .x30) s
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0)
      (fun sf P_f =>
        sf.sp = s0.sp ∧ sf.trace = s0.trace ∧ CalleeSavedPreserved s0 sf ∧
        (P_f ⊢ stackAt s0.sp cmkStack)) := by
  rcases htrace with ⟨htrace, hvregs⟩
  unfold cmkSavedRegs
  cmk_fetches_range_x b ext 0x77c 0x798
  generalize (SP2Ext b ext).fnAddr cmkSym = entry at *
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], ?_, ?_⟩
  · simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm, *]
  · exact cmkStack_recombine s0.sp s0

theorem cmk_epilogue_77c_outcome_x {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} {A : RustAlloc}
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkSym + 1916#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hnpan : (x.model F).1 ≠ .error .panic) (hG' : x.G.AgreeExcept G' (x.touched F))
    (hm : s.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A x.self G' (x.model F).2 ∗ consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗ cmkLowStack s0.sp ∗ A.pool ∗ R)) :
    reaches_outcome (SP2Ext img.base ext) (cmkSpecX F A img) x R s0 s := by
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨sf, hsteps, hpc_sf, hrun_sf, P_f, hm_sf, hsp_sf, htrace_sf, hcc_sf, hP_f⟩ :=
    sepWP_to_reaches_pc (cmk_epilogue_77c_wp_x s0 s hpc hrun hsp hsp_align htrace) hm hL
  refine LibsignalSession.reaches_outcome_steps hsteps
    (reaches_outcome_refl_return hpc_sf hrun_sf ⟨?_, hsp_sf, hcc_sf⟩)
  have hm1 : sf.mem ⊨ stackAt s0.sp cmkStack ∗
      (ratchetAt A x.self G' (x.model F).2 ∗ consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗ cmkLowStack s0.sp ∗ A.pool ∗ R) :=
    Satisfies.mono (sepConj_mono_left hP_f) hm_sf
  simp only [cmkSpecX, Spec.inImage, stackAt_cmkStackX_eq_cmkStack_sep_low]
  refine Satisfies.mono ?_ hm1
  have h_rearrange :
      (stackAt s0.sp cmkStack ∗
        (ratchetAt A x.self G' (x.model F).2 ∗ consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
         (logFilterAddr img ↦₆₄ 0#64) ∗ cmkLowStack s0.sp ∗ A.pool ∗ R)) =
      (ratchetAt A x.self G' (x.model F).2 ∗
       (consumeMessageKeyResultAt A x.ret (x.model F).1 ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ckA 36 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
        (stackAt s0.sp cmkStack ∗ cmkLowStack s0.sp) ∗ A.pool ∗ R)) := by ac_rfl
  rw [h_rearrange]
  have hpost_ent :
      ratchetAt A x.self G' (x.model F).2 ⊢
        ⌜(x.model F).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
          (∃∗ G'' : RatchetGhost,
            ⌜x.G.AgreeExcept G'' (x.touched F)⌝ ∗ ratchetAt A x.self G'' (x.model F).2) :=
    Entails.pure_right ⟨hnpan, htrace_sf⟩
      (Entails.sepExists_right G' (Entails.pure_right hG' (Entails.refl _)))
  refine Entails.trans (sepConj_mono_left hpost_ent) ?_
  exact Entails.of_eq

set_option maxHeartbeats 1600000 in
theorem cmk_dup_0xb4_wp_x {img : Obj.Image} {ext : String → Option (State → State)} {A : RustAlloc}
    (himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (s0 s : State) (v0 v16 v20 : BitVec 32) (v8 : BitVec 64)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkSym + 180#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = x.counter.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ret)
    (hx28 : s.readReg64 .x28 = x.ck.index.zeroExtend 64) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkSym + 1916#64) s
      ((x.ret ↦₃₂ v0) ∗ memRegion (x.ret + 4#64) 4 ∗ ((x.ret + 8#64) ↦₆₄ v8) ∗
       ((x.ret + 16#64) ↦₃₂ v16) ∗ ((x.ret + 20#64) ↦₃₂ v20) ∗
       memRegion (x.ret + 24#64) 64 ∗ (logFilterAddr img ↦₆₄ 0#64))
      (fun sf P_f =>
        sf.sp = s0.sp - 480#64 ∧ sf.spAligned = true ∧
        (sf.trace = s0.trace ∧ calleeSavedVRegs sf = calleeSavedVRegs s0) ∧
        (P_f ⊢ consumeMessageKeyResultAt A x.ret (.error (.duplicatedMessage x.ck.index x.counter)) ∗
          (logFilterAddr img ↦₆₄ 0#64))) := by
  rcases htrace with ⟨htrace, hvregs⟩
  have hentry : (SP2Ext img.base ext).fnAddr cmkSym = img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") := by
    rw [Program.fnAddr_rebase, cmkSym, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")]
  cmk_fetches_range_x img.base ext 0xb4 0xcc
  cmk_fetches_range_x img.base ext 0x150 0x16c
  generalize (SP2Ext img.base ext).fnAddr cmkSym = entry at *
  have hadrp := adrp_0xc0_add_eq_logFilterAddr himg hentry
  clear hentry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, ?_⟩
  simp only [consumeMessageKeyResultAt, errDuplicatedMessage]
  exact Entails.of_eq

theorem cmk_dup_0xb4_outcome_x {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} {A : RustAlloc}
    (himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkSym + 180#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx20 : s.readReg64 .x20 = x.counter.zeroExtend 64) (hx22 : s.readReg64 .x22 = x.ret)
    (hx28 : s.readReg64 .x28 = x.ck.index.zeroExtend 64)
    (hmodel : x.model F = (.error (.duplicatedMessage x.ck.index x.counter), x.st))
    (hm : s.mem ⊨ cmkPreLoopHeap A img x s0 ∗ (cmkLowStack s0.sp ∗ R)) :
    reaches_outcome (SP2Ext img.base ext) (cmkSpecX F A img) x R s0 s := by
  unfold cmkPreLoopHeap at hm
  have hm_slots : s.mem ⊨
      ((∃∗ v0 : BitVec 32, (x.ret ↦₃₂ v0)) ∗ memRegion (x.ret + 4#64) 4 ∗
       (∃∗ v8 : BitVec 64, ((x.ret + 8#64) ↦₆₄ v8)) ∗
       (∃∗ v16 : BitVec 32, ((x.ret + 16#64) ↦₃₂ v16)) ∗
       (∃∗ v20 : BitVec 32, ((x.ret + 20#64) ↦₃₂ v20)) ∗
       memRegion (x.ret + 24#64) 64 ∗ (logFilterAddr img ↦₆₄ 0#64)) ∗
      (ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗ stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0 ∗
       cmkLowStack s0.sp ∗ A.pool ∗ R) := by
    have hm1 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono (chainKeyBytes_entails_memRegion x.ckA x.ck)
          (sepConj_mono_left (memRegion_88_entails_dup_slots x.ret)))))) hm
    exact Satisfies.of_eq hm1
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_slots
  rcases hm_slots with ⟨v20, v16, v8, v0, hm_slots⟩
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align, htrace1, hP1⟩ :=
    sepWP_to_reaches_pc
      (cmk_dup_0xb4_wp_x (A := A) himg x s0 s v0 v16 v20 v8 hpc hrun hsp hsp_align htrace hx20 hx22 hx28)
      hm_slots hL
  have hm1' : s1.mem ⊨
      (consumeMessageKeyResultAt A x.ret (.error (.duplicatedMessage x.ck.index x.counter)) ∗
       (logFilterAddr img ↦₆₄ 0#64)) ∗
      (ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗ stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0 ∗
       cmkLowStack s0.sp ∗ A.pool ∗ R) :=
    Satisfies.mono (sepConj_mono_left hP1) hm1
  have hm1_ep : s1.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A x.self x.G (x.model F).2 ∗ consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗ cmkLowStack s0.sp ∗ A.pool ∗ R) := by
    rw [hmodel]; exact Satisfies.of_eq hm1'
  have hnpan : (x.model F).1 ≠ .error .panic := by rw [hmodel]; intro h; cases h
  have htouch : x.touched F = none := by unfold ConsumeMessageKeyGhost.touched; rw [hmodel]
  have hG' : x.G.AgreeExcept x.G (x.touched F) := by
    rw [htouch]; exact RatchetGhost.AgreeExcept.refl_none x.G
  exact LibsignalSession.reaches_outcome_steps hsteps1
    (cmk_epilogue_77c_outcome_x x x.G R s0 s1 hpc1 hrun1 hsp1 hsp1_align htrace1 hnpan hG' hm1_ep)

/-! ## Message-Key Removal Outcome (`+0x5e4 .. +0x798`) -/

theorem cmk_remove_0x5e4_outcome_x {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} {A : RustAlloc}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length) (hgi : ci < x.G.chains.length)
    (hprops : RatchetChainProps x.G x.st ci hgi hi)
    {p : Nat} (hp : p < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)
    (hfind : x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) = some p)
    (hc_lt : x.counter < x.ck.index)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkSym + 1508#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (htrace : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx2 : s.readReg64 .x2 =
      BitVec.ofNat 64 (((x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = x.G.chains[ci].mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = x.G.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx22 : s.readReg64 .x22 = x.ret)
    (hx24 : s.readReg64 .x24 =
      BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hm : s.mem ⊨
      (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
       ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
         BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
       vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
         (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
       ratchetChainRest A x.self x.G x.st ci hgi hi ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗ cmkLowStack s0.sp ∗ A.pool) ∗ R) :
    reaches_outcome (SP2Ext img.base ext) (cmkSpecX F A img) x R s0 s := by
  set chAddr := x.G.chainsPtr + BitVec.ofNat 64 (ci * 104)
  set g := x.G.chains[ci]
  set c := x.st.receiverChains[ci]
  set gks := g.keys.zip c.messageKeys
  have hstack_eq :
      stackAt (s0.sp - 480#64) 7712 ∗ cmkLowStack s0.sp =
        stackAt (s0.sp - 480#64) extHookStack ∗ memRegion (s0.sp - 20480#64) 3616 := by
    rw [stackAt_7712_sep_low_eq_20000 s0.sp, stackAt_20000_split_extHook s0.sp]; ac_rfl
  have hm_pre : s.mem ⊨
      (A.pool ∗ stackAt (s0.sp - 480#64) extHookStack ∗ memRegion (s0.sp - 480#64) 384 ∗
       memRegion x.ret 88 ∗ ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
       vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks) ∗
      (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗ ratchetChainRest A x.self x.G x.st ci hgi hi ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗ memRegion (s0.sp - 20480#64) 3616 ∗
       cmkSavedRegs s0.sp s0 ∗ R) := by
    have hm_stk : s.mem ⊨
        (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗ ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
         vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
         ratchetChainRest A x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
         (stackAt (s0.sp - 480#64) 7712 ∗ cmkLowStack s0.sp) ∗
         memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0 ∗ A.pool) ∗ R := Satisfies.of_eq hm
    rw [hstack_eq] at hm_stk
    have hm1 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (chainKeyBytes_entails_memRegion x.ckA x.ck)))))))) hm_stk
    exact Satisfies.of_eq hm1
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align, hx29_1, htr1, hP1⟩ :=
    sepWP_to_reaches_pc
      (cmk_remove_0x5e4_wp_x hA g.mkCap g.mkPtr chAddr x.ret gks p hp
        s0 s hfrozen hsym hpc hrun hsp hsp_align hx2 hx8 hx19 hx22 hx24 hx29)
      hm_pre hL
  have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
  have hkl : g.keys.length = c.messageKeys.length := hprops.keys_len
  have hzip_len : gks.length = c.messageKeys.length := by simp [gks, hkl]
  have hp_c : p < c.messageKeys.length := by omega
  have hgks_snd : gks[p].2 = c.messageKeys[p] := by simp [gks, List.getElem_zip]
  have hmodel := cmk_model_past_hit F x hci hi hp_c hfind hc_lt
  set g' : ChainGhost := { g with keys := g.keys.eraseIdx p }
  set c' : ReceiverChain := { c with messageKeys := c.messageKeys.eraseIdx p }
  set G' : RatchetGhost := x.G.setChain ci g'
  have hm1_ep : s1.mem ⊨
      (stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0) ∗
      (ratchetAt A x.self G' (x.model F).2 ∗ consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗ memRegion x.ckA 36 ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗ cmkLowStack s0.sp ∗ A.pool ∗ R) := by
    rw [hmodel, ← hgks_snd]
    have hreassemble := ratchetAt_reassemble_eraseIdx A x.self x.G x.st hi hgi hprops hp
    have hm1'' : s1.mem ⊨
        (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗ ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (gks.length - 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr (gks.eraseIdx p) ∗
          ratchetChainRest A x.self x.G x.st ci hgi hi) ∗
        ((stackAt (s0.sp - 480#64) extHookStack ∗ memRegion (s0.sp - 20480#64) 3616) ∗
          memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0 ∗
          consumeMessageKeyResultAt A x.ret (.ok gks[p].2) ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
          memRegion x.ckA 36 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗ A.pool ∗ R) :=
      Satisfies.of_eq hm1'
    rw [← hstack_eq] at hm1''
    exact Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hreassemble) hm1'')
  have hnpan : (x.model F).1 ≠ .error .panic := by rw [hmodel]; intro h; cases h
  have htouch : x.touched F = some ci := by unfold ConsumeMessageKeyGhost.touched; rw [hmodel]; exact hci
  have hG' : x.G.AgreeExcept G' (x.touched F) := by
    rw [htouch]; exact RatchetGhost.AgreeExcept.setChain x.G hgi g' rfl rfl
  exact LibsignalSession.reaches_outcome_steps hsteps1
    (cmk_epilogue_77c_outcome_x x G' R s0 s1 hpc1 hrun1 hsp1 hsp1_align
      ⟨htr1.1.trans htrace.1, htr1.2.trans htrace.2⟩ hnpan hG' hm1_ep)

/-! ## Position Search Loop (`+0x94 .. +0xb0`) -/

set_option maxHeartbeats 1600000 in
theorem cmk_loop_hit_wp_x {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (mkCap mkPtr v2 v19 v22 v24 v27 v28 v29 : BitVec 64) (counter : BitVec 32)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) (p : Nat) (hp : p < gks.length)
    (heq : gks[p].2.counter = counter) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkSym + 148#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = v2) (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = v19) (hx20 : s.readReg64 .x20 = counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = v22) (hx24 : s.readReg64 .x24 = v24)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = v28) (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkSym + 1508#64) s
      (vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧ s1.spAligned = true ∧
        s1.readReg64 .x2 = v2 ∧ s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 ∧
        s1.readReg64 .x19 = v19 ∧ s1.readReg64 .x20 = counter.zeroExtend 64 ∧
        s1.readReg64 .x22 = v22 ∧ s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x27 = v27 ∧ s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧ (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)) := by
  cmk_fetches_range_x b ext 0x94 0x9c
  generalize (SP2Ext b ext).fnAddr cmkSym = entry at *
  examples_hide_fetches
  refine SepWP.weaken_pre (vecBuf_split_at A 104 8 (messageKeyAt A) mkCap mkPtr gks hp) ?_
  rw [messageKeyAt_expose_counter A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104))]
  simp only [sepConj_assoc]
  wp_step; wp_step; wp_step
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, ?_⟩
  refine Entails.trans ?_ (vecBuf_reassemble_self A 104 8 (messageKeyAt A) mkCap mkPtr gks hp)
  unfold messageKeyAt
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

set_option maxHeartbeats 1600000 in
theorem cmk_loop_miss_head_wp_x {A : RustAlloc} {b : BitVec 64} {ext : String → Option (State → State)}
    (mkCap mkPtr v2 v19 v22 v24 v27 v28 v29 : BitVec 64) (counter : BitVec 32)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) (p : Nat) (hp : p < gks.length)
    (hne : gks[p].2.counter ≠ counter) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkSym + 148#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = v2) (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = v19) (hx20 : s.readReg64 .x20 = counter.zeroExtend 64)
    (hx22 : s.readReg64 .x22 = v22) (hx24 : s.readReg64 .x24 = v24)
    (hx27 : s.readReg64 .x27 = v27) (hx28 : s.readReg64 .x28 = v28) (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkSym + 160#64) s
      (vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧ s1.spAligned = true ∧
        s1.readReg64 .x2 = v2 ∧ s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 ∧
        s1.readReg64 .x19 = v19 ∧ s1.readReg64 .x20 = counter.zeroExtend 64 ∧
        s1.readReg64 .x22 = v22 ∧ s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x27 = v27 ∧ s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧ (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)) := by
  cmk_fetches_range_x b ext 0x94 0x9c
  generalize (SP2Ext b ext).fnAddr cmkSym = entry at *
  examples_hide_fetches
  refine SepWP.weaken_pre (vecBuf_split_at A 104 8 (messageKeyAt A) mkCap mkPtr gks hp) ?_
  rw [messageKeyAt_expose_counter A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104))]
  simp only [sepConj_assoc]
  wp_step; wp_step; wp_step
  apply SepWP.ite_false (by rfl) (by simp [arm64_norm]; exact hne)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, ?_⟩
  refine Entails.trans ?_ (vecBuf_reassemble_self A 104 8 (messageKeyAt A) mkCap mkPtr gks hp)
  unfold messageKeyAt
  exact entails_of_eq (by ac_rfl) (Entails.refl _)

set_option maxHeartbeats 1600000 in
theorem cmk_loop_miss_cont_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    (mkPtr v19 v20 v22 v24 v28 v29 : BitVec 64)
    (p mkLen : Nat) (hp1 : p + 1 < mkLen) (hmax : mkLen ≤ maxMessageKeys) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkSym + 160#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = v19) (hx20 : s.readReg64 .x20 = v20)
    (hx22 : s.readReg64 .x22 = v22) (hx24 : s.readReg64 .x24 = v24)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 p) (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkSym + 148#64) s emp
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧ s1.spAligned = true ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - (p + 1)) * 104) ∧
        s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104) + 56#64 ∧
        s1.readReg64 .x19 = v19 ∧ s1.readReg64 .x20 = v20 ∧
        s1.readReg64 .x22 = v22 ∧ s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x27 = BitVec.ofNat 64 (p + 1) ∧ s1.readReg64 .x28 = v28 ∧
        s1.readReg64 .x29 = v29 ∧ (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧ (P1 ⊢ emp)) := by
  cmk_fetches_range_x b ext 0xa0 0xb0
  generalize (SP2Ext b ext).fnAddr cmkSym = entry at *
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.ite_true (by rfl) (by simp [arm64_norm]; exact remBytes_ne_zero hp1 hmax)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    ?_, ?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], ?_,
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩,
    Entails.refl _⟩
  · simp only [arm64_norm]; exact remBytes_sub_104_eq hp1
  · simp only [arm64_norm]; exact x8_step_84 mkPtr p
  · simp only [arm64_norm]; exact ofNat_p_add_one p

set_option maxHeartbeats 1600000 in
theorem cmk_loop_miss_done_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    (mkPtr v19 v20 v22 v24 v28 v29 : BitVec 64)
    (p mkLen : Nat) (hp1 : p + 1 = mkLen) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkSym + 160#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - p) * 104))
    (_hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (_hx19 : s.readReg64 .x19 = v19) (hx20 : s.readReg64 .x20 = v20)
    (hx22 : s.readReg64 .x22 = v22) (_hx24 : s.readReg64 .x24 = v24)
    (_hx27 : s.readReg64 .x27 = BitVec.ofNat 64 p) (hx28 : s.readReg64 .x28 = v28)
    (_hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkSym + 180#64) s emp
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧ s1.spAligned = true ∧
        s1.readReg64 .x20 = v20 ∧ s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x28 = v28 ∧ (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧ (P1 ⊢ emp)) := by
  cmk_fetches_range_x b ext 0xa0 0xb0
  generalize (SP2Ext b ext).fnAddr cmkSym = entry at *
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.ite_false (by rfl) (by simp [arm64_norm]; exact remBytes_last_eq_zero hp1)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, Entails.refl _⟩

theorem cmk_pos_loop_0x94_outcome_x {img : Obj.Image} {F : ShaCompress}
    {ext : String → Option (State → State)} {A : RustAlloc}
    (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) (himg : Obj.Loads libsignalSessionImage img)
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State)
    {ci : Nat} (hci : x.st.findReceiverChainIndex x.their = some ci)
    (hi : ci < x.st.receiverChains.length) (hgi : ci < x.G.chains.length)
    (hprops : RatchetChainProps x.G x.st ci hgi hi) (hc_lt : x.counter < x.ck.index) :
    ∀ (rem p : Nat) (s : State),
      rem = (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - p →
      p < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length →
      x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) =
        List.findIdx?.go (fun k => k.counter == x.counter)
          (x.st.receiverChains[ci].messageKeys.drop p) p →
      img.FrozenLoaded s → s.symtab = img.symtab →
      s.pc = (SP2Ext img.base ext).fnAddr cmkSym + 148#64 → s.status = .Running →
      s.sp = s0.sp - 480#64 → s.spAligned = true →
      (s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0) →
      s.readReg64 .x2 =
        BitVec.ofNat 64 (((x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length - 1 - p) * 104) →
      s.readReg64 .x8 = x.G.chains[ci].mkPtr + BitVec.ofNat 64 (p * 104) + 56#64 →
      s.readReg64 .x19 = x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) →
      s.readReg64 .x20 = x.counter.zeroExtend 64 → s.readReg64 .x22 = x.ret →
      s.readReg64 .x24 =
        BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length →
      s.readReg64 .x27 = BitVec.ofNat 64 p → s.readReg64 .x28 = x.ck.index.zeroExtend 64 →
      s.readReg64 .x29 = s0.sp - 96#64 →
      (s.mem ⊨
        (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
         ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
           BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
         vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
           (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
         ratchetChainRest A x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗ cmkLowStack s0.sp ∗ A.pool) ∗ R) →
      reaches_outcome (SP2Ext img.base ext) (cmkSpecX F A img) x R s0 s := by
  intro rem
  induction rem with
  | zero => intro p s hrem hp; omega
  | succ k ih =>
    intro p s hrem hp hfind hfrozen hsym hpc hrun hsp hsp_align htrace
      hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29 hm
    set chAddr := x.G.chainsPtr + BitVec.ofNat 64 (ci * 104)
    set g := x.G.chains[ci]
    set c := x.st.receiverChains[ci]
    set gks := g.keys.zip c.messageKeys
    have hkl : g.keys.length = c.messageKeys.length := hprops.keys_len
    have hzip_len : gks.length = c.messageKeys.length := by simp [gks, hkl]
    have hp_c : p < c.messageKeys.length := by omega
    have hgks_snd : gks[p].2 = c.messageKeys[p] := by simp [gks, List.getElem_zip]
    have hm_vec : s.mem ⊨
        vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
        (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗ ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
         ratchetChainRest A x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗ cmkLowStack s0.sp ∗ A.pool ∗ R) :=
      Satisfies.of_eq hm
    by_cases heq : gks[p].2.counter = x.counter
    · have hfind_some : c.messageKeys.findIdx? (fun k => k.counter == x.counter) = some p := by
        rw [hfind, findIdx_go_step hp_c]
        have hbeq : (c.messageKeys[p].counter == x.counter) = true := by
          rw [← hgks_snd]; exact beq_iff_eq.mpr heq
        simp [hbeq]
      refine reaches_outcome.of_codeLoaded fun hL => ?_
      obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align,
        hx2_1, hx8_1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hP1⟩ :=
        sepWP_to_reaches_pc
          (cmk_loop_hit_wp_x g.mkCap g.mkPtr _ chAddr x.ret (BitVec.ofNat 64 gks.length)
            (BitVec.ofNat 64 p) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            x.counter gks p hp heq s0 s hpc hrun hsp hsp_align
            hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29)
          hm_vec hL
      have hm1' : s1.mem ⊨
          (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗ ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
           vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
           ratchetChainRest A x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗ cmkLowStack s0.sp ∗ A.pool) ∗ R :=
        Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP1) hm1)
      exact LibsignalSession.reaches_outcome_steps hsteps1
        (cmk_remove_0x5e4_outcome_x hA x R s0 s1 hci hi hgi hprops hp hfind_some hc_lt
          (hsteps1.frozenLoaded hfrozen) (hsteps1.symtab_eq.trans hsym)
          hpc1 hrun1 hsp1 hsp1_align ⟨htr1.1.trans htrace.1, htr1.2.trans htrace.2⟩
          hx2_1 hx8_1 hx19_1 hx22_1 hx24_1 hx29_1 hm1')
    · have hfind_next :
          c.messageKeys.findIdx? (fun k => k.counter == x.counter) =
            List.findIdx?.go (fun k => k.counter == x.counter)
              (c.messageKeys.drop (p + 1)) (p + 1) := by
        rw [hfind, findIdx_go_step hp_c]
        have hbeq : (c.messageKeys[p].counter == x.counter) = false := by
          rw [← hgks_snd]; exact beq_eq_false_iff_ne.mpr heq
        simp [hbeq]
      refine reaches_outcome.of_codeLoaded fun hL => ?_
      obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align,
        hx2_1, hx8_1, hx19_1, hx20_1, hx22_1, hx24_1, hx27_1, hx28_1, hx29_1, htr1, hP1⟩ :=
        sepWP_to_reaches_pc
          (cmk_loop_miss_head_wp_x g.mkCap g.mkPtr _ chAddr x.ret (BitVec.ofNat 64 gks.length)
            (BitVec.ofNat 64 p) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            x.counter gks p hp heq s0 s hpc hrun hsp hsp_align
            hx2 hx8 hx19 hx20 hx22 hx24 hx27 hx28 hx29)
          hm_vec hL
      have hm1_emp : s1.mem ⊨
          emp ∗
          (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗ ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
           vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
           ratchetChainRest A x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗ cmkLowStack s0.sp ∗ A.pool ∗ R) :=
        Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP1) hm1)
      have hL1 : (SP2Ext img.base ext).CodeLoaded s1.mem := hsteps1.codeLoaded hL
      by_cases hp1 : p + 1 < gks.length
      · have hmax_gks : gks.length ≤ maxMessageKeys := by rw [hzip_len]; exact hprops.mk_max
        obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hsp2, hsp2_align,
          hx2_2, hx8_2, hx19_2, hx20_2, hx22_2, hx24_2, hx27_2, hx28_2, hx29_2, htr2, hP2⟩ :=
          sepWP_to_reaches_pc
            (cmk_loop_miss_cont_wp_x g.mkPtr chAddr (x.counter.zeroExtend 64) x.ret
              (BitVec.ofNat 64 gks.length) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
              p gks.length hp1 hmax_gks s0 s1 hpc1 hrun1 hsp1 hsp1_align
              hx2_1 hx8_1 hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
            hm1_emp hL1
        have hm2' : s2.mem ⊨
            (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗ ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
             vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
             ratchetChainRest A x.self x.G x.st ci hgi hi ∗
             (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
             memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
             stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
             cmkSavedRegs s0.sp s0 ∗ cmkLowStack s0.sp ∗ A.pool) ∗ R :=
          Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP2) hm2)
        have hsteps12 := hsteps1.trans hsteps2
        exact LibsignalSession.reaches_outcome_steps hsteps12
          (ih (p + 1) s2 (by omega) hp1 hfind_next
            (hsteps12.frozenLoaded hfrozen) (hsteps12.symtab_eq.trans hsym)
            hpc2 hrun2 hsp2 hsp2_align ⟨htr2.1.trans (htr1.1.trans htrace.1), htr2.2.trans (htr1.2.trans htrace.2)⟩
            hx2_2 hx8_2 hx19_2 hx20_2 hx22_2 hx24_2 hx27_2 hx28_2 hx29_2 hm2')
      · have hp1_eq : p + 1 = gks.length := by omega
        obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hsp2, hsp2_align,
          hx20_2, hx22_2, hx28_2, htr2, hP2⟩ :=
          sepWP_to_reaches_pc
            (cmk_loop_miss_done_wp_x g.mkPtr chAddr (x.counter.zeroExtend 64) x.ret
              (BitVec.ofNat 64 gks.length) (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
              p gks.length hp1_eq s0 s1 hpc1 hrun1 hsp1 hsp1_align
              hx2_1 hx8_1 hx19_1 hx20_1 hx22_1 hx24_1 hx27_1 hx28_1 hx29_1)
            hm1_emp hL1
        have hm2_pre : s2.mem ⊨ cmkPreLoopHeap A img x s0 ∗ (cmkLowStack s0.sp ∗ R) := by
          unfold cmkPreLoopHeap
          have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
          have hreassemble := ratchetAt_reassemble_self A x.self x.G x.st hi hgi hprops
          have hm2'' : s2.mem ⊨
              (((chAddr + 56#64) ↦₆₄ g.mkPtr) ∗ ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
                vecBuf A 104 8 (messageKeyAt A) g.mkCap g.mkPtr gks ∗
                ratchetChainRest A x.self x.G x.st ci hgi hi) ∗
              ((x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
                memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
                stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
                cmkSavedRegs s0.sp s0 ∗ A.pool ∗ (cmkLowStack s0.sp ∗ R)) :=
            Satisfies.of_eq hm2'
          exact Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hreassemble) hm2'')
        have hfind_none : c.messageKeys.findIdx? (fun k => k.counter == x.counter) = none := by
          rw [hfind_next, List.drop_eq_nil_of_le (by omega), List.findIdx?.go]
        have hmodel := cmk_model_past_miss_chain F x hci hi hfind_none hc_lt
        exact LibsignalSession.reaches_outcome_steps (hsteps1.trans hsteps2)
          (cmk_dup_0xb4_outcome_x himg x R s0 s2 hpc2 hrun2 hsp2 hsp2_align
            ⟨htr2.1.trans (htr1.1.trans htrace.1), htr2.2.trans (htr1.2.trans htrace.2)⟩ hx20_2 hx22_2 hx28_2 hmodel hm2_pre)

/-! ## `find_receiver_chain_index` Call and Post-Call Dispatch -/

def FindIndexAtX (A : RustAlloc) (img : Obj.Image)
    (ext : String → Option (State → State)) (addr : BitVec 64) : Prop :=
  subroutine_ok (SP2Ext img.base ext) addr ((findIndexSpecX img A).inImage img)

theorem call_find_index_wp_x {img : Obj.Image} {ext : String → Option (State → State)} {A : RustAlloc}
    {entry target_pc : BitVec 64}
    (hfind : FindIndexAtX A img ext (entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")))
    (p : BitVec 64) (cs : List (ChainGhost × ReceiverChain))
    (theirA : BitVec 64) (their : PublicKey) (sp_val ret_pc : BitVec 64)
    {s : State} {Frame : SepProp} {post : State → SepProp → Prop}
    (hx0 : s.readReg64 .x0 = p) (hx1 : (s.readReg64 .x1).toNat = cs.length)
    (hx2 : s.readReg64 .x2 = theirA) (hcap : cs.length * 104 < 2 ^ 63)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (hrun : s.status = .Running)
    (hsp : s.sp = sp_val) (hsp_align : s.spAligned = true) (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_val → CalleeSavedPreserved s sf → sf.trace = s.trace →
      (match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
       | some i => sf.readReg64 .x0 = 1#64 ∧ (sf.readReg64 .x1).toNat = i
       | none => sf.readReg64 .x0 = 0#64) →
      SepWP (SP2Ext img.base ext) target_pc sf
        ((arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt sp_val findIndexStackX) ∗ Frame) post) :
    SepWP (SP2Ext img.base ext) target_pc s
      ((arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
        (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt sp_val findIndexStackX) ∗ Frame) post := by
  unfold FindIndexAtX at hfind
  refine SepWP.call_subroutine_frame hfind (x := (p, cs, theirA, their)) (F := Frame)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_
  · intro R hm
    simp only [Spec.inImage, findIndexSpecX, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨by simp_all, ⟨hx0, hx1, hx2, hcap⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · intro R' sf _ hp
    simp only [Spec.inImage, findIndexSpecX] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    simp only [Spec.inImage, findIndexSpecX] at he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    simp only [Spec.inImage, findIndexSpecX, hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨htr, hres⟩ => ?_
    simpa only [sepConj_assoc] using hnext sf h1 h2 (h3.trans hsp) h4 htr hres

set_option maxHeartbeats 1600000 in
theorem cmk_call_find_index_wp_x {img : Obj.Image}
    {ext : String → Option (State → State)} {A : RustAlloc}
    (hFind : FindIndexOkX img A ext)
    (p : BitVec 64) (cs : List (ChainGhost × ReceiverChain))
    (theirA : BitVec 64) (their : PublicKey)
    (v20 v21 v22 v24 v28 v29 : BitVec 64) (s0 s : State)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkSym + 92#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = p) (hx1 : (s.readReg64 .x1).toNat = cs.length)
    (hx2 : s.readReg64 .x2 = theirA) (hx20 : s.readReg64 .x20 = v20)
    (hx21 : s.readReg64 .x21 = v21) (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24) (hx28 : s.readReg64 .x28 = v28)
    (hx29 : s.readReg64 .x29 = v29) (hcap : cs.length * 104 < 2 ^ 63) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkSym + 96#64) s
      (arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt (s0.sp - 480#64) findIndexStackX)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧ s1.spAligned = true ∧
        s1.readReg64 .x20 = v20 ∧ s1.readReg64 .x21 = v21 ∧
        s1.readReg64 .x22 = v22 ∧ s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x28 = v28 ∧ s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (match (cs.map (·.2)).findIdx? (fun c => c.senderRatchetKey == their) with
         | some i => s1.readReg64 .x0 = 1#64 ∧ (s1.readReg64 .x1).toNat = i
         | none => s1.readReg64 .x0 = 0#64) ∧
        (P1 ⊢ arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
              (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt (s0.sp - 480#64) findIndexStackX)) := by
  have hfind_at : FindIndexAtX A img ext ((SP2Ext img.base ext).fnAddr cmkSym + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) := by
    have h := hFind
    unfold FindIndexOkX at h
    rw [SP2Ext_fnAddr] at h
    exact sub_ok_at_caller (k := num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by simp only [arm64_norm]) h
  cmk_fetches_range_x img.base ext 0x5c 0x5c
  generalize (SP2Ext img.base ext).fnAddr cmkSym = entry at *
  examples_hide_fetches
  wp_step
  rw [← sepConj_emp (arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
    (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt (s0.sp - 480#64) findIndexStackX)]
  refine call_find_index_wp_x hfind_at p cs theirA their (s0.sp - 480#64) (entry + bv% (96))
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    hcap (by rw [Obj.Image.frozenLoaded_iff] at hfrozen ⊢; exact hfrozen) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf hres
  have hsp_align' : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf]
    simpa [State.spAligned, hsp] using hsp_align
  rcases hcs with ⟨_, hcs20, hcs21, hcs22, _, hcs24, _, _, _, hcs28, hcs29, hcsv⟩
  rw [sepConj_emp]
  refine SepWP.done hpc_sf hrun_sf ?_
  refine ⟨hsp_sf, hsp_align', ?_, ?_, ?_, ?_, ?_, ?_, ⟨htr_sf, by simp_all [arm64_norm]⟩, hres, Entails.refl _⟩ <;>
    simp_all [arm64_norm]

set_option maxHeartbeats 1600000 in
theorem cmk_after_find_none_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    (v20 v22 v28 : BitVec 64) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkSym + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 0#64) (hx20 : s.readReg64 .x20 = v20)
    (hx22 : s.readReg64 .x22 = v22) (hx28 : s.readReg64 .x28 = v28) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkSym + 180#64) s emp
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧ s1.spAligned = true ∧
        s1.readReg64 .x20 = v20 ∧ s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x28 = v28 ∧ (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧ (P1 ⊢ emp)) := by
  cmk_fetches_range_x b ext 0x60 0x64
  generalize (SP2Ext b ext).fnAddr cmkSym = entry at *
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, Entails.refl _⟩

set_option maxHeartbeats 1600000 in
theorem cmk_after_find_empty_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    (chainsPtr v20 v22 v28 : BitVec 64) (ci chLen : Nat)
    (hci : ci < chLen) (hch_lt : chLen * 104 < 2 ^ 63) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkSym + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 1#64) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx20 : s.readReg64 .x20 = v20) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 chLen)
    (hx22 : s.readReg64 .x22 = v22) (hx24 : s.readReg64 .x24 = chainsPtr)
    (hx28 : s.readReg64 .x28 = v28) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkSym + 180#64) s
      (((chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ 0#64))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧ s1.spAligned = true ∧
        s1.readReg64 .x20 = v20 ∧ s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x28 = v28 ∧ (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ ((chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ 0#64))) := by
  cmk_fetches_range_x b ext 0x60 0x7c
  generalize (SP2Ext b ext).fnAddr cmkSym = entry at *
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.ite_false (by rfl) (by
    have h1 : (BitVec.ofNat 64 ci).toNat = ci := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h2 : (BitVec.ofNat 64 chLen).toNat = chLen := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp_all [arm64_norm, BitVec.ule]; omega)
  wp_step; wp_step
  rw [← add_mul_104_eq_chAddr chainsPtr ci]
  wp_steps
  rw [add_mul_104_eq_chAddr chainsPtr ci]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  exact ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, Entails.refl _⟩

set_option maxHeartbeats 1600000 in
theorem cmk_after_find_nonempty_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    (chainsPtr mkPtr v20 v22 v28 v29 : BitVec 64) (ci chLen mkLen : Nat)
    (hci : ci < chLen) (hch_lt : chLen * 104 < 2 ^ 63)
    (hmk_pos : 0 < mkLen) (hmk_max : mkLen ≤ maxMessageKeys) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkSym + 96#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64) (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = 1#64) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx20 : s.readReg64 .x20 = v20) (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 chLen)
    (hx22 : s.readReg64 .x22 = v22) (hx24 : s.readReg64 .x24 = chainsPtr)
    (hx28 : s.readReg64 .x28 = v28) (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkSym + 148#64) s
      (((chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ mkPtr) ∗
       ((chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ BitVec.ofNat 64 mkLen))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧ s1.spAligned = true ∧
        s1.readReg64 .x2 = BitVec.ofNat 64 ((mkLen - 1 - 0) * 104) ∧
        s1.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (0 * 104) + 56#64 ∧
        s1.readReg64 .x19 = chainsPtr + BitVec.ofNat 64 (ci * 104) ∧
        s1.readReg64 .x20 = v20 ∧ s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 mkLen ∧ s1.readReg64 .x27 = BitVec.ofNat 64 0 ∧
        s1.readReg64 .x28 = v28 ∧ s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ ((chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ mkPtr) ∗
              ((chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ BitVec.ofNat 64 mkLen))) := by
  have hmax_val : maxMessageKeys = 2000 := rfl
  have hcbz_ne : BitVec.ofNat 64 mkLen ≠ 0#64 := by
    intro h
    have hto := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show mkLen < 2 ^ 64 by omega)] at hto
    change mkLen = 0 at hto; omega
  cmk_fetches_range_x b ext 0x60 0x90
  generalize (SP2Ext b ext).fnAddr cmkSym = entry at *
  examples_hide_fetches
  wp_step; wp_step; wp_step; wp_step
  apply SepWP.ite_false (by rfl) (by
    have h1 : (BitVec.ofNat 64 ci).toNat = ci := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have h2 : (BitVec.ofNat 64 chLen).toNat = chLen := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    simp_all [arm64_norm, BitVec.ule]; omega)
  wp_step; wp_step
  rw [← add_mul_104_eq_chAddr chainsPtr ci]
  wp_step; wp_step
  apply SepWP.ite_false (by rfl) (by simp [arm64_norm, hcbz_ne])
  wp_steps
  rw [add_mul_104_eq_chAddr chainsPtr ci]
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by simp_all [arm64_norm], by simp_all [arm64_norm],
    ?_, ?_, ?_, by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], ⟨by simp_all [arm64_norm], by simp_all [arm64_norm]⟩, Entails.refl _⟩
  · simp only [arm64_norm]
    have hmk : mkLen = (mkLen - 1 - 0) + 1 := by omega
    conv => lhs; lhs; rw [show (104#64 : BitVec 64) = BitVec.ofNat 64 104 from rfl, ← BitVec.ofNat_mul, hmk, Nat.add_mul, Nat.one_mul, BitVec.ofNat_add]
    bv_omega
  · simp_all [arm64_norm]
  · simp_all [arm64_norm]

/-! ## Segment S1 Contract -/

theorem s1_ok_x (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) (img : Obj.Image) :
    CmkS1SpecX F A ext img := by
  intro hA himg hFind x R s0 s hc_lt hstate
  rcases hstate with ⟨hpc, hmeta, hregs, hm⟩
  rcases hmeta with ⟨hrun, hsp, _, hsp_align, hx29, htrace, hfrozen, hsym, hvregs⟩
  rcases hregs with ⟨hx0, hx1, hx2, hx20, hx21, hx22, _, hx24, _, _, hx28⟩
  have hpc_sp : s.pc = (SP2Ext img.base ext).fnAddr cmkSym + 92#64 := by
    rw [hpc, cmkTakePC, cmkEntry_eq_sp2_fnAddr himg ext, cmkSym, cmkName]
  set cs := x.G.chains.zip x.st.receiverChains
  have hstack_find :
      stackAt (s0.sp - 480#64) 7712 ∗ cmkLowStack s0.sp =
        stackAt (s0.sp - 480#64) findIndexStackX ∗ memRegion (s0.sp - 20480#64) 2592 := by
    rw [stackAt_7712_sep_low_eq_20000 s0.sp, stackAt_20000_split_findIndexX s0.sp]; ac_rfl
  have hm_exp : s.mem ⊨
      ⌜x.G.chains.length = x.st.receiverChains.length ∧ cs.length * 104 < 2 ^ 63⌝ ∗
      (arrayAt (chainAt A) 104 x.G.chainsPtr cs ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (logFilterAddr img ↦₆₄ 0#64) ∗ stackAt (s0.sp - 480#64) findIndexStackX) ∗
      (ratchetFindRest A x.self x.G x.st ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
       memRegion x.ret 88 ∗ memRegion (s0.sp - 20480#64) 2592 ∗
       memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0 ∗ A.pool ∗ R) := by
    unfold cmkPreLoopHeap at hm
    have hm_stk : s.mem ⊨
        (ratchetAt A x.self x.G x.st ∗ (x.theirA ↦ₛ x.their.bytes.toList) ∗
         (x.ckA ↦ₛ chainKeyBytes x.ck) ∗ memRegion x.ret 88 ∗
         (logFilterAddr img ↦₆₄ 0#64) ∗ (stackAt (s0.sp - 480#64) 7712 ∗ cmkLowStack s0.sp) ∗
         memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0 ∗ A.pool) ∗ R := Satisfies.of_eq hm
    rw [hstack_find] at hm_stk
    have hm1 := Satisfies.mono
      (sepConj_mono_left (sepConj_mono_left (ratchetAt_expose_findIndex A x.self x.G x.st))) hm_stk
    exact Satisfies.of_eq hm1
  rw [satisfies_pure_sepConj] at hm_exp
  rcases hm_exp with ⟨⟨hchains_len, hcs_lt⟩, hm_find⟩
  have hcs_len : cs.length = x.st.receiverChains.length := by simp [cs, hchains_len]
  have hx1_len : (s.readReg64 .x1).toNat = cs.length := by
    rw [hx1, hcs_len, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show x.st.receiverChains.length < 2 ^ 64 by omega)]
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨s1, hsteps1, hpc1, hrun1, P1, hm1, hsp1, hsp1_align,
    hx20_1, hx21_1, hx22_1, hx24_1, hx28_1, hx29_1, htr1, hres, hP1⟩ :=
    sepWP_to_reaches_pc
      (cmk_call_find_index_wp_x hFind x.G.chainsPtr cs x.theirA x.their
        (x.counter.zeroExtend 64) (BitVec.ofNat 64 x.st.receiverChains.length)
        x.ret x.G.chainsPtr (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
        s0 s hpc_sp hrun hsp hsp_align hfrozen hsym
        hx0 hx1_len hx2 hx20 hx21 hx22 hx24 hx28 hx29 hcs_lt)
      hm_find hL
  have hm1_pre : s1.mem ⊨ cmkPreLoopHeap A img x s0 ∗ (cmkLowStack s0.sp ∗ R) := by
    unfold cmkPreLoopHeap
    have hm1' := Satisfies.mono (sepConj_mono_left hP1) hm1
    have hreassemble := ratchetAt_reassemble_findIndex A x.self x.G x.st
    have hm1'' : s1.mem ⊨
        (arrayAt (chainAt A) 104 x.G.chainsPtr cs ∗ ratchetFindRest A x.self x.G x.st) ∗
        ((x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
          memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
          (stackAt (s0.sp - 480#64) findIndexStackX ∗ memRegion (s0.sp - 20480#64) 2592) ∗
          memRegion (s0.sp - 480#64) 384 ∗ cmkSavedRegs s0.sp s0 ∗ A.pool ∗ R) :=
      Satisfies.of_eq hm1'
    rw [← hstack_find] at hm1''
    exact Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hreassemble) hm1'')
  have hL1 : (SP2Ext img.base ext).CodeLoaded s1.mem := hsteps1.codeLoaded hL
  rw [findIdx_map_snd_zip_eq x.G x.st x.their hchains_len] at hres
  cases hci : x.st.findReceiverChainIndex x.their with
  | none =>
    rw [hci] at hres
    have hm1_emp : s1.mem ⊨ emp ∗ (cmkPreLoopHeap A img x s0 ∗ (cmkLowStack s0.sp ∗ R)) := by
      rwa [emp_sepConj]
    obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hsp2, hsp2_align,
      hx20_2, hx22_2, hx28_2, htr2, hP2⟩ :=
      sepWP_to_reaches_pc
        (cmk_after_find_none_wp_x (x.counter.zeroExtend 64) x.ret (x.ck.index.zeroExtend 64)
          s0 s1 hpc1 hrun1 hsp1 hsp1_align hres hx20_1 hx22_1 hx28_1)
        hm1_emp hL1
    have hm2_pre : s2.mem ⊨ cmkPreLoopHeap A img x s0 ∗ (cmkLowStack s0.sp ∗ R) := by
      have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
      rwa [emp_sepConj] at hm2'
    have hmodel := cmk_model_past_no_chain F x hci hc_lt
    exact LibsignalSession.reaches_outcome_steps (hsteps1.trans hsteps2)
      (cmk_dup_0xb4_outcome_x himg x R s0 s2 hpc2 hrun2 hsp2 hsp2_align
        ⟨htr2.1.trans (htr1.1.trans htrace), htr2.2.trans (htr1.2.trans hvregs)⟩ hx20_2 hx22_2 hx28_2 hmodel hm2_pre)
  | some ci =>
    rw [hci] at hres
    rcases hres with ⟨hx0_1, hx1_nat⟩
    have hi : ci < x.st.receiverChains.length := findIdx?_some_lt_length hci
    have hgi : ci < x.G.chains.length := by omega
    have hch_lt : x.st.receiverChains.length * 104 < 2 ^ 63 := by rwa [← hcs_len]
    have hx1_1 : s1.readReg64 .x1 = BitVec.ofNat 64 ci := by
      apply BitVec.eq_of_toNat_eq
      rw [hx1_nat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show ci < 2 ^ 64 by omega)]
    have hm1_chain : s1.mem ⊨
        ⌜RatchetChainProps x.G x.st ci hgi hi⌝ ∗
        (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
         ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
           BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
         vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
           (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
         ratchetChainRest A x.self x.G x.st ci hgi hi ∗
         (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
         memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
         stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
         cmkSavedRegs s0.sp s0 ∗ A.pool ∗ (cmkLowStack s0.sp ∗ R)) := by
      unfold cmkPreLoopHeap at hm1_pre
      have hm1_c := Satisfies.mono
        (sepConj_mono_left (sepConj_mono_left (ratchetAt_expose_chain A x.self x.G x.st hi hgi)))
        hm1_pre
      exact Satisfies.of_eq hm1_c
    rw [satisfies_pure_sepConj] at hm1_chain
    rcases hm1_chain with ⟨hprops, hm1_c⟩
    have hkl : x.G.chains[ci].keys.length = x.st.receiverChains[ci].messageKeys.length :=
      hprops.keys_len
    have hmax_c : x.st.receiverChains[ci].messageKeys.length ≤ maxMessageKeys := hprops.mk_max
    have hzip_len :
        (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length =
          x.st.receiverChains[ci].messageKeys.length := by simp [hkl]
    by_cases hgks : (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length = 0
    · have hm1_empty : s1.mem ⊨
          ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ 0#64) ∗
          (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
           vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
             (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
           ratchetChainRest A x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗ A.pool ∗ (cmkLowStack s0.sp ∗ R)) := by
        rw [hgks] at hm1_c; exact Satisfies.of_eq hm1_c
      obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hsp2, hsp2_align,
        hx20_2, hx22_2, hx28_2, htr2, hP2⟩ :=
        sepWP_to_reaches_pc
          (cmk_after_find_empty_wp_x x.G.chainsPtr (x.counter.zeroExtend 64) x.ret
            (x.ck.index.zeroExtend 64) ci x.st.receiverChains.length hi hch_lt
            s0 s1 hpc1 hrun1 hsp1 hsp1_align hx0_1 hx1_1 hx20_1 hx21_1 hx22_1 hx24_1 hx28_1)
          hm1_empty hL1
      have hm2_pre : s2.mem ⊨ cmkPreLoopHeap A img x s0 ∗ (cmkLowStack s0.sp ∗ R) := by
        unfold cmkPreLoopHeap
        have hm2' := Satisfies.mono (sepConj_mono_left hP2) hm2
        have hreassemble := ratchetAt_reassemble_self A x.self x.G x.st hi hgi hprops
        rw [hgks] at hreassemble
        have hm2'' : s2.mem ⊨
            (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
              ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄ 0#64) ∗
              vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
                (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
              ratchetChainRest A x.self x.G x.st ci hgi hi) ∗
            ((x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
              memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
              stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
              cmkSavedRegs s0.sp s0 ∗ A.pool ∗ (cmkLowStack s0.sp ∗ R)) :=
          Satisfies.of_eq hm2'
        exact Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hreassemble) hm2'')
      have hmk_nil : x.st.receiverChains[ci].messageKeys = [] :=
        List.eq_nil_of_length_eq_zero (by omega)
      have hfind_none :
          x.st.receiverChains[ci].messageKeys.findIdx? (fun k => k.counter == x.counter) = none := by
        simp [hmk_nil]
      have hmodel := cmk_model_past_miss_chain F x hci hi hfind_none hc_lt
      exact LibsignalSession.reaches_outcome_steps (hsteps1.trans hsteps2)
        (cmk_dup_0xb4_outcome_x himg x R s0 s2 hpc2 hrun2 hsp2 hsp2_align
          ⟨htr2.1.trans (htr1.1.trans htrace), htr2.2.trans (htr1.2.trans hvregs)⟩ hx20_2 hx22_2 hx28_2 hmodel hm2_pre)
    · have hmk_pos : 0 < (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length :=
        Nat.pos_of_ne_zero hgks
      have hmk_max :
          (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length ≤ maxMessageKeys := by
        rw [hzip_len]; exact hmax_c
      have hm1_nonempty : s1.mem ⊨
          (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
           ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
             BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length)) ∗
          (vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
             (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
           ratchetChainRest A x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗ cmkLowStack s0.sp ∗ A.pool ∗ R) :=
        Satisfies.of_eq hm1_c
      obtain ⟨s2, hsteps2, hpc2, hrun2, P2, hm2, hsp2, hsp2_align,
        hx2_2, hx8_2, hx19_2, hx20_2, hx22_2, hx24_2, hx27_2, hx28_2, hx29_2, htr2, hP2⟩ :=
        sepWP_to_reaches_pc
          (cmk_after_find_nonempty_wp_x x.G.chainsPtr x.G.chains[ci].mkPtr
            (x.counter.zeroExtend 64) x.ret (x.ck.index.zeroExtend 64) (s0.sp - 96#64)
            ci x.st.receiverChains.length
            (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length
            hi hch_lt hmk_pos hmk_max s0 s1 hpc1 hrun1 hsp1 hsp1_align
            hx0_1 hx1_1 hx20_1 hx21_1 hx22_1 hx24_1 hx28_1 hx29_1)
          hm1_nonempty hL1
      have hm2' : s2.mem ⊨
          (((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 56#64) ↦₆₄ x.G.chains[ci].mkPtr) ∗
           ((x.G.chainsPtr + BitVec.ofNat 64 (ci * 104) + 64#64) ↦₆₄
             BitVec.ofNat 64 (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length) ∗
           vecBuf A 104 8 (messageKeyAt A) x.G.chains[ci].mkCap x.G.chains[ci].mkPtr
             (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys) ∗
           ratchetChainRest A x.self x.G x.st ci hgi hi ∗
           (x.theirA ↦ₛ x.their.bytes.toList) ∗ (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
           memRegion x.ret 88 ∗ (logFilterAddr img ↦₆₄ 0#64) ∗
           stackAt (s0.sp - 480#64) 7712 ∗ memRegion (s0.sp - 480#64) 384 ∗
           cmkSavedRegs s0.sp s0 ∗ cmkLowStack s0.sp ∗ A.pool) ∗ R :=
        Satisfies.of_eq (Satisfies.mono (sepConj_mono_left hP2) hm2)
      have hsteps12 := hsteps1.trans hsteps2
      exact LibsignalSession.reaches_outcome_steps hsteps12
        (cmk_pos_loop_0x94_outcome_x hA himg x R s0 hci hi hgi hprops hc_lt
          (x.G.chains[ci].keys.zip x.st.receiverChains[ci].messageKeys).length 0 s2
          (by omega) hmk_pos rfl
          (hsteps12.frozenLoaded hfrozen) (hsteps12.symtab_eq.trans hsym)
          hpc2 hrun2 hsp2 hsp2_align
          ⟨htr2.1.trans (htr1.1.trans htrace), htr2.2.trans (htr1.2.trans hvregs)⟩
          hx2_2 hx8_2 hx19_2 hx20_2 hx22_2 hx24_2 hx27_2 hx28_2 hx29_2 hm2')

end Proofs.libsignal.Stage1X.CmkX
