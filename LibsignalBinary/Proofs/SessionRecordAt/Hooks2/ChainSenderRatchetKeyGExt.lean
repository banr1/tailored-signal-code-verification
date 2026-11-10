/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG
public import LibsignalBinary.Proofs.SessionRecordAt.Hooks2.DeserDefsX
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false
/-!
# `message::merge<Chain>` Tags 1 and 2 (`sender_ratchet_key`) Leaf Proofs

Proves `chainSenderRatchetKeyG_ok` (`+0x120 → +0x120` on tag 1 `sender_ratchet_key` and tag 2
`sender_ratchet_key_private` in `prost::encoding::message::merge<Chain>`), including X-stack
(`_atW`, `_atWA`) and relocatable `[LibsignalPlacement]` (`lsProg_11 H`, Block `11`) variants.
-/

namespace CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost (sliceCursorAt sliceCursorAfter BytesMergeOk)
open CryptoVerification.E2E.Record
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace ChainMergeStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre_seedChain (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre_seedChain (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre_seedChain (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre_seedChain (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre_seedChain (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre_seedChain (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local simp, local arm64_norm]
theorem getLsbD_63_eq_seedChain (v : BitVec 64) :
    v.getLsbD 63 = !(v >>> 56).ult 128#64 := by
  bv_robdd

end ChainMergeStateSimp
open ChainMergeStateSimp

attribute [local arm64_norm, local wp_norm]
  calleeSavedVRegs_advancePC calleeSavedVRegs_setPC calleeSavedVRegs_setMem
  calleeSavedVRegs_setPState calleeSavedVRegs_writeReg64 calleeSavedVRegs_writeReg32
  calleeSavedVRegs_writeReg
attribute [local arm64_norm ↓, local wp_norm ↓]
  ChainMergeStateSimp.calleeSavedVRegs_setPC_pre_seedChain
  ChainMergeStateSimp.calleeSavedVRegs_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setPC_pre_seedChain
  ChainMergeStateSimp.sp_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setPC_pre_seedChain
  ChainMergeStateSimp.readReg64_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setPC_pre_seedChain
  ChainMergeStateSimp.readReg32_setMem_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setPC_pre_seedChain
  ChainMergeStateSimp.readReg_setMem_setPC_pre_seedChain

attribute [local simp, local arm64_norm] ChainMergeStateSimp.getLsbD_63_eq_seedChain




/-! ## 1. Stepping Tag 1 (`pbBytes 1 srk`) and Tag 2 (`pbBytes 2 priv`) -/


theorem step_chainTag1_g_atWA (img : Obj.Image) {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hBM : Prost.X.BytesMergeOkW img A ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (bs0 srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128)
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      LoopRegsPreserved s0 sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A a srk ∗
          (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          A.pool ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A a bs0 ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        A.pool ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
  have hpb : pbBytes 1 srk = 0x0a#8 :: BitVec.ofNat 8 srk.length :: srk :=
    pbBytes_lt128_eq_seedChain 1 (by decide) srk hsrk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)
  have hcons_eq : pbBytes 1 srk ++ (rest ++ tail) = 0x0a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x0a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x0a#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x0a#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMergeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
      s1.status = .Running →
      s1.sp = sp0 - 256#64 →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      s1.trace = s_init.trace →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMergeName + 0x25c#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a →
      s1.readReg64 .x2 = bufRef →
      LoopRegsPreserved s0 s1 →
      SepWPp (SP2Ext img.base ext) ret s1
        ((vecU8 A a bs0 ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          A.pool ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x0a#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x120 0x144
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x188 0x1b4
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x24c 0x258
    dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    simp only [sepConj_assoc]
    iterate 26 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_atWA (x := dummySeedGhost) img hBM
      a bufRef slot (ptr + 1#64) sp0
      ((SP2Ext img.base ext).fnAddr chainMergeName + 0x25c#64)
      bs0 srk (rest ++ tail) hsrk_lt hrem1_lt
      hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x25c 0x260
    dsimp only [SP2Ext, contractProg, chainMergeName] at hpc2 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (288)) hF2 hsym2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    have hregs2 : LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
      (hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm]⟩))
    rw [pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
      ← pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_chainTag1_g_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hBM : Prost.X.BytesMergeOkW img A0 ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (bs0 srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128)
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      LoopRegsPreserved s0 sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 a srk ∗
          (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 a bs0 ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
  have hp : A0.pool = emp := rfl
  have h := step_chainTag1_g_atWA (A := A0) (R := R) img hBM a bufRef slot ptr sp0 bs0 srk rest tail
    hsrk_lt hlen_lt hpc hrun hsp halign hF hsym htr hx19 hx20 hx24
    (fun sm h1 h2 h3 h4 h5 h6 h7 => by rw [hp, emp_sepConj]; exact hnext sm h1 h2 h3 h4 h5 h6 h7)
  rwa [hp, emp_sepConj] at h

theorem step_chainTag2_g_atWA (img : Obj.Image) {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hBM : Prost.X.BytesMergeOkW img A ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (bs0 priv rest tail : List (BitVec 8))
    (hpriv_lt : priv.length < 128)
    (hlen_lt : (pbBytes 2 priv ++ rest ++ tail).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      LoopRegsPreserved s0 sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A (a + 0x18#64) priv ∗
          (ptr ↦ₛ pbBytes 2 priv) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 priv).length) (rest ++ tail) ∗
          A.pool ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A (a + 0x18#64) bs0 ∗
        sliceCursorAt slot ptr (pbBytes 2 priv ++ (rest ++ tail)) ∗
        A.pool ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
  have hpb : pbBytes 2 priv = 0x12#8 :: BitVec.ofNat 8 priv.length :: priv :=
    pbBytes_lt128_eq_seedChain 2 (by decide) priv hpriv_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)
  have hcons_eq : pbBytes 2 priv ++ (rest ++ tail) = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x12#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = (SP2Ext img.base ext).fnAddr chainMergeName +
        bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")) →
      s1.status = .Running →
      s1.sp = sp0 - 256#64 →
      img.FrozenLoaded s1 →
      s1.symtab = img.symtab →
      s1.trace = s_init.trace →
      s1.readReg64 .lr = (SP2Ext img.base ext).fnAddr chainMergeName + 0x1d0#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x18#64 →
      s1.readReg64 .x2 = bufRef →
      LoopRegsPreserved s0 s1 →
      SepWPp (SP2Ext img.base ext) ret s1
        ((vecU8 A (a + 0x18#64) bs0 ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          A.pool ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
  · intro hnext1
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x120 0x144
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x188 0x1cc
    dsimp only [SP2Ext, contractProg, chainMergeName] at hpc hnext1 ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]"))) hF hsym ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    simp only [sepConj_assoc]
    iterate 28 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hF1 hsym1 (by simp only [htr, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_atWA (x := dummySeedGhost) img hBM
      (a + 0x18#64) bufRef slot (ptr + 1#64) sp0
      ((SP2Ext img.base ext).fnAddr chainMergeName + 0x1d0#64)
      bs0 priv (rest ++ tail) hpriv_lt hrem1_lt
      hpc1 hrun1 hsp1 halign hF1 hsym1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hF2 hsym2 htr2 hcs2 hx0_2
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x1d0 0x1d0
    chainMerge_fetches_range img.base (Rust.withPanics ext) 0x260 0x260
    dsimp only [SP2Ext, contractProg, chainMergeName] at hpc2 hnext ⊢
    generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]" = entry
    examples_hide_fetches
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine SepWPp.of_sepWP_frozen_seedChain (mid := entry + bv% (288)) hF2 hsym2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hF3 hsym3
    have hregs2 : LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hF3 hsym3 (by simp only [htr2, arm64_norm])
      (hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm]⟩))
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_chainTag2_g_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hBM : Prost.X.BytesMergeOkW img A0 ext)
    (a bufRef slot ptr sp0 : BitVec 64)
    (bs0 priv rest tail : List (BitVec 8))
    (hpriv_lt : priv.length < 128)
    (hlen_lt : (pbBytes 2 priv ++ rest ++ tail).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : img.FrozenLoaded s0)
    (hsym : s0.symtab = img.symtab)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (SP2Ext img.base ext).fnAddr chainMergeName + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      img.FrozenLoaded sm →
      sm.symtab = img.symtab →
      sm.trace = s_init.trace →
      LoopRegsPreserved s0 sm →
      SepWPp (SP2Ext img.base ext) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          (ptr ↦ₛ pbBytes 2 priv) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 priv).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (SP2Ext img.base ext) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x18#64) bs0 ∗
        sliceCursorAt slot ptr (pbBytes 2 priv ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
  have hp : A0.pool = emp := rfl
  have h := step_chainTag2_g_atWA (A := A0) (R := R) img hBM a bufRef slot ptr sp0 bs0 priv rest tail
    hpriv_lt hlen_lt hpc hrun hsp halign hF hsym htr hx19 hx20 hx24
    (fun sm h1 h2 h3 h4 h5 h6 h7 => by rw [hp, emp_sepConj]; exact hnext sm h1 h2 h3 h4 h5 h6 h7)
  rwa [hp, emp_sepConj] at h

theorem chainSenderRatchetKeyG_ok_atWA (img : Obj.Image) (A : RustAlloc)
    {ext : String → Option (State → State)}
    (hC : DeserializeCalleesAtWA img A ext) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2)
    (hs : ChainLoopGAtWA img A ext x R s0 k s) :
    ChainStepGAtWA img A ext x R s0 s (ChainLoopGAtWA img A ext x R s0 (k + 1)) := by
  intro hL
  obtain ⟨_, _, hBM, _⟩ := hC
  rcases hs with ⟨hpc, hrun, htr, hvregs, hsym, hF, hsp, hal, hx29, hx19, hx20, hx24, hx21, hx22, hx25,
    hx26, hcOk, hlen, hmem⟩
  have hpc' : s.pc = chainPCAtX img ext 0x120#64 := hpc
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 := by
    have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    rwa [hsp] at h1
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_256 hsp_sub_align
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc
  have hlen_rem : ((x.c.fields[k]'hk).enc ++ rest ++ x.tail).length < 2 ^ 62 := by
    have h1 := hlen
    rw [payload_append_eq_preBytes x.c x.tail k, drop_flatMap_enc hk] at h1
    simp only [rest, List.length_append] at h1 ⊢
    omega
  generalize hfl_eq : x.c.fields[k]'hk = fl
  cases fl with
  | ck i key =>
    rw [hfl_eq] at htag
    simp [ChainField.tag] at htag
  | key mk =>
    rw [hfl_eq] at htag
    simp [ChainField.tag] at htag
  | srk b =>
    have hb_mem : ChainField.srk b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_srk_length_lt hcOk hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 1 b := by
      rw [hfl_eq]
      exact lenField_eq_pbBytes 1 (Or.inl rfl) b hb_lt
    have hlen_pb : (pbBytes 1 b ++ rest ++ x.tail).length < 2 ^ 62 := by
      rwa [← henc]
    let ck := chainGAfter x.c k
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗
      vecU8 A (x.a + 0x18#64) ck.priv ∗
      prostChainGRestAt A x.a ck ∗
      chainMergeSavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A x.a ck.srk ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          A.pool ∗
          stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F) ∗ R := by
      rw [prostChainGAt_eq_split A x.a ck,
        sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (SP2Ext img.base ext)
        (chainPCAtX img ext 0x120#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A x.a ck.srk ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          A.pool ∗
          stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F)
        (fun sm Pm =>
          (sm.mem ⊨ Pm ∗ R) → ChainLoopGAtWA img A ext x R s0 (k + 1) sm)
        (fun sf Pf =>
          (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
      refine step_chainTag1_g_atWA img hBM x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        ck.srk b rest x.tail hb_lt hlen_pb hpc' hrun hsp hsp0_align hF hsym htr hx19 hx20 hx24 ?_
      intro sm hpcm hrunm hspm hFm hsymm htrm hregsm
      refine SepWPp.done hpcm hrunm ?_
      intro hmem_m
      have hal_m : sm.spAligned = true := by
        simp only [State.spAligned, hspm, ← hsp]
        exact hal
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.trans hvregs, hsymm, hFm, hspm, hal_m,
        hregsm.2.2.2.2.2.2.2.1.trans hx29,
        hregsm.1.trans hx19,
        hregsm.2.1.trans hx20,
        hregsm.2.2.2.2.1.trans hx24,
        hregsm.2.2.1.trans hx21,
        hregsm.2.2.2.1.trans hx22,
        hregsm.2.2.2.2.2.1.trans hx25,
        hregsm.2.2.2.2.2.2.1.trans hx26,
        hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗
            vecU8 A x.a b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 1 b) ∗
            sliceCursorAt x.slot
              (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 1 b).length)
              (rest ++ x.tail) ∗
            A.pool ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F) =
          (prostChainGAt A x.a (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            A.pool ∗
            stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗
            chainMergeSavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, prostChainGAt_apply_srk A x.a ck b,
          ← henc, ← curPtr_succ x.ptr hk,
          sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]
        ac_rfl
      rw [hpost_eq] at hmem_m
      simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, hex⟩ := hwp R hmem_pre hL
    rcases hex with ⟨_, _, Pf, hmf, hloop⟩ | ⟨hpan, Pf, hmf, hpan_mem⟩ | ⟨_, hoom⟩
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  | priv b =>
    have hb_mem : ChainField.priv b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_priv_length_lt hcOk hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 2 b := by
      rw [hfl_eq]
      exact lenField_eq_pbBytes 2 (Or.inr rfl) b hb_lt
    have hlen_pb : (pbBytes 2 b ++ rest ++ x.tail).length < 2 ^ 62 := by
      rwa [← henc]
    let ck := chainGAfter x.c k
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗
      vecU8 A x.a ck.srk ∗
      prostChainGRestAt A x.a ck ∗
      chainMergeSavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A (x.a + 0x18#64) ck.priv ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          A.pool ∗
          stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F) ∗ R := by
      rw [prostChainGAt_eq_split A x.a ck,
        sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (SP2Ext img.base ext)
        (chainPCAtX img ext 0x120#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A (x.a + 0x18#64) ck.priv ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          A.pool ∗
          stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F)
        (fun sm Pm =>
          (sm.mem ⊨ Pm ∗ R) → ChainLoopGAtWA img A ext x R s0 (k + 1) sm)
        (fun sf Pf =>
          (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
      refine step_chainTag2_g_atWA img hBM x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        ck.priv b rest x.tail hb_lt hlen_pb hpc' hrun hsp hsp0_align hF hsym htr hx19 hx20 hx24 ?_
      intro sm hpcm hrunm hspm hFm hsymm htrm hregsm
      refine SepWPp.done hpcm hrunm ?_
      intro hmem_m
      have hal_m : sm.spAligned = true := by
        simp only [State.spAligned, hspm, ← hsp]
        exact hal
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.trans hvregs, hsymm, hFm, hspm, hal_m,
        hregsm.2.2.2.2.2.2.2.1.trans hx29,
        hregsm.1.trans hx19,
        hregsm.2.1.trans hx20,
        hregsm.2.2.2.2.1.trans hx24,
        hregsm.2.2.1.trans hx21,
        hregsm.2.2.2.1.trans hx22,
        hregsm.2.2.2.2.2.1.trans hx25,
        hregsm.2.2.2.2.2.2.1.trans hx26,
        hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗
            vecU8 A (x.a + 0x18#64) b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 2 b) ∗
            sliceCursorAt x.slot
              (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 2 b).length)
              (rest ++ x.tail) ∗
            A.pool ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F) =
          (prostChainGAt A x.a (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            A.pool ∗
            stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗
            chainMergeSavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, prostChainGAt_apply_priv A x.a ck b,
          ← henc, ← curPtr_succ x.ptr hk,
          sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]
        ac_rfl
      rw [hpost_eq] at hmem_m
      simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, hex⟩ := hwp R hmem_pre hL
    rcases hex with ⟨_, _, Pf, hmf, hloop⟩ | ⟨hpan, Pf, hmf, hpan_mem⟩ | ⟨_, hoom⟩
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim

theorem chainSenderRatchetKeyG_ok_atW (img : Obj.Image)
    {ext : String → Option (State → State)}
    (hC : DeserializeCalleesAtW img ext) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2)
    (hs : ChainLoopGAtW img ext x R s0 k s) :
    ChainStepGAtW img ext x R s0 s (ChainLoopGAtW img ext x R s0 (k + 1)) := by
  have hp : A0.pool = emp := rfl
  have hsA : ChainLoopGAtWA img A0 ext x R s0 k s := by
    simpa only [ChainLoopGAtWA, ChainLoopGAtW, hp, emp_sepConj] using hs
  intro hL
  obtain ⟨sf, hsteps, hex⟩ := chainSenderRatchetKeyG_ok_atWA img A0 hC x R s0 k s hk htag hsA hL
  refine ⟨sf, hsteps, hex.imp ?_ id⟩
  intro hloop
  simpa only [ChainLoopGAtWA, ChainLoopGAtW, hp, emp_sepConj] using hloop

/-! ## 2. Relocatable `[LibsignalPlacement]` Proof of `message::merge<Chain>` Tags 1 & 2 (`lsProg_11 H`) -/

section Placed

open Arm64.Obj CryptoVerification.E2E.Record.Placed

theorem L1_ChainSenderRatchetKeyGExt_Placed : True := trivial

private theorem of_sepWP_lscro [LibsignalPlacement]
    {prog : Program} {mid ret : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded lsmpl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hnext⟩ | ⟨_, _hoom⟩⟩ := h.elim hm hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ :=
    hnext (hcrl.of_keepsFrozen hsteps.keepsFrozen) R hmm (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem step_chainTag1_g_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hBM : Prost.X.BytesMergePlacedOkW A0 H)
    (a bufRef slot ptr sp0 : BitVec 64)
    (bs0 srk rest tail : List (BitVec 8))
    (hsrk_lt : srk.length < 128)
    (hlen_lt : (pbBytes 1 srk ++ rest ++ tail).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      LoopRegsPreserved s0 sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 a srk ∗
          (ptr ↦ₛ pbBytes 1 srk) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 1 srk).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 a bs0 ∗
        sliceCursorAt slot ptr (pbBytes 1 srk ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
  have hpb : pbBytes 1 srk = 0x0a#8 :: BitVec.ofNat 8 srk.length :: srk :=
    pbBytes_lt128_eq_seedChain 1 (by decide) srk hsrk_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)
  have hcons_eq : pbBytes 1 srk ++ (rest ++ tail) = 0x0a#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x0a#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x0a#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x0a#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = lsmpl.base 7 →
      s1.status = .Running →
      s1.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s_init.trace →
      s1.readReg64 .lr = (blkPl_11).base + 0x25c#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a →
      s1.readReg64 .x2 = bufRef →
      LoopRegsPreserved s0 s1 →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8 A0 a bs0 ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x0a#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
  · intro hnext1
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
    refine of_sepWP_lscro (mid := lsmpl.base 7) hcrl ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    simp only [sepConj_assoc]
    iterate 26 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcrl1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hcrl1 (by simp only [htr, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 srk.length] ++ srk ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_placedW (x := dummySeedGhost) hBM
      a bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x25c#64)
      bs0 srk (rest ++ tail) hsrk_lt hrem1_lt
      hpc1 hrun1 hsp1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine of_sepWP_lscro (mid := (blkPl_11).base + 0x120#64) hcrl2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcrl3
    have hregs2 : LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hcrl3 (by simp only [htr2, arm64_norm])
      (hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm]⟩))
    rw [pbBytes_ptr_advance_seedChain 1 (by decide) ptr srk hsrk_lt,
      ← pbBytes_pointsTo_combine_seedChain 1 (by decide) ptr srk hsrk_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem step_chainTag2_g_placedW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hBM : Prost.X.BytesMergePlacedOkW A0 H)
    (a bufRef slot ptr sp0 : BitVec 64)
    (bs0 priv rest tail : List (BitVec 8))
    (hpriv_lt : priv.length < 128)
    (hlen_lt : (pbBytes 2 priv ++ rest ++ tail).length < 2 ^ 62)
    {R : SepProp}
    {ret : BitVec 64} {s_init s0 : State} {F : SepProp}
    {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_11).base + 0x120#64)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (htr : s0.trace = s_init.trace)
    (hx19 : s0.readReg64 .x19 = bufRef)
    (hx20 : s0.readReg64 .x20 = a)
    (hx24 : s0.readReg64 .x24 = BitVec.ofNat 64 tail.length)
    (hnext : ∀ (sm : State),
      sm.pc = (blkPl_11).base + 0x120#64 →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s_init.trace →
      LoopRegsPreserved s0 sm →
      SepWPp (lsProg_11 H) ret sm
        (((bufRef ↦₆₄ slot) ∗
          vecU8 A0 (a + 0x18#64) priv ∗
          (ptr ↦ₛ pbBytes 2 priv) ∗
          sliceCursorAt slot (ptr + BitVec.ofNat 64 (pbBytes 2 priv).length) (rest ++ tail) ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s0
      (((bufRef ↦₆₄ slot) ∗
        vecU8 A0 (a + 0x18#64) bs0 ∗
        sliceCursorAt slot ptr (pbBytes 2 priv ++ (rest ++ tail)) ∗
        stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ F)
      Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R)) := by
  have hpb : pbBytes 2 priv = 0x12#8 :: BitVec.ofNat 8 priv.length :: priv :=
    pbBytes_lt128_eq_seedChain 2 (by decide) priv hpriv_lt
  let rem1 : List (BitVec 8) := [BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)
  have hcons_eq : pbBytes 2 priv ++ (rest ++ tail) = 0x12#8 :: rem1 := by
    rw [hpb]; simp [rem1, List.cons_append, List.append_assoc]
  have hlen_gt : tail.length < (0x12#8 :: rem1).length := by
    simp only [rem1, List.length_cons, List.length_append]; omega
  have hlen_cons_lt : (0x12#8 :: rem1).length < 2 ^ 62 := by
    rw [← hcons_eq]; simpa [List.append_assoc] using hlen_lt
  have hule_ls := ule_ofNat_of_gt_false_seedChain62 hlen_gt hlen_cons_lt
  have hult_ls := ult_ofNat_of_gt_true_seedChain62 hlen_gt hlen_cons_lt
  have hsub1 := len_cons_sub_one_seedChain 0x12#8 rem1
  refine (?_ :
    (∀ (s1 : State),
      s1.pc = lsmpl.base 7 →
      s1.status = .Running →
      s1.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s_init.trace →
      s1.readReg64 .lr = (blkPl_11).base + 0x1d0#64 →
      (s1.readReg64 .x0).setWidth 8 = 2#8 →
      s1.readReg64 .x1 = a + 0x18#64 →
      s1.readReg64 .x2 = bufRef →
      LoopRegsPreserved s0 s1 →
      SepWPp (lsProg_11 H) ret s1
        ((vecU8 A0 (a + 0x18#64) bs0 ∗
          (bufRef ↦₆₄ slot) ∗
          sliceCursorAt slot (ptr + 1#64) rem1 ∗
          stackAt (sp0 - 256#64) chainMergeSubStackX) ∗ ((ptr ↦₈ 0x12#8) ∗ F))
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s_init sf ∗ R))) → _) ?_
  · intro hnext1
    have h19 : s0.readReg64 (Reg.gpr 19#5) = bufRef := hx19
    have h20 : s0.readReg64 (Reg.gpr 20#5) = a := hx20
    have h24 : s0.readReg64 (Reg.gpr 24#5) = BitVec.ofNat 64 tail.length := hx24
    refine of_sepWP_lscro (mid := lsmpl.base 7) hcrl ?_
    rw [hcons_eq]
    unfold sliceCursorAt
    rw [pointsToBytes_cons]
    simp only [sepConj_assoc]
    iterate 28 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm]) ?_
    intro hcrl1
    refine SepWPp.mono_pre_seedChain ?_ (hnext1 _ (by simp only [arm64_norm]) (by simp only [hrun, arm64_norm])
      (by simp only [hsp, arm64_norm]) hcrl1 (by simp only [htr, arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      (by simp only [arm64_norm]) (by simp only [arm64_norm])
      ⟨by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm],
       by simp only [arm64_norm], by simp only [arm64_norm], by simp only [arm64_norm]⟩)
    unfold sliceCursorAt
    exact sep_ac_seedChain (by ac_rfl)
  · intro s1 hpc1 hrun1 hsp1 hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 hregs1
    have hrem1_lt : ([BitVec.ofNat 8 priv.length] ++ priv ++ (rest ++ tail)).length < 2 ^ 62 := by
      simp only [List.length_cons] at hlen_cons_lt; exact Nat.lt_of_succ_lt hlen_cons_lt
    refine step_chainMerge_bytesMerge_placedW (x := dummySeedGhost) hBM
      (a + 0x18#64) bufRef slot (ptr + 1#64) sp0
      ((blkPl_11).base + 0x1d0#64)
      bs0 priv (rest ++ tail) hpriv_lt hrem1_lt
      hpc1 hrun1 hsp1 halign hcrl1 htr1 hlr1 hx0_1 hx1_1 hx2_1 rfl ?_
    intro s2 hpc2 hrun2 hsp2 hcrl2 htr2 hcs2 hx0_2
    have h0_2 : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    refine of_sepWP_lscro (mid := (blkPl_11).base + 0x120#64) hcrl2 ?_
    iterate 2 wp_step
    refine SepWP.done (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm]) ?_
    intro hcrl3
    have hregs2 : LoopRegsPreserved s0 s2 := hregs1.trans (.of_calleeSaved hcs2)
    refine SepWPp.mono_pre_seedChain ?_ (hnext _ (by simp only [arm64_norm]) (by simp only [hrun2, arm64_norm])
      (by simp only [hsp2, arm64_norm]) hcrl3 (by simp only [htr2, arm64_norm])
      (hregs2.trans ⟨by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm], by simp only [arm64_norm],
        by simp only [arm64_norm]⟩))
    rw [pbBytes_ptr_advance_seedChain 2 (by decide) ptr priv hpriv_lt,
      ← pbBytes_pointsTo_combine_seedChain 2 (by decide) ptr priv hpriv_lt]
    exact sep_ac_seedChain (by ac_rfl)

theorem chainSenderRatchetKeyG_placed_okW [LibsignalPlacement]
    {H : LibsignalHooks}
    (hC : DeserializeCalleesPlacedW H) (x : ChainMergeGenGhost) (R : SepProp) (s0 : State) (k : Nat)
    (s : State) (hk : k < x.c.fields.length)
    (htag : (x.c.fields[k]'hk).tag = 1 ∨ (x.c.fields[k]'hk).tag = 2)
    (hs : ChainLoopGPlacedW x R s0 k s) :
    ChainStepGPlacedW H x R s0 s (ChainLoopGPlacedW x R s0 (k + 1)) := by
  intro hL
  obtain ⟨_, _, hBM, _⟩ := hC
  rcases hs with ⟨hpc, hrun, htr, hvregs, hcrl, hsp, hal, hx29, hx19, hx20, hx24, hx21, hx22, hx25,
    hx26, hcOk, hlen, hmem⟩
  have hpc' : s.pc = chainPlacedPC 0x120#64 := hpc
  have hsp_sub_align : (s0.sp - 256#64) &&& 15#64 = 0#64 := by
    have h1 : s.sp &&& 15#64 = 0#64 := by simpa [State.spAligned, beq_iff_eq] using hal
    rwa [hsp] at h1
  have hsp0_align : s0.sp &&& 15#64 = 0#64 := sp0_aligned_of_sub_256 hsp_sub_align
  let rest : List (BitVec 8) := (x.c.fields.drop (k + 1)).flatMap ChainField.enc
  have hlen_rem : ((x.c.fields[k]'hk).enc ++ rest ++ x.tail).length < 2 ^ 62 := by
    have h1 := hlen
    rw [payload_append_eq_preBytes x.c x.tail k, drop_flatMap_enc hk] at h1
    simp only [rest, List.length_append] at h1 ⊢
    omega
  generalize hfl_eq : x.c.fields[k]'hk = fl
  cases fl with
  | ck i key =>
    rw [hfl_eq] at htag
    simp [ChainField.tag] at htag
  | key mk =>
    rw [hfl_eq] at htag
    simp [ChainField.tag] at htag
  | srk b =>
    have hb_mem : ChainField.srk b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_srk_length_lt hcOk hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 1 b := by
      rw [hfl_eq]
      exact lenField_eq_pbBytes 1 (Or.inl rfl) b hb_lt
    have hlen_pb : (pbBytes 1 b ++ rest ++ x.tail).length < 2 ^ 62 := by
      rwa [← henc]
    let ck := chainGAfter x.c k
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗
      vecU8 A0 (x.a + 0x18#64) ck.priv ∗
      prostChainGRestAt A0 x.a ck ∗
      chainMergeSavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A0 x.a ck.srk ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F) ∗ R := by
      rw [prostChainGAt_eq_split A0 x.a ck,
        sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (lsProg_11 H)
        (chainPlacedPC 0x120#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A0 x.a ck.srk ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 1 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F)
        (fun sm Pm =>
          (sm.mem ⊨ Pm ∗ R) → ChainLoopGPlacedW x R s0 (k + 1) sm)
        (fun sf Pf =>
          (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
      refine step_chainTag1_g_placedW hBM x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        ck.srk b rest x.tail hb_lt hlen_pb hpc' hrun hsp hsp0_align hcrl htr hx19 hx20 hx24 ?_
      intro sm hpcm hrunm hspm hcrlm htrm hregsm
      refine SepWPp.done hpcm hrunm ?_
      intro hmem_m
      have hal_m : sm.spAligned = true := by
        simp only [State.spAligned, hspm, ← hsp]
        exact hal
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.trans hvregs, hcrlm, hspm, hal_m,
        hregsm.2.2.2.2.2.2.2.1.trans hx29,
        hregsm.1.trans hx19,
        hregsm.2.1.trans hx20,
        hregsm.2.2.2.2.1.trans hx24,
        hregsm.2.2.1.trans hx21,
        hregsm.2.2.2.1.trans hx22,
        hregsm.2.2.2.2.2.1.trans hx25,
        hregsm.2.2.2.2.2.2.1.trans hx26,
        hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗
            vecU8 A0 x.a b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 1 b) ∗
            sliceCursorAt x.slot
              (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 1 b).length)
              (rest ++ x.tail) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F) =
          (prostChainGAt A0 x.a (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗
            chainMergeSavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, prostChainGAt_apply_srk A0 x.a ck b,
          ← henc, ← curPtr_succ x.ptr hk,
          sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]
        ac_rfl
      rw [hpost_eq] at hmem_m
      simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, hex⟩ := hwp R hmem_pre hL
    rcases hex with ⟨_, _, Pf, hmf, hloop⟩ | ⟨hpan, Pf, hmf, hpan_mem⟩ | ⟨_, hoom⟩
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim
  | priv b =>
    have hb_mem : ChainField.priv b ∈ x.c.fields := hfl_eq ▸ List.getElem_mem hk
    have hb_lt : b.length < 128 := mem_fields_priv_length_lt hcOk hb_mem
    have henc : (x.c.fields[k]'hk).enc = pbBytes 2 b := by
      rw [hfl_eq]
      exact lenField_eq_pbBytes 2 (Or.inr rfl) b hb_lt
    have hlen_pb : (pbBytes 2 b ++ rest ++ x.tail).length < 2 ^ 62 := by
      rwa [← henc]
    let ck := chainGAfter x.c k
    let F : SepProp :=
      (x.ptr ↦ₛ preBytes x.c k) ∗
      vecU8 A0 x.a ck.srk ∗
      prostChainGRestAt A0 x.a ck ∗
      chainMergeSavedRegs s0.sp s0
    have hmem_pre : s.mem ⊨
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A0 (x.a + 0x18#64) ck.priv ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F) ∗ R := by
      rw [prostChainGAt_eq_split A0 x.a ck,
        sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail k,
        drop_flatMap_enc hk, henc] at hmem
      dsimp only [ck, F, rest] at hmem ⊢
      simp only [List.append_assoc, sepConj_assoc] at hmem ⊢
      exact Satisfies.mono (sep_ac_seedChain (by ac_rfl)) hmem
    have hwp : SepWPp (lsProg_11 H)
        (chainPlacedPC 0x120#64) s
        (((x.bufRef ↦₆₄ x.slot) ∗
          vecU8 A0 (x.a + 0x18#64) ck.priv ∗
          sliceCursorAt x.slot (curPtr x.ptr x.c k) (pbBytes 2 b ++ (rest ++ x.tail)) ∗
          stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F)
        (fun sm Pm =>
          (sm.mem ⊨ Pm ∗ R) → ChainLoopGPlacedW x R s0 (k + 1) sm)
        (fun sf Pf =>
          (sf.mem ⊨ Pf ∗ R) → (sf.mem ⊨ Serialization.allocPanic dummySeedGhost s0 sf ∗ R)) := by
      refine step_chainTag2_g_placedW hBM x.a x.bufRef x.slot (curPtr x.ptr x.c k) s0.sp
        ck.priv b rest x.tail hb_lt hlen_pb hpc' hrun hsp hsp0_align hcrl htr hx19 hx20 hx24 ?_
      intro sm hpcm hrunm hspm hcrlm htrm hregsm
      refine SepWPp.done hpcm hrunm ?_
      intro hmem_m
      have hal_m : sm.spAligned = true := by
        simp only [State.spAligned, hspm, ← hsp]
        exact hal
      refine ⟨hpcm, hrunm, htrm, hregsm.2.2.2.2.2.2.2.2.trans hvregs, hcrlm, hspm, hal_m,
        hregsm.2.2.2.2.2.2.2.1.trans hx29,
        hregsm.1.trans hx19,
        hregsm.2.1.trans hx20,
        hregsm.2.2.2.2.1.trans hx24,
        hregsm.2.2.1.trans hx21,
        hregsm.2.2.2.1.trans hx22,
        hregsm.2.2.2.2.2.1.trans hx25,
        hregsm.2.2.2.2.2.2.1.trans hx26,
        hcOk, hlen, ?_⟩
      have hpost_eq :
          (((x.bufRef ↦₆₄ x.slot) ∗
            vecU8 A0 (x.a + 0x18#64) b ∗
            (curPtr x.ptr x.c k ↦ₛ pbBytes 2 b) ∗
            sliceCursorAt x.slot
              (curPtr x.ptr x.c k + BitVec.ofNat 64 (pbBytes 2 b).length)
              (rest ++ x.tail) ∗
            stackAt (s0.sp - 256#64) chainMergeSubStackX) ∗ F) =
          (prostChainGAt A0 x.a (chainGAfter x.c (k + 1)) ∗
            (x.bufRef ↦₆₄ x.slot) ∗
            sliceCursorAfter x.slot x.ptr (x.c.payload ++ x.tail) (rest ++ x.tail) ∗
            stackAt (s0.sp - 0x100#64) chainMergeSubStackX ∗
            chainMergeSavedRegs s0.sp s0) := by
        rw [chainGAfter_succ hk, hfl_eq, prostChainGAt_apply_priv A0 x.a ck b,
          ← henc, ← curPtr_succ x.ptr hk,
          sliceCursorAfter_eq_preBytes x.slot x.ptr x.c x.tail (k + 1),
          ← pointsToBytes_preBytes_succ x.ptr hk]
        dsimp only [ck, F, rest]
        ac_rfl
      rw [hpost_eq] at hmem_m
      simpa only [sepConj_assoc] using hmem_m
    obtain ⟨sf, hsteps, hex⟩ := hwp R hmem_pre hL
    rcases hex with ⟨_, _, Pf, hmf, hloop⟩ | ⟨hpan, Pf, hmf, hpan_mem⟩ | ⟨_, hoom⟩
    · exact ⟨sf, hsteps, Or.inl (hloop hmf)⟩
    · exact ⟨sf, hsteps, Or.inr ⟨hpan, hpan_mem hmf⟩⟩
    · exact (not_satisfies_false_sepConj hoom).elim

end Placed

end CryptoVerification.E2E.Record.DeserializeGeneral.Leaf.ChainSenderRatchetKeyG


