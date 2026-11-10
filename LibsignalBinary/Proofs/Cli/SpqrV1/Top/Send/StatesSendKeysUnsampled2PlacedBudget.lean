/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

meta import Lean -- shake: keep
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled2Placed
public import LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
public import LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled2
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Relocatable `.keysUnsampled` Sub-Step (`+684..+2588`, Block `427`)

Threads `RustCliAllocBudget` through `<Authenticator>::mac_hdr`, `do_reserve_and_handle`,
and 32-byte MAC append (`+684..+2588`) in Block `427`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled2PlacedBudget

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification (LibsignalPlacement lsmpl lsρ)
open CryptoVerification.Cli.SpqrV1.Top.Send.CodePlaced (blkPC_427 blkPl_427)
open CryptoVerification.LibsignalSpqrV1 (Authenticator Bytes MlKem)
open CryptoVerification.LibsignalTripleRatchet
  (DoReserveCall LibsignalCodeRoLoaded reserveCap sessionMemcpyRegionSpec withLsCodeRoLoaded)
open CryptoVerification.RustHeap (allocHookStack vecU8 vecU8Buf)
open CryptoVerification.SpqrV1.Alloc (doReserve32Stack)
open CryptoVerification.SpqrV1.Auth
  (AuthMacHdrPinnedGhost AuthenticatorGhost authMacHdrStackX authenticatorPinAt)
open CryptoVerification.SpqrV1.ChainProofs (bytesAt_false)
open CryptoVerification.SpqrV1.Poly.NextChunk (PolyNextChunkGhost)
open CryptoVerification.SpqrV1.Top.Send
  (authHeapBufs authInlineWordsAt authenticatorPinAt_eq_inline_heap ekSentInlineWordsAt
   macHdrUnchecked_length macHdr_ok_elim memRegion_104_eq_words13 memRegion_128_eq_words16
   memRegion_24_eq_words3 memRegion_4704_2400_split_macHdr reserveCap_64_64_32
   spqrSendCalleeStack vecU8_len32_expose words16At words16At_entails_memRegion
   words3_entails_memRegion words8At)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget VmPreserved
   fitsEvents_append rustReallocEvents)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.DefsPlacedBudget
  (AllocContractsPlaced spqrSendPlacedEntry spqrSendPlacedProg)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.Phase1PlacedBudget (seq_vm_lscro)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget
  (AuthMacHdrPinnedPlacedOkX DoReserve2PlacedOkX)
open LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampledPlacedBudget.KeysUnsampledHelpers
  (authMacHdrPinned_onPanic_false_of_ok call_lscro_calleeStack_evs_sepWP
   call_lscro_calleeStack_sepWP of_sepWP_lscro_plain spqrSend_session_memcpy_region_ok_placed)
open LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserveBudget
  (doReserve1Raw32Spec doReserve1Raw32SpecWithStack)
open LibsignalBinary.Proofs.SpqrV1.Auth.MacHdrBudget
  (AuthMacHdrEnv authMacHdrEvents authMacHdrPinnedSpec fitsEnv_authMacHdr_iff)
open LibsignalBinary.Proofs.SpqrV1.Poly.NextChunk.DefsPlacedBudget (polyNextChunkPlacedSpec)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (DoReserveEnv doReserveEvents fitsEnv_doReserve_iff)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemcpyRegionBudgetSpec)

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

run_cmd Lean.Elab.Command.liftCoreM do
  for nm in [
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_sub_592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_neg592_eq_hsp,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_add_688_sub_688,
    ``CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp
  ] do
    Lean.Attribute.erase nm `arm64_norm

attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

/-! ## 1. Exact Allocator Event Sequence & Envelope (`+684 -> +2588`) -/

/-- Exact deterministic allocator event list of `.keysUnsampled` sub-step `+684 -> +2588`:
    `<Authenticator>::mac_hdr` (`authMacHdrEvents auth hdr`) followed by
    `do_reserve_and_handle` growing the 64-byte `hdr` buffer by 32 bytes to capacity 128
    (`rustReallocEvents 64 128 1`). -/
def keysUnsampledMacReserveEvents (auth : Authenticator) (hdr : Bytes) : List AllocEvent :=
  authMacHdrEvents auth hdr ++ rustReallocEvents 64 128 1

/-- Exact deterministic allocator event envelope of `.keysUnsampled` sub-step `+684 -> +2588`. -/
def KeysUnsampledMacReserveEnv (auth : Authenticator) (hdr : Bytes) (evs : List AllocEvent) : Prop :=
  evs = keysUnsampledMacReserveEvents auth hdr

theorem keysUnsampledMacReserveEnv_nonempty (auth : Authenticator) (hdr : Bytes) :
    ∃ evs, KeysUnsampledMacReserveEnv auth hdr evs :=
  ⟨keysUnsampledMacReserveEvents auth hdr, rfl⟩

@[simp]
theorem fitsEnv_keysUnsampledMacReserve_iff {M : AllocCostModel} {lim : BudgetLimits} {st : M.σ}
    {auth : Authenticator} {hdr : Bytes} :
    FitsEnv M lim st (KeysUnsampledMacReserveEnv auth hdr) ↔
      FitsEvents M lim st (keysUnsampledMacReserveEvents auth hdr) :=
  FitsEnv.eq_iff

theorem doReserveEvents_hdr64_32 (v ptr : BitVec 64) (bs : Bytes) (hlen : bs.length = 64) :
    doReserveEvents { v := v, cap := 64#64, ptr := ptr, bs := bs, additional := 32 } =
      rustReallocEvents 64 128 1 := by
  unfold doReserveEvents
  have h64_ne : ¬ ((64#64 : BitVec 64) = 0#64) := by decide
  have h64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl
  simp only [hlen, h64_ne, h64_toNat, reserveCap_64_64_32, ↓reduceIte]

theorem fitsEnv_keysUnsampledMacReserve_split {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {auth : Authenticator} {hdr : Bytes} {v ptr : BitVec 64}
    (hhdr_len : hdr.length = 64)
    (h : FitsEnv M lim st (KeysUnsampledMacReserveEnv auth hdr)) :
    FitsEnv M lim st (AuthMacHdrEnv auth hdr) ∧
    FitsEnv M lim (M.stepEvents (authMacHdrEvents auth hdr) st)
      (DoReserveEnv { v := v, cap := 64#64, ptr := ptr, bs := hdr, additional := 32 }) ∧
    M.stepEvents (keysUnsampledMacReserveEvents auth hdr) st =
      M.stepEvents
        (doReserveEvents { v := v, cap := 64#64, ptr := ptr, bs := hdr, additional := 32 })
        (M.stepEvents (authMacHdrEvents auth hdr) st) := by
  rw [fitsEnv_keysUnsampledMacReserve_iff] at h
  unfold keysUnsampledMacReserveEvents at h
  rcases (fitsEvents_append M lim _ _ st).mp h with ⟨hmac, hres⟩
  refine ⟨fitsEnv_authMacHdr_iff.mpr hmac, ?_, ?_⟩
  · rw [fitsEnv_doReserve_iff, doReserveEvents_hdr64_32 v ptr hdr hhdr_len]
    exact hres
  · unfold keysUnsampledMacReserveEvents
    rw [M.stepEvents_append, doReserveEvents_hdr64_32 v ptr hdr hhdr_len]

/-! ## 2. Private Register-Frame, `memcpy`, and Heap-Folding Helpers -/

private structure CallStateAt (s0 s : State) (sp lr : BitVec 64)
    (v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 : BitVec 64) (sm : State) : Prop where
  sp_eq : sm.sp = sp
  lr_eq : sm.readReg64 (Reg.gpr 30#5) = lr
  tr_eq : sm.trace = s0.trace
  x19_eq : sm.readReg64 (Reg.gpr 19#5) = v19
  x20_eq : sm.readReg64 (Reg.gpr 20#5) = v20
  x21_eq : sm.readReg64 (Reg.gpr 21#5) = v21
  x22_eq : sm.readReg64 (Reg.gpr 22#5) = v22
  x23_eq : sm.readReg64 (Reg.gpr 23#5) = v23
  x24_eq : sm.readReg64 (Reg.gpr 24#5) = v24
  x25_eq : sm.readReg64 (Reg.gpr 25#5) = v25
  x26_eq : sm.readReg64 (Reg.gpr 26#5) = v26
  x27_eq : sm.readReg64 (Reg.gpr 27#5) = v27
  x28_eq : sm.readReg64 (Reg.gpr 28#5) = v28
  vregs_eq : calleeSavedVRegs sm = calleeSavedVRegs s

private theorem CallStateAt.of_cs {s0 s sm sf : State}
    {sp lr v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 : BitVec 64}
    (h : CallStateAt s0 s sp lr v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 sm)
    (hsp : sf.sp = sp) (htr : sf.trace = s0.trace)
    (hcs : CalleeSavedPreserved sm sf) :
    CallStateAt s0 s sp (sf.readReg64 (Reg.gpr 30#5))
      v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 sf := by
  rcases hcs with ⟨h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, _, hv⟩
  exact ⟨hsp, rfl, htr,
    h19.trans h.x19_eq, h20.trans h.x20_eq, h21.trans h.x21_eq, h22.trans h.x22_eq,
    h23.trans h.x23_eq, h24.trans h.x24_eq, h25.trans h.x25_eq, h26.trans h.x26_eq,
    h27.trans h.x27_eq, h28.trans h.x28_eq, hv.trans h.vregs_eq⟩

local macro "close_reg_val" : tactic =>
  `(tactic| (
    simp only [State.sp, Reg.lr, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x8,
      Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
      BitVec.add_assoc, wp_norm, arm64_norm, *]))

local macro "mk_call_state" : tactic =>
  `(tactic| refine ⟨by close_reg_val, by close_reg_val, by simp only [wp_norm, arm64_norm, *],
    by close_reg_val, by close_reg_val, by close_reg_val, by close_reg_val,
    by close_reg_val, by close_reg_val, by close_reg_val, by close_reg_val,
    by close_reg_val, by close_reg_val, by simp only [wp_norm, arm64_norm, *]⟩)

private theorem call_memcpy_lscro_x0 {M : AllocCostModel} {A : RustCliAllocBudget M}
    {lim : BudgetLimits} {prog : Program} {entry ret_pc tgt : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionBudgetSpec)
    (dst src : BitVec 64) (bs : Bytes) (st : M.σ)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = entry) (hrun : s.status = .Running)
    (hsp : s.sp = sp_call) (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length)
    (hsplit : P = (memRegion dst bs.length ∗ (src ↦ₛ bs) ∗ A.pool lim st s) ∗ Frame)
    (hnext : ∀ sf : State, LibsignalCodeRoLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call →
      CalleeSavedPreserved s sf → sf.readReg64 (Reg.gpr 0#5) = dst → sf.trace = s0.trace →
      SepWP prog tgt sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs) ∗ A.pool lim st sf) ∗ Frame) post) :
    SepWP prog tgt s P post := by
  rw [hsplit]
  refine of_sepWP_lscro_plain (mid := ret_pc) hcrl ?_
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs))
    (F := A.pool lim st s ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => not_satisfies_false_sepConj h)
    (fun _ _ _ _ h => not_satisfies_false_sepConj h)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec, memcpyRegionSpec]
    simp only [sepConj_assoc, satisfies_pure_sepConj] at hm ⊢
    exact ⟨⟨hx0, hx1, hx2⟩, by ac_nf at hm ⊢⟩
  · dsimp only [sessionMemcpyRegionBudgetSpec, sessionMemcpyRegionSpec]
    rw [sepConj_assoc, sepConj_assoc]
    refine SepWP.pure_elim fun hvm => ?_
    refine SepWP.pure_elim fun ⟨hx0_sf, htr⟩ => ?_
    simp only [Reg.x0] at hx0_sf
    rw [← A.pool_of_vmPreserved hvm]
    exact SepWP.done hpc_sf hrun_sf fun hcrl1 =>
      SepWP.weaken_pre (Entails.of_eq (by sep_ac_rfl))
        (hnext sf hcrl1 hpc_sf hrun_sf (hsp_sf.trans hsp) hcs_sf hx0_sf (htr.trans htrace))

private theorem fold_keysUnsampled_pre_reserve
    (sp ek_ptr dk_ptr epoch hdr_ptr mac_cap mac_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator) :
    authInlineWordsAt g (sp + 4080#64) auth ∗
    ((sp + 4128#64) ↦₆₄ 1152#64) ∗ ((sp + 4136#64) ↦₆₄ ek_ptr) ∗ ((sp + 4144#64) ↦₆₄ 1152#64) ∗
    ((sp + 4152#64) ↦₆₄ 2400#64) ∗ ((sp + 4160#64) ↦₆₄ dk_ptr) ∗ ((sp + 4168#64) ↦₆₄ 2400#64) ∗
    ((sp + 4176#64) ↦₆₄ epoch) ∗
    words16At (sp + 4704#64)
      g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
      g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
      1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64 ∗
    (((sp + 4832#64) ↦₆₄ mac_cap) ∗ ((sp + 4840#64) ↦₆₄ mac_ptr) ∗ ((sp + 4848#64) ↦₆₄ 32#64)) ∗
    memRegion (sp + 4856#64) 2248 ⊢
    ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
    memRegion (sp + 4704#64) 2400 := by
  have h128 := words16At_entails_memRegion (sp + 4704#64)
    g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
    g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
    1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64
  have h24 := words3_entails_memRegion (sp + 4832#64) mac_cap mac_ptr 32#64
  rw [show (sp + 4832#64) + 8#64 = sp + 4840#64 by bv_omega,
      show (sp + 4832#64) + 16#64 = sp + 4848#64 by bv_omega] at h24
  have hlhs :
      authInlineWordsAt g (sp + 4080#64) auth ∗
      ((sp + 4128#64) ↦₆₄ 1152#64) ∗ ((sp + 4136#64) ↦₆₄ ek_ptr) ∗ ((sp + 4144#64) ↦₆₄ 1152#64) ∗
      ((sp + 4152#64) ↦₆₄ 2400#64) ∗ ((sp + 4160#64) ↦₆₄ dk_ptr) ∗ ((sp + 4168#64) ↦₆₄ 2400#64) ∗
      ((sp + 4176#64) ↦₆₄ epoch) ∗
      words16At (sp + 4704#64)
        g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
        g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
        1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64 ∗
      (((sp + 4832#64) ↦₆₄ mac_cap) ∗ ((sp + 4840#64) ↦₆₄ mac_ptr) ∗ ((sp + 4848#64) ↦₆₄ 32#64)) ∗
      memRegion (sp + 4856#64) 2248 =
      ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
      words16At (sp + 4704#64)
        g.rootKey.cap g.rootKey.ptr (BitVec.ofNat 64 auth.rootKey.length)
        g.macKey.cap g.macKey.ptr (BitVec.ofNat 64 auth.macKey.length)
        1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch 64#64 hdr_ptr 64#64 ∗
      (((sp + 4832#64) ↦₆₄ mac_cap) ∗ ((sp + 4840#64) ↦₆₄ mac_ptr) ∗ ((sp + 4848#64) ↦₆₄ 32#64)) ∗
      memRegion (sp + 4856#64) 2248 := by
    dsimp only [ekSentInlineWordsAt]
    simp only [BitVec.add_assoc, arm64_norm]
  rw [hlhs, memRegion_4704_2400_split_macHdr sp]
  exact sepConj_mono (Entails.refl _) (sepConj_mono h128 (sepConj_mono h24 (Entails.refl _)))

private theorem split_hdr_reserve_tail (hdr_ptr' : BitVec 64) (mac : Bytes)
    (hmac_len : mac.length = 32) :
    memRegion (hdr_ptr' + 64#64) 64 =
      memRegion (hdr_ptr' + 64#64) mac.length ∗ memRegion (hdr_ptr' + 96#64) 32 := by
  rw [hmac_len,
      ProofLib.memRegion_split' (b := hdr_ptr' + 64#64) (n := 32) (k := 32)
        (b' := hdr_ptr' + 96#64) rfl (by bv_omega) (by decide)]

private theorem join_hdr_mac_bytes (hdr_ptr' : BitVec 64) (hdr mac : Bytes)
    (hhdr_len : hdr.length = 64) :
    (hdr_ptr' ↦ₛ hdr) ∗ ((hdr_ptr' + 64#64) ↦ₛ mac) ⊢ (hdr_ptr' ↦ₛ (hdr ++ mac)) := by
  rw [pointsToBytes_append, hhdr_len]
  exact Entails.refl _

/-! ## 3. Budget-Threaded Relocatable Sub-Step 1c (`+684 -> +2588`) -/

set_option maxHeartbeats 1600000 in
/-- Non-panicking `SepWP` form of `.keysUnsampled` sub-step 1c (`+684 -> +2588`:
    `<Authenticator>::mac_hdr`, `ekSentInlineWordsAt` staging, `do_reserve_and_handle [local#7]`,
    and 32-byte `mac` `memcpy`) on `spqrSendPlacedProg ext`. -/
theorem step_keysUnsampled_684_to_2588_sepWP_placed {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (sp epoch hdr_ptr ek_ptr dk_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (seed : List.Vector (BitVec 8) 64)
    (mac : Bytes)
    (hmac : auth.macHdr F epoch (K.fromSeed seed).1.toList = .ok mac)
    (hhdr_ne : hdr_ptr ≠ 0)
    (st : M.σ)
    (hfit : FitsEnv M lim st (KeysUnsampledMacReserveEnv auth (K.fromSeed seed).1.toList))
    {tgt : BitVec 64} {s0 s : State} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 684#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = sp + 7136#64)
    (hx1 : s.readReg64 .x1 = epoch)
    (hx2 : s.readReg64 .x2 = hdr_ptr)
    (hx3 : s.readReg64 .x3 = 64#64)
    (hx8 : s.readReg64 .x8 = sp + 4832#64)
    (hx20 : s.readReg64 .x20 = hdr_ptr)
    (hx21 : s.readReg64 .x21 = ek_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx23 : s.readReg64 .x23 = dk_ptr)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx25 : s.readReg64 .x25 = 2400#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = 64#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
      ((sp + 4056#64) ↦₆₄ epoch) ∗
      memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗
      A.live hdr_ptr 64 1 ∗
      (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
      vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
      A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr' mac_cap mac_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      hdr_ptr' ≠ 0 →
      mac_ptr ≠ 0 → (mac_cap == 0#64) = false →
      32 ≤ mac_cap.toNat → mac_cap.toNat < 2 ^ 63 →
      sf.pc = spqrSendPlacedEntry + 2588#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x0 = hdr_ptr' + 64#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = mac_cap →
      sf.readReg64 .x21 = mac_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = hdr_ptr' →
      sf.readReg64 .x24 = 64#64 →
      sf.readReg64 .x25 = 32#64 →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWP (spqrSendPlacedProg ext) tgt sf
        ((authInlineWordsAt g (sp + 2392#64) auth ∗
          authInlineWordsAt g (sp + 7136#64) auth ∗
          authHeapBufs A.repAlloc g auth ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
          memRegion (sp + 4704#64) 2400 ∗
          ((sp + 7104#64) ↦₆₄ 128#64) ∗
          ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗
          ((sp + 7120#64) ↦₆₄ 64#64) ∗
          A.live hdr_ptr' 128 1 ∗
          (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
          memRegion (hdr_ptr' + 96#64) 32 ∗
          A.live mac_ptr mac_cap.toNat 1 ∗
          (mac_ptr ↦ₛ mac) ∗
          memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
          vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          A.pool lim (M.stepEvents (keysUnsampledMacReserveEvents auth (K.fromSeed seed).1.toList) st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post) :
    SepWP (spqrSendPlacedProg ext) tgt s P post := by
  have hmac_at : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 342)
      (withLsCodeRoLoaded lsmpl (authMacHdrPinnedSpec F M A lim)) := hmac_call
  have hres_at : subroutine_ok (spqrSendPlacedProg ext) (lsmpl.base 460)
      (withLsCodeRoLoaded lsmpl (doReserve1Raw32Spec M A lim)) := hres_call
  have hmemcpy := spqrSend_session_memcpy_region_ok_placed hA
  have hhdr_len : (K.fromSeed seed).1.toList.length = 64 := List.Vector.toList_length _
  rcases fitsEnv_keysUnsampledMacReserve_split
    (v := sp + 7104#64) (ptr := hdr_ptr) hhdr_len hfit with ⟨hfit_mac, hfit_res, hstep_all⟩
  let st1 := M.stepEvents (authMacHdrEvents auth (K.fromSeed seed).1.toList) st
  let x_res : DoReserveCall := {
    v := sp + 7104#64, cap := 64#64, ptr := hdr_ptr,
    bs := (K.fromSeed seed).1.toList, additional := 32 }
  let st2 := M.stepEvents (doReserveEvents x_res) st1
  obtain ⟨rfl, _, _⟩ := macHdr_ok_elim hmac
  have hmac_len : (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList).length = 32 :=
    macHdrUnchecked_length F auth epoch _
  dsimp only [spqrSendPlacedProg, spqrSendPlacedEntry, BitVec.ofNat_eq_ofNat]
    at hpc hmac_at hres_at hmemcpy hnext ⊢
  subst hP
  simp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x8,
    Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27]
    at hx0 hx1 hx2 hx3 hx8 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
  rw [memRegion_4704_2400_split_macHdr sp]
  refine seq_vm_lscro (mid := lsmpl.base 342)
    (P_mid :=
      (authInlineWordsAt g (sp + 2392#64) auth ∗
       authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
       ((sp + 4056#64) ↦₆₄ epoch) ∗
       memRegion (sp + 4080#64) 104 ∗
       (memRegion (sp + 4704#64) 128 ∗ memRegion (sp + 4832#64) 24 ∗ memRegion (sp + 4856#64) 2248) ∗
       memRegion (sp + 7104#64) 24 ∗
       A.live hdr_ptr 64 1 ∗
       (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
       vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
       vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
       A.pool lim st s ∗
       stackAt sp spqrSendCalleeStack) ∗ Frame)
    (Q := fun s1 =>
      CallStateAt s0 s sp ((blkPl_427).base + 688#64)
        (s.readReg64 (Reg.gpr 19#5)) hdr_ptr ek_ptr epoch dk_ptr
        (sp + 2384#64) 2400#64 (sp + 4704#64) 64#64 (s.readReg64 (Reg.gpr 28#5)) s1 ∧
      s1.readReg64 .x8 = sp + 4832#64 ∧
      s1.readReg64 .x0 = sp + 7136#64 ∧
      s1.readReg64 .x1 = epoch ∧
      s1.readReg64 .x2 = hdr_ptr ∧
      s1.readReg64 .x3 = 64#64) hcrl ?_ ?_
  · by_vm_steps (
      wp_steps
      refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
          ⟨by mk_call_state, by close_reg_val, by close_reg_val,
           by close_reg_val, by close_reg_val, by close_reg_val⟩⟩)
  · rintro s1 hpc_1 hrun_1 hcrl_1 hvm_1 ⟨hcs_1, hx8_1, hx0_1, hx1_1, hx2_1, hx3_1⟩
    rw [← A.pool_of_vmPreserved hvm_1]
    let x_mac : AuthMacHdrPinnedGhost := {
      outVec := sp + 4832#64, selfA := sp + 7136#64, g := g, auth := auth,
      ep := epoch, hdrRO := false, hdrA := hdr_ptr, hdr := (K.fromSeed seed).1.toList }
    refine call_lscro_calleeStack_evs_sepWP (x := (x_mac, st))
      sp authMacHdrStackX (by decide)
      (T_pre := memRegion (sp + 4832#64) 24 ∗ authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
        (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗ A.pool lim st s1)
      (T_post := fun evs sf =>
        vecU8 A.repAlloc (sp + 4832#64) (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ∗
        authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
        (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗ A.pool lim (M.stepEvents evs st) sf)
      (F := authInlineWordsAt g (sp + 2392#64) auth ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗
        memRegion (sp + 4080#64) 104 ∗ memRegion (sp + 4704#64) 128 ∗ memRegion (sp + 4856#64) 2248 ∗
        memRegion (sp + 7104#64) 24 ∗ A.live hdr_ptr 64 1 ∗
        vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
        vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗ Frame)
      (φ_pre := s1.readReg64 .x8 = x_mac.outVec ∧ s1.readReg64 .x0 = x_mac.selfA ∧
        s1.readReg64 .x1 = x_mac.ep ∧ s1.readReg64 .x2 = x_mac.hdrA ∧
        s1.readReg64 .x3 = BitVec.ofNat 64 x_mac.hdr.length ∧
        41 + x_mac.hdr.length < 2 ^ 63 ∧
        FitsEnv M lim st (AuthMacHdrEnv x_mac.auth x_mac.hdr))
      (φ_post := fun evs sf =>
        x_mac.auth.macHdr F x_mac.ep x_mac.hdr = .ok (x_mac.auth.macHdrUnchecked F x_mac.ep x_mac.hdr) ∧
        sf.trace = s1.trace ∧ AuthMacHdrEnv x_mac.auth x_mac.hdr evs)
      hmac_at hcrl_1
      hpc_1 hrun_1 hcs_1.sp_eq hsp_align
      (ret_pc := (blkPl_427).base + 688#64) hcs_1.lr_eq
      (by dsimp only [authMacHdrPinnedSpec, x_mac]; rw [bytesAt_false]; simp only [sepConj_assoc])
      ⟨hx8_1, hx0_1, hx1_1, hx2_1,
        by change s1.readReg64 .x3 = BitVec.ofNat 64 (K.fromSeed seed).1.toList.length; rw [hhdr_len]; exact hx3_1,
        by change 41 + (K.fromSeed seed).1.toList.length < 2 ^ 63; rw [hhdr_len]; decide,
        hfit_mac⟩
      (by sep_ac_rfl)
      (fun _ _ => rfl)
      (fun sf => authMacHdrPinned_onPanic_false_of_ok x_mac st hmac s1 sf)
      (by
        intro sf
        dsimp only [authMacHdrPinnedSpec, x_mac]
        apply congrArg SepProp.sepExists
        funext evs
        rw [bytesAt_false]
        simp only [sepConj_assoc]) ?_
    intro sm1 evs_mac hpc_sm1 hrun_sm1 hsp_sm1 ⟨_, htr_sm1_s1, hevs_mac⟩ hcrl_sm1
      hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
    have hevs_mac_eq : evs_mac = authMacHdrEvents auth (K.fromSeed seed).1.toList := hevs_mac
    subst hevs_mac_eq
    simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
      Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28]
      at hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1
    rw [hcs_1.tr_eq] at htr_sm1_s1
    rw [hcs_1.x19_eq] at hx19_sm1
    rw [hcs_1.x20_eq] at hx20_sm1
    rw [hcs_1.x21_eq] at hx21_sm1
    rw [hcs_1.x22_eq] at hx22_sm1
    rw [hcs_1.x23_eq] at hx23_sm1
    rw [hcs_1.x24_eq] at hx24_sm1
    rw [hcs_1.x25_eq] at hx25_sm1
    rw [hcs_1.x26_eq] at hx26_sm1
    rw [hcs_1.x27_eq] at hx27_sm1
    rw [hcs_1.x28_eq] at hx28_sm1
    rw [hcs_1.vregs_eq] at hvregs_sm1
    clear hcs_1 hx8_1 hx0_1 hx1_1 hx2_1 hx3_1
    refine SepWP.fold (vecU8_len32_expose (A := A.repAlloc) (sp + 4832#64) _ hmac_len) (by sep_focus) ?_
    wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply SepWP.exists_elim; intro mac_cap
    apply SepWP.exists_elim; intro mac_ptr
    refine SepWP.fold
      (Entails.refl ⌜32 ≤ mac_cap.toNat ∧ mac_cap.toNat < 2 ^ 63 ∧ mac_ptr ≠ 0 ∧ (mac_cap == 0#64) = false⌝)
      (by sep_focus) ?_
    refine SepWP.pure_elim fun ⟨hmac_cap_ge, hmac_cap_lt, hmac_ptr_ne, hmac_cap_b⟩ => ?_
    have hinline_2392 :
        authInlineWordsAt g (sp + 2392#64) auth =
          ((sp + 2392#64) ↦₆₄ g.rootKey.cap) ∗
          ((sp + 2400#64) ↦₆₄ g.rootKey.ptr) ∗
          ((sp + 2408#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          ((sp + 2416#64) ↦₆₄ g.macKey.cap) ∗
          ((sp + 2424#64) ↦₆₄ g.macKey.ptr) ∗
          ((sp + 2432#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) := by
      dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]
    have hinline_7136 :
        authInlineWordsAt g (sp + 7136#64) auth =
          ((sp + 7136#64) ↦₆₄ g.rootKey.cap) ∗
          ((sp + 7144#64) ↦₆₄ g.rootKey.ptr) ∗
          ((sp + 7152#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
          ((sp + 7160#64) ↦₆₄ g.macKey.cap) ∗
          ((sp + 7168#64) ↦₆₄ g.macKey.ptr) ∗
          ((sp + 7176#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length) := by
      dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]
    refine seq_vm_lscro (mid := lsmpl.base 460)
      (P_mid :=
        (authInlineWordsAt g (sp + 2392#64) auth ∗
         authInlineWordsAt g (sp + 7136#64) auth ∗
         authHeapBufs A.repAlloc g auth ∗
         ((sp + 4056#64) ↦₆₄ epoch) ∗
         ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
         memRegion (sp + 4704#64) 2400 ∗
         ((sp + 7104#64) ↦₆₄ 64#64) ∗
         ((sp + 7112#64) ↦₆₄ hdr_ptr) ∗
         ((sp + 7120#64) ↦₆₄ 64#64) ∗
         A.live hdr_ptr 64 1 ∗
         (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
         A.live mac_ptr mac_cap.toNat 1 ∗
         (mac_ptr ↦ₛ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ∗
         memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
         vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
         vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
         A.pool lim st1 sm1 ∗
         stackAt sp spqrSendCalleeStack) ∗ Frame)
      (Q := fun s2 =>
        CallStateAt s0 s sp ((blkPl_427).base + 11900#64)
          (s.readReg64 (Reg.gpr 19#5)) mac_cap mac_ptr epoch dk_ptr
          64#64 32#64 (sp + 4704#64) 64#64 (s.readReg64 (Reg.gpr 28#5)) s2 ∧
        s2.readReg64 .x0 = sp + 7104#64 ∧
        s2.readReg64 .x1 = 64#64 ∧
        s2.readReg64 .x2 = 32#64) hcrl_sm1 ?_ ?_
    · by_vm_steps (
        wp_conv_pre =>
          rw [authenticatorPinAt_eq_inline_heap A.repAlloc g (sp + 7136#64) auth,
              memRegion_104_eq_words13 (sp + 4080#64),
              memRegion_128_eq_words16 (sp + 4704#64),
              memRegion_24_eq_words3 (sp + 7104#64)]
          dsimp only [authInlineWordsAt, words16At, words8At]
          simp only [BitVec.add_assoc, arm64_norm, sepExists_sepConj_left, sepExists_sepConj_right]
        iterate 32 (apply SepWP.exists_elim; intro _)
        wp_steps
        refine SepWP.fold
          (fold_keysUnsampled_pre_reserve sp ek_ptr dk_ptr epoch hdr_ptr mac_cap mac_ptr g auth)
          (by
            (conv => rhs; arg 1; dsimp only [authInlineWordsAt, words16At, words8At]; simp only [BitVec.add_assoc, arm64_norm])
            sep_focus) ?_
        refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          ⟨by simp only [wp_norm, arm64_norm, *],
           Entails.of_eq (by rw [hinline_2392, hinline_7136]; sep_ac_rfl),
           ⟨by mk_call_state, by close_reg_val, by close_reg_val, by close_reg_val⟩⟩)
    · rintro s2 hpc_2 hrun_2 hcrl_2 hvm_2 ⟨hcs_2, hx0_2, hx1_2, hx2_2⟩
      clear htr_sm1_s1 hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
      rw [← A.pool_of_vmPreserved hvm_2]
      have hstk_res : (allocHookStack + 32) + 64 = doReserve32Stack := by decide
      refine call_lscro_calleeStack_sepWP (x := (x_res, st1))
        sp doReserve32Stack (by decide)
        (T_pre := ((sp + 7104#64) ↦₆₄ 64#64) ∗ ((sp + 7112#64) ↦₆₄ hdr_ptr) ∗
          A.live hdr_ptr 64 1 ∗ (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗ A.pool lim st1 s2)
        (T_post := fun sf => (∃∗ p' : BitVec 64,
          ⌜p' ≠ 0#64⌝ ∗ ((sp + 7104#64) ↦₆₄ 128#64) ∗ ((sp + 7112#64) ↦₆₄ p') ∗
          A.live p' 128 1 ∗ (p' ↦ₛ (K.fromSeed seed).1.toList) ∗
          memRegion (p' + 64#64) 64) ∗ A.pool lim st2 sf)
        (F := authInlineWordsAt g (sp + 2392#64) auth ∗ authInlineWordsAt g (sp + 7136#64) auth ∗
          authHeapBufs A.repAlloc g auth ∗ ((sp + 4056#64) ↦₆₄ epoch) ∗
          ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
          memRegion (sp + 4704#64) 2400 ∗ ((sp + 7120#64) ↦₆₄ 64#64) ∗
          A.live mac_ptr mac_cap.toNat 1 ∗
          (mac_ptr ↦ₛ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ∗
          memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
          vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗ Frame)
        (φ_pre := s2.readReg64 .x0 = x_res.v ∧ (s2.readReg64 .x1).toNat = x_res.bs.length ∧
          (s2.readReg64 .x2).toNat = x_res.additional ∧
          x_res.bs.length ≤ x_res.cap.toNat ∧ x_res.ptr ≠ 0#64 ∧
          reserveCap x_res.cap.toNat x_res.bs.length x_res.additional + 1 ≤ 2 ^ 63 ∧
          FitsEnv M lim st1 (DoReserveEnv x_res))
        (φ_post := fun sf => sf.trace = s2.trace)
        hres_at hcrl_2
        hpc_2 hrun_2 hcs_2.sp_eq hsp_align
        (ret_pc := (blkPl_427).base + 11900#64) hcs_2.lr_eq
        (by
          dsimp only [doReserve1Raw32Spec, doReserve1Raw32SpecWithStack, x_res]
          have h64_ne : ((64#64 : BitVec 64) = 0#64) = False := propext (by decide)
          have h64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl
          simp only [hhdr_len, h64_ne, h64_toNat, hstk_res, ↓reduceIte, Nat.sub_self,
            ProofLib.memRegion_zero, sepConj_emp,
            show (sp + 7104#64) + 8#64 = sp + 7112#64 by bv_omega, sepConj_assoc])
        ⟨hx0_2,
          by change (s2.readReg64 .x1).toNat = (K.fromSeed seed).1.toList.length; rw [hx1_2, hhdr_len]; rfl,
          by change (s2.readReg64 .x2).toNat = 32; rw [hx2_2]; rfl,
          by change (K.fromSeed seed).1.toList.length ≤ (64#64 : BitVec 64).toNat; rw [hhdr_len]; decide,
          hhdr_ne,
          by change reserveCap 64 (K.fromSeed seed).1.toList.length 32 + 1 ≤ 2 ^ 63; rw [hhdr_len, reserveCap_64_64_32]; decide,
          hfit_res⟩
        (by sep_ac_rfl)
        (fun _ _ => rfl)
        (fun _ => Entails.refl ⌜False⌝)
        (by
          intro sf
          dsimp only [doReserve1Raw32Spec, doReserve1Raw32SpecWithStack, x_res, st2]
          have h64_toNat : (64#64 : BitVec 64).toNat = 64 := rfl
          simp only [hhdr_len, h64_toNat, reserveCap_64_64_32, hstk_res,
            show BitVec.ofNat 64 128 = 128#64 from rfl,
            show BitVec.ofNat 64 64 = 64#64 from rfl,
            show 128 - 64 = 64 from rfl,
            show (sp + 7104#64) + 8#64 = sp + 7112#64 by bv_omega, sepConj_assoc]) ?_
      intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 htr_sm2_s2 hcrl_sm2
        hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
      simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23,
        Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28]
        at hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2
      rw [hcs_2.tr_eq] at htr_sm2_s2
      rw [hcs_2.x19_eq] at hx19_sm2
      rw [hcs_2.x20_eq] at hx20_sm2
      rw [hcs_2.x21_eq] at hx21_sm2
      rw [hcs_2.x22_eq] at hx22_sm2
      rw [hcs_2.x24_eq] at hx24_sm2
      rw [hcs_2.x25_eq] at hx25_sm2
      rw [hcs_2.x26_eq] at hx26_sm2
      rw [hcs_2.x27_eq] at hx27_sm2
      rw [hcs_2.x28_eq] at hx28_sm2
      rw [hcs_2.vregs_eq] at hvregs_sm2
      clear hcs_2 hx23_sm2 hx0_2 hx1_2 hx2_2
      wp_conv_pre => simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro hdr_ptr'
      refine SepWP.fold (Entails.refl ⌜hdr_ptr' ≠ 0#64⌝) (by sep_focus) ?_
      refine SepWP.pure_elim fun hhdr_ptr'_ne => ?_
      wp_conv_pre => rw [split_hdr_reserve_tail hdr_ptr' _ hmac_len]
      refine seq_vm_lscro (mid := lsρ "memcpy")
        (P_mid :=
          (memRegion (hdr_ptr' + 64#64) (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList).length ∗
           (mac_ptr ↦ₛ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ∗
           A.pool lim st2 sm2) ∗
          (authInlineWordsAt g (sp + 2392#64) auth ∗
           authInlineWordsAt g (sp + 7136#64) auth ∗
           authHeapBufs A.repAlloc g auth ∗
           ((sp + 4056#64) ↦₆₄ epoch) ∗
           ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
           memRegion (sp + 4704#64) 2400 ∗
           ((sp + 7104#64) ↦₆₄ 128#64) ∗
           ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗
           ((sp + 7120#64) ↦₆₄ 64#64) ∗
           A.live hdr_ptr' 128 1 ∗
           (hdr_ptr' ↦ₛ (K.fromSeed seed).1.toList) ∗
           memRegion (hdr_ptr' + 96#64) 32 ∗
           A.live mac_ptr mac_cap.toNat 1 ∗
           memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
           vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
           vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
           stackAt sp spqrSendCalleeStack ∗ Frame))
        (Q := fun s3 =>
          CallStateAt s0 s sp ((blkPl_427).base + 868#64)
            (s.readReg64 (Reg.gpr 19#5)) mac_cap mac_ptr epoch hdr_ptr'
            64#64 32#64 (sp + 4704#64) 64#64 (s.readReg64 (Reg.gpr 28#5)) s3 ∧
          s3.readReg64 .x0 = hdr_ptr' + 64#64 ∧
          s3.readReg64 .x1 = mac_ptr ∧
          (s3.readReg64 .x2).toNat = (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList).length)
        hcrl_sm2 ?_ ?_
      · by_vm_steps (
          wp_steps
          refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
            ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
              ⟨by mk_call_state, by close_reg_val, by close_reg_val,
               by rw [hmac_len]; simp only [Reg.x2, wp_norm, arm64_norm, *]⟩⟩)
      · rintro s3 hpc_3 hrun_3 hcrl_3 hvm_3 ⟨hcs_3, hx0_3, hx1_3, hx2_3⟩
        rw [← A.pool_of_vmPreserved hvm_3]
        refine call_memcpy_lscro_x0 hmemcpy (hdr_ptr' + 64#64) mac_ptr
          (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) st2
          hcrl_3 hpc_3 hrun_3 hcs_3.sp_eq hsp_align hcs_3.lr_eq hcs_3.tr_eq
          hx0_3 hx1_3 hx2_3 rfl
          fun sm3 hcrl_sm3 hpc_sm3 hrun_sm3 hsp_sm3 hcs_sm3 hx0_sm3 htr_sm3 => ?_
        rcases hcs_3.of_cs hsp_sm3 htr_sm3 hcs_sm3 with
          ⟨hsp_3, hlr_3, htr_3, hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hv_3⟩
        refine SepWP.fold
          (join_hdr_mac_bytes hdr_ptr' (K.fromSeed seed).1.toList
            (auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) hhdr_len)
          (by sep_focus) ?_
        refine seq_vm_lscro (mid := (blkPl_427).base + 2588#64)
          (P_mid :=
            (authInlineWordsAt g (sp + 2392#64) auth ∗
             authInlineWordsAt g (sp + 7136#64) auth ∗
             authHeapBufs A.repAlloc g auth ∗
             ((sp + 4056#64) ↦₆₄ epoch) ∗
             ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
             memRegion (sp + 4704#64) 2400 ∗
             ((sp + 7104#64) ↦₆₄ 128#64) ∗
             ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗
             ((sp + 7120#64) ↦₆₄ 64#64) ∗
             A.live hdr_ptr' 128 1 ∗
             (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList)) ∗
             memRegion (hdr_ptr' + 96#64) 32 ∗
             A.live mac_ptr mac_cap.toNat 1 ∗
             (mac_ptr ↦ₛ auth.macHdrUnchecked F epoch (K.fromSeed seed).1.toList) ∗
             memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
             vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
             vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
             A.pool lim st2 sm3 ∗
             stackAt sp spqrSendCalleeStack) ∗ Frame)
          (Q := fun sf =>
            sf.sp = sp ∧
            sf.readReg64 .x0 = hdr_ptr' + 64#64 ∧
            sf.readReg64 .x19 = s.readReg64 .x19 ∧
            sf.readReg64 .x20 = mac_cap ∧
            sf.readReg64 .x21 = mac_ptr ∧
            sf.readReg64 .x22 = epoch ∧
            sf.readReg64 .x23 = hdr_ptr' ∧
            sf.readReg64 .x24 = 64#64 ∧
            sf.readReg64 .x25 = 32#64 ∧
            sf.readReg64 .x26 = sp + 4704#64 ∧
            sf.readReg64 .x28 = s.readReg64 .x28 ∧
            sf.trace = s0.trace ∧
            calleeSavedVRegs sf = calleeSavedVRegs s) hcrl_sm3 ?_ ?_
        · by_vm_steps (
            wp_steps
            refine SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
              ⟨by simp only [wp_norm, arm64_norm, *], Entails.of_eq (by sep_ac_rfl),
                ⟨by close_reg_val, by close_reg_val, by close_reg_val, by close_reg_val,
                 by close_reg_val, by close_reg_val, by close_reg_val, by close_reg_val,
                 by close_reg_val, by close_reg_val, by close_reg_val,
                 by simp only [wp_norm, arm64_norm, *], by simp only [wp_norm, arm64_norm, *]⟩⟩)
        · rintro sf hpc_sf hrun_sf hcrl_sf hvm_sf
            ⟨hsp_sf, hx0_sf, hx19_sf, hx20_sf, hx21_sf, hx22_sf, hx23_sf,
             hx24_sf, hx25_sf, hx26_sf, hx28_sf, htr_sf, hvregs_sf⟩
          have hpool_eq :
              A.pool lim st2 sm3 =
                A.pool lim (M.stepEvents (keysUnsampledMacReserveEvents auth (K.fromSeed seed).1.toList) st) sf := by
            dsimp only [st2, st1]
            rw [hstep_all]
            exact (A.pool_of_vmPreserved hvm_sf).symm
          rw [hpool_eq]
          exact hnext sf hdr_ptr' mac_cap mac_ptr hcrl_sf
            hhdr_ptr'_ne hmac_ptr_ne hmac_cap_b hmac_cap_ge hmac_cap_lt
            hpc_sf hrun_sf hsp_sf hx0_sf hx19_sf hx20_sf hx21_sf hx22_sf
            hx23_sf hx24_sf hx25_sf hx26_sf hx28_sf htr_sf hvregs_sf

/-- Panic-aware `SepWPp` wrapper for `.keysUnsampled` sub-step 1c (`+684 -> +2588`) on
    `spqrSendPlacedProg ext`, polymorphic over any panic postcondition `Qp`. -/
theorem step_keysUnsampled_684_to_2588_placed {F : ShaCompress}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {K : MlKem} {ext : String → Option (State → State)}
    (hA : AllocContractsPlaced M A lim ext)
    (hmac_call : AuthMacHdrPinnedPlacedOkX F M A lim ext)
    (hres_call : DoReserve2PlacedOkX M A lim ext)
    (sp epoch hdr_ptr ek_ptr dk_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator)
    (seed : List.Vector (BitVec 8) 64)
    (mac : Bytes)
    (hmac : auth.macHdr F epoch (K.fromSeed seed).1.toList = .ok mac)
    (hhdr_ne : hdr_ptr ≠ 0)
    (st : M.σ)
    (hfit : FitsEnv M lim st (KeysUnsampledMacReserveEnv auth (K.fromSeed seed).1.toList))
    {ret : BitVec 64} {s0 s : State} {P Frame : SepProp}
    {post Qp : State → SepProp → Prop}
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = spqrSendPlacedEntry + 684#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx0 : s.readReg64 .x0 = sp + 7136#64)
    (hx1 : s.readReg64 .x1 = epoch)
    (hx2 : s.readReg64 .x2 = hdr_ptr)
    (hx3 : s.readReg64 .x3 = 64#64)
    (hx8 : s.readReg64 .x8 = sp + 4832#64)
    (hx20 : s.readReg64 .x20 = hdr_ptr)
    (hx21 : s.readReg64 .x21 = ek_ptr)
    (hx22 : s.readReg64 .x22 = epoch)
    (hx23 : s.readReg64 .x23 = dk_ptr)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx25 : s.readReg64 .x25 = 2400#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = 64#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authenticatorPinAt A.repAlloc g (sp + 7136#64) auth ∗
      ((sp + 4056#64) ↦₆₄ epoch) ∗
      memRegion (sp + 4080#64) 104 ∗
      memRegion (sp + 4704#64) 2400 ∗
      memRegion (sp + 7104#64) 24 ∗
      A.live hdr_ptr 64 1 ∗
      (hdr_ptr ↦ₛ (K.fromSeed seed).1.toList) ∗
      vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
      vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
      A.pool lim st s ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (hdr_ptr' mac_cap mac_ptr : BitVec 64),
      LibsignalCodeRoLoaded lsmpl sf.mem →
      hdr_ptr' ≠ 0 →
      mac_ptr ≠ 0 → (mac_cap == 0#64) = false →
      32 ≤ mac_cap.toNat → mac_cap.toNat < 2 ^ 63 →
      sf.pc = spqrSendPlacedEntry + 2588#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x0 = hdr_ptr' + 64#64 →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = mac_cap →
      sf.readReg64 .x21 = mac_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = hdr_ptr' →
      sf.readReg64 .x24 = 64#64 →
      sf.readReg64 .x25 = 32#64 →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (spqrSendPlacedProg ext) ret sf
        ((authInlineWordsAt g (sp + 2392#64) auth ∗
          authInlineWordsAt g (sp + 7136#64) auth ∗
          authHeapBufs A.repAlloc g auth ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          ekSentInlineWordsAt (sp + 4080#64) g auth 1152#64 ek_ptr 1152#64 2400#64 dk_ptr 2400#64 epoch ∗
          memRegion (sp + 4704#64) 2400 ∗
          ((sp + 7104#64) ↦₆₄ 128#64) ∗
          ((sp + 7112#64) ↦₆₄ hdr_ptr') ∗
          ((sp + 7120#64) ↦₆₄ 64#64) ∗
          A.live hdr_ptr' 128 1 ∗
          (hdr_ptr' ↦ₛ ((K.fromSeed seed).1.toList ++ mac)) ∗
          memRegion (hdr_ptr' + 96#64) 32 ∗
          A.live mac_ptr mac_cap.toNat 1 ∗
          (mac_ptr ↦ₛ mac) ∗
          memRegion (mac_ptr + 32#64) (mac_cap.toNat - 32) ∗
          vecU8Buf A.repAlloc 1152#64 ek_ptr (K.fromSeed seed).2.1.toList ∗
          vecU8Buf A.repAlloc 2400#64 dk_ptr (K.fromSeed seed).2.2.toList ∗
          A.pool lim (M.stepEvents (keysUnsampledMacReserveEvents auth (K.fromSeed seed).1.toList) st) sf ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post Qp) :
    SepWPp (spqrSendPlacedProg ext) ret s P post Qp := by
  refine SepWPp.seq_frozen (mid := spqrSendPlacedEntry + 2588#64)
    (Φ := fun _ => True) (fun _ _ _ _ => trivial) trivial ?_
  exact step_keysUnsampled_684_to_2588_sepWP_placed hA hmac_call hres_call
    sp epoch hdr_ptr ek_ptr dk_ptr g auth seed mac hmac hhdr_ne st hfit
    hcrl hsp_align hpc hrun hsp hx0 hx1 hx2 hx3 hx8 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27
    htrace hP
    fun sf hdr_ptr' mac_cap mac_ptr hcrl_sf hhdr'_ne hmac'_ne hmac_b hmac_ge hmac_lt
      hpc_sf hrun_sf hsp_sf hx0_sf hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf
      hx24_sf hx25_sf hx26_sf hx28_sf htr_sf hvregs_sf =>
      SepWP.done hpc_sf hrun_sf fun _ =>
        hnext sf hdr_ptr' mac_cap mac_ptr hcrl_sf hhdr'_ne hmac'_ne hmac_b hmac_ge hmac_lt
          hpc_sf hrun_sf hsp_sf hx0_sf hx19_sf hx20_sf hx21_sf hx22_sf hx23_sf
          hx24_sf hx25_sf hx26_sf hx28_sf htr_sf hvregs_sf

/-! ## 4. Budget `onPanic` Vacuity Helpers for `polyNextChunkPlacedSpec` -/

theorem polyNextChunkPlaced_onPanic_false_of_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (x : PolyNextChunkGhost) (st : M.σ)
    (_h : x.enc.nextChunk = .ok (x.enc', x.chunk)) (s0 sf : State) :
    (polyNextChunkPlacedSpec M A lim).onPanic (x, st) s0 sf = ⌜False⌝ :=
  rfl

theorem polyNextChunkPlaced_onPanic_of_ok
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Pan : Prop} (x : PolyNextChunkGhost) (st : M.σ)
    (_h : x.enc.nextChunk = .ok (x.enc', x.chunk)) (s0 sf : State) :
    (polyNextChunkPlacedSpec M A lim).onPanic (x, st) s0 sf ⊢
      ⌜Pan ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap :=
  Entails.trans (Entails.of_eq (sepConj_emp ⌜False⌝).symm) (Entails.pure_left False.elim)

end LibsignalBinary.Proofs.Cli.SpqrV1.Top.Send.StatesSendKeysUnsampled2PlacedBudget
