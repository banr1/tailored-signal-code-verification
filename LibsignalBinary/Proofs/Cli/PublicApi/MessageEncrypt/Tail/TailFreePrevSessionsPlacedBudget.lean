/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlaced
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import ProofLib.SepLogic.WP.Apply
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable T1 `previous_sessions` Free Tail (`+0x564..+0x5b4`)

Proves `tailFreePrevSessions_placed_ok` (along with self-contained T2 error/result epilogue bridges
`+0x5b4..+0x660`) on Block `464` (`lsProg_464 Hk`) under `RustCliAllocBudget M` and
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
  FreeOnlyEvs rustDeallocEvents rustCliDeallocBudgetSpec
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget (
  dealloc_placed_ok_at_enc call_nopanic_placed
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  SeamBudget freeOnlyEvs_rustDeallocEvents retagSessionStore retagIdentityStore
  SpqrSendBudgetEnv SessionStoreBudgetEnv IdentityStoreBudgetEnv
  WithStoresEncEnv withStoresEncBudgetSpecV EncTailVBudget SegExitBudget EncEnvBudget
)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees (lsLogOff)
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (
  WithStoresEncGhost withStoresEncStack withStoresEncStackV
  encSubStack encSpillsAtV encSavedRegs nowAt
)
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape (cliTapeAfter)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt (
  encEntryPlaced encCommonPlaced encStoreExtraPlaced withStoresEncStack_join_extra_placed
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon (
  words64At SpeStaged ResStaged pollWith tailRegs TailModel
  unpack64List exists_unpack64List words64At_eq_pointsToBytes
  words64At_entails_memRegion writeResult_frame_entails_stackAtV
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteResult (
  memRegion_eq_exists_words64At words64At_4 words64At_27
  encSavedRegsAtSp encSavedRegs_eq_atSp
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailWriteErr (
  resStaged_of_speStaged
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFreePrevSessions (
  stackAt_encSubStack_alloc mul24_shift_toNat
  vecHeader_prev_weaken vecAt_prev_zero_eq vecAt_prev_nz_eq
)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

private theorem bv_sub_add_lit_local (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit_local BitVec.toNat_zero

/-! ## 1. Budget-Retag & `SeamBudget` Helpers -/

private theorem seamBudget_step_freeOnly {M : AllocCostModel} {lim : BudgetLimits}
    {TopEnv : List AllocEvent → Prop} {st_init st : M.σ} {evs_step : List AllocEvent}
    (h : SeamBudget lim TopEnv st_init st FreeOnlyEvs) (hstep : FreeOnlyEvs evs_step) :
    SeamBudget lim TopEnv st_init (M.stepEvents evs_step st) FreeOnlyEvs :=
  (h.narrow (by rintro _ (h1 | ⟨_, _, rfl, h1, h2⟩); exact h1; exact h1.append h2)).advance hstep

private theorem protocolAddressAt_atState {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ) (s : State) :
    protocolAddressAt (A.atState lim st s) = protocolAddressAt A.repAlloc := rfl

private theorem storeFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (st0 : kit.StoreState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagSessionStore (A' := A') kit).storeFinal st0 ans cs = kit.storeFinal st0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact storeFinal_retag kit _ ans cs

private theorem idFinal_retag {A A' : RustAlloc} {b : BitVec 64}
    (ikit : IdentityStoreSpec A b) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit) :
    ∀ cs, (retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs = ikit.idFinal ist0 ans cs
  | [] => rfl
  | c :: cs => by cases c <;> exact idFinal_retag ikit _ ans cs

private theorem encStoreExtraPlaced_final_retag [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (ans : StoreAnswers (List (BitVec 8)) Unit)
    (cs : List (StoreCall AddrVal (List (BitVec 8))))
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced (retagSessionStore (A' := A') kit)
      ((retagSessionStore (A' := A') kit).storeFinal st0 ans cs)
      (retagIdentityStore (A' := A') ikit)
      ((retagIdentityStore (A' := A') ikit).idFinal ist0 ans cs) x s0 =
    encStoreExtraPlaced kit (kit.storeFinal st0 ans cs)
      ikit (ikit.idFinal ist0 ans cs) x s0 := by
  have hs := storeFinal_retag (A' := A') kit st0 ans cs
  have hi := idFinal_retag (A' := A') ikit ist0 ans cs
  have hfn :
      ∀ (st : kit.StoreState) (ist : ikit.IdState),
        encStoreExtraPlaced (retagSessionStore (A' := A') kit) st
          (retagIdentityStore (A' := A') ikit) ist x s0 =
        encStoreExtraPlaced kit st ikit ist x s0 := fun _ _ => rfl
  exact (hfn _ _).trans (by rw [hs, hi])

private theorem encTail_mem_retag_eq [LibsignalPlacement] {A A' : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced (retagSessionStore (A' := A') kit)
        ((retagSessionStore (A' := A') kit).storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        (retagIdentityStore (A' := A') ikit)
        ((retagIdentityStore (A' := A') ikit).idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) =
    (slotsP ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced kit
        (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
        ikit
        (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2)
        x s0 ∗ R0)) := by
  have hext := encStoreExtraPlaced_final_retag (A' := A') kit st0 ikit ist0 answers
    (x.model C S uuidTryParse answers).2 x s0
  have hvt :
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

private theorem encCommonPlaced_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (draws : Nat) (s0 s1 s2 : State)
    (hvm : VmPreserved s1 s2) :
    encCommonPlaced (A.atState lim st s1) ctl x draws s0 =
      encCommonPlaced (A.atState lim st s2) ctl x draws s0 := by
  rw [(A.atState_eq_of_vmPreserved lim st hvm).symm]

/-! ## 2. `VmPreserved`-Threaded `SepWP` Steppers (`+0x564..+0x660`) -/

theorem freePrevSessions_zero_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp prevPtr : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x564#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x5b4#64) s
      (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧ sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x30 = s.readReg64 .x30 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) := by
  subst hsp
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl⟩)

set_option maxHeartbeats 800000 in
/-- Step `+0x564..+0x590` when `prevCap ≠ 0#64` (`previous_sessions` empty `Vec` buffer deallocation
setup) up to `lsρ lsRustDeallocSym`, preserving `VmPreserved`. -/
theorem freePrevSessions_nz_placed_step_pre [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp prevCap prevPtr : BitVec 64}
    (hcap_nz : prevCap ≠ 0#64)
    (hcap_lt : prevCap.toNat * 24 < 2 ^ 63)
    (hpc : s.pc = encEntryPlaced + 0x564#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp) :
    SepWP (lsProg_464 Hk) (lsρ lsRustDeallocSym) s
      (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.readReg64 .x0 = prevPtr ∧
        (sf.readReg64 .x1).toNat = prevCap.toNat * 24 ∧
        (sf.readReg64 .x2).toNat = 8 ∧
        sf.readReg64 .x30 = encEntryPlaced + 0x5b4#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64))) := by
  subst hsp
  have hsp_align : (s.sp &&& 15#64 == 0#64) = true := hsp_al
  have hmul24 := mul24_shift_toNat hcap_lt
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    exact ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, hmul24, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)

set_option maxHeartbeats 800000 in
theorem writeErr_placed_sepWP [LibsignalPlacement] {H : LibsignalHooks}
    {sp : BitVec 64} {bws dws : List (BitVec 64)} {s : State}
    (hbws : bws.length = 27) (hdws : dws.length = 27)
    (hpc : s.pc = encEntryPlaced + 0x5b4#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (lsProg_464 H) (encEntryPlaced + 0x5f8#64) s
      (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧
        sf.spAligned = true ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x28 = sp + 0x4a0#64 ∧
        sf.readReg64 .x22 = errTag ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) bws)) := by
  subst hsp
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    rw [words64At_27 (s.sp + 0x9d0#64) hbws,
        words64At_27 (s.sp + 0x4a0#64) hdws]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    refine ⟨by simp only [wp_norm, arm64_norm], rfl, hsp_al, rfl, rfl, rfl, hx28, rfl, rfl, rfl,
      rfl, rfl, ?_⟩
    rw [words64At_27 (s.sp + 0x4a0#64) hbws]
    simp only [BitVec.add_assoc, BitVec.reduceAdd])

set_option maxHeartbeats 800000 in
theorem writeResult_placed_sepWP [LibsignalPlacement] {H : LibsignalHooks}
    {sp ret : BitVec 64} {w0 w1 w2 w3 : BitVec 64}
    {bws rws4 rws27 : List (BitVec 64)} {s0 s : State}
    (hbws : bws.length = 27) (hr4 : rws4.length = 4) (hr27 : rws27.length = 27)
    (hpc : s.pc = encEntryPlaced + 0x5f8#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx19 : s.readReg64 .x19 = ret)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx22 : s.readReg64 .x22 = w0)
    (hx27 : s.readReg64 .x27 = w1)
    (hx21 : s.readReg64 .x21 = w2)
    (hx23 : s.readReg64 .x23 = w3) :
    SepWP (lsProg_464 H) (s0.readReg64 .lr) s
      (words64At (sp + 0x4a0#64) bws ∗ words64At ret rws4 ∗
        words64At (ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0)
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp + 0xbe0#64 ∧
        sf.trace = s.trace ∧
        (sf.readReg64 .x19 = s0.readReg64 .x19 ∧
         sf.readReg64 .x20 = s0.readReg64 .x20 ∧
         sf.readReg64 .x21 = s0.readReg64 .x21 ∧
         sf.readReg64 .x22 = s0.readReg64 .x22 ∧
         sf.readReg64 .x23 = s0.readReg64 .x23 ∧
         sf.readReg64 .x24 = s0.readReg64 .x24 ∧
         sf.readReg64 .x25 = s0.readReg64 .x25 ∧
         sf.readReg64 .x26 = s0.readReg64 .x26 ∧
         sf.readReg64 .x27 = s0.readReg64 .x27 ∧
         sf.readReg64 .x28 = s0.readReg64 .x28 ∧
         sf.readReg64 .x29 = s0.readReg64 .x29 ∧
         calleeSavedVRegs sf = calleeSavedVRegs s) ∧
        P_f = (words64At (sp + 0x4a0#64) bws ∗ words64At ret [w0, w1, w2, w3] ∗
          words64At (ret + 0x20#64) bws ∗ encSavedRegsAtSp sp s0)) := by
  subst hsp
  unfold encEntryPlaced at hpc
  dsimp only [lsProg_464, ite_true]
  by_vm_steps (
    rw [words64At_27 (s.sp + 0x4a0#64) hbws,
        words64At_4 ret hr4,
        words64At_27 (ret + 0x20#64) hr27]
    unfold encSavedRegsAtSp
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
    wp_steps
    apply SepWP.done (by rfl) (by exact hrun)
    refine ⟨by simp only [wp_norm, arm64_norm], rfl, rfl,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
    rw [words64At_27 (ret + 0x20#64) hbws]
    simp only [words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc])

/-! ## 3. Budget-Threaded T2 Writer + Epilogue (`+0x5f8..+0x660`) & `Err` (`+0x5b4..+0x660`) -/

theorem tailWriteResult_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (x : WithStoresEncGhost) (st_init st : M.σ) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (w0 w1 w2 w3 : BitVec 64)
    (bs : List (BitVec 8)) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s)
    (hst : ResStaged A.repAlloc x.ret res [w0, w1, w2, w3] bs H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x5f8#64)
      (fun sp s => s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x22 = w0 ∧
        s.readReg64 .x27 = w1 ∧ s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H)
      R s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R s0 s (fun _ => False) := by
  rcases hm with ⟨⟨hmod_res, hcallsRel, hidCallsRel⟩, htrace⟩
  rcases hst with ⟨hres_np, _, hbs_len, hres_ent⟩
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, _hsp0_al, hsp_al, _hx29, hx19, _hcrl, hvregs⟩,
    ⟨hx28, hx22, hx27, hx21, hx23⟩, _hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R s0)) hmem
  obtain ⟨bws, hbws, hbs_eq⟩ := exists_unpack64List 27 (by omega : bs.length = 8 * 27)
  have hbs_words : ∀ a : BitVec 64, (a ↦ₛ bs) = words64At a bws := fun a => by
    rw [hbs_eq, ← words64At_eq_pointsToBytes]
  let sp := s0.sp - 0xbe0#64
  let stf := kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2
  let istf := ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2
  let R' := encStoreExtraPlaced kit stf ikit istf x s0 ∗ R
  change s.mem ⊨
    (memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
      memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R' at hmem
  have hret_split : memRegion x.ret 248 =
      memRegion x.ret (8 * 4) ∗ memRegion (x.ret + 0x20#64) (8 * 27) :=
    memRegion_split' (b := x.ret) (b' := x.ret + 0x20#64) (n := 8 * 4) (k := 8 * 27)
      (by decide) rfl (by decide)
  let F := memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
    memRegion (sp + 0x578#64) 0x608 ∗ H ∗ stackAt sp encSubStack ∗
    (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
    nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗
    FromRecordCallees.lsLogOff ∗ A.pool lim st s
  have hmem1 : s.mem ⊨ memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R')) := by
    have heq :
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R') =
      (memRegion x.ret (8 * 4) ∗ (memRegion (x.ret + 0x20#64) (8 * 27) ∗
      words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R'))) := by
      unfold encCommonPlaced
      rw [protocolAddressAt_atState]
      dsimp only [F, sp, RustCliAllocBudget.atState]
      rw [hbs_words (s0.sp - 0xbe0#64 + 0x4a0#64), hret_split, encSavedRegs_eq_atSp s0.sp s0]
      sep_ac_rfl
    rwa [← heq]
  obtain ⟨rws4, hr4, hmem2⟩ := memRegion_eq_exists_words64At 4 x.ret (by decide) s.mem _ hmem1
  rw [← sepConj_assoc, sepConj_comm (words64At x.ret rws4), sepConj_assoc] at hmem2
  obtain ⟨rws27, hr27, hmem3⟩ :=
    memRegion_eq_exists_words64At 27 (x.ret + 0x20#64) (by decide) s.mem _ hmem2
  have hmem4 : s.mem ⊨
      (words64At (sp + 0x4a0#64) bws ∗ words64At x.ret rws4 ∗
        words64At (x.ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R') := by
    have heq :
      (words64At (x.ret + 0x20#64) rws27 ∗ words64At x.ret rws4 ∗
        words64At (sp + 0x4a0#64) bws ∗ encSavedRegsAtSp sp s0 ∗ (F ∗ R')) =
      ((words64At (sp + 0x4a0#64) bws ∗ words64At x.ret rws4 ∗
        words64At (x.ret + 0x20#64) rws27 ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R')) := by sep_ac_rfl
    rwa [← heq]
  intro hL
  have hwp := writeResult_placed_sepWP (H := Hk) (s0 := s0)
    hbws hr4 hr27 hpc hrun hsp_al hsp hx19 hx28 hx22 hx27 hx21 hx23
  obtain ⟨sf, hsteps, ⟨hpcf, hrunf, P_f, hmf, hvmf, hspf, htracef, hcsf, rfl⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hmem4 hL
  rotate_left; · exact (not_satisfies_false_sepConj _hoom).elim
  rw [hvregs] at hcsf
  have hspf0 : sf.sp = s0.sp := by
    rw [hspf]; bv_omega
  obtain ⟨evs_tot, hevs_tot, hst_tot⟩ := hbud.finish FreeOnlyEvs.nil
  have hpool_eq : A.pool lim st s = A.pool lim (M.stepEvents evs_tot st_init) sf := by
    rw [← A.pool_transport lim st s sf hvmf, ← hst_tot]
    rfl
  refine ⟨sf, hsteps, Or.inr (Or.inl ⟨⟨hpcf, hspf0, hrunf⟩, ⟨hspf0, hcsf⟩, ?_⟩)⟩
  let PostBody :=
    kit.storeAt x.ssA stf ∗
    ikit.identityAt x.idA istf ∗
    apiEncResultAt A.repAlloc x.ret (x.model C S uuidTryParse answers).1 ∗
    nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗
    FromRecordCallees.lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
    A.pool lim (M.stepEvents evs_tot st_init) sf
  have hmf1 : sf.mem ⊨
      ((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗
        FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf)) ∗ R' := by
    have heq :
      ((words64At (sp + 0x4a0#64) bws ∗ words64At x.ret [w0, w1, w2, w3] ∗
        words64At (x.ret + 0x20#64) bws ∗ encSavedRegsAtSp sp s0) ∗ (F ∗ R')) =
      (((words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H) ∗
       (memRegion sp 0x58 ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ bs) ∗ memRegion (sp + 0x578#64) 0x608 ∗
        encSavedRegs s0.sp s0 ∗ stackAt sp encSubStack) ∗
       (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗
        FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf)) ∗ R') := by
      dsimp only [F, sp]
      rw [hpool_eq, ← hbs_words (s0.sp - 0xbe0#64 + 0x4a0#64), ← hbs_words (x.ret + 0x20#64),
          ← encSavedRegs_eq_atSp s0.sp s0]
      sep_ac_rfl
    rwa [← heq]
  have hstack_ent := writeResult_frame_entails_stackAtV kit.ss_vt ikit.id_vt x s0 bs hbs_len
  have hres_ent' :
      words64At x.ret [w0, w1, w2, w3] ∗ ((x.ret + 0x20#64) ↦ₛ bs) ∗ H ⊢
        apiEncResultAt A.repAlloc x.ret (x.model C S uuidTryParse answers).1 := by
    rw [hmod_res]; exact hres_ent
  have hmf2 := Satisfies.mono
    (sepConj_mono_left (sepConj_mono hres_ent' (sepConj_mono_left hstack_ent))) hmf1
  have hmf2' : sf.mem ⊨
      (encStoreExtraPlaced kit stf ikit istf x s0 ∗ stackAt s0.sp withStoresEncStack) ∗
      (apiEncResultAt A.repAlloc x.ret (x.model C S uuidTryParse answers).1 ∗
       nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
       protocolAddressAt A.repAlloc x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗
       FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf) ∗ R := by
    have heq :
      ((apiEncResultAt A.repAlloc x.ret (x.model C S uuidTryParse answers).1 ∗
        stackAt s0.sp withStoresEncStack ∗
        (nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
         protocolAddressAt A.repAlloc x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗
         FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf)) ∗ R') =
      ((encStoreExtraPlaced kit stf ikit istf x s0 ∗ stackAt s0.sp withStoresEncStack) ∗
       (apiEncResultAt A.repAlloc x.ret (x.model C S uuidTryParse answers).1 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗
        FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf) ∗ R) := by
      dsimp only [R']; sep_ac_rfl
    rwa [← heq]
  have hmf2'' := Satisfies.mono
    (sepConj_mono_left (withStoresEncStack_join_extra_placed kit stf ikit istf x s0)) hmf2'
  have hmf3 : sf.mem ⊨ PostBody ∗ R := by
    have heq :
      ((kit.storeAt x.ssA stf ∗ ikit.identityAt x.idA istf ∗
        stackAt s0.sp (withStoresEncStackV kit ikit)) ∗
       (apiEncResultAt A.repAlloc x.ret (x.model C S uuidTryParse answers).1 ∗
        nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
        protocolAddressAt A.repAlloc x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗
        FromRecordCallees.lsLogOff ∗ A.pool lim (M.stepEvents evs_tot st_init) sf) ∗ R) =
      (PostBody ∗ R) := by
      dsimp only [PostBody]; sep_ac_rfl
    rwa [← heq]
  have hpure : (x.model C S uuidTryParse answers).1 ≠ .error .panic ∧
      kit.callsRel st0 answers (x.model C S uuidTryParse answers).2 ∧
      ikit.idCallsRel ist0 answers (x.model C S uuidTryParse answers).2 ∧
      sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S uuidTryParse answers).2 ∧
      WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x evs_tot :=
    ⟨hmod_res ▸ hres_np, hcallsRel, hidCallsRel, htracef.trans htrace, hevs_tot⟩
  have hmf4 : sf.mem ⊨
      (⌜(x.model C S uuidTryParse answers).1 ≠ .error .panic ∧
        kit.callsRel st0 answers (x.model C S uuidTryParse answers).2 ∧
        ikit.idCallsRel ist0 answers (x.model C S uuidTryParse answers).2 ∧
        sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S uuidTryParse answers).2 ∧
        WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x evs_tot⌝ ∗
       PostBody) ∗ R := by
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpure, hmf3⟩
  let PostAt (ans : StoreAnswers (List (BitVec 8)) Unit) (evs : List AllocEvent) : SepProp :=
    ⌜(x.model C S uuidTryParse ans).1 ≠ .error .panic ∧
      kit.callsRel st0 ans (x.model C S uuidTryParse ans).2 ∧
      ikit.idCallsRel ist0 ans (x.model C S uuidTryParse ans).2 ∧
      sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S uuidTryParse ans).2 ∧
      WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x evs⌝ ∗
    kit.storeAt x.ssA (kit.storeFinal st0 ans (x.model C S uuidTryParse ans).2) ∗
    ikit.identityAt x.idA (ikit.idFinal ist0 ans (x.model C S uuidTryParse ans).2) ∗
    apiEncResultAt A.repAlloc x.ret (x.model C S uuidTryParse ans).1 ∗
    nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗
    protocolAddressAt A.repAlloc x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws S ans) ∗
    FromRecordCallees.lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗
    A.pool lim (M.stepEvents evs st_init) sf
  have hmf4' : sf.mem ⊨ PostAt answers evs_tot ∗ R := hmf4
  have hmf5 : sf.mem ⊨ (∃∗ evs : List AllocEvent, PostAt answers evs) ∗ R :=
    Satisfies.mono (sepConj_mono_left (Entails.sepExists_intro (P := PostAt answers) evs_tot)) hmf4'
  exact Satisfies.mono
    (sepConj_mono_left (Entails.sepExists_intro (P := fun ans => ∃∗ evs, PostAt ans evs) answers))
    hmf5

theorem tailWriteErr_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x5b4#64)
      (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  have hpoll : pollWith sp 0x9d0 [w3, w4, w5] =
      memRegion (sp + 0x46a#64) 0x36 ∗ memRegion (sp + 0x4a0#64) (8 * 27) ∗
        memRegion (sp + 0x578#64) 0x458 ∗ words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
        memRegion (sp + 0x9e8#64) (8 * 24) ∗ memRegion (sp + 0xaa8#64) 0xd8 := by
    change memRegion (sp + 0x46a#64) 0x566 ∗ words64At (sp + 0x9d0#64) [w3, w4, w5] ∗
      memRegion (sp + 0x9e8#64) 0x198 = _
    rw [@memRegion_split' (sp + 0x46a#64) (sp + 0x4a0#64) 0x36 0x530 0x566
        (by decide) (by bv_omega) (by decide),
      @memRegion_split' (sp + 0x4a0#64) (sp + 0x578#64) (8 * 27) 0x458 0x530
        (by decide) (by bv_omega) (by decide),
      @memRegion_split' (sp + 0x9e8#64) (sp + 0xaa8#64) (8 * 24) 0xd8 0x198
        (by decide) (by bv_omega) (by decide)]
    sep_ac_rfl
  let F := memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗ memRegion (sp + 0x46a#64) 0x36 ∗
    memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0xaa8#64) 0xd8 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
  have hmem1 : s.mem ⊨ memRegion (sp + 0x9e8#64) (8 * 24) ∗
      (memRegion (sp + 0x4a0#64) (8 * 27) ∗ words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ (F ∗ R)) := by
    have heq :
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
      (memRegion (sp + 0x9e8#64) (8 * 24) ∗
       (memRegion (sp + 0x4a0#64) (8 * 27) ∗ words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ (F ∗ R))) := by
      rw [hpoll]
      dsimp only [F, sp]
      sep_ac_rfl
    rwa [← heq]
  obtain ⟨jws, hjws, hmem2⟩ :=
    memRegion_eq_exists_words64At 24 (sp + 0x9e8#64) (by decide) s.mem _ hmem1
  rw [← sepConj_assoc, sepConj_comm (words64At (sp + 0x9e8#64) jws), sepConj_assoc] at hmem2
  obtain ⟨dws, hdws, hmem3⟩ :=
    memRegion_eq_exists_words64At 27 (sp + 0x4a0#64) (by decide) s.mem _ hmem2
  let bws := w3 :: w4 :: w5 :: jws
  have hbws : bws.length = 27 := by simp [bws, hjws]
  have hbws_eq :
      words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ words64At (sp + 0x9e8#64) jws =
        words64At (sp + 0x9d0#64) bws := by
    simp only [bws, words64At, sepConj_emp, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hmem4 : s.mem ⊨
      (words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws) ∗ (F ∗ R) := by
    have heq :
      (words64At (sp + 0x4a0#64) dws ∗ words64At (sp + 0x9e8#64) jws ∗
        words64At (sp + 0x9d0#64) [w3, w4, w5] ∗ (F ∗ R)) =
      ((words64At (sp + 0x9d0#64) bws ∗ words64At (sp + 0x4a0#64) dws) ∗ (F ∗ R)) := by
      rw [← hbws_eq]; sep_ac_rfl
    rwa [← heq]
  have hwp := writeErr_placed_sepWP (H := Hk) hbws hdws hpc hrun hsp_al hsp hx26 hx28
  refine SegExitBudget.of_sepWP (R0 := R0) hmem4 hwp ?_
  intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
    ⟨hvm1, hsp1, hsp1_al, htr1, hx29_1, hx19_1, hx28_1, hx22_1, hx27_1, hx21_1, hx23_1, hvregs1, hPf⟩
  subst hPf
  have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  have hst1 := resStaged_of_speStaged hst hjws
  refine tailWriteResult_placed_ok x st_init st R0 s0 s1 answers (.error e) errTag w0 w1 w2
    (unpack64List bws) H hm1 hst1 ⟨hbud, ?_⟩
  refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
    hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
    ⟨hx28_1, hx22_1, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
    hstack_le, ?_⟩
  refine Eq.mpr (congrArg (s1.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
  have hjoin_low :
      memRegion (sp + 0x110#64) 0x35a ∗ memRegion (sp + 0x46a#64) 0x36 =
        memRegion (sp + 0x110#64) 0x390 :=
    (@memRegion_split' (sp + 0x110#64) (sp + 0x46a#64) 0x35a 0x36 0x390
      (by decide) (by bv_omega) (by decide)).symm
  have hbws_mem : words64At (sp + 0x9d0#64) bws ⊢ memRegion (sp + 0x9d0#64) 0xd8 := by
    have h0xd8 : (0xd8 : Nat) = 8 * bws.length := by omega
    rw [h0xd8]
    exact words64At_entails_memRegion (sp + 0x9d0#64) bws (by omega)
  have hjoin_high :
      memRegion (sp + 0x578#64) 0x608 =
        memRegion (sp + 0x578#64) 0x458 ∗ memRegion (sp + 0x9d0#64) 0xd8 ∗
          memRegion (sp + 0xaa8#64) 0xd8 := by
    rw [@memRegion_split' (sp + 0x578#64) (sp + 0x9d0#64) 0x458 0x1b0 0x608
        (by decide) (by bv_omega) (by decide),
      @memRegion_split' (sp + 0x9d0#64) (sp + 0xaa8#64) 0xd8 0xd8 0x1b0
        (by decide) (by bv_omega) (by decide)]
  have hmf2 := Satisfies.mono (sepConj_mono_left (sepConj_mono_left hbws_mem)) hmf1
  have heq :
      ((memRegion (sp + 0x9d0#64) 0xd8 ∗ words64At (sp + 0x4a0#64) bws) ∗ (F ∗ R)) =
      ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗
        ((sp + 0x4a0#64) ↦ₛ unpack64List bws) ∗ memRegion (sp + 0x578#64) 0x608 ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
    dsimp only [F]
    rw [encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1,
        ← words64At_eq_pointsToBytes (sp + 0x4a0#64) bws, ← hjoin_low, hjoin_high]
    sep_ac_rfl
  rwa [← heq]

/-! ## 4. Budget-Threaded T1 `previous_sessions` Free (`+0x564..+0x5b4`, `tailFreePrevSessions_placed_ok`) -/

theorem tailFreePrevSessions_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (prevCap prevPtr : BitVec 64)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x564#64) (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗
        vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S uuidTryParse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S uuidTryParse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx26, hx28, hx27, hx21, hx23⟩, hstack_le, hmem⟩
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) hmem
  let sp := s0.sp - 0xbe0#64
  change s.mem ⊨
    (memRegion sp 0x58 ∗
      vecAt A.repAlloc 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
      memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  by_cases hcap : prevCap = 0#64
  · subst hcap
    rw [vecAt_prev_zero_eq A.repAlloc sp prevPtr] at hmem
    let F := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0
    have hmem_re : s.mem ⊨
        ⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
        ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ (F ∗ R)) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64))) ∗
            memRegion (sp + 0x128#64) 0x158 ∗ memRegion (sp + 0x280#64) 0x1ea ∗
            pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ (0#64 : BitVec 64).toNat ∧ (0#64 : BitVec 64).toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ (F ∗ R))) := by
        dsimp only [F]; sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    have hwp := freePrevSessions_zero_placed_sepWP (Hk := Hk) (prevPtr := prevPtr) hpc hrun hsp_al hsp
    refine SegExitBudget.of_sepWP (R0 := R0) hmem_re.2 hwp ?_
    intro s1 P_f _ hsteps1 hpc1 hrun1 hmf1
      ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, _, hvregs1, hPf⟩
    subst hPf
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, htr1.trans hm.2⟩
    refine tailWriteErr_placed_ok x st_init st R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H hm1 hst ⟨hbud, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
      ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1.trans hx27, hx21_1.trans hx21, hx23_1.trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea) ∗
        (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗ (F ∗ R)) =
          ((((sp + 0x110#64) ↦₆₄ 0#64) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        dsimp only [F]
        rw [encCommonPlaced_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (vecHeader_prev_weaken sp 0#64 prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x35a ∗
         (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]
  · rw [vecAt_prev_nz_eq A.repAlloc sp prevCap prevPtr hcap] at hmem
    let F_core := memRegion sp 0x58 ∗ memRegion (sp + 0x128#64) 0x158 ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
      encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
      nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
      memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - allocHookStack) ∗
      encSavedRegs s0.sp s0
    have hmem_re :
        s.mem ⊨ ⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗
           ((A.pool lim st s ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
             memRegion prevPtr (prevCap.toNat * 24) ∗ stackAt sp allocHookStack ∗ F_core) ∗ R)) := by
      have heq :
          ((memRegion sp 0x58 ∗
            (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
              (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
               ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
               memRegion prevPtr (prevCap.toNat * 24))) ∗
            memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R) =
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
           ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗ ((sp + 0x120#64) ↦₆₄ 0#64)) ∗
            ((A.pool lim st s ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
              memRegion prevPtr (prevCap.toNat * 24) ∗ stackAt sp allocHookStack ∗ F_core) ∗ R))) := by
        unfold encCommonPlaced
        rw [protocolAddressAt_atState]
        change ((memRegion sp 0x58 ∗
          (⌜0 ≤ prevCap.toNat ∧ prevCap.toNat * 24 < 2 ^ 63 ∧ prevPtr ≠ 0#64⌝ ∗
            (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
             ((sp + 0x120#64) ↦₆₄ 0#64) ∗ A.live prevPtr (prevCap.toNat * 24) 8 ∗
             memRegion prevPtr (prevCap.toNat * 24))) ∗
          memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
          nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
          stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st s) ∗ R) = _
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F_core]
        sep_ac_rfl
      rwa [← heq]
    rw [satisfies_pure_sepConj] at hmem_re
    rcases hmem_re with ⟨⟨_, hcap_lt, _⟩, hmem2⟩
    have hwp := freePrevSessions_nz_placed_step_pre (Hk := Hk) (prevPtr := prevPtr)
      hcap hcap_lt hpc hrun hsp_al hsp
    refine SegExitBudget.of_sepWP (R0 := R0) hmem2 hwp ?_
    intro s_pre P_pre _ hsteps_pre hpc_pre hrun_pre hmf_pre
      ⟨hvm_pre, hsp_pre, hsp_pre_al, htr_pre, hx0_pre, hx1_pre, hx2_pre, hlr_pre,
        hx19_pre, hx21_pre, hx23_pre, _hx25_pre, hx26_pre, hx27_pre, hx28_pre, hx29_pre, hvregs_pre, hP_pre⟩
    subst hP_pre
    have hm_dealloc : s_pre.mem ⊨
        (rustCliDeallocBudgetSpec M A lim).pre (prevPtr, prevCap.toNat * 24, 8, st) s_pre ∗
        ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ F_core) ∗ R) := by
      dsimp only [rustCliDeallocBudgetSpec]
      rw [hsp_pre]
      rw [← A.pool_transport lim st s s_pre hvm_pre] at hmf_pre
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0_pre, hx1_pre, hx2_pre,
        by rw [hlr_pre]; exact LibsignalBinary.Proofs.Placed.ElfLsRetAddr.lsRetAddr624_base_add 464 0x5b4#64 (by decide) (by decide)⟩,
        Eq.mp (congrArg (s_pre.mem ⊨ ·) (by sep_ac_rfl)) hmf_pre⟩
    refine call_nopanic_placed (R0 := R0) (dealloc_placed_ok_at_enc env)
      (prevPtr, prevCap.toNat * 24, 8, st) hpc_pre hrun_pre hsp_pre_al hlr_pre hm_dealloc ?_
    intro s1 hsteps_call hpc1 hrun1 hsp1_pre hsp1_al hcs1 hmf1
    obtain ⟨hx19_c, _, hx21_c, _, hx23_c, _, _, hx26_c, hx27_c, hx28_c, hx29_c, hvregs_c⟩ := hcs1
    dsimp only [rustCliDeallocBudgetSpec] at hmf1
    rw [hsp_pre] at hmf1
    have hsp1 : s1.sp = sp := hsp1_pre.trans hsp_pre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hmf1
    obtain ⟨⟨hacp1, _⟩, hmf1⟩ := hmf1
    have htr_call : s1.trace = s_pre.trace := hacp1.2.1
    have hbud1 := seamBudget_step_freeOnly hbud (freeOnlyEvs_rustDeallocEvents (prevCap.toNat * 24) 8)
    set st1 := M.stepEvents (rustDeallocEvents (prevCap.toNat * 24) 8) st
    have hm1 : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s1 :=
      ⟨hm.1, (htr_call.trans htr_pre).trans hm.2⟩
    have hcrl1 : CryptoVerification.LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem :=
      hcrl.of_keepsFrozen (hsteps_pre.trans hsteps_call).keepsFrozen
    refine tailWriteErr_placed_ok x st_init st1 R0 s0 s1 answers e w0 w1 w2 w3 w4 w5 H hm1 hst ⟨hbud1, ?_⟩
    refine ⟨hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al,
      (hx29_c.trans hx29_pre).trans hx29,
      (hx19_c.trans hx19_pre).trans hx19,
      hcrl1,
      (hvregs_c.trans hvregs_pre).trans hvregs⟩,
      ⟨(hx26_c.trans hx26_pre).trans hx26,
       (hx28_c.trans hx28_pre).trans hx28,
       (hx27_c.trans hx27_pre).trans hx27,
       (hx21_c.trans hx21_pre).trans hx21,
       (hx23_c.trans hx23_pre).trans hx23⟩,
      hstack_le, ?_⟩
    refine Eq.mpr (congrArg (s1.mem ⊨ ·)
      (encTail_mem_retag_eq kit st0 ikit ist0 C ctl S x answers _ R0 s0)) ?_
    have hmf2 : s1.mem ⊨
        (((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
          ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
          memRegion (sp + 0x280#64) 0x1ea) ∗
        (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
          encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
          encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by
      have heq :
          ((A.pool lim st1 s1 ∗ stackAt sp allocHookStack) ∗
           ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
             ((sp + 0x120#64) ↦₆₄ 0#64) ∗ F_core) ∗ R)) =
          ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) := by
        unfold encCommonPlaced
        rw [protocolAddressAt_atState]
        change _ = ((((sp + 0x110#64) ↦₆₄ prevCap) ∗ ((sp + 0x118#64) ↦₆₄ prevPtr) ∗
            ((sp + 0x120#64) ↦₆₄ 0#64) ∗ memRegion (sp + 0x128#64) 0x158 ∗
            memRegion (sp + 0x280#64) 0x1ea) ∗
           (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
             encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
             ((x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A.repAlloc x.rem x.remA ∗ protocolAddressAt A.repAlloc x.loc x.locA ∗
              nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest (x.draws S answers) ∗ FromRecordCallees.lsLogOff ∗
              stackAt sp encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool lim st1 s1) ∗ R))
        rw [stackAt_encSubStack_alloc sp]
        dsimp only [F_core]
        sep_ac_rfl
      rwa [← heq]
    have hmf3 := Satisfies.mono (sepConj_mono_left (vecHeader_prev_weaken sp prevCap prevPtr)) hmf2
    have heq2 :
        (memRegion (sp + 0x110#64) 0x35a ∗
         (memRegion sp 0x58 ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H ∗
           encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
           encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R)) =
        ((memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         encCommonPlaced (A.atState lim st1 s1) ctl x (x.draws S answers) s0 ∗ R) := by sep_ac_rfl
    rwa [← heq2]

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFreePrevSessionsPlacedBudget
