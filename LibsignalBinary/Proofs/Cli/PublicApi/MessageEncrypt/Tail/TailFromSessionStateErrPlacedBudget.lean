/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErr
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErrPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlacedBudget
public import LibsignalBinary.Proofs.Common.SharedHelpers
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
public import ProofLib.SepLogic.WP.Apply
public meta import ProofLib.SepLogic.WP -- shake: keep
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Budget-Threaded Relocatable T1 `from_session_state` Error Tail (`+0x49c..+0x564`)

Proves `fromSessionStateErr_placed_sepWP` and `tailFromSessionStateErr_placed_ok` on Block `464`
(`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErrPlacedBudget

open Arm64 ProofLib SepProp ProofLib.ProgramReflection
open LibsignalBinary.Heap (
  AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved
)
open LibsignalBinary.Proofs.Placed.BudgetPoolSync (
  hooksException sepWP_seg_ls_vm
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins (
  retagSessionStore retagIdentityStore SpqrSendBudgetEnv
  EncTailVBudget SegExitBudget EncEnvBudget
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins (
  dropSessionStructureLocal2BudgetSpec EncEnvFullBudget
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefsBudget (
  EncEnvPlaced EncTailVPlaced SegExitPlaced toTempTwinsIkitEnv toTempTwinsKitEnv
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.CommonPlacedBudget (
  segExitBudget_of_sepWP
)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailDropRecordStepsPlacedBudget (
  tailDropRecordCur_placed_ok_of_dropSs
)
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageEncrypt (
  WithStoresEncGhost encSpillsAtV curScratch
)
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt (
  encEntryPlaced encCommonPlaced encStoreExtraPlaced
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailCommon (
  SpeStaged pollWith tailRegs TailModel
)
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr (
  pollWith_588_mem_elim pollFrom_post_mem_weaken satisfies_memRegion_1
)
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr (
  cliEncCommonRest encCommonPlaced_eq_logOff_rest
)

export CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.TailFromSessionStateErr (
  cliEncCommonRest encCommonPlaced_eq_logOff_rest
)

set_option maxRecDepth 200000

private theorem bv_sub_add_lit_local (x a b : BitVec 64) : x - a + b = x - (a - b) := by
  bv_omega

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit_local BitVec.toNat_zero

/-! ## 1. Budget-Retag & `VmPreserved` Frame Helpers -/

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
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit)
    (slotsP : SepProp) (R0 : SepProp) (s0 : State) :
    (slotsP ∗
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced (retagSessionStore (A' := A') kit)
        ((retagSessionStore (A' := A') kit).storeFinal st0 answers (x.model C S parse answers).2)
        (retagIdentityStore (A' := A') ikit)
        ((retagIdentityStore (A' := A') ikit).idFinal ist0 answers (x.model C S parse answers).2)
        x s0 ∗ R0)) =
    (slotsP ∗
      encSpillsAtV kit.ss_vt ikit.id_vt (s0.sp - 0xbe0#64) x ∗
      memRegion x.ret 248 ∗
      encCommonPlaced A' ctl x (x.draws S answers) s0 ∗
      (encStoreExtraPlaced kit
        (kit.storeFinal st0 answers (x.model C S parse answers).2)
        ikit
        (ikit.idFinal ist0 answers (x.model C S parse answers).2)
        x s0 ∗ R0)) := by
  have hext := encStoreExtraPlaced_final_retag (A' := A') kit st0 ikit ist0 answers
    (x.model C S parse answers).2 x s0
  have hvt :
      encSpillsAtV (retagSessionStore (A' := A') kit).ss_vt
        (retagIdentityStore (A' := A') ikit).id_vt =
      encSpillsAtV kit.ss_vt ikit.id_vt := rfl
  exact congrArg (slotsP ∗ ·)
    (congrArg₂ sepConj (congrFun (congrFun hvt _) _)
      (congrArg (memRegion x.ret 248 ∗ ·)
        (congrArg (encCommonPlaced A' ctl x (x.draws S answers) s0 ∗ ·)
          (congrArg (· ∗ R0) hext))))

theorem cliEncCommonRest_vmPreserved [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (st : M.σ)
    (ctl : BitVec 64) (x : WithStoresEncGhost) (draws : Nat) (s0 s1 s2 : State)
    (hvm : VmPreserved s1 s2) :
    cliEncCommonRest (A.atState lim st s1) ctl x draws s0 =
      cliEncCommonRest (A.atState lim st s2) ctl x draws s0 := by
  rw [(A.atState_eq_of_vmPreserved lim st hvm).symm]

/-! ## 2. `VmPreserved`-Strengthened `SepWP` (`+0x49c..+0x54c`) -/

set_option maxHeartbeats 800000 in
theorem fromSessionStateErr_placed_sepWP [LibsignalPlacement]
    {Hk : LibsignalHooks}
    {s : State} {sp : BitVec 64}
    {w0 w1 w2 w3 w4 w5 : BitVec 64}
    {u850 u858 u860 u9d0 u9d8 u9e0 uab0 uab8 uac0 uac8 uad0 uad8 : BitVec 64}
    (hpc : s.pc = encEntryPlaced + 0x49c#64)
    (hrun : s.status = .Running)
    (hsp_al : s.spAligned = true)
    (hsp : s.sp = sp)
    (hx21 : s.readReg64 .x21 = sp + 0x580#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (lsProg_464 Hk)
      (encEntryPlaced + 0x54c#64) s
      (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
        ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
        ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗
        ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x9d0#64) ↦₆₄ u9d0) ∗ ((sp + 0x9d8#64) ↦₆₄ u9d8) ∗
        ((sp + 0x9e0#64) ↦₆₄ u9e0) ∗
        ((sp + 0xab0#64) ↦₆₄ uab0) ∗ ((sp + 0xab8#64) ↦₆₄ uab8) ∗
        ((sp + 0xac0#64) ↦₆₄ uac0) ∗ ((sp + 0xac8#64) ↦₆₄ uac8) ∗
        ((sp + 0xad0#64) ↦₆₄ uad0) ∗ ((sp + 0xad8#64) ↦₆₄ uad8) ∗
        (lsLogFilterAddr ↦₆₄ 0#64))
      (fun sf P_f =>
        VmPreserved s sf ∧
        sf.sp = sp ∧ sf.spAligned = true ∧ sf.trace = s.trace ∧
        sf.symtab = s.symtab ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x21 = w1 ∧
        sf.readReg64 .x23 = w2 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧
        sf.readReg64 .x27 = w0 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        P_f = (((sp + 0x588#64) ↦₆₄ w0) ∗ ((sp + 0x590#64) ↦₆₄ w1) ∗
          ((sp + 0x598#64) ↦₆₄ w2) ∗ ((sp + 0x5a0#64) ↦₆₄ w3) ∗
          ((sp + 0x5a8#64) ↦₆₄ w4) ∗ ((sp + 0x5b0#64) ↦₆₄ w5) ∗
          ((sp + 0x850#64) ↦₆₄ w3) ∗ ((sp + 0x858#64) ↦₆₄ w4) ∗
          ((sp + 0x860#64) ↦₆₄ w5) ∗
          ((sp + 0x9d0#64) ↦₆₄ w3) ∗ ((sp + 0x9d8#64) ↦₆₄ w4) ∗
          ((sp + 0x9e0#64) ↦₆₄ w5) ∗
          ((sp + 0xab0#64) ↦₆₄ w0) ∗ ((sp + 0xab8#64) ↦₆₄ w1) ∗
          ((sp + 0xac0#64) ↦₆₄ w2) ∗ ((sp + 0xac8#64) ↦₆₄ w3) ∗
          ((sp + 0xad0#64) ↦₆₄ w4) ∗ ((sp + 0xad8#64) ↦₆₄ w5) ∗
          (lsLogFilterAddr ↦₆₄ 0#64))) := by
  subst hsp
  apply sepWP_seg_ls_vm (Q := lsProg_464 (hooksException Hk)) blkLib_eq_464
    (mid := encEntryPlaced + 0x54c#64)
  intro m_strip
  unfold encEntryPlaced at hpc ⊢
  dsimp only [lsProg_464, ite_true, lsLogFilterAddr, lsLogFilterSym]
  wp_steps
  refine SepWP.done (by rfl) (by exact hrun) fun m_real hnsp => ?_
  apply SepWP.done (by rfl) (by exact hrun)
  have hvm : VmPreserved s _ :=
    hnsp.toVmPreserved (by wp_norm_lhs)
  exact ⟨hvm, rfl, hsp_al, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, by sep_ac_rfl⟩

/-! ## 3. Budget-Threaded T1 From-Error Steppers & Tail Discharges (`+0x49c`) -/

theorem tailFromSessionStateErrBudget_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s)
    (hcur : ∀ (s1 : State) (b469 : BitVec 8),
      TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s1 →
      EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        x st_init st answers (encEntryPlaced + 0x54c#64) (tailRegs w0 w1 w2)
        (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
        R0 s0 s1 →
      SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
        x st_init R0 s0 s1 (fun _ => False)) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) := by
  let R := encStoreExtraPlaced kit (kit.storeFinal st0 answers (x.model C S parse answers).2)
    ikit (ikit.idFinal ist0 answers (x.model C S parse answers).2) x s0 ∗ R0
  rcases hs with ⟨hbud, hpc, ⟨hrun, hsp, hsp0_al, hsp_al, hx29, hx19, hcrl, hvregs⟩,
    ⟨hx21, hx25, hx26, hx28⟩, hstack_le, hmem⟩
  let sp := s0.sp - 0xbe0#64
  have hmem := Eq.mp (congrArg (s.mem ⊨ ·)
    (encTail_mem_retag_eq (A' := A.atState lim st s) kit st0 ikit ist0 C ctl parse S x answers _ R0 s0)) hmem
  change s.mem ⊨
    (curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R at hmem
  have h1ea : memRegion (sp + 0x280#64) 0x1ea =
      memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1 := by
    rw [memRegion_split' (b := sp + 0x280#64) (b' := sp + 0x469#64) (N := 0x1ea) (n := 0x1e9) (k := 1)
          (by decide) (by bv_omega) (by decide)]
  rw [h1ea, encCommonPlaced_eq_logOff_rest (A.atState lim st s) ctl x (x.draws S answers) s0] at hmem
  let F_inv := curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
    memRegion (sp + 0x280#64) 0x1e9 ∗ H ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    cliEncCommonRest (A.atState lim st s) ctl x (x.draws S answers) s0 ∗ R
  have hmem_469 : s.mem ⊨
      memRegion (sp + 0x469#64) 1 ∗
      (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ F_inv) := by
    have heq :
        ((curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
          (memRegion (sp + 0x280#64) 0x1e9 ∗ memRegion (sp + 0x469#64) 1) ∗
          pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
         encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
         ((lsLogFilterAddr ↦₆₄ 0#64) ∗ cliEncCommonRest (A.atState lim st s) ctl x (x.draws S answers) s0) ∗ R) =
        (memRegion (sp + 0x469#64) 1 ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗ F_inv)) := by
      dsimp only [F_inv]; sep_ac_rfl
    rwa [← heq]
  obtain ⟨b469, hmem_b469⟩ := satisfies_memRegion_1 hmem_469
  have hmem_poll : s.mem ⊨
      pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv) := by
    have heq :
        (((sp + 0x469#64) ↦₈ b469) ∗
         (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
           (lsLogFilterAddr ↦₆₄ 0#64) ∗ F_inv)) =
        (pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗
         (lsLogFilterAddr ↦₆₄ 0#64) ∗ (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) := by sep_ac_rfl
    rwa [← heq]
  obtain ⟨u850, u858, u860, u9d0, u9d8, u9e0, uab0, uab8, uac0, uac8, uad0, uad8, hmem_wp⟩ :=
    pollWith_588_mem_elim hmem_poll
  have hx29' : s.readReg64 .x29 = sp + 0xb80#64 := by
    rw [hx29]; dsimp only [sp]; bv_omega
  have hwp := fromSessionStateErr_placed_sepWP (Hk := Hk) (w0 := w0) (w1 := w1) (w2 := w2)
    (w3 := w3) (w4 := w4) (w5 := w5)
    (u850 := u850) (u858 := u858) (u860 := u860) (u9d0 := u9d0) (u9d8 := u9d8) (u9e0 := u9e0)
    (uab0 := uab0) (uab8 := uab8) (uac0 := uac0) (uac8 := uac8) (uad0 := uad0) (uad8 := uad8)
    hpc hrun hsp_al hsp hx21 hx25 hx26 hx28 hx29'
  refine segExitBudget_of_sepWP (R := R0) hmem_wp hwp ?_
  intro s1 P_f hsteps1 hpc1 hrun1 hmf1
    ⟨hvm1, hsp1, hsp1_al, htr1, _hsym1, hx19_1, hx21_1, hx23_1, _, hx26_1, hx27_1, hx28_1, hx29_1, hvregs1, hPf⟩
  subst hPf
  have hm1 : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s1 :=
    ⟨hm.1, htr1.trans hm.2⟩
  refine hcur s1 b469 hm1
    ⟨hbud, hpc1, ⟨hrun1, hsp1, hsp0_al, hsp1_al, hx29_1.trans hx29, hx19_1.trans hx19,
      hcrl.of_keepsFrozen hsteps1.keepsFrozen, hvregs1.trans hvregs⟩,
     ⟨hx26_1.trans hx26, hx28_1.trans hx28, hx27_1, hx21_1, hx23_1⟩,
     hstack_le, ?_⟩
  refine Eq.mpr (congrArg (s1.mem ⊨ ·)
    (encTail_mem_retag_eq (A' := A.atState lim st s1) kit st0 ikit ist0 C ctl parse S x answers _ R0 s0)) ?_
  have hmf2 := pollFrom_post_mem_weaken hmf1
  change s1.mem ⊨
    (curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
      memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
      pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
    encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
    encCommonPlaced (A.atState lim st s1) ctl x (x.draws S answers) s0 ∗ R
  rw [encCommonPlaced_eq_logOff_rest (A.atState lim st s1) ctl x (x.draws S answers) s0]
  have heq :
      (pollWith sp 0x9d0 [w3, w4, w5] ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        (((sp + 0x469#64) ↦₈ b469) ∗ F_inv)) =
      ((curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H) ∗
       encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
       ((lsLogFilterAddr ↦₆₄ 0#64) ∗ cliEncCommonRest (A.atState lim st s1) ctl x (x.draws S answers) s0) ∗ R) := by
    dsimp only [F_inv]
    rw [cliEncCommonRest_vmPreserved A lim st ctl x (x.draws S answers) s0 s s1 hvm1]
    sep_ac_rfl
  rwa [← heq]

theorem tailFromSessionStateErrPlaced_step [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      x st_init st answers (encEntryPlaced + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s)
    (hcur : ∀ (s1 : State) (b469 : BitVec 8),
      TailModel kit st0 ikit ist0 C S parse encRecord x answers (.error e) s0 s1 →
      EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
        x st_init st answers (encEntryPlaced + 0x54c#64) (tailRegs w0 w1 w2)
        (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
          memRegion (sp + 0x280#64) 0x1e9 ∗ ((sp + 0x469#64) ↦₈ b469) ∗
          pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
        R0 s0 s1 →
      SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
        x st_init R0 s0 s1 (fun _ => False)) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) :=
  tailFromSessionStateErrBudget_step x st_init st R0 s0 s answers e w0 w1 w2 w3 w4 w5 H g rec hm hs hcur

theorem tailFromSessionStateErr_placed_ok_of_dropSs [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (env : EncEnvBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 442)
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec M A lim)))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) :=
  tailFromSessionStateErrBudget_step x st_init st R0 s0 s answers e w0 w1 w2 w3 w4 w5 H g rec hm hs
    fun s1 b469 hm1 hs1 =>
      tailDropRecordCur_placed_ok_of_dropSs env hdrop x st_init st R0 s0 s1 answers e
        w0 w1 w2 w3 w4 w5 H curScratch (Or.inl rfl) g rec b469 hm1 hst hs1

theorem tailFromSessionStateErr_placed_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (env : EncEnvFullBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) :=
  tailFromSessionStateErr_placed_ok_of_dropSs env.toEncEnvBudget env.calleesFull.dropSs
    x st_init st R0 s0 s answers e w0 w1 w2 w3 w4 w5 H g rec hm hst hs

theorem tailFromSessionStateErrPlaced_ok_of_dropSs [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (envB : EncEnvBudget A lim kit (toTempTwinsKitEnv kitEnv) st0 ikit (toTempTwinsIkitEnv ikitEnv) ist0
      Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (hdrop : subroutine_ok (lsProg_464 Hk) (lsmpl.base 442)
      (StoreKit.withLsRoCl lsmpl (dropSessionStructureLocal2BudgetSpec M A lim)))
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) :=
  tailFromSessionStateErr_placed_ok_of_dropSs envB hdrop
    x st_init st R0 s0 s answers e w0 w1 w2 w3 w4 w5 H g rec hm hst hs

theorem tailFromSessionStateErrPlaced_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    {kit : SessionStoreSpec A.repAlloc 0#64}
    {kitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.SessionStoreKitBudget.SessionStoreBudgetEnv kit}
    {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64}
    {ikitEnv : LibsignalBinary.Proofs.PublicApi.StoreKit.IdentityStoreKitBudget.IdentityStoreBudgetEnv ikit}
    {ist0 : ikit.IdState}
    (env : EncEnvPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (envB : EncEnvBudget A lim kit (toTempTwinsKitEnv kitEnv) st0 ikit (toTempTwinsIkitEnv ikitEnv) ist0
      Scope Q C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (R0 : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A.repAlloc x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv
      x st_init st answers (encEntryPlaced + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A.repAlloc (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R0 s0 s) :
    SegExitPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s (fun _ => False) :=
  tailFromSessionStateErrPlaced_ok_of_dropSs envB env.callees.toTempTwinsFull.dropSs
    x st_init st R0 s0 s answers e w0 w1 w2 w3 w4 w5 H g rec hm hst hs

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErrPlacedBudget
