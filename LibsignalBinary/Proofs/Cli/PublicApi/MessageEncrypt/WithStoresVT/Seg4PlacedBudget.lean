/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public meta import LibsignalBinary.Proofs.Placed.BudgetVmSteps -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegIdentityPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegIdentity
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalEnc
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import ProofLib.RegChain
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable `WithStoresVT` (Part 4): `SegIdentity` and `SegSignal` Prefix

Defines the frame-generalised `VT` budget contracts (`withStoresEncBudgetSpecVT`,
`otrEncryptBudgetSpecQF`, `otrEncryptBudgetSpecQT`, `EncCalleesTBudget`, `EncEnvTBudget`) and
`h45_SegExitVTPlaced` combinators, and proves `h45_segIdentity_placed_okVT`,
`h45_segSignal_to_ack_placed`, and `h45_segSignal_ack_to_enc_placed` on Block `464`
(`lsProg_464 Hk`) under `RustCliAllocBudget M` and `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4PlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalUnackPlacedBudget (SegSignalAckStateVPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalEncPlacedBudget (SegSignalEncStateVPlaced)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalMemPlacedBudget (segSignal_placed_step_bl segSignal_placed_step_enc)
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget.TempTwins (timeAddBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Getters.IdentityBudget (remote_identity_key_placed_ok)
open LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItemsBudget (unackItems_ls_placed_ok)

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegIdentity hiding spAligned_of_sp_eq
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding
  ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced
  EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced
  SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced
  SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced
  SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName
  cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced
  encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym
  lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec
  otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced
  withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed
  withStoresEncStack_split_extra_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames CryptoGames.HKDF CryptoGames.HMAC
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. `VT` Budget Specifications & Environment -/

/-- Relocatable `withStoresEncBudgetSpecV` with `64 ≤ x.rest.length` and `F` (e.g. `TokenInit img`)
framed in `pre` and `post`. -/
def withStoresEncBudgetSpecVT [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) :
    Spec (WithStoresEncGhost × M.σ) :=
  let base := withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
    C ctl uuidParse S sendEnv encRecord
  { base with
    pre := fun (x, st_init) s =>
      ⌜64 ≤ x.rest.length⌝ ∗ F ∗ base.pre (x, st_init) s
    post := fun (x, st_init) s0 sf =>
      F ∗ base.post (x, st_init) s0 sf }

/-- Relocatable budget-threaded `OTR::encrypt` spec for `(pqrState, rest)` satisfying `Q`, with `F` framed. -/
def otrEncryptBudgetSpecQF [LibsignalPlacement] {M : AllocCostModel}
    (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  { otrEncryptBudgetSpec C A lim ctl parse S sendEnv with
    pre := fun (x, st) s =>
      ⌜FitsEnv M lim st (OtrEncryptEnv C S sendEnv parse x)⌝ ∗
        (otrEncryptPlacedSpecQF Q F C (A.atState lim st s) ctl parse S).pre x s
    post := fun (x, st) s0 sf =>
      ∃∗ evs : List AllocEvent,
        ⌜OtrEncryptEnv C S sendEnv parse x evs⌝ ∗
        (otrEncryptPlacedSpecQF Q F C (A.atState lim (M.stepEvents evs st) sf) ctl parse S).post x s0 sf }

/-- Relocatable budget-threaded `OTR::encrypt` spec at `Q := (pq.length < 2^32 ∧ 64 ≤ rest.length)` with `F` framed. -/
def otrEncryptBudgetSpecQT [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv) :
    Spec (OtrEncryptGhost × M.σ) :=
  otrEncryptBudgetSpecQF (fun pq rest => pq.length < 2 ^ 32 ∧ 64 ≤ rest.length)
    F C A lim ctl parse S sendEnv

/-- Budget-threaded `EncCalleesBudget` bundle with `otrEnc` using `otrEncryptBudgetSpecQT F`. -/
structure EncCalleesTBudget [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp) (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (H : LibsignalHooks) : Prop where
  remoteIk : subroutine_ok (lsProg_464 H) (lsmpl.base 29)
    (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyBudgetSpec A.repAlloc))
  otrEnc : subroutine_ok (lsProg_464 H)
    (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
    (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQT F C A lim ctl parse S sendEnv))
  unack : subroutine_ok (lsProg_464 H) (lsmpl.base 36)
    (StoreKit.withLsRoCl lsmpl (unackItemsBudgetSpec A.repAlloc))

/-- Construct `EncCalleesTBudget` from `timeAddVm` and `hotrEnc` by discharging `remoteIk` and `unack`. -/
theorem EncCalleesTBudget.of_otrEnc [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {H : LibsignalHooks}
    (htimeAddVm : HookSat H lsTimeAddSym
      (LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.WithLsRet.withLsRet timeAddBudgetSpec))
    (hotrEnc : subroutine_ok (lsProg_464 H)
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQT F C A lim ctl parse S sendEnv))) :
    EncCalleesTBudget F C A lim ctl parse S sendEnv H where
  remoteIk :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_464 H)
      (remote_identity_key_placed_ok A.repAlloc H)
  otrEnc := hotrEnc
  unack :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_464 H)
      (unackItems_ls_placed_ok htimeAddVm)

/-- Budget-threaded `EncEnvTPlaced` with `callees : EncCalleesTBudget F` and `scopeQ` specialized
to `s.state.pqRatchetState.length < 2 ^ 32`. -/
structure EncEnvTBudget [LibsignalPlacement] {M : AllocCostModel}
    (F : SepProp)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  hooks : PublicApiEncHooksBudget A lim H
  ikitOk : IdentityStoreKitBudgetOkI A lim ikit ikitEnv H
  callees : EncCalleesTBudget F C A lim ctl parse S sendEnv H
  vtables : SessionOnlyVtablesPlacedOk kit
  idVtables : IdentityVtablesPlacedOk ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  scopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s →
    s.state.pqRatchetState.length < 2 ^ 32
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    kit.addrOk x.rem.val →
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

theorem h45_otrEncryptBudgetOkQ_false [LibsignalPlacement] {M : AllocCostModel}
    {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64} {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {H : LibsignalHooks} :
    subroutine_ok (lsProg_464 H)
      (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName)
      (StoreKit.withLsRoCl lsmpl (otrEncryptBudgetSpecQ (fun _ => False) C A lim ctl parse S sendEnv)) := by
  refine Arm64.subroutine_ok_outcome_intro fun (x, st) R s0 _ _ hpre _ => ?_
  have ⟨_, hp⟩ := StoreKit.extract_withLsRoCl hpre
  dsimp only [otrEncryptBudgetSpecQ, otrEncryptPlacedSpecQ] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  rcases hp with ⟨_, hp'⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp'
  exact False.elim hp'.1

theorem h45_subroutineOutcome_vt_of_v_placed [LibsignalPlacement] {M : AllocCostModel}
    {F : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64} {uuidParse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 sf : State}
    (h : SubroutineOutcome
      (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidParse S sendEnv encRecord)
      (x, st_init) (F ∗ R) s0 sf) :
    SubroutineOutcome
      (withStoresEncBudgetSpecVT F A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidParse S sendEnv encRecord)
      (x, st_init) R s0 sf := by
  rcases h with ⟨h1, hcs, hpost⟩ | ⟨hpan, honp⟩ | ⟨code, hexit, honex⟩ | ⟨_hoom, honoom⟩
  · refine Or.inl ⟨h1, hcs, ?_⟩
    dsimp only [withStoresEncBudgetSpecVT]
    exact Satisfies.mono (Entails.of_eq (by sep_ac_rfl)) hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStoresEncBudgetSpecVT, withStoresEncBudgetSpecV, StoreKit.withLsCodeRoLoaded] at honp ⊢
    refine Satisfies.mono ?_ honp
    rw [← sepConj_assoc, sepConj_assoc ⌜_⌝ anyHeap F]
    exact sepConj_mono_left (sepConj_mono_right (entails_anyHeap (anyHeap ∗ F)))
  · refine Or.inr (Or.inr (Or.inl ⟨code, hexit, ?_⟩))
    change sf.mem ⊨ ⌜False⌝ ∗ (F ∗ R) at honex
    rw [satisfies_pure_sepConj] at honex
    exact False.elim honex.1
  · change sf.mem ⊨ ⌜False⌝ ∗ (F ∗ R) at honoom
    rw [satisfies_pure_sepConj] at honoom
    exact False.elim honoom.1

/-! ## 2. `SegIdentity` (`h45_segIdentity_placed_okVT`) -/

section SegIdentity

private theorem segIdentity_placed_step_pre [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp : BitVec 64} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x2c8#64) (hrun : s.status = .Running) (hsp : s.sp = sp) :
    SepWP (lsProg_464 Hk) (lsmpl.base 29) s emp
      (fun sm Pm =>
        VmPreserved s sm ∧ sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = s.readReg64 .x0 ∧ sm.readReg64 .x8 = s.readReg64 .x8 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧ sm.readReg64 .x23 = s.readReg64 .x23 ∧
        sm.readReg64 .x24 = s.readReg64 .x24 ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 Reg.lr = encEntryPlaced + 0x2cc#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧ (Pm ⊢ emp)) := by
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true]
  wp_steps_vm

set_option maxHeartbeats 1200000 in
private theorem segIdentity_placed_step_ok [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp : BitVec 64} {c0 d0 u868 : BitVec 32} {c4 c30 d4 d30 u86c ub08 : BitVec 16}
    {c6 c14 c22 d6 d14 d22 ub00 : BitVec 64} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x2cc#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x58#64) (hx24 : s.readReg64 .x24 = sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64) (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x344#64) s
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
        ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
        ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
        ((sp + 0x868#64) ↦₃₂ u868) ∗ ((sp + 0x86c#64) ↦₁₆ u86c) ∗
        ((sp + 0xb00#64) ↦₆₄ ub00) ∗ ((sp + 0xb08#64) ↦₁₆ ub08))
      (fun sm Pm =>
        VmPreserved s sm ∧ sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧ sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x22 = s.readReg64 .x22 ∧ sm.readReg64 .x23 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = s.readReg64 .x27 ∧ sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = sp + 0xb80#64 ∧ calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          ikChunks6 (sp + 0x350#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
          ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ∗
          ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30))) := by
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true, ikChunks6]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps_vm

private theorem exists_pointsTo16_of_memRegion2_placed (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 2 ∗ R) : ∃ v : BitVec 16, m ⊨ (a ↦₁₆ v) ∗ R := by
  rw [memRegion_split a 1 1 (by decide), ProofLib.memRegion_one a,
      ProofLib.memRegion_one (a + 1#64)] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨b0, b1, hm⟩ := hm
  rw [pointsTo8_pair] at hm
  exact ⟨_, hm⟩

private theorem exists_pointsTo32_of_memRegion4_placed (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 4 ∗ R) : ∃ v : BitVec 32, m ⊨ (a ↦₃₂ v) ∗ R := by
  rw [ProofLib.memRegion_four a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

private theorem exists_pointsTo64_of_memRegion8_placed (a : BitVec 64) {m : Memory} {R : SepProp}
    (hm : m ⊨ memRegion a 8 ∗ R) : ∃ v : BitVec 64, m ⊨ (a ↦₆₄ v) ∗ R := by
  rw [ProofLib.memRegion_eight a, sepExists_sepConj_left, satisfies_sepExists] at hm
  exact hm

private def identityRestFramePlaced [LibsignalPlacement] (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (sp : BitVec 64) (s0 : State) : SepProp :=
  sessionRecordWithoutRemIk A sp g G sess taken ∗ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗ memRegion (sp + 0x350#64) 0x118 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗ memRegion x.ret 248 ∗
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - remoteIdentityKeyStack) ∗
  encSavedRegs s0.sp s0 ∗ A.pool

private theorem otrState_placed_mem_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr sp : BitVec 64) (R : SepProp) (s0 : State) {m : Memory}
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hm : m ⊨ (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118) ∗ curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) :
    ∃ (g : RecordGhost) (G : SessionGhost), g.cur = some G ∧
      (match taken.remoteIdentity with
       | none => G.remoteIk.bytes = []
       | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
      (m ⊨ emp ∗ ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
        memRegion (sp + 0x580#64) 34 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt sp remoteIdentityKeyStack ∗
        identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R)) := by
  unfold takenSlots at hm
  simp only [sepConj_assoc] at hm
  obtain ⟨g, G, hgcur, hrem, hm⟩ := sessionRecordAt_taken_extract_remIk A sp sess taken hm
  have h46a : memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 34 ∗ memRegion (sp + 0x5a2#64) 0x5de := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide), mr_cut_add sp (0x46a + 0x116) 34 0x5de (by decide)]
  have hlog : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  unfold encCommonPlaced at hm
  rw [hsp0, hlog, h46a, stackAt_sub sp encSubStack remoteIdentityKeyStack] at hm
  refine ⟨g, G, hgcur, hrem, ?_⟩
  unfold identityRestFramePlaced; rw [emp_sepConj]
  exact Eq.mp (congrArg (m ⊨ ·) (by sep_ac_rfl)) hm

private theorem remoteIk_placed_pre_frame [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (sp : BitVec 64) (R Pm1 : SepProp) (s0 s1 : State)
    (hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hrem : match taken.remoteIdentity with
      | none => G.remoteIk.bytes = []
      | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)
    (hsp1 : s1.sp = sp) (hx0 : s1.readReg64 .x0 = sp + 0x128#64) (hx8 : s1.readReg64 .x8 = sp + 0x580#64)
    (hPm1 : Pm1 ⊢ emp)
    (hm1 : s1.mem ⊨ Pm1 ∗ ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗
      memRegion (sp + 0x580#64) 34 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp remoteIdentityKeyStack ∗
      identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R)) :
    s1.mem ⊨ (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyPlacedSpec A)).pre
        ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 ∗
      (identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0 ∗ R) := by
  have hm1' := Satisfies.mono (sepConj_mono_left hPm1) hm1
  rw [emp_sepConj] at hm1'
  dsimp only [StoreKit.withLsRoCl, remoteIdentityKeyPlacedSpec]
  rw [hsp1]
  have h1 : s1.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝ ∗
      ⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64 ∧
        (match taken.remoteIdentity with
         | none => G.remoteIk.bytes = []
         | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)⌝ ∗
      ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗ memRegion (sp + 0x580#64) 34 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp remoteIdentityKeyStack ∗
        identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R) := by
    rw [satisfies_pure_sepConj, satisfies_pure_sepConj]
    exact ⟨hcrl1, ⟨hx0, hx8, hrem⟩, hm1'⟩
  exact Eq.mp (congrArg (s1.mem ⊨ ·) (by sep_ac_rfl)) h1

private theorem remoteIk_placed_post_repack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hgcur : g.cur = some G) (htaken_rem : taken.remoteIdentity = some otr.remoteIdentityKey)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp1 : s1.sp = sp)
    (hpost : s2.mem ⊨ ((StoreKit.withLsRoCl lsmpl (remoteIdentityKeyPlacedSpec A)).post
        ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 s2 ∗
      identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R) :
    StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem ∧ s2.trace = s1.trace ∧
    (s2.mem ⊨ ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗ memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) := by
  dsimp only [StoreKit.withLsRoCl, remoteIdentityKeyPlacedSpec] at hpost
  rw [hsp1, htaken_rem] at hpost
  dsimp only [remoteIdentityOkAt] at hpost
  have h581 : (sp + 0x580#64) + 1#64 = sp + 0x581#64 := by bv_omega
  have h582 : (sp + 0x580#64) + 2#64 = sp + 0x582#64 := by bv_omega
  rw [h581, h582] at hpost
  have h1 : s2.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem⌝ ∗ ⌜s2.trace = s1.trace⌝ ∗
      ((vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗ ((sp + 0x580#64) ↦₈ 0#8) ∗
        ((sp + 0x581#64) ↦₈ 1#8) ∗ ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp remoteIdentityKeyStack ∗
        identityRestFramePlaced ss_vt id_vt A ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨hcrl2, htr, hmem⟩
  refine ⟨hcrl2, htr, ?_⟩
  unfold identityRestFramePlaced at hmem
  have hrec := sessionRecordAt_taken_restore_remIk A sp g G sess taken hgcur
  have hlog : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  have hmem_rearr : s2.mem ⊨
      (vecGhostAt A G.remoteIk ((sp + 0x128#64) + 0x18#64) ∗ sessionRecordWithoutRemIk A sp g G sess taken) ∗
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - remoteIdentityKeyStack) ∗
        stackAt sp remoteIdentityKeyStack) ∗
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗ memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗ memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      encSavedRegs s0.sp s0 ∗ A.pool ∗ R :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack remoteIdentityKeyStack] at hmem_rearr
  have hmem_fold := Satisfies.mono (sepConj_mono_left hrec) hmem_rearr
  unfold encCommonPlaced; rw [hsp0, hlog]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem_fold

private def identityStepFramePlaced [LibsignalPlacement] (ss_vt id_vt : BitVec 64)
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (sp : BitVec 64) (s0 : State) : SepProp :=
  (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x2c6 ∗
  memRegion (sp + 0x86e#64) 0x292 ∗ memRegion (sp + 0xb0a#64) 0x76 ∗
  memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0

private theorem remoteIk_placed_ok_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (sp : BitVec 64)
    (R : SepProp) (s0 s2 : State)
    (hm : s2.mem ⊨ ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ((sp + 0x582#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗ memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x5de ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) :
    ∃ (c0 d0 u868 : BitVec 32) (c4 c30 d4 d30 u86c ub08 : BitVec 16)
      (c6 c14 c22 d6 d14 d22 ub00 : BitVec 64),
      (∀ o : BitVec 64, (o ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) =
        ikChunks6 o c0 c4 c6 c14 c22 c30) ∧
      (s2.mem ⊨ (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
          ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
          ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
          ((sp + 0x868#64) ↦₃₂ u868) ∗ ((sp + 0x86c#64) ↦₁₆ u86c) ∗
          ((sp + 0xb00#64) ↦₆₄ ub00) ∗ ((sp + 0xb08#64) ↦₁₆ ub08)) ∗
        (identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0 ∗ R)) := by
  obtain ⟨c0, c4, c6, c14, c22, c30, hpack⟩ :=
    exists_ikChunks6_of_length_32 (bs := otr.remoteIdentityKey.publicKey.bytes.toList)
      (List.Vector.toList_length _)
  rw [hpack (sp + 0x582#64)] at hm
  have h350 : memRegion (sp + 0x350#64) 0x118 =
      memRegion (sp + 0x350#64) 32 ∗ memRegion (sp + 0x370#64) 0xf8 :=
    mr_cut_add sp 0x350 32 0xf8 (by decide)
  have h5a2 : memRegion (sp + 0x5a2#64) 0x5de = memRegion (sp + 0x5a2#64) 0x2c6 ∗
      memRegion (sp + 0x868#64) 4 ∗ memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0x86e#64) 0x292 ∗
      memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗ memRegion (sp + 0xb0a#64) 0x76 := by
    rw [show sp + 0x5a2#64 = sp + BitVec.ofNat 64 0x5a2 from rfl,
      mr_cut_add sp 0x5a2 0x2c6 0x318 (by decide), mr_cut_add sp (0x5a2 + 0x2c6) 4 0x314 (by decide),
      mr_cut_add sp (0x5a2 + 0x2c6 + 4) 2 0x312 (by decide), mr_cut_add sp (0x5a2 + 0x2c6 + 4 + 2) 0x292 0x80 (by decide),
      mr_cut_add sp (0x5a2 + 0x2c6 + 4 + 2 + 0x292) 8 0x78 (by decide), mr_cut_add sp (0x5a2 + 0x2c6 + 4 + 2 + 0x292 + 8) 2 0x76 (by decide)]
  rw [h350, h5a2] at hm
  let Fst := identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0
  have hm_d : s2.mem ⊨ memRegion (sp + 0x350#64) 32 ∗ (memRegion (sp + 0x868#64) 4 ∗
      memRegion (sp + 0x86c#64) 2 ∗ memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗ Fst ∗ R) := by
    dsimp only [Fst]; unfold identityStepFramePlaced; exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm
  obtain ⟨d0, d4, d6, d14, d22, d30, hm_d⟩ := exists_ikChunks6_of_memRegion32 (sp + 0x350#64) hm_d
  have hm_868 : s2.mem ⊨ memRegion (sp + 0x868#64) 4 ∗ (memRegion (sp + 0x86c#64) 2 ∗
      memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗ ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗ Fst ∗ R) := Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_d
  obtain ⟨u868, hm_868⟩ := exists_pointsTo32_of_memRegion4_placed (sp + 0x868#64) hm_868
  have hm_86c : s2.mem ⊨ memRegion (sp + 0x86c#64) 2 ∗ (memRegion (sp + 0xb00#64) 8 ∗
      memRegion (sp + 0xb08#64) 2 ∗ ((sp + 0x868#64) ↦₃₂ u868) ∗ ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗ Fst ∗ R) := Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_868
  obtain ⟨u86c, hm_86c⟩ := exists_pointsTo16_of_memRegion2_placed (sp + 0x86c#64) hm_86c
  have hm_b00 : s2.mem ⊨ memRegion (sp + 0xb00#64) 8 ∗ (memRegion (sp + 0xb08#64) 2 ∗
      ((sp + 0x86c#64) ↦₁₆ u86c) ∗ ((sp + 0x868#64) ↦₃₂ u868) ∗ ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗ Fst ∗ R) := Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_86c
  obtain ⟨ub00, hm_b00⟩ := exists_pointsTo64_of_memRegion8_placed (sp + 0xb00#64) hm_b00
  have hm_b08 : s2.mem ⊨ memRegion (sp + 0xb08#64) 2 ∗ (((sp + 0xb00#64) ↦₆₄ ub00) ∗
      ((sp + 0x86c#64) ↦₁₆ u86c) ∗ ((sp + 0x868#64) ↦₃₂ u868) ∗ ikChunks6 (sp + 0x350#64) d0 d4 d6 d14 d22 d30 ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗ Fst ∗ R) := Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_b00
  obtain ⟨ub08, hm_b08⟩ := exists_pointsTo16_of_memRegion2_placed (sp + 0xb08#64) hm_b08
  exact ⟨c0, d0, u868, c4, c30, d4, d30, u86c, ub08, c6, c14, c22, d6, d14, d22, ub00, hpack,
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_b08⟩

private theorem remoteIk_placed_ok_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (c0 : BitVec 32) (c4 c30 : BitVec 16) (c6 c14 c22 : BitVec 64)
    (sp : BitVec 64) (R Pm3 : SepProp) (s0 s3 : State)
    (hpack : ∀ o : BitVec 64, (o ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) = ikChunks6 o c0 c4 c6 c14 c22 c30)
    (hPm3 : Pm3 ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ikChunks6 (sp + 0x350#64) c0 c4 c6 c14 c22 c30 ∗
      ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗ ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ∗
      ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ∗ ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30))
    (hm3 : s3.mem ⊨ Pm3 ∗ (identityStepFramePlaced ss_vt id_vt A ctl x sess taken pqCap pqPtr otr sp s0 ∗ R)) :
    s3.mem ⊨ (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm3) hm3
  rw [← hpack (sp + 0x350#64)] at hm1
  have h580_ent : ((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗
      ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30 ⊢ memRegion (sp + 0x580#64) 34 := by
    rw [show sp + 0x580#64 = sp + BitVec.ofNat 64 0x580 from rfl,
        mr_cut_add sp 0x580 1 33 (by decide), mr_cut_add sp (0x580 + 1) 1 32 (by decide)]
    exact sepConj_mono (pointsTo8_entails_memRegion _ _)
      (sepConj_mono (pointsTo8_entails_memRegion _ _) (ikChunks6_entails_memRegion _ _ _ _ _ _ _))
  have h868_ent : ((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4) ⊢ memRegion (sp + 0x868#64) 4 ∗ memRegion (sp + 0x86c#64) 2 :=
    sepConj_mono (pointsTo32_entails_memRegion _ _) (pointsTo16_entails_memRegion _ _)
  have hb00_ent : ((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30) ⊢ memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 :=
    sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo16_entails_memRegion _ _)
  have h46a_eq : memRegion (sp + 0x46a#64) 0x716 = memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 34 ∗
      memRegion (sp + 0x5a2#64) 0x2c6 ∗ memRegion (sp + 0x868#64) 4 ∗ memRegion (sp + 0x86c#64) 2 ∗
      memRegion (sp + 0x86e#64) 0x292 ∗ memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗ memRegion (sp + 0xb0a#64) 0x76 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
      mr_cut_add sp 0x46a 0x116 0x600 (by decide), mr_cut_add sp (0x46a + 0x116) 34 0x5de (by decide),
      mr_cut_add sp (0x46a + 0x116 + 34) 0x2c6 0x318 (by decide), mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6) 4 0x314 (by decide),
      mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4) 2 0x312 (by decide), mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4 + 2) 0x292 0x80 (by decide),
      mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4 + 2 + 0x292) 8 0x78 (by decide), mr_cut_add sp (0x46a + 0x116 + 34 + 0x2c6 + 4 + 2 + 0x292 + 8) 2 0x76 (by decide)]
  unfold identityStepFramePlaced at hm1
  have hm_rearr : s3.mem ⊨ (((sp + 0x580#64) ↦₈ 0#8) ∗ ((sp + 0x581#64) ↦₈ 1#8) ∗ ikChunks6 (sp + 0x582#64) c0 c4 c6 c14 c22 c30) ∗
      (((sp + 0x868#64) ↦₃₂ c0) ∗ ((sp + 0x86c#64) ↦₁₆ c4)) ∗ (((sp + 0xb00#64) ↦₆₄ c22) ∗ ((sp + 0xb08#64) ↦₁₆ c30)) ∗
      ((∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
        otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗ ((sp + 0x350#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
        memRegion (sp + 0x370#64) 0xf8 ∗ curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5a2#64) 0x2c6 ∗ memRegion (sp + 0x86e#64) 0x292 ∗
        memRegion (sp + 0xb0a#64) 0x76 ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm_mono := Satisfies.mono (sepConj_mono h580_ent (sepConj_mono h868_ent (sepConj_mono_left hb00_ent))) hm_rearr
  have hm_poll : s3.mem ⊨ (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 34 ∗
        memRegion (sp + 0x5a2#64) 0x2c6 ∗ memRegion (sp + 0x868#64) 4 ∗ memRegion (sp + 0x86c#64) 2 ∗
        memRegion (sp + 0x86e#64) 0x292 ∗ memRegion (sp + 0xb00#64) 8 ∗ memRegion (sp + 0xb08#64) 2 ∗ memRegion (sp + 0xb0a#64) 0x76) ∗
      (∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗ ((sp + 0x350#64) ↦ₛ otr.remoteIdentityKey.publicKey.bytes.toList) ∗
      memRegion (sp + 0x370#64) 0xf8 ∗ curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R := Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll; unfold takenSlots
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm_poll

theorem h45_segIdentity_placed_okVT [LibsignalPlacement] {F0 : SepProp}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {M : AllocCostModel} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R0 : SepProp)
    (s0 s : State)
    (hotrBudget : OtrStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken pqCap pqPtr R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => ∃ k,
        KeyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
          x st_init st r sess otr taken pqCap pqPtr k R0 s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hotrBudget with ⟨hbud, hcur, hsc, hfrom, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx0, hx8, hx20, hx22, hx23, hx24, hx25, hx26, hx27, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  dsimp only [retagSessionStore, retagIdentityStore] at hsc htr hm
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hsp_x29 : s0.sp - 0x60#64 = sp + 0xb80#64 := by rw [← hsp0]; bv_omega
  have hs_pc' : s.pc = encEntryPlaced + 0x2c8#64 := hs_pc
  have htaken_rem : taken.remoteIdentity = some otr.remoteIdentityKey :=
    taken_remoteIdentity_eq_some hfrom
  obtain ⟨g, G, hgcur, hrem, hm_unp⟩ :=
    otrState_placed_mem_unpack (A.atState lim st s) ctl x sess otr taken pqCap pqPtr sp R s0 hsp0 hm
  refine SegExitBudget.of_sepWP hm_unp (segIdentity_placed_step_pre hs_pc' hrun hsp) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hvm01, hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x22, hs1_x23, hs1_x24, hs1_x25,
      hs1_x26, hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_pre := remoteIk_placed_pre_frame (A.atState lim st s) ctl x g G sess taken pqCap pqPtr otr sp R Pm1 s0 s1
    hcrl1 hrem hs1_sp (hs1_x0.trans hx0) (hs1_x8.trans hx8) hPm1 hm1
  refine SegExitBudget.call hEnv.callees.remoteIk
    ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyBudgetSpec A.repAlloc)).onExit
            ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ code s1 _ = ⌜False⌝
            from rfl, satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun _ _ _ hpan => by
      rw [show (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyBudgetSpec A.repAlloc)).onPanic
            ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 _ = ⌜False⌝
            from rfl, sepConj_assoc, satisfies_pure_sepConj] at hpan
      exact hpan.1.elim)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x23 : s2.readReg64 .x23 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x29 : s2.readReg64 .x29 = sp + 0xb80#64 := by reg_chain
  have hpost_eq : ∀ xc s1' s2',
      (StoreKit.withLsRoCl lsmpl (remoteIdentityKeyBudgetSpec A.repAlloc)).post xc s1' s2' =
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2'.mem⌝ ∗
          (⌜VmPreserved s1' s2'⌝ ∗ (remoteIdentityKeyPlacedSpec (A.atState lim st s)).post xc s1' s2') :=
    fun _ _ _ => rfl
  rw [hpost_eq] at hpost2
  have hpost2_vm : s2.mem ⊨ ⌜VmPreserved s1 s2⌝ ∗
      (((StoreKit.withLsRoCl lsmpl (remoteIdentityKeyPlacedSpec (A.atState lim st s))).post
          ⟨sp + 0x128#64, G.remoteIk, taken.remoteIdentity, sp + 0x580#64⟩ s1 s2 ∗
        identityRestFramePlaced kit.ss_vt ikit.id_vt (A.atState lim st s) ctl x g G sess taken pqCap pqPtr otr sp s0) ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost2
  rw [satisfies_pure_sepConj] at hpost2_vm
  rcases hpost2_vm with ⟨hvm12, hpost2'⟩
  obtain ⟨hcrl2, hs2_tr, hm2⟩ := remoteIk_placed_post_repack (A.atState lim st s) ctl x g G sess taken pqCap pqPtr otr
    sp R s0 s1 s2 hgcur htaken_rem hsp0 hs1_sp hpost2'
  obtain ⟨c0, d0, u868, c4, c30, d4, d30, u86c, ub08, c6, c14, c22, d6, d14, d22, ub00,
    hpack, hm2_unp⟩ :=
    remoteIk_placed_ok_unpack (A.atState lim st s) ctl x sess taken pqCap pqPtr otr sp R s0 s2 hm2
  refine SegExitBudget.of_sepWP hm2_unp
    (segIdentity_placed_step_ok hs2_pc hs2_run hs2_sp' hs2_al hs2_x23 hs2_x24 hs2_x25 hs2_x29) ?_
  intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
    ⟨hvm23, hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x25, hs3_x26,
      hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
  have hm3_ok := remoteIk_placed_ok_pack (A.atState lim st s) ctl x sess taken pqCap pqPtr otr
    c0 c4 c30 c6 c14 c22 sp R Pm3 s0 s3 hpack hPm3 hm3
  have hvm03 : VmPreserved s s3 := hvm01.trans (hvm12.trans hvm23)
  rw [(A.atState_eq_of_vmPreserved lim st hvm03).symm] at hm3_ok
  have hbud' : SeamBudget lim
      (WithStoresEncEnv kit kitEnv st0 ikit ikitEnv ist0 Scope C S sendEnv uuidTryParse x) st_init st
      (FromKeyEnv C S sendEnv uuidTryParse kit kitEnv st0 ikit ikitEnv ist0 x sess otr taken
        otr.remoteIdentityKey) :=
    hbud.narrow (fun _ hev => Or.inr ⟨otr.remoteIdentityKey, htaken_rem, hev⟩)
  refine SegExitBudget.next ⟨otr.remoteIdentityKey, hbud', hcur, hsc, hfrom, htaken_rem, ?_⟩
  dsimp only [retagSessionStore, retagIdentityStore]
  exact ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
    by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩, by reg_chain,
    ⟨hs3_x0, hs3_x8, by reg_chain, by reg_chain, hs3_x23, hs3_x25,
      by reg_chain, by reg_chain, by reg_chain⟩,
    hpt, hrest, hloc, hnow, hstk, hm3_ok⟩

end SegIdentity

/-! ## 3. `h45_SegExitVTPlaced` Combinators & `SegSignal` Prefix (`to_ack`, `ack_to_enc`) -/

section SegSignal

/-- Segment continuation wrapper for `withStoresEncBudgetSpecVT F0` on `lsProg_464 H`. -/
def h45_SegExitVTPlaced [LibsignalPlacement] {M : AllocCostModel}
    (F0 : SepProp)
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (kit : SessionStoreSpec A.repAlloc 0#64) (kitEnv : SessionStoreBudgetEnv kit) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A.repAlloc 0#64) (ikitEnv : IdentityStoreBudgetEnv ikit) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (sendEnv : SpqrSendBudgetEnv)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (x : WithStoresEncGhost) (st_init : M.σ) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (lsProg_464 H).CodeLoaded s.mem →
    ∃ sf, Steps (lsProg_464 H) s sf ∧
      (next sf ∨
        SubroutineOutcome
          (withStoresEncBudgetSpecVT F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
            C ctl parse S sendEnv encRecord)
          (x, st_init) R s0 sf)

theorem h45_segExitVT_of_segExit_placed [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h : SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
      x st_init (F0 ∗ R) s0 s next) :
    h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
      x st_init R s0 s next := by
  intro hL; obtain ⟨sf, hst, hnext | hout⟩ := h hL
  · exact ⟨sf, hst, Or.inl hnext⟩
  · exact ⟨sf, hst, Or.inr (h45_subroutineOutcome_vt_of_v_placed hout)⟩

theorem h45_segExitVT_trans_placed [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {mid next : State → Prop}
    (h1 : h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
      x st_init R s0 s mid)
    (h2 : ∀ sm, mid sm → h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv
      encRecord H x st_init R s0 sm next) :
    h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
      x st_init R s0 s next := by
  intro hL; obtain ⟨sm, hst1, hmid | hout⟩ := h1 hL
  · obtain ⟨sf, hst2, hnext⟩ := h2 sm hmid (hst1.codeLoaded hL)
    exact ⟨sf, hst1.trans hst2, hnext⟩
  · exact ⟨sm, hst1, Or.inr hout⟩

theorem h45_segExitVT_of_false_placed [LibsignalPlacement] {M : AllocCostModel} {F0 : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop} {C : Crypto} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)} {H : LibsignalHooks}
    {x : WithStoresEncGhost} {st_init : M.σ} {R : SepProp} {s0 s : State} {next : State → Prop}
    (h : h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
      x st_init R s0 s (fun _ => False)) :
    h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl parse S sendEnv encRecord H
      x st_init R s0 s next := by
  intro hL; obtain ⟨sf, hst, hfalse | hout⟩ := h hL
  · exact False.elim hfalse
  · exact ⟨sf, hst, Or.inr hout⟩

theorem h45_segExitVT_call_sub_placed [LibsignalPlacement] {α : Type} {M : AllocCostModel}
    {C : Crypto} {F0 : SepProp}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {ctl : BitVec 64} {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks} {x : WithStoresEncGhost} {st_init : M.σ} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_464 H) entry spec) (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (lsProg_464 H) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (withStoresEncBudgetSpecV A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord).onPanic (x, st_init) s0 sf ∗ R0))
    (hnext : ∀ sm : State, (lsProg_464 H).CodeLoaded s.mem →
      Steps (lsProg_464 H) s sm → sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm → (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
        C ctl uuidTryParse S sendEnv encRecord H x st_init R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    h45_SegExitVTPlaced F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope
      C ctl uuidTryParse S sendEnv encRecord H x st_init R0 s0 s next := by
  intro hL
  have hwpp : SepWPp (lsProg_464 H) ret_pc s (spec.pre xc s ∗ F)
      (fun sm Pm => sm.sp = s.sp ∧ CalleeSavedPreserved s sm ∧ Pm = spec.post xc s sm ∗ F)
      (fun sf Pf => Pf = spec.onPanic xc s sf ∗ F) :=
    SepWPp.call (x := xc) (F := F) hcall hpc hrun hsp hlr
      (fun _ h => by rwa [sepConj_assoc] at h) hexit (fun _ _ => rfl)
      (fun _ hpcm hrunm hspm hcsm => SepWPp.done hpcm hrunm ⟨hspm, hcsm, rfl⟩)
      (fun sf R' hst hmem => False.elim (hoom sf (F ∗ R') hst hmem))
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, hspm, hcsm, rfl⟩ | ⟨hpan, _, hpost, rfl⟩ | ⟨_, hoom_f⟩⟩ :=
    hwpp R (by rwa [← sepConj_assoc] at hm) hL
  · obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (not_satisfies_false_sepConj hoom_f).elim

private def segSignalUnackRestFramePlaced [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (g : RecordGhost)
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (pqCap pqPtr : BitVec 64)
    (k : IdentityKey) (sp : BitVec 64) (s0 : State) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
  otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
  ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x5d8#64) 0x5a8 ∗ memRegion x.ret 248 ∗
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - unackItemsStack) ∗
  encSavedRegs s0.sp s0 ∗ A.pool

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_keyState_mem_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (sp : BitVec 64) (R : SepProp) (s0 : State)
    {m : Memory} (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hm : m ⊨ (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) :
    ∃ g G, m ⊨ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
        memRegion (sp + 0x580#64) 88 ∗ FromRecordCallees.lsLogOff ∗ stackAt sp unackItemsStack ∗
        segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗ R) := by
  unfold takenSlots encCommonPlaced at hm
  rw [hsp0] at hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm
  obtain ⟨g, hm⟩ := hm
  have hm_rec := Satisfies.mono (sepConj_mono_left (segSignal_rec_unpack A sp g sess taken)) hm
  simp only [sepExists_sepConj_left, satisfies_sepExists, sepConj_assoc] at hm_rec
  obtain ⟨G, hm_rec⟩ := hm_rec
  have h46a : memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 88 ∗ memRegion (sp + 0x5d8#64) 0x5a8 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide), mr_cut_add sp (0x46a + 0x116) 88 0x5a8 (by decide)]
  rw [h46a, stackAt_sub sp encSubStack unackItemsStack] at hm_rec
  refine ⟨g, G, ?_⟩
  unfold segSignalUnackRestFramePlaced
  exact Eq.mp (congrArg (m ⊨ ·) (by sep_ac_rfl)) hm_rec

private theorem segSignal_placed_unack_pre_frame [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R Pm : SepProp) (s0 s1 : State)
    (hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hsp1 : s1.sp = sp) (hx0 : s1.readReg64 .x0 = sp + 0x128#64) (hx8 : s1.readReg64 .x8 = sp + 0x580#64)
    (hPm : Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))
    (hm : s1.mem ⊨ Pm ∗ ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
      memRegion (sp + 0x580#64) 88 ∗ FromRecordCallees.lsLogOff ∗ stackAt sp unackItemsStack ∗
      segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗ R)) :
    s1.mem ⊨ (StoreKit.withLsRoCl lsmpl
        (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec A)).pre
        ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 ∗
      ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗ R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  dsimp only [StoreKit.withLsRoCl,
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec]
  rw [hsp1]
  have hpure : (⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝ : SepProp) ∗
      ⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
          memRegion (sp + 0x580#64) 88 ∗ FromRecordCallees.lsLogOff ∗ stackAt sp unackItemsStack ∗
          segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗ R)) =
      (((⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ∗
        memRegion (sp + 0x580#64) 88 ∗ FromRecordCallees.lsLogOff ∗ stackAt sp unackItemsStack) ∗
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝) ∗
        ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0) ∗ R)) := by
    sep_ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hcrl1, ⟨hx0, hx8⟩, hm'⟩

private theorem segSignal_placed_unack_panic_absurd [LibsignalPlacement] (A : RustAlloc)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (sp : BitVec 64) (F R : SepProp) (s1 sf : State) (hpk : sess.pendingPreKey = none)
    (hpost : sf.mem ⊨ ((StoreKit.withLsRoCl lsmpl
        (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec A)).onPanic
      ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 sf ∗ F) ∗ R) : False := by
  unfold StoreKit.withLsRoCl
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec at hpost
  dsimp only at hpost
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpost
  rcases hpost.1.1 with ⟨items, hsome, _⟩
  change sess.pendingPreKey = some items at hsome
  rw [hpk] at hsome
  cases hsome

set_option maxHeartbeats 800000 in
private theorem segSignal_placed_unack_post_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64) (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (sp : BitVec 64) (R : SepProp) (s0 s1 s2 : State)
    (hsp0 : s0.sp - 0xbe0#64 = sp) (hsp1 : s1.sp = sp) (hpk : sess.pendingPreKey = none)
    (hpost : s2.mem ⊨ ((StoreKit.withLsRoCl lsmpl
        (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec A)).post
      ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 s2 ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        segSignalUnackRestFramePlaced (ss_vt := ss_vt) (id_vt := id_vt) A ctl x g otr pqCap pqPtr k sp s0)) ∗ R) :
    StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem ∧ s2.trace = s1.trace ∧
    (s2.mem ⊨ (takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
        ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
        memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) := by
  have hout : unackOutAt (sp + 0x580#64) G.kyber
      ({ sess with state := taken }).pendingKyberPreKey
      ({ sess with state := taken }).pendingPreKey =
      ((sp + 0x580#64) ↦₃₂ 2#32) ∗ memRegion (sp + 0x584#64) 84 := by
    change unackOutAt (sp + 0x580#64) G.kyber sess.pendingKyberPreKey sess.pendingPreKey = _
    rw [hpk]; unfold unackOutAt
    have h584 : (sp + 0x580#64) + 4#64 = sp + 0x584#64 := by bv_omega
    rw [h584]
  dsimp only [StoreKit.withLsRoCl,
    CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec] at hpost
  rw [hsp1, hout] at hpost
  simp only [sepConj_assoc] at hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj] at hpost
  rcases hpost with ⟨hcrl2, htr, hmem⟩
  refine ⟨hcrl2, htr, ?_⟩
  unfold segSignalUnackRestFramePlaced at hmem
  have hrec : vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
      sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken } ⊢
      ∃∗ g' : RecordGhost, sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess taken) :=
    Entails.trans (segSignal_rec_pack A sp g.prevCap g.prevPtr G sess taken)
      (Entails.sepExists_right ⟨g.prevCap, g.prevPtr, some G⟩ (Entails.refl _))
  have hmem_rearr : s2.mem ⊨
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateReprAt A (sp + 0x128#64) G { sess with state := taken }) ∗
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - unackItemsStack) ∗
        stackAt sp unackItemsStack) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8 ∗ memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ FromRecordCallees.lsLogOff ∗
      encSavedRegs s0.sp s0 ∗ A.pool ∗ R :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack unackItemsStack] at hmem_rearr
  have hmem_fold := Satisfies.mono (sepConj_mono_left hrec) hmem_rearr
  unfold takenSlots encCommonPlaced; rw [hsp0]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem_fold

theorem h45_segSignal_to_ack_placed [LibsignalPlacement]
    {F0 : SepProp} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (hEnv : EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State) (hpk : sess.pendingPreKey = none)
    (hs : KeyStateVBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord
      x st_init st r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => SegSignalAckStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord
        x st_init st r sess otr taken pqCap pqPtr k R0 s0 s') := by
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hs with ⟨hbud, hcur, hsc, hfrom, hrem, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx0, hx8, hx20, _hx22, hx23, hx25, hx26, hx27, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  dsimp only [retagSessionStore, retagIdentityStore] at hsc htr hm
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  obtain ⟨g, G, hm_unp⟩ :=
    segSignal_placed_keyState_mem_unpack (A.atState lim st s) ctl x sess otr taken pqCap pqPtr k sp R s0 hsp0 hm
  refine SegExitBudget.of_sepWP hm_unp (segSignal_placed_step_bl hs_pc hrun hsp hal) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hvm01, hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x23, hs1_x25, hs1_x26, hs1_x27,
      hs1_x28, hs1_x29, hs1_vregs, hs1_lr, hPm1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_pre := segSignal_placed_unack_pre_frame (A.atState lim st s) ctl x g G sess otr taken pqCap pqPtr k sp R Pm1 s0 s1
    hcrl1 hs1_sp (hs1_x0.trans hx0) (hs1_x8.trans hx8) hPm1 hm1
  refine SegExitBudget.call hEnv.callees.unack
    ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (unackItemsBudgetSpec A.repAlloc)).onExit
        ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpost =>
      (segSignal_placed_unack_panic_absurd (A.atState lim st s) G sess taken sp _ R s1 sf hpk hpost).elim)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hpost_eq : ∀ xc s1' s2',
      (StoreKit.withLsRoCl lsmpl (unackItemsBudgetSpec A.repAlloc)).post xc s1' s2' =
        ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2'.mem⌝ ∗
          (⌜VmPreserved s1' s2'⌝ ∗
            (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec
              (A.atState lim st s)).post xc s1' s2') :=
    fun _ _ _ => rfl
  rw [hpost_eq] at hpost2
  have hpost2_vm : s2.mem ⊨ ⌜VmPreserved s1 s2⌝ ∗
      (((StoreKit.withLsRoCl lsmpl
          (CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.UnackItems.unackItemsPlacedSpec
            (A.atState lim st s))).post
          ⟨sp + 0x128#64, G, { sess with state := taken }, sp + 0x580#64⟩ s1 s2 ∗
        (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          segSignalUnackRestFramePlaced (ss_vt := kit.ss_vt) (id_vt := ikit.id_vt)
            (A.atState lim st s) ctl x g otr pqCap pqPtr k sp s0)) ∗ R) := by
    dsimp only [StoreKit.withLsRoCl]
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost2
  rw [satisfies_pure_sepConj] at hpost2_vm
  rcases hpost2_vm with ⟨hvm12, hpost2'⟩
  have ⟨hcrl2, hs2_tr, hm2⟩ := segSignal_placed_unack_post_pack (A.atState lim st s) ctl x g G sess otr taken pqCap pqPtr k sp R
    s0 s1 s2 hsp0 hs1_sp hpk hpost2'
  rw [(A.atState_eq_of_vmPreserved lim st (hvm01.trans hvm12)).symm] at hm2
  refine SegExitBudget.next ⟨hbud, hcur, hsc, hfrom, hrem, hpk, hs2_pc,
    ⟨hs2_run, by reg_chain, hal0, hs2_al, by reg_chain, by reg_chain, hcrl2,
      (hcs12.2.2.2.2.2.2.2.2.2.2.2).trans (hs1_vregs.trans hvregs)⟩, by reg_chain,
    by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain, by reg_chain,
    hpt, hrest, hloc, hnow, hstk, hm2⟩

set_option maxHeartbeats 1600000 in
theorem h45_segSignal_ack_to_enc_placed [LibsignalPlacement]
    {F0 : SepProp} {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks}
    (_hEnv : EncEnvTBudget F0 A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk)
    (x : WithStoresEncGhost) (st_init st : M.σ) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
    (R0 : SepProp) (s0 s : State)
    (hs : SegSignalAckStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord
      x st_init st r sess otr taken pqCap pqPtr k R0 s0 s) :
    SegExitBudget A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord Hk
      x st_init R0 s0 s
      (fun s' => SegSignalEncStateVPlaced A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl S sendEnv encRecord
        x st_init st r sess otr taken pqCap pqPtr k R0 s0 s') := by
  obtain ⟨hbud, hcur, hsc, hfrom, hrem, hnone, hs_pc, ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, hx20, hx23, hx25, hx26, hx27, hx28, hpt, hrest, hloc, hnow, hstk, hm⟩ := hs
  set sp := s0.sp - 0xbe0#64 with hsp0
  change s.mem ⊨
    (takenSlots (A.atState lim st s) sp sess taken ∗
      otrAt (A.atState lim st s) (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8) ∗
    curScratch sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗
    (memRegion (sp + 0x46a#64) 0x116 ∗ ((sp + 0x580#64) ↦₃₂ 2#32) ∗
      memRegion (sp + 0x584#64) 84 ∗ memRegion (sp + 0x5d8#64) 0x5a8) ∗
    memRegion x.ret 248 ∗ encCommonPlaced (A.atState lim st s) ctl x 0 s0 ∗
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) at hm
  unfold curScratch encSpillsAtV at hm
  have hscr : memRegion sp 0x50 =
      memRegion sp 0x38 ∗ memRegion (sp + 0x38#64) 8 ∗ memRegion (sp + 0x40#64) 8 ∗ memRegion (sp + 0x48#64) 8 := by
    rw [segSignal_memRegion_cut sp (sp + 0x38#64) 0x50 0x38 0x18 rfl rfl (by decide),
      segSignal_memRegion_cut (sp + 0x38#64) (sp + 0x40#64) 0x18 8 0x10 (by bv_omega) rfl (by decide),
      segSignal_memRegion_cut (sp + 0x40#64) (sp + 0x48#64) 0x10 8 8 (by bv_omega) rfl (by decide)]
  have h584 : memRegion (sp + 0x584#64) 84 =
      memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗ memRegion (sp + 0x590#64) 8 ∗
        memRegion (sp + 0x598#64) 4 ∗ memRegion (sp + 0x59c#64) 8 ∗ memRegion (sp + 0x5a4#64) 8 ∗
        memRegion (sp + 0x5ac#64) 8 ∗ memRegion (sp + 0x5b4#64) 8 ∗ memRegion (sp + 0x5bc#64) 4 ∗
        memRegion (sp + 0x5c0#64) 24 := by
    rw [show (84 : Nat) = 4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + 24)))))))) from rfl,
      show sp + 0x584#64 = sp + BitVec.ofNat 64 0x584 from rfl,
      mr_cut_add sp 0x584 4 _ (by decide), mr_cut_add sp (0x584 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8) 8 _ (by decide), mr_cut_add sp (0x584 + 4 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x584 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  have h5d8 : memRegion (sp + 0x5d8#64) 0x5a8 =
      memRegion (sp + 0x5d8#64) 32 ∗ memRegion (sp + 0x5f8#64) 0x278 ∗
        memRegion (sp + 0x870#64) 8 ∗ memRegion (sp + 0x878#64) 8 ∗
        memRegion (sp + 0x880#64) 8 ∗ memRegion (sp + 0x888#64) 8 ∗
        memRegion (sp + 0x890#64) 4 ∗ memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x5a8 : Nat) = 32 + (0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec)))))) from rfl,
      show sp + 0x5d8#64 = sp + BitVec.ofNat 64 0x5d8 from rfl,
      mr_cut_add sp 0x5d8 32 _ (by decide), mr_cut_add sp (0x5d8 + 32) 0x278 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5d8 + 32 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  rw [hscr, h584, h5d8] at hm
  obtain ⟨u38, hm⟩ := segSignal_peel8 (sp + 0x38#64) (by sep_focus) hm
  obtain ⟨u40, hm⟩ := segSignal_peel8 (sp + 0x40#64) (by sep_focus) hm
  obtain ⟨u48, hm⟩ := segSignal_peel8 (sp + 0x48#64) (by sep_focus) hm
  obtain ⟨a0, hm⟩ := segSignal_peel4 (sp + 0x584#64) (by sep_focus) hm
  obtain ⟨a1, hm⟩ := segSignal_peel8 (sp + 0x588#64) (by sep_focus) hm
  obtain ⟨a2, hm⟩ := segSignal_peel8 (sp + 0x590#64) (by sep_focus) hm
  obtain ⟨a3, hm⟩ := segSignal_peel4 (sp + 0x598#64) (by sep_focus) hm
  obtain ⟨c0, hm⟩ := segSignal_peel8 (sp + 0x59c#64) (by sep_focus) hm
  obtain ⟨c1, hm⟩ := segSignal_peel8 (sp + 0x5a4#64) (by sep_focus) hm
  obtain ⟨c2, hm⟩ := segSignal_peel8 (sp + 0x5ac#64) (by sep_focus) hm
  obtain ⟨c3, hm⟩ := segSignal_peel8 (sp + 0x5b4#64) (by sep_focus) hm
  obtain ⟨c4, hm⟩ := segSignal_peel4 (sp + 0x5bc#64) (by sep_focus) hm
  obtain ⟨e0, hm⟩ := segSignal_peel8 (sp + 0x870#64) (by sep_focus) hm
  obtain ⟨e1, hm⟩ := segSignal_peel8 (sp + 0x878#64) (by sep_focus) hm
  obtain ⟨e2, hm⟩ := segSignal_peel8 (sp + 0x880#64) (by sep_focus) hm
  obtain ⟨e3, hm⟩ := segSignal_peel8 (sp + 0x888#64) (by sep_focus) hm
  obtain ⟨e4, hm⟩ := segSignal_peel4 (sp + 0x890#64) (by sep_focus) hm
  have hm4 := segSignal_focusR' (T := ((sp + 0x38#64) ↦₆₄ u38) ∗ ((sp + 0x40#64) ↦₆₄ u40) ∗
      ((sp + 0x48#64) ↦₆₄ u48) ∗ ((sp + 0xb0#64) ↦₆₄ x.ptA) ∗
      ((sp + 0xb8#64) ↦₆₄ BitVec.ofNat 64 x.ptext.length) ∗ ((sp + 0xc0#64) ↦₆₄ x.remA) ∗
      ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
      ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
      ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
      ((sp + 0x5bc#64) ↦₃₂ c4) ∗ ((sp + 0x870#64) ↦₆₄ e0) ∗ ((sp + 0x878#64) ↦₆₄ e1) ∗
      ((sp + 0x880#64) ↦₆₄ e2) ∗ ((sp + 0x888#64) ↦₆₄ e3) ∗ ((sp + 0x890#64) ↦₃₂ e4))
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0) (by sep_focus) (by sep_focus) hm
  refine SegExitBudget.of_sepWP hm4 (segSignal_placed_step_enc hs_pc hrun hsp hal hx23 hx25 hx27) ?_
  intro s3 Pm3 _hL hsteps hs3_pc hs3_run hm5
    ⟨hvm03, hs3_sp, hs3_tr, hx0, hx1, hx2, hx3, hx4, hx5, hs3_x19, hs3_x20, hs3_x25, hs3_x26, hs3_x28,
      hs3_x29, hs3_vregs, hlr, hPm3⟩
  have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl.of_keepsFrozen hsteps.keepsFrozen
  have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hal (hs3_sp.trans hsp.symm)
  let p32 := pointsTo32_entails_memRegion; let p64 := pointsTo64_entails_memRegion; let er := Entails.refl
  have hPost := Entails.trans hPm3 (sepConj_mono (er _) (sepConj_mono (er _) (sepConj_mono (p64 _ _)
    (sepConj_mono (er _) (sepConj_mono (er _) (sepConj_mono (er _) (sepConj_mono (p32 _ _)
    (sepConj_mono (p32 _ _) (sepConj_mono (p64 _ _) (sepConj_mono (p64 _ _) (sepConj_mono (p32 _ _)
    (sepConj_mono (p64 _ _) (sepConj_mono (p64 _ _) (sepConj_mono (p64 _ _) (sepConj_mono (p64 _ _)
    (sepConj_mono (p32 _ _) (sepConj_mono (p64 _ _) (sepConj_mono (p64 _ _) (sepConj_mono (p64 _ _)
    (sepConj_mono (p64 _ _) (p32 _ _)))))))))))))))))))))
  have hm7 := Satisfies.mono (sepConj_mono_left hPost) hm5
  rw [(A.atState_eq_of_vmPreserved lim st hvm03).symm] at hm7
  refine SegExitBudget.next ?_; unfold SegSignalEncStateVPlaced
  refine ⟨hbud, hcur, hsc, hfrom, hrem, hnone, hs3_pc, hlr, ⟨hs3_run, hs3_sp, hal0, hs3_al,
      hs3_x29.trans hx29, hs3_x19.trans hx19, hcrl3, hs3_vregs.trans hvregs⟩, hs3_tr.trans htr,
    hx0, hx1, hx2, hx3, hx4, hx5, hs3_x20.trans hx20, hs3_x25.trans hx25, hs3_x26.trans hx26,
    hs3_x28.trans hx28, hpt, hrest, hloc, hnow, hstk, ?_⟩
  rw [← hsp0]
  have h580g : memRegion (sp + 0x580#64) 120 =
      memRegion (sp + 0x580#64) 4 ∗ memRegion (sp + 0x584#64) 4 ∗ memRegion (sp + 0x588#64) 8 ∗
      memRegion (sp + 0x590#64) 8 ∗ memRegion (sp + 0x598#64) 4 ∗ memRegion (sp + 0x59c#64) 8 ∗
      memRegion (sp + 0x5a4#64) 8 ∗ memRegion (sp + 0x5ac#64) 8 ∗ memRegion (sp + 0x5b4#64) 8 ∗
      memRegion (sp + 0x5bc#64) 4 ∗ memRegion (sp + 0x5c0#64) 24 ∗ memRegion (sp + 0x5d8#64) 32 := by
    rw [show (120 : Nat) = 4 + (4 + (8 + (8 + (4 + (8 + (8 + (8 + (8 + (4 + (24 + 32)))))))))) from rfl,
      show sp + 0x580#64 = sp + BitVec.ofNat 64 0x580 from rfl,
      mr_cut_add sp 0x580 4 _ (by decide), mr_cut_add sp (0x580 + 4) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4) 8 _ (by decide), mr_cut_add sp (0x580 + 4 + 4 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8) 4 _ (by decide), mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8) 8 _ (by decide), mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8) 8 _ (by decide), mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8) 4 _ (by decide),
      mr_cut_add sp (0x580 + 4 + 4 + 8 + 8 + 4 + 8 + 8 + 8 + 8 + 4) 24 _ (by decide)]
  have h5f8g : memRegion (sp + 0x5f8#64) 0x588 =
      memRegion (sp + 0x5f8#64) 0x278 ∗ memRegion (sp + 0x870#64) 8 ∗ memRegion (sp + 0x878#64) 8 ∗
      memRegion (sp + 0x880#64) 8 ∗ memRegion (sp + 0x888#64) 8 ∗ memRegion (sp + 0x890#64) 4 ∗
      memRegion (sp + 0x894#64) 0x2ec := by
    rw [show (0x588 : Nat) = 0x278 + (8 + (8 + (8 + (8 + (4 + 0x2ec))))) from rfl,
      show sp + 0x5f8#64 = sp + BitVec.ofNat 64 0x5f8 from rfl,
      mr_cut_add sp 0x5f8 0x278 _ (by decide), mr_cut_add sp (0x5f8 + 0x278) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8) 8 _ (by decide), mr_cut_add sp (0x5f8 + 0x278 + 8 + 8) 8 _ (by decide),
      mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8) 8 _ (by decide), mr_cut_add sp (0x5f8 + 0x278 + 8 + 8 + 8 + 8) 4 _ (by decide)]
  rw [h580g, h5f8g]; unfold cmScratch encSpillsAtV
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm7

end SegSignal

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.WithStoresVT.Seg4PlacedBudget
