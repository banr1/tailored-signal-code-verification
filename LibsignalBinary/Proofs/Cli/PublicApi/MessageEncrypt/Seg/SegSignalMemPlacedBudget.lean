/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegFromPlacedBudget
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget
public meta import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget -- shake: keep
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalMem
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegSignalFrame
import LibsignalBinary.Proofs.Common.SharedHelpers
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Budget-Threaded Relocatable Step Lemmas and Panic Bridge for `segSignal`

Provides the four Block `464` (`lsProg_464 Hk`) basic-block stepping lemmas for `segSignal`
(`+0x344..+0x418`) and `segSignal_panic_bridge_placed` under `RustCliAllocBudget M` and
`[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalMemPlacedBudget

open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegSignal
open CryptoVerification.LibsignalPublicApi.MessageEncrypt hiding ApplyStateVPlaced CmStateVPlaced CurStateVPlaced EncCalleesPlaced EncEnvPlaced EncFsCtxPlaced EncSeamVPlaced EncSegsVPlaced KeyStateVPlaced OtrStateVPlaced PublicApiEncHooksPlaced SaveStateVPlaced SegApplyStoreSpecVPlaced SegExitPlaced SegFinishSpecVPlaced SegFromSpecVPlaced SegIdentitySpecVPlaced SegLoadSpecVPlaced SegPreKeySpecVPlaced SegSaveSpecVPlaced SegSignalSpecVPlaced SegTrustSpecVPlaced StoredStateVPlaced applyPCPlaced blkPl_198_ρ_otrEncryptName cmPCPlaced curPCPlaced encCommonPlaced encEntryPlaced encMidMetaPlaced encStoreExtraPlaced encSubStack_join_extra_placed encSubStack_split_extra_placed keyPCPlaced lsDurationSinceSym lsExpectFailedSym lsHandleAllocErrorSym lsStringCloneSym lsTimeAddSym otrEncryptPlacedSpec otrEncryptPlacedSpecQ otrEncryptPlacedSpecQF otrPCPlaced savePCPlaced storedPCPlaced withStoresEncPlacedSpecV withStoresEncPlacedSpecV_pre_addrOk withStoresEncStack_join_extra_placed withStoresEncStack_split_extra_placed
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced
open CryptoVerification.CliRatchet.Placed
open CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open ProofLib.ProgramReflection
open LibsignalBinary.Heap
open CryptoGames
open CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails hiding EncTailVPlaced tailCmDrop_placed_ok tailDropRecord_placed_ok tailFreePrevSessions_placed_ok tailFromSessionStateErr_placed_ok tailPreKeyEncryptErr_placed_ok tailSignalEncryptErr_placed_ok tailStoreHookErr_placed_ok tailWriteErr_placed_ok tailWriteResult_placed_ok
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails
open LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## 1. Relocatable Steppers on Block `464` (`lsProg_464 Hk`) -/

/-- `+0x344`: `bl` the pre-key items getter (`lsmpl.base 36`). -/
theorem segSignal_placed_step_bl [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp u : BitVec 64} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x344#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (_hal : s.spAligned = true) :
    SepWP (lsProg_464 Hk) (lsmpl.base 36) s ((sp + 0x280#64) ↦₆₄ u)
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = s.readReg64 .x0 ∧ sm.readReg64 .x8 = s.readReg64 .x8 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x23 = s.readReg64 .x23 ∧ sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧ sm.readReg64 .x27 = s.readReg64 .x27 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 Reg.lr = encEntryPlaced + 0x348#64 ∧
        (Pm ⊢ (sp + 0x280#64) ↦₆₄ u)) := by
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true]
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
/-- `+0x348..+0x3a0`: the getter returned `None` (tag 2); spill the key / OTR pointers, copy the
junk `sp+0x59c..0x5c0` to `sp+0x870..0x894`, `bl OTR::encrypt(sp+0x580, sp+0x288, ptA, len, 0,
remA)`. -/
theorem segSignal_placed_step_enc [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp : BitVec 64} {s : State}
    {u38 u40 u48 ptA len remA a1 a2 c0 c1 c2 c3 e0 e1 e2 e3 : BitVec 64}
    {a0 a3 c4 e4 : BitVec 32}
    (hs_pc : s.pc = encEntryPlaced + 0x348#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx23 : s.readReg64 .x23 = sp + 0x58#64) (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx27 : s.readReg64 .x27 = sp + 0xc0#64) :
    SepWP (lsProg_464 Hk) (libsignalSessionLib.fnAddr lsmpl CryptoVerification.Cli.LibsignalTripleRatchet.otrEncryptName) s
      (((sp + 0x38#64) ↦₆₄ u38) ∗ ((sp + 0x40#64) ↦₆₄ u40) ∗ ((sp + 0x48#64) ↦₆₄ u48) ∗
        ((sp + 0xb0#64) ↦₆₄ ptA) ∗ ((sp + 0xb8#64) ↦₆₄ len) ∗ ((sp + 0xc0#64) ↦₆₄ remA) ∗
        ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
        ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
        ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
        ((sp + 0x5bc#64) ↦₃₂ c4) ∗
        ((sp + 0x870#64) ↦₆₄ e0) ∗ ((sp + 0x878#64) ↦₆₄ e1) ∗ ((sp + 0x880#64) ↦₆₄ e2) ∗
        ((sp + 0x888#64) ↦₆₄ e3) ∗ ((sp + 0x890#64) ↦₃₂ e4))
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x580#64 ∧ sm.readReg64 .x1 = sp + 0x288#64 ∧
        sm.readReg64 .x2 = ptA ∧ sm.readReg64 .x3 = len ∧ sm.readReg64 .x4 = 0#64 ∧
        sm.readReg64 .x5 = remA ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        sm.readReg64 Reg.lr = encEntryPlaced + 0x3a4#64 ∧
        (Pm ⊢ ((sp + 0x38#64) ↦₆₄ (sp + 0x288#64)) ∗ ((sp + 0x40#64) ↦₆₄ (sp + 0x350#64)) ∗
          ((sp + 0x48#64) ↦₆₄ (sp + 0xc0#64)) ∗
          ((sp + 0xb0#64) ↦₆₄ ptA) ∗ ((sp + 0xb8#64) ↦₆₄ len) ∗ ((sp + 0xc0#64) ↦₆₄ remA) ∗
          ((sp + 0x580#64) ↦₃₂ 2#32) ∗ ((sp + 0x584#64) ↦₃₂ a0) ∗ ((sp + 0x588#64) ↦₆₄ a1) ∗
          ((sp + 0x590#64) ↦₆₄ a2) ∗ ((sp + 0x598#64) ↦₃₂ a3) ∗ ((sp + 0x59c#64) ↦₆₄ c0) ∗
          ((sp + 0x5a4#64) ↦₆₄ c1) ∗ ((sp + 0x5ac#64) ↦₆₄ c2) ∗ ((sp + 0x5b4#64) ↦₆₄ c3) ∗
          ((sp + 0x5bc#64) ↦₃₂ c4) ∗
          ((sp + 0x870#64) ↦₆₄ c0) ∗ ((sp + 0x878#64) ↦₆₄ c1) ∗ ((sp + 0x880#64) ↦₆₄ c2) ∗
          ((sp + 0x888#64) ↦₆₄ c3) ∗ ((sp + 0x890#64) ↦₃₂ c4))) := by
  rw [← blkPl_198_ρ_otrEncryptName]
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true]
  wp_steps_vm

set_option maxHeartbeats 1600000 in
/-- `+0x3a4..+0x3c8`: `OTR::encrypt` returned `Err` (word 0 = `errTag`): `w0..w2` to
`x27, x21, x23`, `w3..w5` to `sp+0xb00..0xb18`, `b.eq` to the T5 signal tail `+0xc14`. -/
theorem segSignal_placed_step_err [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp : BitVec 64} {s : State}
    {w0 w1 w2 w3 w4 w5 v0 v1 v2 : BitVec 64}
    (hs_pc : s.pc = encEntryPlaced + 0x3a4#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64) (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xc14#64) s
      (((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        words64At (sp + 0xb00#64) [v0, v1, v2])
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x21 = w1 ∧ sm.readReg64 .x23 = w2 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x27 = w0 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x580#64) ↦₆₄ errTag) ∗ words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
          words64At (sp + 0xb00#64) [w3, w4, w5])) := by
  unfold encEntryPlaced at hs_pc ⊢
  unfold errTag
  dsimp only [lsProg_464, ite_true]
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps_vm

set_option maxHeartbeats 3200000 in
/-- `+0x3a4..+0x418`: `OTR::encrypt` returned `Ok` (word 0 = the message's pq `Vec` capacity,
`≠ -1`): copy the 15 words `sp+0x580 → sp+0x378`, the tag `ctSignalTag` to `sp+0x370`, `b` to the
Cm seam `+0xa70`. -/
theorem segSignal_placed_step_ok [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp : BitVec 64} {s : State}
    {w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 v0 v1 v2 : BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 : BitVec 64}
    (hs_pc : s.pc = encEntryPlaced + 0x3a4#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (hal : s.spAligned = true)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64) (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx29 : s.readReg64 .x29 = sp + 0xb80#64) (hw0 : w0 + 1#64 ≠ 0#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0xa70#64) s
      (words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13,
          w14] ∗
        words64At (sp + 0xb00#64) [v0, v1, v2] ∗
        words64At (sp + 0x370#64) [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13,
          d14, d15])
      (fun sm Pm =>
        VmPreserved s sm ∧
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧ sm.readReg64 .x20 = s.readReg64 .x20 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧ sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧ sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ words64At (sp + 0x580#64) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12,
            w13, w14] ∗
          words64At (sp + 0xb00#64) [w4, w5, w6] ∗
          words64At (sp + 0x370#64) [0x8000000000000000#64, w0, w1, w2, w3, w4, w5, w6, w7, w8,
            w9, w10, w11, w12, w13, w14])) := by
  have hw0_beq : (w0 + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hw0
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true]
  simp only [words64At, sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps_vm

/-! ## 2. Relocatable Panic Bridge (`segSignal_panic_bridge_placed`) -/

/-- **Panic bridge** under `[LibsignalPlacement]`: `OTR::encrypt`'s panic (model panic or
`spqr::send` panic; `allocFailedIn` is eliminated under `FitsEnv`) establishes
`withStoresEncBudgetSpecV`'s `onPanic` (answers `okAnswers r .newOrUnchanged`). -/
theorem segSignal_panic_bridge_placed [LibsignalPlacement]
    {M : AllocCostModel}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {ctl : BitVec 64}
    {S : SpqrModel} {sendEnv : SpqrSendBudgetEnv}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A.repAlloc 0#64} {kitEnv : SessionStoreBudgetEnv kit} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A.repAlloc 0#64} {ikitEnv : IdentityStoreBudgetEnv ikit} {ist0 : ikit.IdState}
    {x : WithStoresEncGhost} {st_init st1 : M.σ} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {sp pqCap pqPtr : BitVec 64}
    {F X R0 : SepProp} {s0 s1 sf : State}
    (hcur : r.currentSession = some sess) (hsc : kit.ScopeAt Scope st0 x.rem.val r)
    (hnone : sess.pendingPreKey = none)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken))
    (hrem : taken.remoteIdentity = some k)
    (htr1 : s1.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)))
    (hpost : sf.mem ⊨ ((StoreKit.withLsRoCl lsmpl
        (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.otrEncryptBudgetSpecQ
          Q C A lim ctl uuidTryParse S sendEnv)).onPanic
      (segSignalEncGhost sp pqCap pqPtr otr x, st1) s1 sf ∗ F) ∗ (X ∗ R0)) :
    sf.mem ⊨
      (LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.withStoresEncBudgetSpecV
        A lim kit kitEnv st0 ikit ikitEnv ist0 Scope C ctl uuidTryParse S sendEnv encRecord).onPanic
        (x, st_init) s0 sf ∗ R0 := by
  unfold StoreKit.withLsRoCl
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.otrEncryptBudgetSpecQ
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.otrEncryptBudgetSpec
    at hpost
  dsimp only at hpost
  have h1 : sf.mem ⊨ ⌜(((segSignalEncGhost sp pqCap pqPtr otr x).model C S uuidTryParse).1 = .error .panic ∨
        S.sendPanics otr.pqrState x.rest) ∧ s1.trace <+: sf.trace⌝ ∗
      ((anyHeap ∗ F ∗ X) ∗ R0) :=
    Eq.mp (congrArg (sf.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj] at h1
  rcases h1 with ⟨⟨hpan_or, hpref1⟩, hmem⟩
  have hany : anyHeap ∗ F ∗ X ⊢ anyHeap := ProofLib.entails_anyHeap _
  have hmem' : sf.mem ⊨ anyHeap ∗ R0 := Satisfies.mono (sepConj_mono_left hany) hmem
  have hpref01 : s0.trace <+: s1.trace := by
    rw [htr1]
    exact List.prefix_append _ _
  have hpref0f : s0.trace <+: sf.trace := hpref01.trans hpref1
  unfold
    LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegTrustCommonPlacedBudget.TempTwins.withStoresEncBudgetSpecV
    StoreKit.withLsCodeRoLoaded
  dsimp only
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hpref0f, ?_⟩, hmem'⟩
  have hload : s0.trace ++ kit.loadEvs encRecord x.rem.val
      (okAnswers r IdentityChange.newOrUnchanged).loadSession <+: sf.trace := by
    have : s0.trace ++ kit.loadEvs encRecord x.rem.val
        (okAnswers r IdentityChange.newOrUnchanged).loadSession = s1.trace := by
      rw [htr1]
      rfl
    rw [this]
    exact hpref1
  rcases hpan_or with herr | hsp
  · refine ⟨okAnswers r .newOrUnchanged, hsc.2, hload, Or.inl ?_⟩
    rw [segSignalEncGhost_model] at herr
    rw [segSignal_model_err hcur hnone hfrom hrem (execOk_of_exec_error herr)]
    rfl
  · refine ⟨okAnswers r .newOrUnchanged, hsc.2, hload, Or.inr ?_⟩
    exact ⟨otr.pqrState, (segSignal_sendState (S := S) (x := x) hcur hnone hfrom hrem).1, hsp⟩

end LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.Seg.SegSignalMemPlacedBudget
