/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4DefsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4SaveIdPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StorePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4None
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4SaveId
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Store

/-!
# Relocatable Matched-Session Stage P4 Composition (`+0x34dc → exit`)

Composes `stageP4_matched_saveIdentity_vregs_placed` (`Matched.M4SaveIdPlaced`) and
`stageP4_matched_storeSession_vregs_placed` (`Matched.M4StorePlaced`) to prove
`stageP4_matched_placed_ok : StageP4MatchedPlacedStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp stackAt_sub_eq
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession

/-- Relocatable `[LibsignalPlacement]` matched-session Stage P4
(`(blkPl_518).base + 0x34dc → s0.readReg64 .x30`, `opkIdIsSome = 2#32`). -/
def StageP4MatchedPlacedStmt [LibsignalPlacement] : Prop :=
  ∀ {A : RustAlloc} (ext : String → Option (State → State))
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64),
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A) →
    subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)) →
    SessionOnlyKitPlacedOkSE kit Scope encRecord (Rust.withPanics ext) →
    SessionOnlyVtablesPlacedOk kit →
    IdentityStoreKitPlacedOkI ikit (Rust.withPanics ext) →
    IdentityVtablesPlacedOk ikit →
    ∀ (s0 s : State)
      (coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
       kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
      (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
      (peer : AddrGhost) (remoteIk : IdentityKey)
      (sst0 : kit.StoreState) (ist0 : ikit.IdState)
      (g : RecordGhost) (G : SessionGhost) (ss : Session (List (BitVec 8))),
      SessionExtraRel G ss →
      kit.RecOk ⟨some ss⟩ →
      kit.addrOk peer.val →
      ikit.addrOk peer.val →
      pt.length ≤ ptCap.toNat →
      ptCap.toNat < 2 ^ 63 →
      ptPtr ≠ 0#64 →
      stageP4MatchedCallStack kit ikit ≤ 2 ^ 64 →
      FsAt (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
        (lsProg_518 (Rust.withPanics ext)) s →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = (blkPl_518).base + 0x34dc#64 →
      s.status = .Running →
      (s.sp &&& 15#64 == 0#64) = true →
      s0.trace <+: s.trace →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x24 = s.sp + 0x370#64 →
      s.readReg64 .x25 = s.sp + 0x210#64 →
      s.readReg64 .x26 = outPtr →
      s.readReg64 .x27 = ctxPtr →
      s.readReg64 .x28 = 0xfffffffffffffffe#64 →
      calleeSavedVRegs s = calleeSavedVRegs s0 →
      SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
        (stageP4MatchedPrePlaced kit ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk
          sst0 ist0 g G ss.state)
        (fun sf Pf =>
          Steps (lsProg_518 (Rust.withPanics ext)) s sf ∧
          sf.sp = s.sp + 0xcd0#64 ∧
          ClosureCalleeSavedP4 s0 sf ∧
          calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
          StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
          StageP4MatchedBranchPlaced kit ikit encRecord s0 s coroPtr msgPtr outPtr
            remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt
            ptCap ptPtr v_3d0 opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk
            sst0 ist0 ss sf Pf)
        (PanicOomProp s0)

set_option maxHeartbeats 1200000 in
/-- Verifies relocatable `[LibsignalPlacement]` matched-session Stage P4
(`(blkPl_518).base + 0x34dc → s0.readReg64 .x30`, `opkIdIsSome = 2#32`) over general
`prevSessionsEmptyAt A coroPtr g`. -/
theorem stageP4_matched_placed_ok [LibsignalPlacement] : StageP4MatchedPlacedStmt := by
  intro A ext Scope encRecord kit ikit hdealloc hDropSS3 hkit hsVt hikit hiVt
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ss
    hExtra hrec_ok haddr_ss haddr_id hpt_le hcap_lt hptr_nz hsp_ub hfs
    hcro hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_matched kit ikit) hsp_ub
  have hsp_store : storeSessionCallStack kit ≤ 2 ^ 64 :=
    Nat.le_trans (storeSessionStack_le_matched kit ikit) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4MatchedSaveIdPrePlaced ikit s0 s coroPtr outPtr remoteAddrPtr remoteIkPtr
      idStorePtr ptCap ptPtr v_3d0 b_2c0 pt peer remoteIk ist0 g G ss.state)
    (by
      unfold stageP4MatchedPrePlaced stageP4MatchedSharedPlaced
        stageP4MatchedSaveIdPrePlaced stageP4MatchedSaveIdSharedPlaced
      rw [stack_matched_to_saveId kit ikit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_matched_saveIdentity_vregs_placed ext ikit hdealloc hDropSS3 hikit hiVt
    s0 s coroPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr ptCap ptPtr v_3d0
    b_2c0 pt peer remoteIk ist0 g G ss.state _ _
    haddr_id hpt_le hsp_save
    (hfs.mono (fun _ h => h.2) id)
    hcro hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c s1 P1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 _
      hcro1 hvregs1 hP1 => ?_)
    (fun sf Pf hstf hrelf _ _ hspf htrf hcsf hvregsf hcrof hPf => ?_)
  · -- P4.1 Ok(c) → P4.4 store_session at +0x3cc
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit)
      (T := stageP4MatchedStorePrePlaced kit s0 s1 coroPtr outPtr remoteAddrPtr sessionStorePtr
        ptCap ptPtr b_2c0 pt peer sst0 g G ss)
      hP1
      ((stack_matched_to_saveId kit ikit s.sp hsp_ub).symm.trans
        (stack_matched_to_storeSession kit ikit s.sp hsp_ub))
      (by unfold stageP4MatchedSaveIdOkPostPlaced stageP4MatchedSaveIdSharedPlaced; sep_focus)
      (by unfold stageP4MatchedStorePrePlaced stageP4MatchedStoreSharedPlaced; rw [hsp1]; sep_focus)
      ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have htr1_pfx : s0.trace <+: s1.trace :=
      htr1 ▸ htr_pfx.trans (List.prefix_append _ _)
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.2 peer.val remoteIk (.ok c))
    refine stageP4_matched_storeSession_vregs_placed ext Scope encRecord kit hdealloc hDropSS3
      hkit hsVt s0 s1 coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr ptCap ptPtr
      b_2c0 pt peer sst0 g G ss _ _
      hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_store
      (hfs1.mono (fun _ h => h.1) id)
      hcro1 hpc1 hrun1 hsp1_align htr1_pfx
      hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1) hx26_1 hx27_1 hvregs1
      (fun sf Pf hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hcrof hPf => ?_)
      (fun sf Pf hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hcrof hPf => ?_)
    · -- P4.4 Ok(())
      refine ⟨storeSessionVtablesPlacedAt kit,
        stageP4MatchedExitAtPlaced kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId (vecResultAt A outPtr (.ok pt))
          pt peer remoteIk
          (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))
          (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hcrof,
        .ok c hrel1 hrel2 (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf (Entails.of_eq ?_)
      unfold stageP4MatchedStoreOkPostPlaced stageP4MatchedStoreSharedPlaced
        stageP4MatchedExitAtPlaced stageP4MatchedSharedPlaced
      rw [hsp1, stack_matched_to_storeSession kit ikit s.sp hsp_ub]
      ac_rfl
    · -- P4.4 Err(())
      refine ⟨storeSessionVtablesPlacedAt kit,
        stageP4MatchedExitAtPlaced kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId (storePollPlacedOutAt outPtr (.error ()))
          pt peer remoteIk
          (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))
          (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hcrof,
        .storeErr c hrel1 hrel2 (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf (Entails.of_eq ?_)
      unfold stageP4MatchedStoreErrPostPlaced stageP4MatchedStoreSharedPlaced
        stageP4MatchedExitAtPlaced stageP4MatchedSharedPlaced
      rw [hsp1, stack_matched_to_storeSession kit ikit s.sp hsp_ub]
      ac_rfl
  · -- P4.1 Err(())
    refine ⟨saveIdVtablesAt ikit,
      stageP4MatchedExitAtPlaced kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (savePollPlacedOutAt outPtr (.error ()))
        pt peer remoteIk sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())),
      ?_, hstf, hspf, hcsf, hvregsf, hcrof,
      .saveErr hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4MatchedSaveIdErrPostPlaced stageP4MatchedSaveIdSharedPlaced
      stageP4MatchedExitAtPlaced stageP4MatchedSharedPlaced
    rw [stack_matched_to_saveId kit ikit s.sp hsp_ub]
    ac_rfl

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
