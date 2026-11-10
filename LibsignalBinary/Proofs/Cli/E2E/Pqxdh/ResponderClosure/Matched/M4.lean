/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Defs
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4None
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4SaveId
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Store
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Matched-Session Stage P4 Composition (`+0x34dc → exit`)

Composes `stageP4_matched_saveIdentity_vregs` (`Matched.M4SaveId`) and
`stageP4_matched_storeSession_vregs` (`Matched.M4Store`) to prove `stageP4_matched_ok :
StageP4MatchedExtStmt`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
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
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

set_option maxHeartbeats 1200000 in
/-- Dealloc-only (`StageP4Alloc img.base A ext`) matched-session Stage P4
(`+0x34dc → s0.readReg64 .x30`) for `opkIdIsSome = 2#32` (skipping `mark_kyber_pre_key_used` and
`remove_pre_key`) over general `prevSessionsEmptyAt A coroPtr g`. -/
theorem stageP4_matched_p4_ok : StageP4MatchedP4ExtStmt := by
  intro A img ext Scope encRecord kit ikit hA hDropSS3 hkit hsVt hikit hiVt _himg
    s0 s coroPtr msgPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk sst0 ist0 g G ss
    hb hExtra hrec_ok haddr_ss haddr_id hpt_le hcap_lt hptr_nz hsp_ub hfs
    hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_matched kit ikit) hsp_ub
  have hsp_store : storeSessionCallStack kit ≤ 2 ^ 64 :=
    Nat.le_trans (storeSessionStack_le_matched kit ikit) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4MatchedSaveIdPre img ikit s0 s coroPtr outPtr remoteAddrPtr remoteIkPtr
      idStorePtr ptCap ptPtr v_3d0 b_2c0 pt peer remoteIk ist0 g G ss.state)
    (by
      unfold stageP4MatchedPre stageP4MatchedShared stageP4MatchedSaveIdPre stageP4MatchedSaveIdShared
      rw [stack_matched_to_saveId kit ikit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_matched_saveIdentity_vregs_p4 img ext ikit hA hDropSS3 hikit hiVt
    s0 s coroPtr ctxPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr ptCap ptPtr v_3d0
    b_2c0 pt peer remoteIk ist0 g G ss.state _ _
    hb haddr_id hpt_le hsp_save
    (hfs.mono (fun _ h => h.2) id)
    hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c s1 P1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 _
      hF1 hsym1 hvregs1 hP1 => ?_)
    (fun sf Pf hstf hrelf _ _ hspf htrf hcsf hvregsf hFf hsymf hPf => ?_)
  · -- P4.1 Ok(c) → P4.4 store_session at +0x3cc
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit)
      (T := stageP4MatchedStorePre img kit s0 s1 coroPtr outPtr remoteAddrPtr sessionStorePtr
        ptCap ptPtr b_2c0 pt peer sst0 g G ss)
      hP1
      ((stack_matched_to_saveId kit ikit s.sp hsp_ub).symm.trans
        (stack_matched_to_storeSession kit ikit s.sp hsp_ub))
      (by unfold stageP4MatchedSaveIdOkPost stageP4MatchedSaveIdShared; sep_focus)
      (by unfold stageP4MatchedStorePre stageP4MatchedStoreShared; rw [hsp1]; sep_focus)
      ?_
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have htr1_pfx : s0.trace <+: s1.trace :=
      htr1 ▸ htr_pfx.trans (List.prefix_append _ _)
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.2 peer.val remoteIk (.ok c))
    refine stageP4_matched_storeSession_vregs_p4 img ext Scope encRecord kit hA hDropSS3 hkit hsVt
      s0 s1 coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr ptCap ptPtr
      b_2c0 pt peer sst0 g G ss _ _
      hb hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_store
      (hfs1.mono (fun _ h => h.1) id)
      hF1 hsym1 hpc1 hrun1 hsp1_align htr1_pfx
      hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1) hx26_1 hx27_1 hvregs1
      (fun sf Pf hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hFf hsymf hPf => ?_)
      (fun sf Pf hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hFf hsymf hPf => ?_)
    · -- P4.4 Ok(())
      refine ⟨storeSessionVtablesAt img kit,
        stageP4MatchedExitAt img kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId (vecResultAt A outPtr (.ok pt))
          pt peer remoteIk
          (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))
          (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hFf, hsymf,
        .ok c hrel1 hrel2 (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf (Entails.of_eq ?_)
      unfold stageP4MatchedStoreOkPost stageP4MatchedStoreShared stageP4MatchedExitAt stageP4MatchedShared
      rw [hsp1, stack_matched_to_storeSession kit ikit s.sp hsp_ub]
      ac_rfl
    · -- P4.4 Err(())
      refine ⟨storeSessionVtablesAt img kit,
        stageP4MatchedExitAt img kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
          opkHi kyberPreKeyId signedPreKeyId (storePollOutAt img.base outPtr (.error ()))
          pt peer remoteIk
          (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))
          (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hFf, hsymf,
        .storeErr c hrel1 hrel2 (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf (Entails.of_eq ?_)
      unfold stageP4MatchedStoreErrPost stageP4MatchedStoreShared stageP4MatchedExitAt stageP4MatchedShared
      rw [hsp1, stack_matched_to_storeSession kit ikit s.sp hsp_ub]
      ac_rfl
  · -- P4.1 Err(())
    refine ⟨saveIdVtablesAt ikit,
      stageP4MatchedExitAt img kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (savePollOutAt img.base outPtr (.error ()))
        pt peer remoteIk sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())),
      ?_, hstf, hspf, hcsf, hvregsf, hFf, hsymf,
      .saveErr hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4MatchedSaveIdErrPost stageP4MatchedSaveIdShared stageP4MatchedExitAt stageP4MatchedShared
    rw [stack_matched_to_saveId kit ikit s.sp hsp_ub]
    ac_rfl

theorem stageP4_matched_x_ok : StageP4MatchedXExtStmt :=
  fun {_A} img ext {_Scope} {_encRecord} kit ikit hAlloc =>
    stageP4_matched_p4_ok img ext kit ikit (.of_allocHooks img.base hAlloc)

abbrev stageP4_matched_of_allocHooks := @stageP4_matched_x_ok

/-- Matched-session Stage P4 (`+0x34dc → s0.readReg64 .x30`) under `AllocContracts`. -/
theorem stageP4_matched_ok : StageP4MatchedExtStmt :=
  fun {_A} img ext {_Scope} {_encRecord} kit ikit hA =>
    stageP4_matched_p4_ok img ext kit ikit (.of_allocContracts hA)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
