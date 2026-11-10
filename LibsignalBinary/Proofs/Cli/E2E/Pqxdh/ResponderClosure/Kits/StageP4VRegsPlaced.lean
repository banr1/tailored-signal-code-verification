/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProofPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsKyberRefused
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsMarkKyberProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNone
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsRemovePreKeyProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsSaveIdProof

/-!
# Relocatable Stage P4 Composition with `calleeSavedVRegs`

Proves `stageP4_some_v1_vregs_kits_placed_ok` (`opkId? = some opkId`) and
`stageP4_v1_vregs_kits_placed_ok` (`opkId? : Option (BitVec 32)`) on Block `518` (`lsProg_518 ext`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
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
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

private theorem sepConj_assoc5_pl (a b c d e f : SepProp) :
    (a ∗ b ∗ c ∗ d ∗ e) ∗ f = a ∗ b ∗ c ∗ d ∗ e ∗ f := by
  simp only [sepConj_assoc]

/-! ## Placed Stage P4 for `opkId? = some opkId` -/

set_option maxHeartbeats 1200000 in
theorem stageP4_some_v1_vregs_mark_remove_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64) (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope encRecord ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI ikit ext) (hiVt : IdentityVtablesPlacedOk ikit)
    (hpkKit : PreKeyRemoveKitPlacedOk pkKit ext) (hpVt : PreKeyVtablesPlacedOk pkKit)
    (hkpkKit : KyberPreKeyMarkKitPlacedOk kpkKit ext) (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4RawPrePlaced kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4RawBranchPlaced kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (some opkId) kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
          sst0 ist0 pst0 kst0 ss sf Pf)
      (PanicOomProp s0) := by
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_mark : markKyberCallStack kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans (markKyberStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_rem : removePreKeyCallStack pkKit ≤ 2 ^ 64 :=
    Nat.le_trans (removePreKeyStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4SaveIdPrePlaced ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
      idStorePtr kyberStorePtr kpkKit.kpk_vt prevStatesPtr ptCap ptPtr v_3d0
      1#32 opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G ss.state)
    (by
      unfold stageP4RawPrePlaced stageP4SharedPlaced stageP4SaveIdPrePlaced stageP4SaveIdSharedPlaced
      rw [lsLogOff_eq_pointsTo64, stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_saveIdentity_dispatch_vregs_kits_placed ext ikit hdealloc hDropSS3 hikit hiVt
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kpkKit.kpk_vt (0#64 + kpkKit.markShimOff) prevStatesPtr ptCap ptPtr v_3d0
    1#32 opkId kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G ss.state _ _
    haddr_id (by decide) hpt_le hsp_save
    (fun hro' hP' => hkVt.markSlot hro' hP')
    (hfs.mono (fun _ h => h.2.1) id)
    hcro hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c s1 P1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx3_1
      hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hlr1 hcro1 hvregs1 hP1 => ?_)
    (fun sf Pf hstf hrelf _ _ hspf htrf hcsf hvregsf hcrof hPf => ?_)
  · -- P4.1 Ok(c) → P4.2 mark_kyber_pre_key_used (some opkId)
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff)))
      (T := stageP4MarkKyberPrePlaced kpkKit s0 s1 coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt baseKey kst0 G ss.state ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ pkKit.pk_vt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId))
      hP1
      ((stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
        (stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub))
      (by unfold stageP4SaveIdOkPostPlaced stageP4SaveIdSharedPlaced; sep_focus)
      (by unfold stageP4MarkKyberPrePlaced stageP4MarkKyberSharedPlaced; rw [hsp1]; sep_focus)
      ?_
    rw [sepConj_assoc5_pl]
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have htr1_pfx : s0.trace <+: s1.trace :=
      htr1 ▸ htr_pfx.trans (List.prefix_append _ _)
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.1.2 peer.val remoteIk (.ok c))
    refine stageP4_markKyber_some_dispatch_vregs_mark_placed ext kpkKit hdealloc hDropSS3 hkpkKit hkVt
      s0 s1 coroPtr ctxPtr msgPtr outPtr kyberStorePtr preKeyStorePtr pkKit.pk_vt
      (0#64 + pkKit.removeShimOff) prevStatesPtr ptCap ptPtr
      opkId kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G ss.state _ _
      hmark_ok hpt_le hsp_mark
      (fun hro' hP' => hpVt.removeSlot hro' hP')
      (hfs1.mono (fun _ h => h.2.2.2) id)
      hcro1 hpc1 hrun1 hsp1_align htr1_pfx
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1)
      hx26_1 hx27_1 hx28_1 hlr1 hvregs1
      (fun s2 P2 hst2 hrel2 hpc2 hrun2 hsp2_1 htr2 hx0_2 hx1_2 hx19_2 hx24_2 hx25_2
        hx26_2 hx27_2 _ hlr2 hcro2 hvregs2 hP2 => ?_)
      (fun e sf Pf hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hcrof hPf => ?_)
    · -- P4.2 Ok(()) → P4.3 remove_pre_key(opkId)
      have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have htr2_pfx : s0.trace <+: s2.trace :=
        htr2 ▸ htr1_pfx.trans (List.prefix_append _ _)
      have hfs2 := hfs1.of_steps hst2 htr2
        (fun hQ => hQ.2.2.2.2 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      refine SepWPp.drop_swap_focus_pre
        (Drop := markKyberVtablesAt kpkKit ∗
          ((pkKit.pk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + pkKit.removeShimOff)))
        (T := stageP4RemovePreKeyPrePlaced pkKit s0 s2 coroPtr outPtr preKeyStorePtr
          prevStatesPtr ptCap ptPtr b_2c0 pt pst0 G ss.state)
        hP2
        ((stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
          (stack_stageP4_to_removePreKey kit ikit pkKit kpkKit s.sp hsp_ub))
        (by unfold stageP4MarkKyberOkPostPlaced stageP4MarkKyberSharedPlaced; rw [hsp1]; sep_focus)
        (by unfold stageP4RemovePreKeyPrePlaced stageP4RemovePreKeySharedPlaced; rw [hsp2]; sep_focus)
        ?_
      refine stageP4_removePreKey_some_dispatch_vregs_remove_placed ext pkKit hdealloc hDropSS3 hpkKit hpVt
        s0 s2 coroPtr ctxPtr outPtr preKeyStorePtr prevStatesPtr ptCap ptPtr opkId
        b_2c0 pt pst0 G ss.state _ _
        hrem_ok hpt_le hsp_rem
        (hfs2.mono (fun _ h => h.2.2.1) id)
        hcro2 hpc2 hrun2 hsp2_align htr2_pfx
        hx0_2 hx1_2 hx19_2 (hsp2.symm ▸ hsp1 ▸ hx24_2) (hsp2.symm ▸ hsp1 ▸ hx25_2)
        hx26_2 hx27_2 hlr2 hvregs2
        (fun s3 P3 hst3 hrel3 hpc3 hrun3 hsp3_2 htr3 hx19_3 hx24_3 hx25_3 hx26_3 hx27_3 _
          hvregs3 hcro3 hP3 => ?_)
        (fun e sf Pf hst3 hrel3 _ _ hspf htr3 hcsf hvregsf hcrof hPf => ?_)
      · -- P4.3 Ok(()) → P4.4 store_session at +0x3cc
        have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
        have htr3_pfx : s0.trace <+: s3.trace :=
          htr3 ▸ htr2_pfx.trans (List.prefix_append _ _)
        have hfs3 := hfs2.of_steps hst3 htr3 (fun hQ => hQ.2.2.1.2 opkId (.ok ()))
        have hto3cc :
            P3 ⊢ removePreKeyVtablesAt pkKit ∗
              stageP4At3ccPrePlaced kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
                remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
                ptCap ptPtr v_3d0
                (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
                kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
                sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
                (pkKit.removeUpdate pst0 opkId (.ok ()))
                (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss := by
          refine Entails.trans hP3
            (Entails.replace_factor
              (coro2ac_words_entails_memRegion20 coroPtr 1#32 opkId 1#32
                kyberPreKeyId signedPreKeyId)
              (by
                unfold stageP4RemovePreKeyOkPostPlaced stageP4RemovePreKeySharedPlaced
                rw [hsp2, coro298_split_eq coroPtr 1#32 opkId]
                sep_focus)
              (by
                unfold stageP4At3ccPrePlaced stageP4SharedPlaced
                rw [lsLogOff_eq_pointsTo64, stack_stageP4_to_removePreKey kit ikit pkKit kpkKit s.sp hsp_ub]
                ac_rfl))
        refine SepWPp.drop_pre_of_entails hto3cc ?_
        refine stageP4_at_3cc_vregs_kits_placed ext Scope encRecord kit ikit pkKit kpkKit
          hdealloc hDropSS3 hkit hsVt s0 s s3
          coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
          preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
          (pkKit.removeUpdate pst0 opkId (.ok ()))
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss _
          hprev_nz hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_ub
          (hfs3.mono (fun _ h => h.1) id)
          hcro3 hpc3 hrun3 hsp3 hsp_align htr3_pfx
          hx19_3 (hsp2 ▸ hx24_3) (hsp2 ▸ hx25_3) hx26_3 hx27_3 hvregs3
          (fun sf Pf hst4 hrel4 hspf htr4 hcsf hvregsf hcrof hPf =>
            ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
              hst1.trans (hst2.trans (hst3.trans hst4)), hspf, hcsf, hvregsf, hcrof,
              .ok c hrel1 hrel2 hrel3 hrel4
                (by rw [htr4, htr3, htr2, htr1])
                hPf⟩)
          (fun sf Pf hst4 hrel4 hspf htr4 hcsf hvregsf hcrof hPf =>
            ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
              hst1.trans (hst2.trans (hst3.trans hst4)), hspf, hcsf, hvregsf, hcrof,
              .storeErr c hrel1 hrel2 hrel3 hrel4
                (by rw [htr4, htr3, htr2, htr1])
                hPf⟩)
      · -- P4.3 Err(e)
        refine ⟨removePreKeyVtablesAt pkKit,
          stageP4ExitAtPlaced kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
            sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
            (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
            (speErrAt pkKit.removeErr outPtr e)
            kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
            sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
            (pkKit.removeUpdate pst0 opkId (.error e))
            (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())),
          ?_, hst1.trans (hst2.trans hst3), by rw [hspf, hsp2], hcsf, hvregsf, hcrof,
          .removeErr opkId c e rfl hrel1 hrel2 hrel3
            (by rw [htr3, htr2, htr1]) (Entails.refl _)⟩
        refine Entails.trans hPf
          (Entails.replace_factor
            (coro2ac_words_entails_memRegion20 coroPtr 1#32 opkId 1#32
              kyberPreKeyId signedPreKeyId)
            (by
              unfold stageP4RemovePreKeyErrPostPlaced stageP4RemovePreKeySharedPlaced
              rw [hsp2, coro298_split_eq coroPtr 1#32 opkId]
              sep_focus)
            (by
              unfold stageP4ExitAtPlaced stageP4SharedPlaced
              rw [lsLogOff_eq_pointsTo64, stack_stageP4_to_removePreKey kit ikit pkKit kpkKit s.sp hsp_ub]
              ac_rfl))
    · -- P4.2 Err(e)
      refine ⟨markKyberVtablesAt kpkKit,
        stageP4ExitAtPlaced kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (speErrAt kpkKit.markErr outPtr e)
          kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hcrof,
        .markErr c e hrel1 hrel2 (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf
        (Entails.replace_factor
          (coro2ac_words_entails_memRegion20 coroPtr 1#32 opkId 1#32
            kyberPreKeyId signedPreKeyId)
          (by
            unfold stageP4MarkKyberErrPostPlaced stageP4MarkKyberSharedPlaced
            rw [hsp1, coro298_split_eq coroPtr 1#32 opkId]
            sep_focus)
          (by
            unfold stageP4ExitAtPlaced stageP4SharedPlaced
            rw [lsLogOff_eq_pointsTo64, stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
            ac_rfl))
  · -- P4.1 Err()
    refine ⟨saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (0#64 + kpkKit.markShimOff)),
      stageP4ExitAtPlaced kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        (savePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0,
      ?_, hstf, hspf, hcsf, hvregsf, hcrof,
      .saveErr hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4SaveIdErrPostPlaced stageP4SaveIdSharedPlaced stageP4ExitAtPlaced stageP4SharedPlaced
    rw [lsLogOff_eq_pointsTo64, stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl

/-! ## Unified `Option (BitVec 32)` placed Stage P4 theorem -/

theorem stageP4_v1_vregs_mark_remove_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64) (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope encRecord ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI ikit ext) (hiVt : IdentityVtablesPlacedOk ikit)
    (hpkKit : PreKeyRemoveKitPlacedOk pkKit ext) (hpVt : PreKeyVtablesPlacedOk pkKit)
    (hkpkKit : KyberPreKeyMarkKitPlacedOk kpkKit ext) (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : ∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4PrePlaced kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4BranchPlaced kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt peer remoteIk
          baseKey sst0 ist0 pst0 kst0 ss sf Pf)
      (PanicOomProp s0) := by
  cases opkId? with
  | none =>
    unfold stageP4PrePlaced stageP4RawPrePlaced coroOpkIdAtP4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun opkIdDummy => ?_
    refine SepWPp.mono_post_panic ?_ (fun _ _ h => h)
      (stageP4_none_v1_vregs_mark_placed_ok ext Scope encRecord kit ikit pkKit kpkKit
        hdealloc hDropSS3 hkit hsVt hikit hiVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevStatesPtr ptCap ptPtr v_3d0 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt
        peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
        hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hpt_le hcap_lt hptr_nz
        hsp_ub hfs hcro hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs)
    rintro sf Pf ⟨hst, hspf, hcsf, hvregsf, hcrof, hbr⟩
    exact ⟨hst, hspf, hcsf, hvregsf, hcrof,
      hbr.mono_opkSlot (by unfold coroOpkIdAtP4; exact Entails.sepExists_right opkIdDummy (Entails.refl _))⟩
  | some opkId =>
    exact stageP4_some_v1_vregs_mark_remove_placed_ok ext Scope encRecord kit ikit pkKit kpkKit
      hdealloc hDropSS3 hkit hsVt hikit hiVt hpkKit hpVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr
      outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
      kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId kyberPreKeyId signedPreKeyId
      b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
      hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok (hrem_ok opkId rfl)
      hpt_le hcap_lt hptr_nz hsp_ub hfs hcro hpc hrun hsp_align htr_pfx
      hx19 hx24 hx25 hx26 hx27 hx28 hvregs

theorem stageP4_some_v1_vregs_kits_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64) (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope encRecord ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI ikit ext) (hiVt : IdentityVtablesPlacedOk ikit)
    (hpkKit : PreKeyStoreKitPlacedOk pkKit ext) (hpVt : PreKeyVtablesPlacedOk pkKit)
    (hkpkKit : KyberPreKeyStoreKitPlacedOk kpkKit ext) (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4RawPrePlaced kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4RawBranchPlaced kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (some opkId) kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
          sst0 ist0 pst0 kst0 ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_some_v1_vregs_mark_remove_placed_ok ext Scope encRecord kit ikit pkKit kpkKit
    hdealloc hDropSS3 hkit hsVt hikit hiVt (preKeyRemoveKitPlacedOk_of_store hpkKit) hpVt (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt s0 s
    coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId kyberPreKeyId
    signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hpt_le hcap_lt hptr_nz
    hsp_ub hfs hcro hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

theorem stageP4_v1_vregs_kits_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64) (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkit : SessionOnlyKitPlacedOkSE kit Scope encRecord ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    (hikit : IdentityStoreKitPlacedOkI ikit ext) (hiVt : IdentityVtablesPlacedOk ikit)
    (hpkKit : PreKeyStoreKitPlacedOk pkKit ext) (hpVt : PreKeyVtablesPlacedOk pkKit)
    (hkpkKit : KyberPreKeyStoreKitPlacedOk kpkKit ext) (hkVt : KyberPreKeyVtablesPlacedOk kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : ∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (lsProg_518 ext) s)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x34dc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s
      (stageP4PrePlaced kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (lsProg_518 ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem ∧
        StageP4BranchPlaced kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt peer remoteIk
          baseKey sst0 ist0 pst0 kst0 ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_v1_vregs_mark_remove_placed_ok ext Scope encRecord kit ikit pkKit kpkKit
    hdealloc hDropSS3 hkit hsVt hikit hiVt (preKeyRemoveKitPlacedOk_of_store hpkKit) hpVt (kyberPreKeyMarkKitPlacedOk_of_store hkpkKit) hkVt s0 s
    coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
    preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 opkId? kyberPreKeyId
    signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
    hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hpt_le hcap_lt hptr_nz
    hsp_ub hfs hcro hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
