/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Defs
public import LibsignalBinary.Proofs.PublicApi.StoreKit.PreKeyStoreKitE
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Mark
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Remove
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1SaveId
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Stage P4 Over-Path Top-Level Specification (`previous_sessions = [enc]`)

Proves `stageP4_none_prev1_vregs_kits_ok`, `stageP4_some_prev1_vregs_kits_ok`, and the unified
`opkId? : Option (BitVec 32)` composition `stageP4_prev1_vregs_kits_ok` (`+0x34dc → s0.readReg64 .x30`)
when `coroPtr + 0xe0` holds a 1-element `previous_sessions` vector `prevVecAt [enc]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

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
open CryptoVerification.E2E.Pqxdh.ResponderClosure hiding
  PanicOomProp eq_of_sep_emp outPtr48_split_eq decryptPrekeySavedRegsAt_add_cd0
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

private theorem sepConj_assoc5_prev1 (a b c d e f : SepProp) :
    (a ∗ b ∗ c ∗ d ∗ e) ∗ f = a ∗ b ∗ c ∗ d ∗ e ∗ f := by
  simp only [sepConj_assoc]

set_option maxHeartbeats 1200000 in
/-- Stage P4 (`opkId? = none`, `+0x34dc → s0.readReg64 .x30`) over a 1-element `prevVecAt [enc]`
using `dealloc` only. -/
theorem stageP4_none_prev1_vregs_kits_dealloc_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hdealloc :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A))
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
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
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) := by
  let hA : StageP4Alloc img.base A ext := ⟨hdealloc⟩
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_mark : markKyberCallStack kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans (markKyberStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4SaveIdPrev1Pre img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
      idStorePtr kyberStorePtr kpkKit.kpk_vt prevCap prevPtr ptCap ptPtr v_3d0
      0#32 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk ist0 G ss.state)
    (by
      unfold stageP4Prev1RawPre stageP4Prev1Shared stageP4SaveIdPrev1Pre stageP4SaveIdPrev1Shared
      rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_saveIdentity_prev1_vregs_kits_p4 img ext ikit hA hDropSS3 hikit hiVt
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kpkKit.kpk_vt (img.base + kpkKit.markShimOff) prevCap prevPtr ptCap ptPtr v_3d0
    0#32 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk ist0 G ss.state _ _
    hb haddr_id (by decide) hpt_le hsp_save
    (fun hF' hP' => hkVt.markSlot hF' hP')
    (hfs.mono (fun _ h => h.2.1) id)
    hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c s1 P1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx3_1
      hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hlr1 hF1 hsym1 hvregs1 hP1 => ?_)
    (fun sf Pf hstf hrelf _ _ hspf htrf hcsf hvregsf hFf hsymf hPf => ?_)
  ·
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kpkKit.markShimOff)))
      (T := stageP4MarkKyberPrev1Pre img kpkKit s0 s1 coroPtr msgPtr outPtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr b_2c0 pt enc baseKey kst0 G ss.state ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32))
      hP1
      ((stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
        (stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub))
      (by unfold stageP4SaveIdPrev1OkPost stageP4SaveIdPrev1Shared; sep_focus)
      (by unfold stageP4MarkKyberPrev1Pre stageP4MarkKyberPrev1Shared; rw [hsp1]; sep_focus)
      ?_
    rw [sepConj_assoc]
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have htr1_pfx : s0.trace <+: s1.trace :=
      htr1 ▸ htr_pfx.trans (List.prefix_append _ _)
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.1.2 peer.val remoteIk (.ok c))
    refine stageP4_markKyber_none_prev1_vregs_kits_p4 img ext kpkKit hA hDropSS3 hkpkKit hkVt
      s0 s1 coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevCap prevPtr ptCap ptPtr
      kyberPreKeyId signedPreKeyId b_2c0 pt enc baseKey kst0 G ss.state _ _
      hb hmark_ok hpt_le hsp_mark
      (hfs1.mono (fun _ h => h.2.2.2) id)
      hF1 hsym1 hpc1 hrun1 hsp1_align htr1_pfx
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1)
      hx26_1 hx27_1 hx28_1 hlr1 hvregs1
      (fun s2 P2 hst2 hrel2 hpc2 hrun2 hsp2_1 htr2 hx19_2 hx24_2 hx25_2 hx26_2 hx27_2 _
        hF2 hsym2 hvregs2 hP2 => ?_)
      (fun e sf Pf hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hFf hsymf hPf => ?_)
    ·
      have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
      have htr2_pfx : s0.trace <+: s2.trace :=
        htr2 ▸ htr1_pfx.trans (List.prefix_append _ _)
      have hfs2 := hfs1.of_steps hst2 htr2
        (fun hQ => hQ.2.2.2.2 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      have hto3cc :
          P2 ⊢ markKyberVtablesAt kpkKit ∗
            stageP4At3ccPrev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
              remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
              ptCap ptPtr v_3d0
              (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
              kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
              sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
              (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss := by
        refine Entails.trans hP2
          (Entails.replace_factor
            (coro2ac_words_entails_memRegion20 coroPtr 0#32 opkIdDummy 1#32
              kyberPreKeyId signedPreKeyId)
            (by
              unfold stageP4MarkKyberPrev1OkPost stageP4MarkKyberPrev1Shared
              rw [hsp1, coro298_split_eq coroPtr 0#32 opkIdDummy]
              sep_focus)
            (by
              unfold stageP4At3ccPrev1Pre stageP4Prev1Shared
              rw [stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
              ac_rfl))
      refine SepWPp.drop_pre_of_entails hto3cc ?_
      refine stageP4_at_3cc_prev1_vregs_kits_p4 img ext kit ops ikit pkKit kpkKit
        hA hDropSS3 hkit hsVt s0 s s2
        coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss _
        hb hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_ub
        (hfs2.mono (fun _ h => h.1) id)
        hF2 hsym2 hpc2 hrun2 hsp2 hsp_align htr2_pfx
        hx19_2 (hsp1 ▸ hx24_2) (hsp1 ▸ hx25_2) hx26_2 hx27_2 hvregs2
        (fun sf Pf hst4 hrel4 hspf htr4 hcsf hvregsf hFf hsymf hPf =>
          ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
            hst1.trans (hst2.trans hst4), hspf, hcsf, hvregsf, hFf, hsymf,
            .ok c hrel1 hrel2 trivial hrel4
              (by simp only [List.append_nil]; rw [htr4, htr2, htr1])
              hPf⟩)
        (fun sf Pf hst4 hrel4 hspf htr4 hcsf hvregsf hFf hsymf hPf =>
          ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
            hst1.trans (hst2.trans hst4), hspf, hcsf, hvregsf, hFf, hsymf,
            .storeErr c hrel1 hrel2 trivial hrel4
              (by simp only [List.append_nil]; rw [htr4, htr2, htr1])
              hPf⟩)
    ·
      refine ⟨markKyberVtablesAt kpkKit,
        stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          (speErrAt kpkKit.markErr outPtr e)
          kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hFf, hsymf,
        .markErr c e hrel1 hrel2 (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf
        (Entails.replace_factor
          (coro2ac_words_entails_memRegion20 coroPtr 0#32 opkIdDummy 1#32
            kyberPreKeyId signedPreKeyId)
          (by
            unfold stageP4MarkKyberPrev1ErrPost stageP4MarkKyberPrev1Shared
            rw [hsp1, coro298_split_eq coroPtr 0#32 opkIdDummy]
            sep_focus)
          (by
            unfold stageP4Prev1ExitAt stageP4Prev1Shared
            rw [stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
            ac_rfl))
  ·
    refine ⟨saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kpkKit.markShimOff)),
      stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        (savePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0,
      ?_, hstf, hspf, hcsf, hvregsf, hFf, hsymf,
      .saveErr hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4SaveIdPrev1ErrPost stageP4SaveIdPrev1Shared
      stageP4Prev1ExitAt stageP4Prev1Shared
    rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl

theorem stageP4_none_prev1_vregs_kits_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext) (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64) (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc) (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val) (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat) (hcap_lt : ptCap.toNat < 2 ^ 63) (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_none_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit hA.dealloc hDropSS3
    hkit hsVt hikit hiVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0
    G ss hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hpt_le hcap_lt hptr_nz hsp_ub hfs hF hsym
    hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

theorem stageP4_none_prev1_vregs_kits_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContractsMem4K img.base A ext) (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64) (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc) (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val) (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat) (hcap_lt : ptCap.toNat < 2 ^ 63) (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_none_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit hA.dealloc hDropSS3
    hkit hsVt hikit hiVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0
    G ss hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hpt_le hcap_lt hptr_nz hsp_ub hfs hF hsym
    hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

theorem stageP4_none_prev1_vregs_kits_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContracts img.base A ext) (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64) (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc) (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val) (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hpt_le : pt.length ≤ ptCap.toNat) (hcap_lt : ptCap.toNat < 2 ^ 63) (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_none_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit hA.dealloc hDropSS3
    hkit hsVt hikit hiVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0
    G ss hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hpt_le hcap_lt hptr_nz hsp_ub hfs hF hsym
    hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

set_option maxHeartbeats 1200000 in
/-- Stage P4 (`opkId? = some opkId`, `+0x34dc → s0.readReg64 .x30`) over a 1-element
`prevVecAt [enc]` using `dealloc` only. -/
theorem stageP4_some_prev1_vregs_kits_dealloc_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hdealloc :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A))
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hpkKit : PreKeyStoreKitOkImgE img pkKit ext) (hpVt : PreKeyVtablesOk img pkKit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
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
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (some opkId) kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) := by
  let hA : StageP4Alloc img.base A ext := ⟨hdealloc⟩
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_mark : markKyberCallStack kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans (markKyberStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_rem : removePreKeyCallStack pkKit ≤ 2 ^ 64 :=
    Nat.le_trans (removePreKeyStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4SaveIdPrev1Pre img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
      idStorePtr kyberStorePtr kpkKit.kpk_vt prevCap prevPtr ptCap ptPtr v_3d0
      1#32 opkId kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk ist0 G ss.state)
    (by
      unfold stageP4Prev1RawPre stageP4Prev1Shared stageP4SaveIdPrev1Pre stageP4SaveIdPrev1Shared
      rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_saveIdentity_prev1_vregs_kits_p4 img ext ikit hA hDropSS3 hikit hiVt
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kpkKit.kpk_vt (img.base + kpkKit.markShimOff) prevCap prevPtr ptCap ptPtr v_3d0
    1#32 opkId kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk ist0 G ss.state _ _
    hb haddr_id (by decide) hpt_le hsp_save
    (fun hF' hP' => hkVt.markSlot hF' hP')
    (hfs.mono (fun _ h => h.2.1) id)
    hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs
    (fun c s1 P1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx3_1
      hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hlr1 hF1 hsym1 hvregs1 hP1 => ?_)
    (fun sf Pf hstf hrelf _ _ hspf htrf hcsf hvregsf hFf hsymf hPf => ?_)
  ·
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kpkKit.markShimOff)))
      (T := stageP4MarkKyberPrev1Pre img kpkKit s0 s1 coroPtr msgPtr outPtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr b_2c0 pt enc baseKey kst0 G ss.state ∗
        ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
        ((coroPtr + 0xb0#64) ↦₆₄ pkKit.pk_vt) ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 1#32) ∗
        ((coroPtr + 0x2b0#64) ↦₃₂ opkId))
      hP1
      ((stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
        (stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub))
      (by unfold stageP4SaveIdPrev1OkPost stageP4SaveIdPrev1Shared; sep_focus)
      (by unfold stageP4MarkKyberPrev1Pre stageP4MarkKyberPrev1Shared; rw [hsp1]; sep_focus)
      ?_
    rw [sepConj_assoc5_prev1]
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have htr1_pfx : s0.trace <+: s1.trace :=
      htr1 ▸ htr_pfx.trans (List.prefix_append _ _)
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.1.2 peer.val remoteIk (.ok c))
    refine stageP4_markKyber_some_prev1_vregs_kits_p4 img ext kpkKit hA hDropSS3 hkpkKit hkVt
      s0 s1 coroPtr ctxPtr msgPtr outPtr kyberStorePtr preKeyStorePtr pkKit.pk_vt
      (img.base + pkKit.removeShimOff) prevCap prevPtr ptCap ptPtr
      opkId kyberPreKeyId signedPreKeyId b_2c0 pt enc baseKey kst0 G ss.state _ _
      hb hmark_ok hpt_le hsp_mark
      (fun hF' hP' => hpVt.removeSlot hF' hP')
      (hfs1.mono (fun _ h => h.2.2.2) id)
      hF1 hsym1 hpc1 hrun1 hsp1_align htr1_pfx
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1)
      hx26_1 hx27_1 hx28_1 hlr1 hvregs1
      (fun s2 P2 hst2 hrel2 hpc2 hrun2 hsp2_1 htr2 hx0_2 hx1_2 hx19_2 hx24_2 hx25_2
        hx26_2 hx27_2 _ hlr2 hF2 hsym2 hvregs2 hP2 => ?_)
      (fun e sf Pf hst2 hrel2 _ _ hspf htr2 hcsf hvregsf hFf hsymf hPf => ?_)
    ·
      have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
      have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2]; exact hsp_align
      have htr2_pfx : s0.trace <+: s2.trace :=
        htr2 ▸ htr1_pfx.trans (List.prefix_append _ _)
      have hfs2 := hfs1.of_steps hst2 htr2
        (fun hQ => hQ.2.2.2.2 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      refine SepWPp.drop_swap_focus_pre
        (Drop := markKyberVtablesAt kpkKit ∗
          ((pkKit.pk_vt + 0x28#64) ↦₆₄ᵣ (img.base + pkKit.removeShimOff)))
        (T := stageP4RemovePreKeyPrev1Pre img pkKit s0 s2 coroPtr outPtr preKeyStorePtr
          prevCap prevPtr ptCap ptPtr b_2c0 pt enc pst0 G ss.state)
        hP2
        ((stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
          (stack_stageP4_to_removePreKey kit ikit pkKit kpkKit s.sp hsp_ub))
        (by unfold stageP4MarkKyberPrev1OkPost stageP4MarkKyberPrev1Shared; rw [hsp1]; sep_focus)
        (by unfold stageP4RemovePreKeyPrev1Pre stageP4RemovePreKeyPrev1Shared; rw [hsp2]; sep_focus)
        ?_
      refine stageP4_removePreKey_some_prev1_vregs_kits_p4 img ext pkKit hA hDropSS3 hpkKit hpVt
        s0 s2 coroPtr ctxPtr outPtr preKeyStorePtr prevCap prevPtr ptCap ptPtr opkId
        b_2c0 pt enc pst0 G ss.state _ _
        hb hrem_ok hpt_le hsp_rem
        (hfs2.mono (fun _ h => h.2.2.1) id)
        hF2 hsym2 hpc2 hrun2 hsp2_align htr2_pfx
        hx0_2 hx1_2 hx19_2 (hsp2.symm ▸ hsp1 ▸ hx24_2) (hsp2.symm ▸ hsp1 ▸ hx25_2)
        hx26_2 hx27_2 hlr2 hvregs2
        (fun s3 P3 hst3 hrel3 hpc3 hrun3 hsp3_2 htr3 hx19_3 hx24_3 hx25_3 hx26_3 hx27_3 _
          hvregs3 hF3 hsym3 hP3 => ?_)
        (fun e sf Pf hst3 hrel3 _ _ hspf htr3 hcsf hvregsf hFf hsymf hPf => ?_)
      ·
        have hsp3 : s3.sp = s.sp := hsp3_2.trans hsp2
        have htr3_pfx : s0.trace <+: s3.trace :=
          htr3 ▸ htr2_pfx.trans (List.prefix_append _ _)
        have hfs3 := hfs2.of_steps hst3 htr3 (fun hQ => hQ.2.2.1.2 opkId (.ok ()))
        have hto3cc :
            P3 ⊢ removePreKeyVtablesAt pkKit ∗
              stageP4At3ccPrev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
                remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
                prevCap prevPtr ptCap ptPtr v_3d0
                (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
                kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
                sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
                (pkKit.removeUpdate pst0 opkId (.ok ()))
                (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss := by
          refine Entails.trans hP3
            (Entails.replace_factor
              (coro2ac_words_entails_memRegion20 coroPtr 1#32 opkId 1#32
                kyberPreKeyId signedPreKeyId)
              (by
                unfold stageP4RemovePreKeyPrev1OkPost stageP4RemovePreKeyPrev1Shared
                rw [hsp2, coro298_split_eq coroPtr 1#32 opkId]
                sep_focus)
              (by
                unfold stageP4At3ccPrev1Pre stageP4Prev1Shared
                rw [stack_stageP4_to_removePreKey kit ikit pkKit kpkKit s.sp hsp_ub]
                ac_rfl))
        refine SepWPp.drop_pre_of_entails hto3cc ?_
        refine stageP4_at_3cc_prev1_vregs_kits_p4 img ext kit ops ikit pkKit kpkKit
          hA hDropSS3 hkit hsVt s0 s s3
          coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
          preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
          (pkKit.removeUpdate pst0 opkId (.ok ()))
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss _
          hb hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_ub
          (hfs3.mono (fun _ h => h.1) id)
          hF3 hsym3 hpc3 hrun3 hsp3 hsp_align htr3_pfx
          hx19_3 (hsp2 ▸ hx24_3) (hsp2 ▸ hx25_3) hx26_3 hx27_3 hvregs3
          (fun sf Pf hst4 hrel4 hspf htr4 hcsf hvregsf hFf hsymf hPf =>
            ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
              hst1.trans (hst2.trans (hst3.trans hst4)), hspf, hcsf, hvregsf, hFf, hsymf,
              .ok c hrel1 hrel2 hrel3 hrel4
                (by rw [htr4, htr3, htr2, htr1])
                hPf⟩)
          (fun sf Pf hst4 hrel4 hspf htr4 hcsf hvregsf hFf hsymf hPf =>
            ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
              hst1.trans (hst2.trans (hst3.trans hst4)), hspf, hcsf, hvregsf, hFf, hsymf,
              .storeErr c hrel1 hrel2 hrel3 hrel4
                (by rw [htr4, htr3, htr2, htr1])
                hPf⟩)
      ·
        refine ⟨removePreKeyVtablesAt pkKit,
          stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
            sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
            (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
            (speErrAt pkKit.removeErr outPtr e)
            kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
            sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
            (pkKit.removeUpdate pst0 opkId (.error e))
            (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())),
          ?_, hst1.trans (hst2.trans hst3), by rw [hspf, hsp2], hcsf, hvregsf, hFf, hsymf,
          .removeErr opkId c e rfl hrel1 hrel2 hrel3
            (by rw [htr3, htr2, htr1]) (Entails.refl _)⟩
        refine Entails.trans hPf
          (Entails.replace_factor
            (coro2ac_words_entails_memRegion20 coroPtr 1#32 opkId 1#32
              kyberPreKeyId signedPreKeyId)
            (by
              unfold stageP4RemovePreKeyPrev1ErrPost stageP4RemovePreKeyPrev1Shared
              rw [hsp2, coro298_split_eq coroPtr 1#32 opkId]
              sep_focus)
            (by
              unfold stageP4Prev1ExitAt stageP4Prev1Shared
              rw [stack_stageP4_to_removePreKey kit ikit pkKit kpkKit s.sp hsp_ub]
              ac_rfl))
    ·
      refine ⟨markKyberVtablesAt kpkKit,
        stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (speErrAt kpkKit.markErr outPtr e)
          kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hvregsf, hFf, hsymf,
        .markErr c e hrel1 hrel2 (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf
        (Entails.replace_factor
          (coro2ac_words_entails_memRegion20 coroPtr 1#32 opkId 1#32
            kyberPreKeyId signedPreKeyId)
          (by
            unfold stageP4MarkKyberPrev1ErrPost stageP4MarkKyberPrev1Shared
            rw [hsp1, coro298_split_eq coroPtr 1#32 opkId]
            sep_focus)
          (by
            unfold stageP4Prev1ExitAt stageP4Prev1Shared
            rw [stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
            ac_rfl))
  ·
    refine ⟨saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kpkKit.markShimOff)),
      stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        (savePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0,
      ?_, hstf, hspf, hcsf, hvregsf, hFf, hsymf,
      .saveErr hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4SaveIdPrev1ErrPost stageP4SaveIdPrev1Shared
      stageP4Prev1ExitAt stageP4Prev1Shared
    rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl

theorem stageP4_some_prev1_vregs_kits_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext) (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hpkKit : PreKeyStoreKitOkImgE img pkKit ext) (hpVt : PreKeyVtablesOk img pkKit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64) (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc) (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val) (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : pkKit.removeIdOk opkId) (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63) (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (some opkId) kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_some_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit hA.dealloc hDropSS3
    hkit hsVt hikit hiVt hpkKit hpVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr
    v_3d0 opkId kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0
    G ss hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hsp_ub hfs hF
    hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

theorem stageP4_some_prev1_vregs_kits_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContractsMem4K img.base A ext) (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hpkKit : PreKeyStoreKitOkImgE img pkKit ext) (hpVt : PreKeyVtablesOk img pkKit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64) (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc) (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val) (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : pkKit.removeIdOk opkId) (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63) (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (some opkId) kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_some_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit hA.dealloc hDropSS3
    hkit hsVt hikit hiVt hpkKit hpVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr
    v_3d0 opkId kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0
    G ss hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hsp_ub hfs hF
    hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

theorem stageP4_some_prev1_vregs_kits_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContracts img.base A ext) (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hpkKit : PreKeyStoreKitOkImgE img pkKit ext) (hpVt : PreKeyVtablesOk img pkKit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64) (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc) (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val) (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : pkKit.removeIdOk opkId) (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63) (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
        kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 (((coroPtr + 0x298#64) ↦₃₂ 1#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkId))
          (some opkId) kyberPreKeyId signedPreKeyId pt enc peer remoteIk baseKey
          sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_some_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit hA.dealloc hDropSS3
    hkit hsVt hikit hiVt hpkKit hpVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr
    v_3d0 opkId kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0
    G ss hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hsp_ub hfs hF
    hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

/-- Unified Stage P4 (`+0x34dc → s0.readReg64 .x30`) over `opkId? : Option (BitVec 32)` and a
1-element `prevVecAt [enc]`, delivering `StageP4Prev1Branch` using `dealloc` only. -/
theorem stageP4_prev1_vregs_kits_dealloc_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hdealloc :
      subroutine_ok (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr deallocName) (rustDeallocSpec A))
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hpkKit : PreKeyStoreKitOkImgE img pkKit ext) (hpVt : PreKeyVtablesOk img pkKit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val)
    (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : ∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
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
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        StageP4Prev1Branch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
          baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) := by
  cases opkId? with
  | none =>
    unfold stageP4Prev1Pre stageP4Prev1RawPre coroOpkIdAtP4
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun opkIdDummy => ?_
    refine SepWPp.mono_post_panic ?_ (fun _ _ h => h)
      (stageP4_none_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit
        hdealloc hDropSS3 hkit hsVt hikit hiVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt enc
        peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
        hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hpt_le hcap_lt hptr_nz
        hsp_ub hfs hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs)
    rintro sf Pf ⟨hst, hspf, hcsf, hvregsf, hFf, hsymf, hbr⟩
    exact ⟨hst, hspf, hcsf, hvregsf, hFf, hsymf,
      hbr.mono_opkSlot
        (by unfold coroOpkIdAtP4; exact Entails.sepExists_right opkIdDummy (Entails.refl _))⟩
  | some opkId =>
    exact stageP4_some_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit
      hdealloc hDropSS3 hkit hsVt hikit hiVt hpkKit hpVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr
      outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr
      kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 opkId kyberPreKeyId signedPreKeyId
      b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0 G ss
      hb hExtra hrec_ok haddr_ss haddr_id hmark_ok (hrem_ok opkId rfl)
      hpt_le hcap_lt hptr_nz hsp_ub hfs hF hsym hpc hrun hsp_align htr_pfx
      hx19 hx24 hx25 hx26 hx27 hx28 hvregs

theorem stageP4_prev1_vregs_kits_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext) (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hpkKit : PreKeyStoreKitOkImgE img pkKit ext) (hpVt : PreKeyVtablesOk img pkKit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64) (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc) (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val) (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : ∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat) (hcap_lt : ptCap.toNat < 2 ^ 63) (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        StageP4Prev1Branch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
          baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit hA.dealloc hDropSS3
    hkit hsVt hikit hiVt hpkKit hpVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr
    v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0
    G ss hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hsp_ub hfs hF
    hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

theorem stageP4_prev1_vregs_kits_4k_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContractsMem4K img.base A ext) (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hpkKit : PreKeyStoreKitOkImgE img pkKit ext) (hpVt : PreKeyVtablesOk img pkKit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64) (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc) (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val) (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : ∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat) (hcap_lt : ptCap.toNat < 2 ^ 63) (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        StageP4Prev1Branch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
          baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit hA.dealloc hDropSS3
    hkit hsVt hikit hiVt hpkKit hpVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr
    v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0
    G ss hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hsp_ub hfs hF
    hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

/-- Unified Stage P4 (`+0x34dc → s0.readReg64 .x30`) over `opkId? : Option (BitVec 32)` and a
1-element `prevVecAt [enc]`, delivering `StageP4Prev1Branch`. -/
theorem stageP4_prev1_vregs_kits_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContracts img.base A ext) (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hpkKit : PreKeyStoreKitOkImgE img pkKit ext) (hpVt : PreKeyVtablesOk img pkKit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState) (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64) (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc) (haddr_ss : kit.addrOk peer.val)
    (haddr_id : ikit.addrOk peer.val) (hmark_ok : kpkKit.markOk kyberPreKeyId signedPreKeyId baseKey)
    (hrem_ok : ∀ opkId, opkId? = some opkId → pkKit.removeIdOk opkId)
    (hpt_le : pt.length ≤ ptCap.toNat) (hcap_lt : ptCap.toNat < 2 ^ 63) (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs : FsAt (stageP4EnvOk kit ikit pkKit kpkKit) (stageP4Quiet kit ikit pkKit kpkKit)
      (tripleRatchetProgAtExt img.base ext) s)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x34dc#64)
    (hrun : s.status = .Running) (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr_pfx : s0.trace <+: s.trace) (hx19 : s.readReg64 .x19 = coroPtr)
    (hx24 : s.readReg64 .x24 = s.sp + 0x370#64) (hx25 : s.readReg64 .x25 = s.sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr) (hx27 : s.readReg64 .x27 = ctxPtr)
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4Prev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧ sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧ calleeSavedVRegs sf = calleeSavedVRegs s0 ∧
        img.FrozenLoaded sf ∧ sf.symtab = img.symtab ∧
        StageP4Prev1Branch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          ptCap ptPtr v_3d0 opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
          baseKey sst0 ist0 pst0 kst0 G ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_prev1_vregs_kits_dealloc_ok img ext kit ops ikit pkKit kpkKit hA.dealloc hDropSS3
    hkit hsVt hikit hiVt hpkKit hpVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr
    v_3d0 opkId? kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey sst0 ist0 pst0 kst0
    G ss hb hExtra hrec_ok haddr_ss haddr_id hmark_ok hrem_ok hpt_le hcap_lt hptr_nz hsp_ub hfs hF
    hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28 hvregs

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
