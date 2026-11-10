/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.CloseStepsBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1SaveIdPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1RemovePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1MarkPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1StorePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4VRegsNonePlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Placed Stage P4 Over-Path Outcome Classification and `+0x3cc` Wrapper

Defines the `[LibsignalPlacement]` five-way outcome classification `StageP4Prev1BranchPlaced` over a
1-element `previous_sessions` vector `prevVecAt [enc]` and proves the Substage P4.4 wrapper
`stageP4_at_3cc_prev1_vregs_kits_p4_placed` (`+0x3cc → s0.readReg64 .x30`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.OverP34
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.SignalSession

/-! ## Placed Five-Way Outcome Classification -/

/-- Placed five-way outcome classification of Stage P4 (`+0x34dc → s0.readReg64 .x30`) parameterized by `opkSlot`. -/
inductive StageP4Prev1RawBranchPlaced [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp) (opkId? : Option (BitVec 32))
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt enc : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop where
  | ok (c : IdentityChange)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : match opkId? with
              | none => True
              | some opkId => pkKit.removeRel pst0 opkId (.ok ()))
      (hstore : ops.storeRelPrev1 sst0 peer.val G ss enc (.ok ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        ops.storeEvsPrev1 peer.val G ss enc (.ok ()))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced b kit ikit pkKit kpkKit s0 s coroPtr msgPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        ptCap ptPtr v_3d0 opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | saveErr
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced b kit ikit pkKit kpkKit s0 s coroPtr msgPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        ptCap ptPtr v_3d0 opkSlot (savePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0)
  | markErr (c : IdentityChange) (e : kpkKit.MarkErr)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced b kit ikit pkKit kpkKit s0 s coroPtr msgPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        ptCap ptPtr v_3d0 opkSlot (speErrAt kpkKit.markErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)))
  | removeErr (opkId : BitVec 32) (c : IdentityChange) (e : pkKit.RemoveErr)
      (hopk : opkId? = some opkId)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : pkKit.removeRel pst0 opkId (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        pkKit.removeEvs opkId (.error e))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced b kit ikit pkKit kpkKit s0 s coroPtr msgPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        ptCap ptPtr v_3d0 opkSlot (speErrAt pkKit.removeErr outPtr e)
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (pkKit.removeUpdate pst0 opkId (.error e))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | storeErr (c : IdentityChange)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : match opkId? with
              | none => True
              | some opkId => pkKit.removeRel pst0 opkId (.ok ()))
      (hstore : ops.storeRelPrev1 sst0 peer.val G ss enc (.error ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        ops.storeEvsPrev1 peer.val G ss enc (.error ()))
      (hpost : Pf ⊢ stageP4Prev1ExitAtPlaced b kit ikit pkKit kpkKit s0 s coroPtr msgPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        ptCap ptPtr v_3d0 opkSlot (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))

/-- Placed five-way Stage P4 outcome classification over `coroOpkIdAtP4 coroPtr opkId?`. -/
abbrev StageP4Prev1BranchPlaced [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b) (kpkKit : KyberPreKeyStoreSpec A b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt enc : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop :=
  StageP4Prev1RawBranchPlaced kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    (coroOpkIdAtP4 coroPtr opkId?) opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
    baseKey sst0 ist0 pst0 kst0 G ss sf Pf

theorem StageP4Prev1RawBranchPlaced.mono_opkSlot [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    {kit : SessionStoreSpec A b} {ops : StorePrev1Ops kit}
    {ikit : IdentityStoreSpec A b}
    {pkKit : PreKeyStoreSpec A b} {kpkKit : KyberPreKeyStoreSpec A b}
    {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64}
    {opkSlot1 opkSlot2 : SepProp} {opkId? : Option (BitVec 32)}
    {kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt enc : List (BitVec 8)} {peer : AddrGhost} {remoteIk : IdentityKey} {baseKey : PublicKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {G : SessionGhost} {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (hopk : opkSlot1 ⊢ opkSlot2)
    (h : StageP4Prev1RawBranchPlaced kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
      ptCap ptPtr v_3d0 opkSlot1 opkId? kyberPreKeyId signedPreKeyId pt enc peer
      remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf) :
    StageP4Prev1RawBranchPlaced kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
      ptCap ptPtr v_3d0 opkSlot2 opkId? kyberPreKeyId signedPreKeyId pt enc peer
      remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf := by
  have hexit : ∀ outSlot sstf istf pstf kstf,
      stageP4Prev1ExitAtPlaced b kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot1 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sstf istf pstf kstf ⊢
      stageP4Prev1ExitAtPlaced b kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot2 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sstf istf pstf kstf :=
    fun _ _ _ _ _ => by
      unfold stageP4Prev1ExitAtPlaced
      exact sepConj_mono_right (sepConj_mono_left hopk)
  rcases h with ⟨c, hs, hm, hr, hst, htr, hp⟩ | ⟨hs, htr, hp⟩ | ⟨c, e, hs, hm, htr, hp⟩ |
    ⟨opkId, c, e, hopk_eq, hs, hm, hr, htr, hp⟩ | ⟨c, hs, hm, hr, hst, htr, hp⟩
  · exact .ok c hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .saveErr hs htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .markErr c e hs hm htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .removeErr opkId c e hopk_eq hs hm hr htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .storeErr c hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _))

/-! ## Placed Substage P4.4 Wrapper (`+0x3cc → s0.readReg64 .x30`) -/

set_option maxHeartbeats 800000 in
/-- Placed Substage P4.4 (`store_session`, `+0x3cc → s0.readReg64 .x30`) wrapper on the 4-kit
`stageP4At3ccPrev1PrePlaced` frame. -/
theorem stageP4_at_3cc_prev1_vregs_kits_p4_placed [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A 0#64) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A 0#64)
    (pkKit : PreKeyStoreSpec A 0#64) (kpkKit : KyberPreKeyStoreSpec A 0#64)
    (hdealloc : subroutine_ok (lsProg_518 ext)
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc") (rustDeallocSpec A))
    (hDropSS3 : subroutine_ok (lsProg_518 ext)
      (lsmpl.base 512) (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (hkit : SessionPrev1KitPlacedOkSE kit ops ext)
    (hsVt : SessionOnlyVtablesPlacedOk kit)
    {Qfs : Prop} (s0 s s3 : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
    (haddr_ss : kit.addrOk peer.val)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs3 : FsAt kit.envOk Qfs (lsProg_518 ext) s3)
    (hcro3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem)
    (hpc3 : s3.pc = (blkPl_518).base + 0x3cc#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr3_pfx : s0.trace <+: s3.trace)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hOk : ∀ (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s3 sf →
      ops.storeRelPrev1 sst0 peer.val G ss enc (.ok ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ ops.storeEvsPrev1 peer.val G ss enc (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4Prev1ExitAtPlaced 0#64 kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ())) ist1 pst1 kst1) →
      Q sf Pf)
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (lsProg_518 ext) s3 sf →
      ops.storeRelPrev1 sst0 peer.val G ss enc (.error ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ ops.storeEvsPrev1 peer.val G ss enc (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem →
      (Pf ⊢ stageP4Prev1ExitAtPlaced 0#64 kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ())) ist1 pst1 kst1) →
      Q sf Pf) :
    SepWPp (lsProg_518 ext) (s0.readReg64 .x30) s3
      (stageP4At3ccPrev1PrePlaced 0#64 kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
        remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        prevCap prevPtr ptCap ptPtr v_3d0 opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt enc peer
        remoteIk baseKey sst0 ist1 pst1 kst1 G ss)
      Q (PanicOomProp s0) := by
  have hsp_ss : storeSessionCallStack kit ≤ 2 ^ 64 :=
    Nat.le_trans (storeSessionStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4StoreSessionPrev1PrePlaced kit s0 s3 coroPtr outPtr remoteAddrPtr sessionStorePtr
      prevCap prevPtr ptCap ptPtr b_2c0 pt enc peer sst0 G ss)
    (by
      unfold stageP4At3ccPrev1PrePlaced stageP4Prev1SharedPlaced
        stageP4StoreSessionPrev1PrePlaced stageP4StoreSessionPrev1SharedPlaced
      rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_storeSession_prev1_vregs_kits_p4_placed ext kit ops hdealloc hDropSS3 hkit hsVt
    s0 s3 coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr prevCap prevPtr ptCap ptPtr
    b_2c0 pt enc peer sst0 G ss _ _
    hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_ss
    hfs3 hcro3 hpc3 hrun3 hsp3_align htr3_pfx
    hx19_3 (hsp3.symm ▸ hx24_3) (hsp3.symm ▸ hx25_3) hx26_3 hx27_3 hvregs3
    (fun sf Pf hst4 hrel4 _ _ hspf htr4 hcsf hvregsf hcrof hPf => ?_)
    (fun sf Pf hst4 hrel4 _ _ hspf htr4 hcsf hvregsf hcrof hPf => ?_)
  · refine ⟨storeSessionVtablesPlacedAt kit,
      stageP4Prev1ExitAtPlaced 0#64 kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ())) ist1 pst1 kst1,
      ?_, hOk sf _ hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hvregsf hcrof (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionPrev1OkPostPlaced stageP4StoreSessionPrev1SharedPlaced
      stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl
  · refine ⟨storeSessionVtablesPlacedAt kit,
      stageP4Prev1ExitAtPlaced 0#64 kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (storePollPlacedOutAt outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ())) ist1 pst1 kst1,
      ?_, hErr sf _ hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hvregsf hcrof (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionPrev1ErrPostPlaced stageP4StoreSessionPrev1SharedPlaced
      stageP4Prev1ExitAtPlaced stageP4Prev1SharedPlaced
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl

abbrev stageP4_at_3cc_prev1_vregs_kits_placed := @stageP4_at_3cc_prev1_vregs_kits_p4_placed

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
