/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.SessionOnlyKitE
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSession
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4MarkKyberProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4SaveIdProof
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4StoreSessionProof
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Stage P4 Outcome Branches, `+0x3cc` Tail, and `none` OPK Arm

Defines the five-way outcome classification `StageP4RawBranch` / `StageP4Branch` (`ok`, `saveErr`,
`markErr`, `removeErr`, `storeErr`), the shared `+0x3cc → exit` `store_session` wrapper
`stageP4_at_3cc_kits`, and `stageP4_none_v1_kits_ok` (`opkId? = none`, skipping `remove_pre_key`).
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

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

/-! ## Five-way outcome classification -/

/-- Outcome branches of Stage P4 (`+0x34dc → s0.readReg64 .x30`) parameterized by an `opkSlot`
    assertion at `coroPtr + 0x298..0x2a0`. -/
inductive StageP4RawBranch {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp) (opkId? : Option (BitVec 32))
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop where
  | ok (c : IdentityChange)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      (hrem : match opkId? with
              | none => True
              | some opkId => pkKit.removeRel pst0 opkId (.ok ()))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()))
      (hpost : Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | saveErr
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot (savePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0)
  | markErr (c : IdentityChange) (e : kpkKit.MarkErr)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e))
      (hpost : Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
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
      (hpost : Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
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
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.ok ()) ++
        (match opkId? with | none => [] | some opkId => pkKit.removeEvs opkId (.ok ())) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()))
      (hpost : Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot (storePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))

abbrev StageP4Branch {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop :=
  StageP4RawBranch img kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr
    v_3d0 (coroOpkIdAtP4 coroPtr opkId?) opkId? kyberPreKeyId signedPreKeyId pt peer remoteIk
    baseKey sst0 ist0 pst0 kst0 ss sf Pf

theorem StageP4RawBranch.mono_opkSlot {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ikit : IdentityStoreSpec A img.base}
    {pkKit : PreKeyStoreSpec A img.base} {kpkKit : KyberPreKeyStoreSpec A img.base}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {s0 s : State}
    {coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64}
    {opkSlot1 opkSlot2 : SepProp} {opkId? : Option (BitVec 32)}
    {kyberPreKeyId signedPreKeyId : BitVec 32}
    {pt : List (BitVec 8)} {peer : AddrGhost} {remoteIk : IdentityKey} {baseKey : PublicKey}
    {sst0 : kit.StoreState} {ist0 : ikit.IdState}
    {pst0 : pkKit.PkState} {kst0 : kpkKit.KpkState}
    {ss : Session (List (BitVec 8))} {sf : State} {Pf : SepProp}
    (hopk : opkSlot1 ⊢ opkSlot2)
    (h : StageP4RawBranch img kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
      prevStatesPtr ptCap ptPtr v_3d0 opkSlot1 opkId? kyberPreKeyId signedPreKeyId pt peer
      remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf) :
    StageP4RawBranch img kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
      prevStatesPtr ptCap ptPtr v_3d0 opkSlot2 opkId? kyberPreKeyId signedPreKeyId pt peer
      remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf := by
  have hexit : ∀ outSlot sstf istf pstf kstf,
      stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkSlot1 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sstf istf pstf kstf ⊢
      stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkSlot2 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sstf istf pstf kstf :=
    fun _ _ _ _ _ => by
      unfold stageP4ExitAt
      exact sepConj_mono_right (sepConj_mono_left hopk)
  rcases h with ⟨c, hs, hm, hr, hst, htr, hp⟩ | ⟨hs, htr, hp⟩ | ⟨c, e, hs, hm, htr, hp⟩ |
    ⟨opkId, c, e, hopk_eq, hs, hm, hr, htr, hp⟩ | ⟨c, hs, hm, hr, hst, htr, hp⟩
  · exact .ok c hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .saveErr hs htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .markErr c e hs hm htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .removeErr opkId c e hopk_eq hs hm hr htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .storeErr c hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _))

/-! ## Frame-focusing helpers and shared `+0x3cc → exit` wrapper -/

/-- Focus a `SepWPp` precondition `P` into `T ∗ F`, letting `(by ...; sep_focus)` infer `F`. -/
theorem SepWPp.focus_pre {prog : Program} {ret : BitVec 64} {s : State}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hfoc : P = T ∗ F)
    (h : SepWPp prog ret s (T ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  hfoc ▸ h

/-- Drop a left factor `Drop` while simultaneously focusing the remaining assertion into `T ∗ F`. -/
theorem SepWPp.drop_focus_pre {prog : Program} {ret : BitVec 64} {s : State}
    {Drop P P' T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hp : P ⊢ P') (hfoc : P' = (Drop ∗ T) ∗ F)
    (h : SepWPp prog ret s (T ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.drop_pre_of_entails (by rw [← sepConj_assoc]; exact hfoc ▸ hp) h

/-- Swap a non-adjacent sub-factor `A = B` on `P'` via `sep_focus`, then focus `B ∗ R` into
    `(Drop ∗ T) ∗ F` and drop `Drop`. -/
theorem SepWPp.drop_swap_focus_pre {prog : Program} {ret : BitVec 64} {s : State}
    {A B R Drop P P' T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hp : P ⊢ P') (hab : A = B)
    (hfoc1 : P' = A ∗ R)
    (hfoc2 : B ∗ R = (Drop ∗ T) ∗ F)
    (h : SepWPp prog ret s (T ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.drop_focus_pre hp (by rw [hfoc1, hab, hfoc2]) h

/-- Spatial assertion on the full 4-kit Stage P4 frame at `+0x3cc` (entering Substage P4.4
    `SessionStore::store_session`). -/
def stageP4At3ccPre {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4Shared img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  opkSlot ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  sessionStateAt A (coroPtr + 0xf8#64) G ss.state ∗
  ((coroPtr + 0x280#64) ↦₆₄ ptCap) ∗
  ((coroPtr + 0x288#64) ↦₆₄ ptPtr) ∗
  ((coroPtr + 0x290#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist1 ∗
  kpkKit.storeAt kyberStorePtr kst1 ∗
  pkKit.storeAt preKeyStorePtr pst1 ∗
  kit.storeAt sessionStorePtr sst0

set_option maxHeartbeats 800000 in
/-- Shared `+0x3cc → s0.readReg64 .x30` Substage P4.4 (`store_session`) wrapper on the 4-kit
    `stageP4At3ccPre` frame, common to both `opkId? = none` and `opkId? = some opkId`. -/
theorem stageP4_at_3cc_kits_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hsVt : SessionOnlyVtablesOk img kit)
    {Qfs : Prop}
    (s0 s s3 : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs3 : FsAt kit.envOk Qfs (tripleRatchetProgAtExt img.base ext) s3)
    (hF3 : img.FrozenLoaded s3) (hsym3 : s3.symtab = img.symtab)
    (hpc3 : s3.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x3cc#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr3_pfx : s0.trace <+: s3.trace)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hOk : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s3 sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ())) ist1 pst1 kst1) →
      Q sf Pf)
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s3 sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkSlot (storePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ())) ist1 pst1 kst1) →
      Q sf Pf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
      (stageP4At3ccPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist1 pst1 kst1 G ss)
      Q (PanicOomProp s0) := by
  have hsp_ss : storeSessionCallStack kit ≤ 2 ^ 64 :=
    Nat.le_trans (storeSessionStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4StoreSessionPre img kit s0 s3 coroPtr outPtr remoteAddrPtr sessionStorePtr
      prevStatesPtr ptCap ptPtr b_2c0 pt peer sst0 G ss)
    (by
      unfold stageP4At3ccPre stageP4Shared stageP4StoreSessionPre stageP4StoreSessionShared
      rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_storeSession_dispatch_kits_p4 img ext Scope encRecord kit hA hDropSS3 hkit hsVt
    s0 s3 coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr prevStatesPtr ptCap ptPtr
    b_2c0 pt peer sst0 G ss _ _
    hb hprev_nz hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_ss
    hfs3 hF3 hsym3 hpc3 hrun3 hsp3_align htr3_pfx
    hx19_3 (hsp3.symm ▸ hx24_3) (hsp3.symm ▸ hx25_3) hx26_3 hx27_3
    (fun sf Pf hst4 hrel4 _ _ hspf htr4 hcsf hFf hsymf hPf => ?_)
    (fun sf Pf hst4 hrel4 _ _ hspf htr4 hcsf hFf hsymf hPf => ?_)
  · refine ⟨storeSessionVtablesAt img kit,
      stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ())) ist1 pst1 kst1,
      ?_, hOk sf _ hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hFf hsymf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionOkPost stageP4StoreSessionShared stageP4ExitAt stageP4Shared
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl
  · refine ⟨storeSessionVtablesAt img kit,
      stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkSlot (storePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ())) ist1 pst1 kst1,
      ?_, hErr sf _ hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hFf hsymf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionErrPost stageP4StoreSessionShared stageP4ExitAt stageP4Shared
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl

theorem stageP4_at_3cc_kits {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext)
    (hsVt : SessionOnlyVtablesOk img kit)
    {Qfs : Prop}
    (s0 s s3 : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
    (haddr_ss : kit.addrOk peer.val)
    (hpt_le : pt.length ≤ ptCap.toNat)
    (hcap_lt : ptCap.toNat < 2 ^ 63)
    (hptr_nz : ptPtr ≠ 0#64)
    (hsp_ub : stageP4CallStack kit ikit pkKit kpkKit ≤ 2 ^ 64)
    (hfs3 : FsAt kit.envOk Qfs (tripleRatchetProgAtExt img.base ext) s3)
    (hF3 : img.FrozenLoaded s3) (hsym3 : s3.symtab = img.symtab)
    (hpc3 : s3.pc =
      (tripleRatchetProgAtExt img.base ext).fnAddr decryptPrekeyClosureName + 0x3cc#64)
    (hrun3 : s3.status = .Running)
    (hsp3 : s3.sp = s.sp)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (htr3_pfx : s0.trace <+: s3.trace)
    (hx19_3 : s3.readReg64 .x19 = coroPtr)
    (hx24_3 : s3.readReg64 .x24 = s.sp + 0x370#64)
    (hx25_3 : s3.readReg64 .x25 = s.sp + 0x210#64)
    (hx26_3 : s3.readReg64 .x26 = outPtr)
    (hx27_3 : s3.readReg64 .x27 = ctxPtr)
    (hOk : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s3 sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ())) ist1 pst1 kst1) →
      Q sf Pf)
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s3 sf →
      kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        opkSlot (storePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ())) ist1 pst1 kst1) →
      Q sf Pf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
      (stageP4At3ccPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0 opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist1 pst1 kst1 G ss)
      Q (PanicOomProp s0) :=
  stageP4_at_3cc_kits_p4 img ext Scope encRecord kit ikit pkKit kpkKit (.of_allocContracts hA)
    hDropSS3 hkit hsVt s0 s s3 coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
    opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist1 pst1 kst1
    G ss Q hb hprev_nz hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_ub hfs3 hF3 hsym3
    hpc3 hrun3 hsp3 hsp_align htr3_pfx hx19_3 hx24_3 hx25_3 hx26_3 hx27_3 hOk hErr

/-! ## Stage P4 for `opkId? = none` -/

set_option maxHeartbeats 1200000 in
/-- Verifies Stage P4 (`+0x34dc → s0.readReg64 .x30`) when `opkId? = none`, sequencing
`save_identity`, `mark_kyber_pre_key_used` (`opkIdIsSome = 0#32`, skipping `remove_pre_key`), and
`store_session` together with their error-unwind exits. -/
theorem stageP4_none_v1_kits_ok_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
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
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        StageP4RawBranch img kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf)
      (PanicOomProp s0) := by
  have hsp_save : saveIdCallStack ikit ≤ 2 ^ 64 :=
    Nat.le_trans (saveIdStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp_mark : markKyberCallStack kpkKit ≤ 2 ^ 64 :=
    Nat.le_trans (markKyberStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4SaveIdPre img ikit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
      idStorePtr kyberStorePtr kpkKit.kpk_vt prevStatesPtr ptCap ptPtr v_3d0
      0#32 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G ss.state)
    (by
      unfold stageP4RawPre stageP4Shared stageP4SaveIdPre stageP4SaveIdShared
      rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_saveIdentity_dispatch_kits_p4 img ext ikit hA hDropSS3 hikit hiVt
    s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr idStorePtr
    kyberStorePtr kpkKit.kpk_vt (img.base + kpkKit.markShimOff) prevStatesPtr ptCap ptPtr v_3d0
    0#32 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk ist0 G ss.state _ _
    hb haddr_id (by decide) hpt_le hsp_save
    (fun hF' hP' => hkVt.markSlot hF' hP')
    (hfs.mono (fun _ h => h.2.1) id)
    hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28
    (fun c s1 P1 hst1 hrel1 hpc1 hrun1 hsp1 htr1 hx0_1 hx1_1 hx2_1 hx3_1
      hx19_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hlr1 hF1 hsym1 hP1 => ?_)
    (fun sf Pf hstf hrelf _ _ hspf htrf hcsf hFf hsymf hPf => ?_)
  · -- P4.1 Ok(c) → P4.2 mark_kyber_pre_key_used (none)
    refine SepWPp.drop_swap_focus_pre
      (Drop := saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kpkKit.markShimOff)))
      (T := stageP4MarkKyberPre img kpkKit s0 s1 coroPtr msgPtr outPtr kyberStorePtr
        prevStatesPtr ptCap ptPtr b_2c0 pt baseKey kst0 G ss.state ∗
        ((coroPtr + 0x2ac#64) ↦₃₂ 0#32))
      hP1
      ((stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub).symm.trans
        (stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub))
      (by unfold stageP4SaveIdOkPost stageP4SaveIdShared; sep_focus)
      (by unfold stageP4MarkKyberPre stageP4MarkKyberShared; rw [hsp1]; sep_focus)
      ?_
    rw [sepConj_assoc]
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1]; exact hsp_align
    have htr1_pfx : s0.trace <+: s1.trace :=
      htr1 ▸ htr_pfx.trans (List.prefix_append _ _)
    have hfs1 := hfs.of_steps hst1 htr1 (fun hQ => hQ.2.1.2 peer.val remoteIk (.ok c))
    refine stageP4_markKyber_none_dispatch_kits_p4 img ext kpkKit hA hDropSS3 hkpkKit hkVt
      s0 s1 coroPtr ctxPtr msgPtr outPtr kyberStorePtr prevStatesPtr ptCap ptPtr
      kyberPreKeyId signedPreKeyId b_2c0 pt baseKey kst0 G ss.state _ _
      hb hmark_ok hpt_le hsp_mark
      (hfs1.mono (fun _ h => h.2.2.2) id)
      hF1 hsym1 hpc1 hrun1 hsp1_align htr1_pfx
      hx0_1 hx1_1 hx2_1 hx3_1 hx19_1 (hsp1.symm ▸ hx24_1) (hsp1.symm ▸ hx25_1)
      hx26_1 hx27_1 hx28_1 hlr1
      (fun s2 P2 hst2 hrel2 hpc2 hrun2 hsp2_1 htr2 hx19_2 hx24_2 hx25_2 hx26_2 hx27_2 _
        hF2 hsym2 hP2 => ?_)
      (fun e sf Pf hst2 hrel2 _ _ hspf htr2 hcsf hFf hsymf hPf => ?_)
    · -- P4.2 Ok(()) → P4.4 store_session at +0x3cc
      have hsp2 : s2.sp = s.sp := hsp2_1.trans hsp1
      have htr2_pfx : s0.trace <+: s2.trace :=
        htr2 ▸ htr1_pfx.trans (List.prefix_append _ _)
      have hfs2 := hfs1.of_steps hst2 htr2
        (fun hQ => hQ.2.2.2.2 kyberPreKeyId signedPreKeyId baseKey (.ok ()))
      have hto3cc :
          P2 ⊢ markKyberVtablesAt kpkKit ∗
            stageP4At3ccPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
              remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
              ptCap ptPtr v_3d0
              (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
              kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
              sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
              (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss := by
        refine Entails.trans hP2
          (Entails.replace_factor
            (coro2ac_words_entails_memRegion20 coroPtr 0#32 opkIdDummy 1#32
              kyberPreKeyId signedPreKeyId)
            (by
              unfold stageP4MarkKyberOkPost stageP4MarkKyberShared
              rw [hsp1, coro298_split_eq coroPtr 0#32 opkIdDummy]
              sep_focus)
            (by
              unfold stageP4At3ccPre stageP4Shared
              rw [stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
              ac_rfl))
      refine SepWPp.drop_pre_of_entails hto3cc ?_
      refine stageP4_at_3cc_kits_p4 img ext Scope encRecord kit ikit pkKit kpkKit
        hA hDropSS3 hkit hsVt s0 s s2
        coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
        preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())) G ss _
        hb hprev_nz hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_ub
        (hfs2.mono (fun _ h => h.1) id)
        hF2 hsym2 hpc2 hrun2 hsp2 hsp_align htr2_pfx
        hx19_2 (hsp1 ▸ hx24_2) (hsp1 ▸ hx25_2) hx26_2 hx27_2
        (fun sf Pf hst4 hrel4 hspf htr4 hcsf hFf hsymf hPf =>
          ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
            hst1.trans (hst2.trans hst4), hspf, hcsf, hFf, hsymf,
            .ok c hrel1 hrel2 trivial hrel4
              (by simp only [List.append_nil]; rw [htr4, htr2, htr1])
              hPf⟩)
        (fun sf Pf hst4 hrel4 hspf htr4 hcsf hFf hsymf hPf =>
          ⟨emp, Pf, by rw [emp_sepConj]; exact Entails.refl _,
            hst1.trans (hst2.trans hst4), hspf, hcsf, hFf, hsymf,
            .storeErr c hrel1 hrel2 trivial hrel4
              (by simp only [List.append_nil]; rw [htr4, htr2, htr1])
              hPf⟩)
    · -- P4.2 Err(e)
      refine ⟨markKyberVtablesAt kpkKit,
        stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
          sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          (speErrAt kpkKit.markErr outPtr e)
          kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
          sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)) pst0
          (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.error e)),
        ?_, hst1.trans hst2, by rw [hspf, hsp1], hcsf, hFf, hsymf,
        .markErr c e hrel1 hrel2 (by rw [htr2, htr1, List.append_assoc]) (Entails.refl _)⟩
      refine Entails.trans hPf
        (Entails.replace_factor
          (coro2ac_words_entails_memRegion20 coroPtr 0#32 opkIdDummy 1#32
            kyberPreKeyId signedPreKeyId)
          (by
            unfold stageP4MarkKyberErrPost stageP4MarkKyberShared
            rw [hsp1, coro298_split_eq coroPtr 0#32 opkIdDummy]
            sep_focus)
          (by
            unfold stageP4ExitAt stageP4Shared
            rw [stack_stageP4_to_markKyber kit ikit pkKit kpkKit s.sp hsp_ub]
            ac_rfl))
  · -- P4.1 Err()
    refine ⟨saveIdVtablesAt ikit ∗
        ((kpkKit.kpk_vt + 0x28#64) ↦₆₄ᵣ (img.base + kpkKit.markShimOff)),
      stageP4ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        (savePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0,
      ?_, hstf, hspf, hcsf, hFf, hsymf,
      .saveErr hrelf htrf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4SaveIdErrPost stageP4SaveIdShared stageP4ExitAt stageP4Shared
    rw [stack_stageP4_to_saveId kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl

theorem stageP4_none_v1_kits_ok {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionOnlyKitOkSE kit Scope encRecord ext) (hsVt : SessionOnlyVtablesOk img kit)
    (hikit : IdentityStoreKitOkIE img ikit ext) (hiVt : IdentityVtablesOk img ikit)
    (hkpkKit : KyberPreKeyStoreKitOkImgE img kpkKit ext) (hkVt : KyberPreKeyVtablesOk img kpkKit)
    (s0 s : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkIdDummy kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hprev_nz : prevStatesPtr ≠ 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : kit.RecOk ⟨some ss⟩)
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
    (hx28 : s.readReg64 .x28 = 0xfffffffffffffffe#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
      (stageP4RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr
        ptCap ptPtr v_3d0
        (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
        kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey
        sst0 ist0 pst0 kst0 G ss.state)
      (fun sf Pf =>
        Steps (tripleRatchetProgAtExt img.base ext) s sf ∧
        sf.sp = s.sp + 0xcd0#64 ∧
        ClosureCalleeSavedP4 s0 sf ∧
        img.FrozenLoaded sf ∧
        sf.symtab = img.symtab ∧
        StageP4RawBranch img kit ikit pkKit kpkKit encRecord s0 s coroPtr msgPtr outPtr
          remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
          prevStatesPtr ptCap ptPtr v_3d0
          (((coroPtr + 0x298#64) ↦₃₂ 0#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkIdDummy))
          none kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sst0 ist0 pst0 kst0 ss sf Pf)
      (PanicOomProp s0) :=
  stageP4_none_v1_kits_ok_p4 img ext Scope encRecord kit ikit pkKit kpkKit (.of_allocContracts hA)
    hDropSS3 hkit hsVt hikit hiVt hkpkKit hkVt s0 s coroPtr ctxPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevStatesPtr ptCap ptPtr
    v_3d0 opkIdDummy kyberPreKeyId signedPreKeyId b_2c0 pt peer remoteIk baseKey sst0 ist0 pst0
    kst0 G ss hb hprev_nz hExtra hrec_ok haddr_ss haddr_id hmark_ok hpt_le hcap_lt hptr_nz hsp_ub
    hfs hF hsym hpc hrun hsp_align htr_pfx hx19 hx24 hx25 hx26 hx27 hx28

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
