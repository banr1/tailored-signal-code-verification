/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP4Prev1Store
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4KyberRefused
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP4None
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly -- shake: keep

/-!
# Stage P4 Over-Path Spatial Bundles, Outcome Classification, and `+0x3cc` Wrapper

Defines the 4-kit Stage P4 spatial predicates and five-way outcome classification
(`StageP4Prev1Branch`) over a 1-element `previous_sessions` vector `prevVecAt [enc]`, and proves the
Substage P4.4 wrapper `stageP4_at_3cc_prev1_vregs_kits` (`+0x3cc → s0.readReg64 .x30`).
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
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

/-! ## 4-Kit Spatial Predicates and Five-Way Outcome Classification -/

/-- Shared spatial resources preserved across Stage P4 (`+0x34dc → s0.readReg64 .x30`). -/
def stageP4Prev1Shared {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey) : SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ kit.ss_vt) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0xa8#64) ↦₆₄ preKeyStorePtr) ∗
  ((coroPtr + 0xb0#64) ↦₆₄ pkKit.pk_vt) ∗
  ((coroPtr + 0xc8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xd0#64) ↦₆₄ kpkKit.kpk_vt) ∗
  ((coroPtr + 0x2a0#64) ↦₆₄ (kyberPreKeyId ++ 1#32)) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ signedPreKeyId) ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
  memRegion (s.sp + 0x250#64) 20 ∗
  ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
  ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x2b0#64) 36 ∗
  memRegion (s.sp + 0x2e0#64) 36 ∗
  memRegion (s.sp + 0x310#64) 36 ∗
  memRegion (s.sp + 0x340#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  logOff img ∗
  A.pool ∗
  stackAt s.sp (stageP4CallStack kit ikit pkKit kpkKit)

/-- Stage P4 entry assertion at `+0x34dc` parameterized by `opkSlot` over `prevVecAt [enc]`. -/
def stageP4Prev1RawPre {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4Prev1Shared img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
  sessionStateAt A (coroPtr + 0xf8#64) G st ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  opkSlot ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0 ∗
  kpkKit.storeAt kyberStorePtr kst0 ∗
  pkKit.storeAt preKeyStorePtr pst0 ∗
  kit.storeAt sessionStorePtr sst0

/-- Stage P4 entry assertion at `+0x34dc` over `opkId? : Option (BitVec 32)` and `prevVecAt [enc]`. -/
abbrev stageP4Prev1Pre {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4Prev1RawPre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0
    (coroOpkIdAtP4 coroPtr opkId?) kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
    sst0 ist0 pst0 kst0 G st

/-- Stage P4 spatial assertion at `+0x3cc` (`store_session`) over `prevVecAt [enc]`. -/
def stageP4At3ccPrev1Pre {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) : SepProp :=
  stageP4Prev1Shared img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  opkSlot ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  prevVecAt A (coroPtr + 0xe0#64) prevCap prevPtr [enc] ∗
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

/-- Exit spatial assertion common to all five Stage P4 outcomes, with `coroPtr + 0xe0..0x250`
collapsed to `memRegion (coroPtr + 0xe0#64) 368`. -/
def stageP4Prev1ExitAt {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot outSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (baseKey : PublicKey)
    (sstf : kit.StoreState) (istf : ikit.IdState)
    (pstf : pkKit.PkState) (kstf : kpkKit.KpkState) : SepProp :=
  stageP4Prev1Shared img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey ∗
  opkSlot ∗
  outSlot ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  memRegion (coroPtr + 0x2ac#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr istf ∗
  kpkKit.storeAt kyberStorePtr kstf ∗
  pkKit.storeAt preKeyStorePtr pstf ∗
  kit.storeAt sessionStorePtr sstf

/-- Five-way outcome classification of Stage P4 (`+0x34dc → s0.readReg64 .x30`) parameterized by `opkSlot`. -/
inductive StageP4Prev1RawBranch {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
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
      (hpost : Pf ⊢ stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        ptCap ptPtr v_3d0 opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))
  | saveErr
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        ptCap ptPtr v_3d0 opkSlot (savePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())) pst0 kst0)
  | markErr (c : IdentityChange) (e : kpkKit.MarkErr)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hmark : kpkKit.markRel kst0 kyberPreKeyId signedPreKeyId baseKey (.error e))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kpkKit.markEvs kyberPreKeyId signedPreKeyId baseKey (.error e))
      (hpost : Pf ⊢ stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
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
      (hpost : Pf ⊢ stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
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
      (hpost : Pf ⊢ stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
        ptCap ptPtr v_3d0 opkSlot (storePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c))
        (match opkId? with | none => pst0 | some opkId => pkKit.removeUpdate pst0 opkId (.ok ()))
        (kpkKit.markUpdate kst0 kyberPreKeyId signedPreKeyId baseKey (.ok ())))

/-- Five-way Stage P4 outcome classification over `coroOpkIdAtP4 coroPtr opkId?`. -/
abbrev StageP4Prev1Branch {A : RustAlloc} (img : Obj.Image)
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkId? : Option (BitVec 32)) (kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt enc : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (pst0 : pkKit.PkState) (kst0 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop :=
  StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
    remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
    (coroOpkIdAtP4 coroPtr opkId?) opkId? kyberPreKeyId signedPreKeyId pt enc peer remoteIk
    baseKey sst0 ist0 pst0 kst0 G ss sf Pf

theorem StageP4Prev1RawBranch.mono_opkSlot {A : RustAlloc} {img : Obj.Image}
    {kit : SessionStoreSpec A img.base} {ops : StorePrev1Ops kit}
    {ikit : IdentityStoreSpec A img.base}
    {pkKit : PreKeyStoreSpec A img.base} {kpkKit : KyberPreKeyStoreSpec A img.base}
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
    (h : StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
      ptCap ptPtr v_3d0 opkSlot1 opkId? kyberPreKeyId signedPreKeyId pt enc peer
      remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf) :
    StageP4Prev1RawBranch img kit ops ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr
      remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr
      ptCap ptPtr v_3d0 opkSlot2 opkId? kyberPreKeyId signedPreKeyId pt enc peer
      remoteIk baseKey sst0 ist0 pst0 kst0 G ss sf Pf := by
  have hexit : ∀ outSlot sstf istf pstf kstf,
      stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot1 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sstf istf pstf kstf ⊢
      stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot2 outSlot kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey sstf istf pstf kstf :=
    fun _ _ _ _ _ => by
      unfold stageP4Prev1ExitAt
      exact sepConj_mono_right (sepConj_mono_left hopk)
  rcases h with ⟨c, hs, hm, hr, hst, htr, hp⟩ | ⟨hs, htr, hp⟩ | ⟨c, e, hs, hm, htr, hp⟩ |
    ⟨opkId, c, e, hopk_eq, hs, hm, hr, htr, hp⟩ | ⟨c, hs, hm, hr, hst, htr, hp⟩
  · exact .ok c hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .saveErr hs htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .markErr c e hs hm htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .removeErr opkId c e hopk_eq hs hm hr htr (Entails.trans hp (hexit _ _ _ _ _))
  · exact .storeErr c hs hm hr hst htr (Entails.trans hp (hexit _ _ _ _ _))

/-! ## Substage P4.4 Wrapper (`+0x3cc → s0.readReg64 .x30`) -/

set_option maxHeartbeats 800000 in
/-- Substage P4.4 (`store_session`, `+0x3cc → s0.readReg64 .x30`) wrapper on the 4-kit
`stageP4At3ccPrev1Pre` frame under `StageP4Alloc` (`dealloc` only). -/
theorem stageP4_at_3cc_prev1_vregs_kits_p4 {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : StageP4Alloc img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext)
    (hsVt : SessionOnlyVtablesOk img kit)
    {Qfs : Prop}
    (s0 s s3 : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
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
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hOk : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s3 sf →
      ops.storeRelPrev1 sst0 peer.val G ss enc (.ok ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ ops.storeEvsPrev1 peer.val G ss enc (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ())) ist1 pst1 kst1) →
      Q sf Pf)
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s3 sf →
      ops.storeRelPrev1 sst0 peer.val G ss enc (.error ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ ops.storeEvsPrev1 peer.val G ss enc (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (storePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ())) ist1 pst1 kst1) →
      Q sf Pf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
      (stageP4At3ccPrev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist1 pst1 kst1 G ss)
      Q (PanicOomProp s0) := by
  have hsp_ss : storeSessionCallStack kit ≤ 2 ^ 64 :=
    Nat.le_trans (storeSessionStack_le_stageP4 kit ikit pkKit kpkKit) hsp_ub
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3]; exact hsp_align
  refine SepWPp.congr_post_drop_left ?_
  refine SepWPp.focus_pre
    (T := stageP4StoreSessionPrev1Pre img kit s0 s3 coroPtr outPtr remoteAddrPtr sessionStorePtr
      prevCap prevPtr ptCap ptPtr b_2c0 pt enc peer sst0 G ss)
    (by
      unfold stageP4At3ccPrev1Pre stageP4Prev1Shared
        stageP4StoreSessionPrev1Pre stageP4StoreSessionPrev1Shared
      rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
      sep_focus)
    ?_
  refine stageP4_storeSession_prev1_vregs_kits_p4 img ext kit ops hA hDropSS3 hkit hsVt
    s0 s3 coroPtr ctxPtr outPtr remoteAddrPtr sessionStorePtr prevCap prevPtr ptCap ptPtr
    b_2c0 pt enc peer sst0 G ss _ _
    hb hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_ss
    hfs3 hF3 hsym3 hpc3 hrun3 hsp3_align htr3_pfx
    hx19_3 (hsp3.symm ▸ hx24_3) (hsp3.symm ▸ hx25_3) hx26_3 hx27_3 hvregs3
    (fun sf Pf hst4 hrel4 _ _ hspf htr4 hcsf hvregsf hFf hsymf hPf => ?_)
    (fun sf Pf hst4 hrel4 _ _ hspf htr4 hcsf hvregsf hFf hsymf hPf => ?_)
  · refine ⟨storeSessionVtablesAt img kit,
      stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ())) ist1 pst1 kst1,
      ?_, hOk sf _ hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hvregsf hFf hsymf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionPrev1OkPost stageP4StoreSessionPrev1Shared
      stageP4Prev1ExitAt stageP4Prev1Shared
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl
  · refine ⟨storeSessionVtablesAt img kit,
      stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (storePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ())) ist1 pst1 kst1,
      ?_, hErr sf _ hst4 hrel4 (by rw [hspf, hsp3]) htr4 hcsf hvregsf hFf hsymf (Entails.refl _)⟩
    refine Entails.trans hPf (Entails.of_eq ?_)
    unfold stageP4StoreSessionPrev1ErrPost stageP4StoreSessionPrev1Shared
      stageP4Prev1ExitAt stageP4Prev1Shared
    rw [hsp3, stack_stageP4_to_storeSession kit ikit pkKit kpkKit s.sp hsp_ub]
    ac_rfl

theorem stageP4_at_3cc_prev1_vregs_kits {A : RustAlloc} (img : Obj.Image)
    (ext : String → Option (State → State))
    (kit : SessionStoreSpec A img.base) (ops : StorePrev1Ops kit)
    (ikit : IdentityStoreSpec A img.base)
    (pkKit : PreKeyStoreSpec A img.base) (kpkKit : KyberPreKeyStoreSpec A img.base)
    (hA : AllocContracts img.base A ext)
    (hDropSS3 : DropSessionStructure3OkExt img.base A ext)
    (hkit : SessionPrev1KitOkSE kit ops ext)
    (hsVt : SessionOnlyVtablesOk img kit)
    {Qfs : Prop}
    (s0 s s3 : State)
    (coroPtr ctxPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     preKeyStorePtr kyberStorePtr prevCap prevPtr ptCap ptPtr v_3d0 : BitVec 64)
    (opkSlot : SepProp)
    (kyberPreKeyId signedPreKeyId : BitVec 32)
    (b_2c0 : BitVec 8) (pt enc : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey) (baseKey : PublicKey)
    (sst0 : kit.StoreState) (ist1 : ikit.IdState)
    (pst1 : pkKit.PkState) (kst1 : kpkKit.KpkState)
    (G : SessionGhost) (ss : Session (List (BitVec 8)))
    (Q : State → SepProp → Prop)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (hExtra : SessionExtraRel G ss)
    (hrec_ok : ops.RecPrev1Ok G ss enc)
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
    (hvregs3 : calleeSavedVRegs s3 = calleeSavedVRegs s0)
    (hOk : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s3 sf →
      ops.storeRelPrev1 sst0 peer.val G ss enc (.ok ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ ops.storeEvsPrev1 peer.val G ss enc (.ok ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (vecResultAt A outPtr (.ok pt))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.ok ())) ist1 pst1 kst1) →
      Q sf Pf)
    (hErr : ∀ (sf : State) (Pf : SepProp),
      Steps (tripleRatchetProgAtExt img.base ext) s3 sf →
      ops.storeRelPrev1 sst0 peer.val G ss enc (.error ()) →
      sf.sp = s.sp + 0xcd0#64 →
      sf.trace = s3.trace ++ ops.storeEvsPrev1 peer.val G ss enc (.error ()) →
      ClosureCalleeSavedP4 s0 sf →
      calleeSavedVRegs sf = calleeSavedVRegs s0 →
      img.FrozenLoaded sf →
      sf.symtab = img.symtab →
      (Pf ⊢ stageP4Prev1ExitAt img kit ikit pkKit kpkKit s0 s coroPtr msgPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr ptCap ptPtr v_3d0
        opkSlot (storePollOutAt img.base outPtr (.error ()))
        kyberPreKeyId signedPreKeyId pt peer remoteIk baseKey
        (ops.storeUpdatePrev1 sst0 peer.val G ss enc (.error ())) ist1 pst1 kst1) →
      Q sf Pf) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s3
      (stageP4At3ccPrev1Pre img kit ikit pkKit kpkKit s0 s coroPtr msgPtr outPtr remoteAddrPtr
        remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap prevPtr
        ptCap ptPtr v_3d0 opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk baseKey
        sst0 ist1 pst1 kst1 G ss)
      Q (PanicOomProp s0) :=
  stageP4_at_3cc_prev1_vregs_kits_p4 img ext kit ops ikit pkKit kpkKit
    (StageP4Alloc.of_allocContracts hA) hDropSS3 hkit hsVt s0 s s3 coroPtr ctxPtr msgPtr outPtr
    remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr preKeyStorePtr kyberStorePtr prevCap
    prevPtr ptCap ptPtr v_3d0 opkSlot kyberPreKeyId signedPreKeyId b_2c0 pt enc peer remoteIk
    baseKey sst0 ist1 pst1 kst1 G ss Q hb hExtra hrec_ok haddr_ss hpt_le hcap_lt hptr_nz hsp_ub
    hfs3 hF3 hsym3 hpc3 hrun3 hsp3 hsp_align htr3_pfx hx19_3 hx24_3 hx25_3 hx26_3 hx27_3 hvregs3
    hOk hErr

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
