/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M4StoreStepsPlaced
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP4a
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.StageP1
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Bin.Hooks

/-!
# Relocatable Matched-Session Stage P4: Spatial Bundles and Outcome
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

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

/-- Shared spatial resources across `P4.1` (`save_identity`) and `P4.4` (`store_session`) on
matched-session Stage P4 (`opkIdIsSome = 2#32`) under `[LibsignalPlacement]`. -/
def stageP4MatchedSharedPlaced [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey) :
    SepProp :=
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x88#64) ↦₆₄ sessionStorePtr) ∗
  ((coroPtr + 0x90#64) ↦₆₄ kit.ss_vt) ∗
  ((coroPtr + 0x98#64) ↦₆₄ idStorePtr) ∗
  ((coroPtr + 0xa0#64) ↦₆₄ ikit.id_vt) ∗
  ((coroPtr + 0xb8#64) ↦₆₄ kyberStorePtr) ∗
  ((coroPtr + 0xc0#64) ↦₆₄ kyberStoreVt) ∗
  ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
  ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
  ((coroPtr + 0x2a0#64) ↦₃₂ kyberPreKeyId) ∗
  ((coroPtr + 0x2a4#64) ↦₃₂ signedPreKeyId) ∗
  memRegion (coroPtr + 0x2ac#64) 8 ∗
  memRegion (coroPtr + 0x2c8#64) 16 ∗
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
  ((s.sp + 0x90#64) ↦₆₄ remoteIkPtr) ∗
  ((s.sp + 0xa8#64) ↦₆₄ remoteAddrPtr) ∗
  memRegion (s.sp + 0x250#64) 20 ∗
  ((s.sp + 0x270#64) ↦₆₄ 0xfffffffffffffffe#64) ∗
  ((s.sp + 0x278#64) ↦₆₄ ptCap) ∗
  ((s.sp + 0x280#64) ↦₆₄ ptPtr) ∗
  ((s.sp + 0x288#64) ↦₆₄ BitVec.ofNat 64 pt.length) ∗
  memRegion (s.sp + 0x290#64) 16 ∗
  memRegion (s.sp + 0x2b0#64) 36 ∗
  memRegion (s.sp + 0x340#64) 36 ∗
  memRegion (s.sp + 0x370#64) 36 ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x3d0#64) ↦₆₄ v_3d0) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗
  memRegion (s.sp + 0x3e0#64) 48 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0 ∗
  protocolAddressAt A peer remoteAddrPtr ∗
  (remoteIkPtr ↦ₛ remoteIk.publicKey.bytes.toList) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool ∗
  stackAt s.sp (stageP4MatchedCallStack kit ikit)

/-- Spatial precondition at `+0x34dc` for matched-session Stage P4 under
`[LibsignalPlacement]`. -/
def stageP4MatchedPrePlaced [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32) (b_2c0 : BitVec 8) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (g : RecordGhost) (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  stageP4MatchedSharedPlaced kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateAt A (coroPtr + 0xf8#64) G st ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  (ptPtr ↦ₛ pt) ∗
  (if ptCap = 0#64 then emp
   else A.live ptPtr ptCap.toNat 1 ∗
     memRegion (ptPtr + BitVec.ofNat 64 pt.length) (ptCap.toNat - pt.length)) ∗
  memRegion outPtr 48 ∗
  ikit.identityAt idStorePtr ist0 ∗
  kit.storeAt sessionStorePtr sst0

/-- Spatial postcondition at `s0.readReg64 .x30` for matched-session Stage P4 under
`[LibsignalPlacement]`. -/
def stageP4MatchedExitAtPlaced [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (s0 s : State)
    (coroPtr msgPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (outSlot : SepProp) (pt : List (BitVec 8))
    (peer : AddrGhost) (remoteIk : IdentityKey)
    (sstf : kit.StoreState) (istf : ikit.IdState) : SepProp :=
  stageP4MatchedSharedPlaced kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
    sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
    opkHi kyberPreKeyId signedPreKeyId pt peer remoteIk ∗
  outSlot ∗
  memRegion (coroPtr + 0xe0#64) 368 ∗
  memRegion (coroPtr + 0x280#64) 24 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ikit.identityAt idStorePtr istf ∗
  kit.storeAt sessionStorePtr sstf

/-- Three-way outcome classification of matched-session Stage P4 under
`[LibsignalPlacement]`. -/
inductive StageP4MatchedBranchPlaced [LibsignalPlacement] {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (s0 s : State)
    (coroPtr msgPtr outPtr remoteAddrPtr remoteIkPtr sessionStorePtr idStorePtr
     kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0 : BitVec 64)
    (opkHi kyberPreKeyId signedPreKeyId : BitVec 32)
    (pt : List (BitVec 8)) (peer : AddrGhost) (remoteIk : IdentityKey)
    (sst0 : kit.StoreState) (ist0 : ikit.IdState)
    (ss : Session (List (BitVec 8))) (sf : State) (Pf : SepProp) : Prop where
  | ok (c : IdentityChange)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.ok ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.ok ()))
      (hpost : Pf ⊢ stageP4MatchedExitAtPlaced kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (vecResultAt A outPtr (.ok pt))
        pt peer remoteIk
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.ok ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)))
  | saveErr
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.error ()))
      (htr : sf.trace = s.trace ++ ikit.saveEvs peer.val remoteIk (.error ()))
      (hpost : Pf ⊢ stageP4MatchedExitAtPlaced kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (savePollPlacedOutAt outPtr (.error ()))
        pt peer remoteIk sst0 (ikit.saveUpdate ist0 peer.val remoteIk (.error ())))
  | storeErr (c : IdentityChange)
      (hsave : ikit.saveRel ist0 peer.val remoteIk (.ok c))
      (hstore : kit.storeRel sst0 peer.val ⟨some ss⟩ (.error ()))
      (htr : sf.trace = s.trace ++
        ikit.saveEvs peer.val remoteIk (.ok c) ++
        kit.storeEvs encRecord peer.val ⟨some ss⟩ (.error ()))
      (hpost : Pf ⊢ stageP4MatchedExitAtPlaced kit ikit s0 s coroPtr msgPtr remoteAddrPtr remoteIkPtr
        sessionStorePtr idStorePtr kyberStorePtr kyberStoreVt ptCap ptPtr v_3d0
        opkHi kyberPreKeyId signedPreKeyId (storePollPlacedOutAt outPtr (.error ()))
        pt peer remoteIk
        (kit.storeUpdate sst0 peer.val ⟨some ss⟩ (.error ()))
        (ikit.saveUpdate ist0 peer.val remoteIk (.ok c)))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
