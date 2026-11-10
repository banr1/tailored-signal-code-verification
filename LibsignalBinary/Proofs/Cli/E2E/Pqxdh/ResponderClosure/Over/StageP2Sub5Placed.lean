/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6Aux
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub6
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Bridges
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.StageP2Sub4Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksB6
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub6Aux
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2bAux
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.InitializeAliceStage1Common
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Sub6V1
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Trans

/-!
# Placed Stage P2 Over-Path Entry Precondition

Defines the `[LibsignalPlacement]` populated-record Stage P2 entry precondition
`stageP2OverPreAtPlaced` at `+0x0868`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.StoreKit.Identity
open CryptoVerification.LibsignalPublicApi.StoreKit.IdentitySelf
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecsBinary
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding PanicOomProp
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched (prevSessionsEmptyAt)

/-- Placed spatial precondition at `+0x0868` for `stageP2_over_v1_kits` on a populated 1-session
record (`prevSessionsEmptyAt A coroPtr g ∗ sessionStateReprAt A (coroPtr + 0xf8) recG sess`). -/
def stageP2OverPreAtPlaced [LibsignalPlacement] (A : RustAlloc) (b : BitVec 64)
    (spkKit : SignedPreKeyStoreSpec A b)
    (kpkKit : KyberPreKeyStoreSpec A b)
    (pkKit : PreKeyStoreSpec A b)
    (ikit : IdentityStoreSpec A b)
    (s0 : State)
    (sp fp coroPtr ctxPtr outPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr preKeyStorePtr spkStorePtr kyberStorePtr
     v_330 v_388 u_488 u_80 u_88 u_90 u_a8 u_b8 u_d0 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte b_2c0 b_390 b_4b0 b_4f1 b_4f2 : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (stSpk : spkKit.SpkState) (stKpk : kpkKit.KpkState) (stPk : pkKit.PkState) (stId : ikit.IdState)
    (gMe gPeer : AddrGhost)
    (g : RecordGhost) (recG : SessionGhost) (sess : Session (List (BitVec 8)))
    (stk : Nat) (Frame : SepProp) : SepProp :=
  spkKit.storeAt spkStorePtr stSpk ∗
  kpkKit.storeAt kyberStorePtr stKpk ∗
  pkKit.storeAt preKeyStorePtr stPk ∗
  ikit.identityAt idStorePtr stId ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
  ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateReprAt A (coroPtr + 0xf8#64) recG sess ∗
  cells (coroPtr + 0x250#64) 6 ∗
  memRegion (coroPtr + 0x298#64) 20 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  memRegion (coroPtr + 0x398#64) 96 ∗
  cells (coroPtr + 0x3f8#64) 6 ∗
  cells (coroPtr + 0x468#64) 4 ∗
  ((coroPtr + 0x488#64) ↦₆₄ u_488) ∗
  ((coroPtr + 0x4b0#64) ↦₈ b_4b0) ∗
  memRegion (coroPtr + 0x4b1#64) 64 ∗
  ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  p2CoroScratchTailAt coroPtr ∗
  p2MsgFieldsAt msgPtr ctBufPtr hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId ∗
  protocolAddressAt A gMe localAddrPtr ∗
  protocolAddressAt A gPeer remoteAddrPtr ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗
  ((sp + 0x88#64) ↦₆₄ u_88) ∗
  ((sp + 0x90#64) ↦₆₄ u_90) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ (coroPtr + 0x390#64)) ∗
  ((sp + 0xb8#64) ↦₆₄ u_b8) ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 0x270#64) 9 ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3a0#64) 8 ∗
  memRegion (sp + 0x3ac#64) 1 ∗
  memRegion (sp + 0x3b0#64) 48 ∗
  memRegion (sp + 0x3e0#64) 368 ∗
  cells (sp + 0x560#64) 4 ∗
  cells (sp + 0x6a0#64) 4 ∗
  cells (sp + 0x7e0#64) 4 ∗
  cells (sp + 0x930#64) 8 ∗
  memRegion (sp + 0xa90#64) 288 ∗
  memRegion (fp + 0xffffffffffffff80#64) 9 ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  memRegion outPtr 48 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool ∗
  stackAt sp stk ∗
  Frame

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
end
