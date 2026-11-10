/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2DefsPlacedBudget

/-!
# Budget-Threaded Relocatable Stage P2 Error Frame

Defines `p2ErrFrameAtPlaced` over `A : RustCliAllocBudget M` (`A.pool lim st sf`) and bridges it
to `Poll.p2ErrFrameAtPlaced (A.atState lim st)`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlacedBudget

open Arm64 ProofLib
open CryptoVerification (LibsignalPlacement)
open CryptoVerification.LibsignalTripleRatchetRepr (AddrGhost)
open CryptoVerification.E2E.Pqxdh.Initiator (HandshakeHdr)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget)

/-- Budget-threaded placed common coroutine, stack, message, address, and allocator spatial frame
delivered uniformly at `s0.readReg64 .x30` on all 6 Stage-P2 error exits (Arms 1–6), with
allocator pool `A.pool lim st sf`. -/
def p2ErrFrameAtPlaced [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 sf : State)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) : SepProp :=
  CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2ErrFrameAtPlaced
    (A.atState lim st sf) s0
    sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
    idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388
    hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
    gMe gPeer stk Frame

theorem p2ErrFrameAtPlaced_eq_atState [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (st : M.σ) (s0 sf : State)
    (sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
     idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388 : BitVec 64)
    (hdr : HandshakeHdr) (msgVerByte : BitVec 8)
    (opkIdWord kyberPreKeyId remoteRegId signedPreKeyId : BitVec 32)
    (gMe gPeer : AddrGhost) (stk : Nat) (Frame : SepProp) :
    p2ErrFrameAtPlaced A lim st s0 sf
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388
      hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      gMe gPeer stk Frame =
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits.p2ErrFrameAtPlaced
      (A.atState lim st sf) s0
      sp fp coroPtr msgPtr ctBufPtr remoteAddrPtr localAddrPtr
      idStorePtr idVt preKeyStorePtr pkVt kyberStorePtr kpkVt v_330 v_388
      hdr msgVerByte opkIdWord kyberPreKeyId remoteRegId signedPreKeyId
      gMe gPeer stk Frame := rfl

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BridgePlacedBudget
