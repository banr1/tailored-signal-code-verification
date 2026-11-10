/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSMInstance
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSessionSM
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.CryptoGames.CKA.LibsignalCKA
public import LibsignalBinary.Specifications.CryptoGames.SM.Construction
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.WireRatchetDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.PubDefs
public import LibsignalBinary.Specifications.CryptoGames.SM.LibsignalGame
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.HybridWith

/-!
# Proof-side libsignal SM instance definitions

Proof-side definitions (`lCls` and `libsignalSessionScheme`) extending the specification in
`LibsignalSMInstance`.
-/

@[expose] public section

open OracleComp OracleSpec ENNReal
namespace CryptoGames
namespace Ratchet
namespace LibsignalInst
open HMAC HKDF CBC LibsignalAead SM.Construction CKA LibsignalSession AEADScheme MACScheme

/-- AD class extracting the header epoch `t` (DEV-LS8). -/
def lCls {Pt : Type} (a : ℕ × (Header Pt × LibsignalMsgPublicPart)) : ℕ := a.2.1.1

/-- **DEV-LS26 (formalization): initial keys and epoch 0.** Wraps a libsignal `Params` bundle as an
`SMSchemeR` initialized from `rootKdf F k_root (encPt lam)` (with PQXDH out of scope), where Alice
draws her first sending key at initialization and retains a receiver chain for Bob's signed
pre-key. -/
def libsignalSessionScheme {PQ PQC Pt : Type} [Inhabited PQ] (P : Params PQ PQC) (ℓ : ℕ)
    (encPt : Pt → List (BitVec 8)) (lam : Pt) :
    SMSchemeR (RootKey × BitVec 256 × BitVec 256 × BitVec 256) (GhostState PQ) (Plain ℓ) PQC
      (BitVec 256) (List (BitVec 8)) where
  initA k := let rc := rootKdf P.C.F k.1 (encPt lam)
    P.initA ⟨rc.1, rc.2, k.2.1, k.2.2.1, k.2.2.2⟩
  initB k := let rc := rootKdf P.C.F k.1 (encPt lam)
    P.initB ⟨rc.1, rc.2, k.2.1, k.2.2.1, k.2.2.2⟩
  send g m r := P.send g m.toList r
  receive g c rc := (P.receive g c rc).map fun x => (x.1, x.2.1, x.2.2.1, padOrTruncatePlain ℓ x.2.2.2)

end LibsignalInst
end Ratchet
end CryptoGames
