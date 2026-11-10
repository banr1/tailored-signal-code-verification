/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieAuxPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.AcceptDHaPure
public import Symbolic.Proofs.SR.SendSpecWPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SessionPrimsPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Prelude
public import Symbolic.Proofs.Refinement.X25519Covered -- shake: keep

/-!
# Normalized Pre-Decrypt `StateRel` and `AcceptTieD`

Defines `AcceptTieD` for an accepting pre-key decryption at a fixed random draw, plaintext, and
encoded record, and proves `rpkN_stateRel_norm` on the normalized pre-decrypt session state.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.AcceptD

cref_open

open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoProofLib.Refinement
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (StateAndMessage)
open DY.Libsignal.Refinement (ExternCryptoLawsHold sha256CompressFunction)
open DY.Libsignal.PQXDH
open Proofs.libsignal.SR (interpW)
open Symbolic.Swarm.CREF.CliPure (AcceptRecTie AcceptSt0ModelInvs pureSpqrEmptyAsNone)
open Symbolic.Swarm.CREF.CliPure.RpkCli (pureCoinsOf)

/-- Tie between the pre-decrypt session `st0`, post-decrypt session `st'`, random draw `d`,
plaintext `pt`, and encoded record `sm` for an accepting pre-key call. -/
def AcceptTieD (interpretation : ExternInterpretation) (r : ProtocolSetup) (p : PreKeyFields)
    (d pt : HwBytes) (sm : StateAndMessage) : Prop :=
  ∃ (st0 st' : SessionState HwBytes) (expected : Option HwBytes),
    AcceptRecTie r p (p.baseKey.take 33) st' sm ∧
    AcceptSt0ModelInvs interpretation r p st0 ∧
    (∀ sc, st0.senderChain = some sc → sc.ratchetKey.privateKey.bytes =
      List.Vector.ofFn (fun i =>
        (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)).getD i.val 0#8)) ∧
    Mut.exec
      (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
        (Proofs.libsignal.Hooks2.cryptoOf' interpretation) (interpW interpretation)
        (pureSpqrEmptyAsNone (sha256CompressFunction interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interpretation))
        expected p.inner .preKey (pureCoinsOf d)) st0 = (.ok pt, st')

end Symbolic.Swarm.CREF.CliPure.AcceptD

namespace Symbolic.Swarm.CREF.CliPure

cref_open

open CryptoProofLib.Refinement (ExternInterpretation)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)

/-- Bob's signed pre-key public key as a `PublicKey`, matching `dhPk (setupSecret r 2)` under
`gamma`. -/
def rpkSpkPub (interpretation : ExternInterpretation) (r : ProtocolSetup) :
    CryptoGames.LibsignalSession.PublicKey :=
  ⟨DY.Libsignal.TripleRatchet.Refinement.vec32
    ((interpretation DY.Libsignal.Refinement.x25519PublicKeySymbol
      [DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)]).getD [])⟩

theorem rpkSpkPub_serialize {interpretation : ExternInterpretation}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    (r : ProtocolSetup) :
    (rpkSpkPub interpretation r).serialize =
      TR.serializedKey ((interpretation DY.Libsignal.Refinement.x25519PublicKeySymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)]).getD []) := by
  unfold rpkSpkPub CryptoGames.LibsignalSession.PublicKey.serialize TR.serializedKey
  congr 1
  exact Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _
    (hEq.x25519_public_key_length _)

theorem rpkN_acceptSt0ModelInvs_norm {interpretation : ExternInterpretation}
    {r : ProtocolSetup} {p : PreKeyFields}
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (P : CryptoGames.LibsignalSession.PublicKey)
    (hinv : AcceptSt0ModelInvs interpretation r p s.state) :
    AcceptSt0ModelInvs interpretation r p (RpkDHa.rpkSessionNorm P s).state := by
  obtain ⟨ct_wire, hver, hrc, hct, hlen, hbase, hmsg, hrem, hloc, hrk, ⟨_pubKp, hsc⟩, hpq⟩ := hinv
  refine ⟨ct_wire, hver, hrc, hct, hlen, hbase, hmsg, hrem, hloc, hrk, ⟨P, ?_⟩, hpq⟩
  show s.state.senderChain.map _ = _
  rw [hsc]
  rfl

/-- Normalized form of `rpkTie_stateRel_init` on `RpkDHa.rpkSessionNorm`, discharging the sender
ratchet public key and `previousCounter = 0` obligations directly. -/
theorem rpkN_stateRel_norm {interpretation : ExternInterpretation}
    (hEq : DY.Libsignal.Refinement.ExternCryptoLawsHold interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics}
    (hInit : S.init = Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf interpretation)
    {g : Ghost} (hCompat : GhostAndSemMatchSetup interpretation r S g)
    {b : HwBytes} {p : PreKeyFields}
    (hp : parsePreKeyWire b = some p)
    {ms : List Move} {x : PreKeyRep} (hx : x ∈ preKeyRepresentations interpretation r S g ms b)
    (hnk : ¬ KyberMismatch interpretation r p)
    {keys : PQXDH.HandshakeKeys} (hkeys : TR.bobKeys r p x = some keys)
    {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hinv : AcceptSt0ModelInvs interpretation r p s.state)
    (rt : DY.Bytes) :
    TR.StateRel interpretation S g
      { peer := r.alice, myIk := PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 1)),
        peerIk := PQXDH.serializedIk (setupPublic r 0), rk := keys.rk, dhs := setupSecret r 2,
        cks := keys.ck, ns := 0, pn := 0,
        sid := DY.Concat.concat (DY.X25519.normalizeX25519Key rt) keys.rk,
        initiator := false,
        rIdx := 0, recv := [],
        spqr := DY.Spqr.spqrInit keys.pqr DY.Libsignal.TripleRatchet.spqrB2A }
      (sessionToRecordRec (RpkDHa.rpkSessionNorm (rpkSpkPub interpretation r) s)) := by
  refine rpkTie_stateRel_init hEq hwf hInit hCompat hp hx hnk hkeys
    (rpkN_acceptSt0ModelInvs_norm (rpkSpkPub interpretation r) hinv) ?_ rfl rt _ rfl
  intro sc hsc
  change s.state.senderChain.map _ = some sc at hsc
  rcases hsc0 : s.state.senderChain with _ | sc0
  · rw [hsc0] at hsc; cases hsc
  · rw [hsc0, Option.map_some] at hsc
    cases hsc
    exact rpkSpkPub_serialize hEq r

end Symbolic.Swarm.CREF.CliPure
