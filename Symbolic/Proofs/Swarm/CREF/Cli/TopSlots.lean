/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.InitiateSlot
public import Symbolic.Proofs.Swarm.CREF.Cli.DirInvBridge
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Alice Directory-Invariant Bridges for CLI Slots

Relates `PqPartyInv` and `PqDirInv` to `Slots.AliceInitPartyInv` and `Slots.AliceDirState`
for Alice's `init` calls, and proves injectivity of `HMAC.keyToBytes32`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli
open Symbolic.Swarm.CREF.CliPure

open DY DY.Comparse
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E
open CryptoVerification.SignalSession
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure

theorem slotsModelAgree_iff (interp : ExternInterpretation) (P : PEParams) :
    Slots.ModelAgree interp P ↔ ModelAgree interp P :=
  Iff.rfl

theorem aliceInitPartyInv_of_pqPartyInv {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {accepted : List HwBytes} {st : PqParty} {d : DirectorySnapshot}
    (hext : ExternContractsHoldCli interp) (hwf : ProtocolSetupWF r)
    (hA : PqPartyInv interp P r accepted r.alice st d) :
    Slots.AliceInitPartyInv interp P r d st where
  alice := by
    obtain ⟨hsig, hot, hkot, hklr⟩ := hA.alice_stores rfl
    have hid : idSecret r r.alice = secretBytes r 0 := by simp [idSecret, ProtocolSetup.ikASecBytes]
    have hreg : regIdOf r r.alice = r.regIdA := by simp [regIdOf]
    have hpsec : peerIdSecret r r.alice = secretBytes r 1 := by simp [peerIdSecret, ProtocolSetup.ikBSecBytes]
    have hv0 := Slots.bytesToVec_32_eq_vec32 (secretBytes_0_length hwf)
    have hv1 := Slots.bytesToVec_32_eq_vec32
      (hext.1.x25519_public_key_length (clamp (secretBytes r 1)))
    refine ⟨hA.party_eq.trans (partyOf_alice r), ?_, ?_, hsig, hot, hkot, hklr⟩
    · rw [hA.me_eq, hid, hreg, hv0]
    · rw [hA.peerId_eq, hpsec]; dsimp only [pubBytes]; rw [hv1]
  session_reach := hA.session_reach
  dir_eq := hA.dir_eq

theorem pqDirInv_update_alice {interp : ExternInterpretation} {P : PEParams}
    {r : ProtocolSetup} {t t' : CliTurn} {accepted : List HwBytes} {st' : PqParty}
    (hext : ExternContractsHoldCli interp) (hwf : ProtocolSetupWF r)
    (hDir : PqDirInv interp P r t accepted)
    (hdirs_other : ∀ q, q ≠ r.alice → t'.dirs q = t.dirs q)
    (hbobOff : t'.bobOff = t.bobOff)
    (hd' : Slots.AliceDirState interp P r (t'.dirs r.alice) st') :
    PqDirInv interp P r t' accepted := by
  have hid : idSecret r r.alice = secretBytes r 0 := by simp [idSecret, ProtocolSetup.ikASecBytes]
  have hreg : regIdOf r r.alice = r.regIdA := by simp [regIdOf]
  have hpsec : peerIdSecret r r.alice = secretBytes r 1 := by simp [peerIdSecret, ProtocolSetup.ikBSecBytes]
  have hv0 := Slots.bytesToVec_32_eq_vec32 (secretBytes_0_length hwf)
  have hv1 := Slots.bytesToVec_32_eq_vec32
    (hext.1.x25519_public_key_length (clamp (secretBytes r 1)))
  have hA' : PqPartyInv interp P r accepted r.alice st' (t'.dirs r.alice) := by
    refine ⟨hd'.alice.party_eq.trans (partyOf_alice r).symm, ?_, ?_,
      fun _ => ⟨hd'.alice.signed_nil, hd'.alice.oneTime_nil,
        hd'.alice.kyberOneTime_nil, hd'.alice.kyberLastResort_nil⟩,
      fun hne => absurd rfl hne,
      fun x g hs => ⟨(hd'.wf.1 x g hs).1, (hd'.wf.1 x g hs).2.1⟩,
      hd'.dir_eq⟩
    · rw [hd'.alice.me_eq, hid, hreg, hv0]
    · rw [hd'.alice.peerId_eq, hpsec]; dsimp only [pubBytes]; rw [hv1]
  obtain ⟨_, ⟨stB, hB⟩, hoth⟩ := hDir
  refine ⟨⟨st', hA'⟩, ⟨stB, ?_⟩, fun p ha hb => (hdirs_other p ha).trans (hoth p ha hb)⟩
  rw [hbobOff, hdirs_other r.bob hwf.1.symm]
  exact hB

theorem keyToBytes32_inj {a b : BitVec 256}
    (h : CryptoGames.HMAC.keyToBytes32 a = CryptoGames.HMAC.keyToBytes32 b) : a = b := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have hj := congrArg (fun l => l[k / 8]?) h
  simp only [CryptoGames.HMAC.keyToBytes32, List.getElem?_ofFn,
    show k / 8 < 32 by omega, ↓reduceDIte, Option.some.injEq] at hj
  have hi := congrArg (fun v => v.getLsbD (k % 8)) hj
  simpa only [BitVec.getLsbD_extractLsb', show k % 8 < 8 by omega, decide_true, Bool.true_and,
    show 8 * (k / 8) + k % 8 = k by omega] using hi

end Symbolic.Swarm.CREF.Cli
