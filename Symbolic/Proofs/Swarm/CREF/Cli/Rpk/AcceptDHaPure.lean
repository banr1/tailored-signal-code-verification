/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Refinement.RecordBytesBridge
public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PinCoinsPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepRatchetDHaPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Normalized DH Ratchet Step Congruence for Pre-Key Sessions

Defines `rpkSessionNorm`, which replaces the sender chain's public key and zeroes `previousCounter`,
and lifts `stateRel_and_consumeMessageKey_of_dhRatchetStep_tr` to sessions related via `StateRel`
only after `rpkSessionNorm`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure.RpkDHa

cref_open
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (sha256CompressFunction ExternCryptoLawsHold)
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Hooks2
open Symbolic.Swarm.CREF.CliPure.RpkCli (pinCoins)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState)

/-- Replaces the sender chain's public key in `s` with `P` and sets `previousCounter := 0`. -/
def rpkSessionNorm (P : PublicKey) (s : Session (List (BitVec 8))) :
    Session (List (BitVec 8)) :=
  { s with
    state :=
      { s.state with
        previousCounter := 0
        senderChain := s.state.senderChain.map fun sc =>
          { sc with ratchetKey := { sc.ratchetKey with publicKey := P } } } }

theorem rpkD_dhRatchetStep_congr {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r0 r0' r1 : RatchetState} {ck : ChainKey}
    (hok : Mut.exec (RatchetState.dhRatchetStep C their coins) r0 = (.ok ck, r1))
    (hrk : r0'.rootKey = r0.rootKey) (hrc : r0'.receiverChains = r0.receiverChains)
    (hmfj : r0'.maxForwardJumps = r0.maxForwardJumps)
    (P : PublicKey)
    (hsc : r0'.senderChain = r0.senderChain.map fun sc =>
      { sc with ratchetKey := { sc.ratchetKey with publicKey := P } }) :
    Mut.exec (RatchetState.dhRatchetStep C their coins) r0' = (.ok ck, r1) := by
  obtain ⟨sc, newRootKey, finalRootKey, senderChainKey, hsc0, hrc1, hrc2, hr1⟩ :=
    dhRatchetStep_ok_inv hok
  rw [hsc0, Option.map_some] at hsc
  subst hr1
  rcases r0' with ⟨rk', sc', rcs', pc', mfj'⟩
  rcases r0 with ⟨rk, scO, rcs, pc, mfj⟩
  dsimp only at hrk hrc hmfj hsc hsc0 hrc1 ⊢
  subst hrk hrc hmfj hsc hsc0
  unfold RatchetState.dhRatchetStep RatchetState.takeRootKey Mut.exec
  simp [hrc1, hrc2, liftE, ExceptT.run, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, StateT.run,
    StateT.bind, bind, get, getThe, MonadStateOf.get, StateT.get, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, pure, ExceptT.pure, StateT.pure, Functor.map,
    StateT.map, ExceptT.lift, liftM, monadLift, MonadLift.monadLift, modify]

theorem rpkD_dhRatchetStep_norm {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {s : Session (List (BitVec 8))} {r1 : RatchetState}
    {ck : ChainKey} (P : PublicKey)
    (hok : Mut.exec (RatchetState.dhRatchetStep C their coins) (ratchetStateOf s.state) =
      (.ok ck, r1)) :
    Mut.exec (RatchetState.dhRatchetStep C their coins)
      (ratchetStateOf (rpkSessionNorm P s).state) = (.ok ck, r1) :=
  rpkD_dhRatchetStep_congr hok rfl rfl rfl P rfl

/-- Establishes post-step `StateRel` and `consumeMessageKey` properties for `dhRatchetStep` on `s`
from `StateRel` on the normalized session `rpkSessionNorm P s`. -/
theorem rpkD_stateRel_and_consumeMessageKey_of_dhRatchetStep
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (hEquations : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    {st : TRState} {s : Session (List (BitVec 8))}
    (P : PublicKey)
    (hrel : StateRel interpretation S g st (sessionToRecordRec (rpkSessionNorm P s)))
    (hRkLen : (gamma interpretation S g st.rk).length = 32)
    (hDhsLen : (gamma interpretation S g st.dhs).length = 32)
    (hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32)
    {their : PublicKey} {pk : DY.Bytes} {counter : BitVec 32}
    (hTheir : their = ⟨vec32 (gamma interpretation S g pk)⟩)
    (hPkLen : (gamma interpretation S g pk).length = 32)
    {rngIdx : Nat} {rngBytes : List (BitVec 8)}
    (hRng : g.σ rngIdx 32 = rngBytes) (hRngLen : rngBytes.length = 32)
    {spqr' : DY.Bytes} {newPqrState : List (BitVec 8)}
    (hspqr' : gamma interpretation S g spqr' = newPqrState)
    {ck_r ck_adv ck_next : ChainKey} {r1 r_adv r2 : RatchetState}
    (hFindNone : (ratchetStateOf s.state).findReceiverChainKey their = .ok none)
    (hStep :
      Mut.exec
        (RatchetState.dhRatchetStep (cryptoOf' interpretation E D) their (pinCoins (some rngBytes)))
        (ratchetStateOf s.state) = (.ok ck_r, r1))
    (hNotLt : ¬ (counter < ck_r.index))
    (hJump : (counter - ck_r.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps)
    (hAdv :
      Mut.exec
        (RatchetState.advanceChain (sha256CompressFunction interpretation)
          their counter (counter - ck_r.index).toNat ck_r)
        r1 = (.ok ck_adv, r_adv))
    (hNext : ck_adv.nextChainKey (sha256CompressFunction interpretation) = .ok ck_next)
    (hSet : Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2)) :
    let F := sha256CompressFunction interpretation
    let msgCounter := UInt32.ofBitVec counter
    let (st1, c) := trDhRatchetState st pk rngIdx
    findRecvChain st.recv pk = none ∧
    ∃ (mks' : List MessageKeyGenerator) (seed : DY.Bytes) (c' : RecvChain),
      consumeMessageKey c msgCounter = some (seed, c') ∧
      (ck_adv.messageKeys F).seed = gamma interpretation S g seed ∧
      (ck_adv.messageKeys F).counter = counter ∧
      c'.ratchetKey = pk ∧
      c'.rIdx = st.rIdx + 2 ∧
      c.index = 0 ∧
      c.rIdx = st.rIdx + 2 ∧
      r2 = { r1 with
        receiverChains := r1.receiverChains.set (r1.receiverChains.length - 1)
          { senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' } } ∧
      StateRel interpretation S g { st1 with recv := setRecvChain st1.recv c', spqr := spqr' }
        (sessionToRecordRec
          { s with
            state :=
              { s.state with
                rootKey := r2.rootKey, previousCounter := r2.previousCounter,
                senderChain := r2.senderChain, receiverChains := r2.receiverChains,
                pqRatchetState := newPqrState, pendingPreKey := false }
            pendingPreKey := none, pendingKyberPreKey := none }) ∧
      (∀ rc ∈ r2.receiverChains,
        rc ∈ s.state.receiverChains ∨
        rc = { senderRatchetKey := their, chainKey := some ck_next, messageKeys := mks' }) ∧
      (∀ k ∈ mks',
        ∃ j < msgCounter.toNat - c.index.toNat,
          k.counter = c.index.toBitVec + BitVec.ofNat 32 j ∧
          UInt32.ofBitVec k.counter = c.index + UInt32.ofNat j ∧
          UInt32.ofBitVec k.counter ≠ msgCounter ∧
          k.seed = gamma interpretation S g (kdfCk (chainKeyAt c.chainKey j)).2 ∧
          k.seed.length = 32) := by
  exact Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.stateRel_and_consumeMessageKey_of_dhRatchetStep_tr
    interpretation S g hEquations E D hrel hRkLen hDhsLen hCkLens hTheir hPkLen hRng hRngLen
    hspqr' (s := rpkSessionNorm P s) hFindNone (rpkD_dhRatchetStep_norm P hStep) hNotLt hJump
    hAdv hNext hSet

end Symbolic.Swarm.CREF.CliPure.RpkDHa
