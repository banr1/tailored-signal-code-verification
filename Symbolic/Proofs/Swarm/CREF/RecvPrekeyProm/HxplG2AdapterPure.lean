/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyProm.BinPure
public import Symbolic.Proofs.RngG.R3ModelInv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepNoRatchetWAtHelpersPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TROpen

/-!
# Decrypt Branch Selectors and Adapters on Session Promotion

Defines the three decrypt branch selectors (`PromDecSelSkipped`, `PromDecSelNoRatchet`,
`PromDecSelRatchetDH`), inverts `PromBinAcceptOut` along each `DecryptOkBranch` arm, and proves
their trichotomy (`prom_decSel_cases_out`).
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false

namespace Symbolic.Swarm.CREF.CliPure

cref_open
cref_open_tr

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Hooks2 (cryptoOf')
open Proofs.libsignal.SR (interpW)
open Symbolic.Swarm.CREF.CliPure.RpkCli (pinCoins)
open Proofs.libsignal.RngG.R3 (ratchetStateOf DecryptOkBranch)
open Symbolic.Swarm.TRREF.SpqrSemOf (spqrModelOf)

abbrev PromDecSel : Type :=
  Session (List (BitVec 8)) → SignalMessage → List MachineEvent → BitVec 256 → Prop

/-- Cached skipped-key branch: existing receiver chain for `msg.senderRatchetKey` with
`msg.counter < ck.index`. -/
def PromDecSelSkipped : PromDecSel := fun sess msg mid coins =>
  ∃ (ci : Nat) (rc : ReceiverChain) (ck : ChainKey),
    mid = [] ∧ coins = 0#256 ∧
    sess.state.receiverChains[ci]? = some rc ∧
    rc.senderRatchetKey = msg.senderRatchetKey ∧
    rc.chainKey = some ck ∧ msg.counter < ck.index

/-- Existing-chain branch without DH ratchet: `ck.index <= msg.counter`. -/
def PromDecSelNoRatchet : PromDecSel := fun sess msg mid coins =>
  ∃ (ci : Nat) (rc : ReceiverChain) (ck : ChainKey),
    mid = [] ∧ coins = 0#256 ∧
    sess.state.receiverChains[ci]? = some rc ∧
    rc.senderRatchetKey = msg.senderRatchetKey ∧
    rc.chainKey = some ck ∧ ck.index ≤ msg.counter

/-- New-chain DH-ratchet branch: one 32-byte `rng` draw and no matching receiver chain. -/
def PromDecSelRatchetDH : PromDecSel := fun sess msg mid coins =>
  ∃ rngBytes : HwBytes,
    mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧
    coins = Symbolic.Swarm.CREF.CliPure.RpkCli.pinCoins (some rngBytes) ∧
    ∀ rc ∈ sess.state.receiverChains, rc.senderRatchetKey ≠ msg.senderRatchetKey

theorem prom_find_eq_of_getElem {st : SessionState (List (BitVec 8))} {their : PublicKey}
    {ci : Nat} {rc : ReceiverChain} {ck ck' : ChainKey}
    (hnodup : (st.receiverChains.map ReceiverChain.senderRatchetKey).Nodup)
    (hrc : st.receiverChains[ci]? = some rc) (hrc_key : rc.senderRatchetKey = their)
    (hck : rc.chainKey = some ck)
    (hFind : (ratchetStateOf st).findReceiverChainKey their = .ok (some ck')) : ck' = ck := by
  obtain ⟨ci', rc', _, hrc', hsrk', hck'⟩ :=
    Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
  have hci : ci' = ci :=
    Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep.getElem?_receiverChains_inj_of_nodup hnodup hrc' hrc hsrk' hrc_key
  subst hci
  cases Option.some.inj (hrc'.symm.trans hrc)
  exact Option.some.inj (hck'.symm.trans hck)

theorem prom_noChain_of_find_none {st : SessionState (List (BitVec 8))} {their : PublicKey}
    (hFind : (ratchetStateOf st).findReceiverChainKey their = .ok none) :
    ∀ rc ∈ st.receiverChains, rc.senderRatchetKey ≠ their := by
  have hci := Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_none _ _ hFind
  intro rc hMem hEq
  unfold CryptoGames.LibsignalSession.RatchetState.findReceiverChainIndex at hci
  rw [List.findIdx?_eq_none_iff] at hci
  have hFalse := hci rc hMem
  simp [hEq] at hFalse

section AdapterOut
variable {interpretation : ExternInterpretation} {r : ProtocolSetup}
  {rec b : HwBytes} {mid : List MachineEvent} {sm : StateAndMessage} {pf : PreKeyFields}
  {sess sess' : Session (List (BitVec 8))}
  {coins : BitVec 256} {expected : Option (List (BitVec 8))} {pt : List (BitVec 8)}

theorem prom_exec_branch_out
    (hOut : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt) :
    ∃ (remIk : IdentityKey) (r2 : RatchetState) (mkGen : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : CryptoGames.HKDF.Salt)
      (st' : SessionState (List (BitVec 8))),
      sess.state.remoteIdentity = some remIk ∧
      (spqrModelOf interpretation).recv sess.state.pqRatchetState pf.inner.pqRatchet =
        .ok (newPqrState, pqrKey) ∧
      (interpW interpretation).dec (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).cipherKey
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).iv pf.inner.ciphertext = some pt ∧
      st' = { sess.state with
        rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
        receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false } ∧
      sess'.state = st' ∧
      sm.state = CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩ ∧
      DecryptOkBranch (cryptoOf' interpretation) (ratchetStateOf sess.state) remIk
        sess.state.localIdentity expected pf.inner .preKey coins pqrKey r2 mkGen := by
  obtain ⟨remIk, tr_out, hRem, hTr, hSt2⟩ :=
    Proofs.libsignal.RngG.R3.tryDecryptWithStateW_ok_inv hOut.hexec
  obtain ⟨ck, r1, r2, mkGen, newPqrState, pqrKey, hEnsure, hConsume, hSpqr, hMac, hDec, hTrOut⟩ :=
    Proofs.libsignal.RngG.R3.tripleRatchet_decryptW_ok_inv hTr
  subst hTrOut
  exact ⟨remIk, r2, mkGen, newPqrState, pqrKey, _, hRem, hSpqr, hDec, rfl, hSt2, hOut.hstate,
    Proofs.libsignal.RngG.R3.decryptOkBranch_of_ensure_consume hEnsure hConsume hMac⟩

theorem prom_adapter_skipped_out
    (hOut : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt)
    (hnodup : (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup)
    (hsel : PromDecSelSkipped sess pf.inner mid coins) :
    ∃ (remIk : IdentityKey) (ck : ChainKey) (r2 : RatchetState) (mkGen : MessageKeyGenerator)
      (newPqrState : List (BitVec 8)) (pqrKey : CryptoGames.HKDF.Salt)
      (st' : SessionState (List (BitVec 8))),
      mid = [] ∧ coins = 0#256 ∧
      sess.state.remoteIdentity = some remIk ∧
      (ratchetStateOf sess.state).findReceiverChainKey pf.inner.senderRatchetKey = .ok (some ck) ∧
      pf.inner.counter < ck.index ∧
      Mut.exec (RatchetState.takeSkippedKey pf.inner.senderRatchetKey pf.inner.counter)
        (ratchetStateOf sess.state) = (.ok (some mkGen), r2) ∧
      (spqrModelOf interpretation).recv sess.state.pqRatchetState pf.inner.pqRatchet =
        .ok (newPqrState, pqrKey) ∧
      pf.inner.verifyMacWithAddresses (cryptoOf' interpretation).F expected remIk
        sess.state.localIdentity (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true ∧
      (interpW interpretation).dec (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).cipherKey
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).iv pf.inner.ciphertext = some pt ∧
      st' = { sess.state with
        rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
        receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false } ∧
      sess'.state = st' ∧
      sm.state = CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩ := by
  obtain ⟨ci, rc, ck, hmid, hcoins, hrc, hrc_key, hck, hlt⟩ := hsel
  obtain ⟨remIk, r2, mkGen, newPqrState, pqrKey, st', hRem, hSpqr, hDec, hSt', hsess', hstate, hBr⟩ :=
    prom_exec_branch_out hOut
  cases hBr with
  | skipped ck' hFind hLt hTake hMac =>
    exact ⟨remIk, ck', r2, mkGen, newPqrState, pqrKey, st', hmid, hcoins, hRem, hFind, hLt, hTake,
      hSpqr, hMac, hDec, hSt', hsess', hstate⟩
  | existing ck' _ _ _ hFind hNotLt _ _ _ _ _ _ =>
    cases prom_find_eq_of_getElem hnodup hrc hrc_key hck hFind
    exact absurd hlt hNotLt
  | ratchet _ _ _ _ _ hFind _ _ _ _ _ _ _ _ =>
    exact absurd hrc_key (prom_noChain_of_find_none hFind rc (List.mem_of_getElem? hrc))

theorem prom_adapter_noRatchet_out
    (hOut : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt)
    (hnodup : (sess.state.receiverChains.map ReceiverChain.senderRatchetKey).Nodup)
    (hsel : PromDecSelNoRatchet sess pf.inner mid coins) :
    ∃ (remIk : IdentityKey) (ck ck_adv ck_next : ChainKey) (r_adv r2 : RatchetState)
      (mkGen : MessageKeyGenerator) (newPqrState : List (BitVec 8)) (pqrKey : CryptoGames.HKDF.Salt)
      (st' : SessionState (List (BitVec 8))),
      mid = [] ∧ coins = 0#256 ∧
      sess.state.remoteIdentity = some remIk ∧
      (ratchetStateOf sess.state).findReceiverChainKey pf.inner.senderRatchetKey = .ok (some ck) ∧
      ¬ (pf.inner.counter < ck.index) ∧
      (pf.inner.counter - ck.index).toNat ≤ (ratchetStateOf sess.state).maxForwardJumps ∧
      Mut.exec (RatchetState.advanceChain (cryptoOf' interpretation).F pf.inner.senderRatchetKey
        pf.inner.counter (pf.inner.counter - ck.index).toNat ck) (ratchetStateOf sess.state) =
        (.ok ck_adv, r_adv) ∧
      ck_adv.nextChainKey (cryptoOf' interpretation).F = .ok ck_next ∧
      Mut.exec (RatchetState.setReceiverChainKey pf.inner.senderRatchetKey ck_next) r_adv = (.ok (), r2) ∧
      mkGen = ck_adv.messageKeys (cryptoOf' interpretation).F ∧
      (spqrModelOf interpretation).recv sess.state.pqRatchetState pf.inner.pqRatchet =
        .ok (newPqrState, pqrKey) ∧
      pf.inner.verifyMacWithAddresses (cryptoOf' interpretation).F expected remIk
        sess.state.localIdentity (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true ∧
      (interpW interpretation).dec (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).cipherKey
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).iv pf.inner.ciphertext = some pt ∧
      st' = { sess.state with
        rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
        receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false } ∧
      sess'.state = st' ∧
      sm.state = CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩ := by
  obtain ⟨ci, rc, ck, hmid, hcoins, hrc, hrc_key, hck, hle⟩ := hsel
  obtain ⟨remIk, r2, mkGen, newPqrState, pqrKey, st', hRem, hSpqr, hDec, hSt', hsess', hstate, hBr⟩ :=
    prom_exec_branch_out hOut
  cases hBr with
  | skipped ck' hFind hLt _ _ =>
    cases prom_find_eq_of_getElem hnodup hrc hrc_key hck hFind
    exact absurd hLt (BitVec.not_lt.mpr hle)
  | existing ck' ck_adv ck_next r_adv hFind hNotLt hJump hAdv hNext hSet hMkGen hMac =>
    exact ⟨remIk, ck', ck_adv, ck_next, r_adv, r2, mkGen, newPqrState, pqrKey, st', hmid, hcoins,
      hRem, hFind, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hSpqr, hMac, hDec, hSt', hsess', hstate⟩
  | ratchet _ _ _ _ _ hFind _ _ _ _ _ _ _ _ =>
    exact absurd hrc_key (prom_noChain_of_find_none hFind rc (List.mem_of_getElem? hrc))

theorem prom_adapter_ratchetDH_out
    (hOut : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt)
    (hsel : PromDecSelRatchetDH sess pf.inner mid coins) :
    ∃ (rngBytes : HwBytes) (remIk : IdentityKey) (ck ck_adv ck_next : ChainKey)
      (r1 r_adv r2 : RatchetState) (mkGen : MessageKeyGenerator) (newPqrState : List (BitVec 8))
      (pqrKey : CryptoGames.HKDF.Salt) (st' : SessionState (List (BitVec 8))),
      mid = [.rng rngBytes] ∧ rngBytes.length = 32 ∧ coins = pinCoins (some rngBytes) ∧
      sess.state.remoteIdentity = some remIk ∧
      (ratchetStateOf sess.state).findReceiverChainKey pf.inner.senderRatchetKey = .ok none ∧
      Mut.exec (RatchetState.dhRatchetStep (cryptoOf' interpretation) pf.inner.senderRatchetKey
        (pinCoins (some rngBytes))) (ratchetStateOf sess.state) = (.ok ck, r1) ∧
      ¬ (pf.inner.counter < ck.index) ∧
      (pf.inner.counter - ck.index).toNat ≤ r1.maxForwardJumps ∧
      Mut.exec (RatchetState.advanceChain (cryptoOf' interpretation).F pf.inner.senderRatchetKey
        pf.inner.counter (pf.inner.counter - ck.index).toNat ck) r1 = (.ok ck_adv, r_adv) ∧
      ck_adv.nextChainKey (cryptoOf' interpretation).F = .ok ck_next ∧
      Mut.exec (RatchetState.setReceiverChainKey pf.inner.senderRatchetKey ck_next) r_adv = (.ok (), r2) ∧
      mkGen = ck_adv.messageKeys (cryptoOf' interpretation).F ∧
      (spqrModelOf interpretation).recv sess.state.pqRatchetState pf.inner.pqRatchet =
        .ok (newPqrState, pqrKey) ∧
      pf.inner.verifyMacWithAddresses (cryptoOf' interpretation).F expected remIk
        sess.state.localIdentity (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).macKey = true ∧
      (interpW interpretation).dec (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).cipherKey
        (mkGen.generateKeys (cryptoOf' interpretation).F pqrKey).iv pf.inner.ciphertext = some pt ∧
      st' = { sess.state with
        rootKey := r2.rootKey, previousCounter := r2.previousCounter, senderChain := r2.senderChain,
        receiverChains := r2.receiverChains, pqRatchetState := newPqrState, pendingPreKey := false } ∧
      sess'.state = st' ∧
      sm.state = CryptoVerification.E2E.Record.encodeRecord ⟨some sess'⟩ := by
  obtain ⟨rngBytes, hmid, hlen, hcoins, hnone⟩ := hsel
  obtain ⟨remIk, r2, mkGen, newPqrState, pqrKey, st', hRem, hSpqr, hDec, hSt', hsess', hstate, hBr⟩ :=
    prom_exec_branch_out hOut
  cases hBr with
  | skipped ck' hFind _ _ _ =>
    obtain ⟨_, rc, _, hrc, hsrk, _⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    exact absurd hsrk (hnone rc (List.mem_of_getElem? hrc))
  | existing ck' _ _ _ hFind _ _ _ _ _ _ _ =>
    obtain ⟨_, rc, _, hrc, hsrk, _⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    exact absurd hsrk (hnone rc (List.mem_of_getElem? hrc))
  | ratchet ck ck_adv ck_next r1 r_adv hFind hDh hNotLt hJump hAdv hNext hSet hMkGen hMac =>
    exact ⟨rngBytes, remIk, ck, ck_adv, ck_next, r1, r_adv, r2, mkGen, newPqrState, pqrKey, st',
      hmid, hlen, hcoins, hRem, hFind, hcoins ▸ hDh, hNotLt, hJump, hAdv, hNext, hSet, hMkGen, hSpqr,
      hMac, hDec, hSt', hsess', hstate⟩

/-- Branch trichotomy over `PromBinAcceptOut` when `mid = []` implies `pureDrawsCoins = false`. -/
theorem prom_decSel_cases_out
    (hOut : PromBinAcceptOut interpretation r rec b mid sm pf sess sess' coins expected pt)
    (hND : mid = [] → pureDrawsCoins (cryptoOf' interpretation) sess.state pf.inner.senderRatchetKey = false) :
    PromDecSelSkipped sess pf.inner mid coins ∨ PromDecSelNoRatchet sess pf.inner mid coins ∨
      PromDecSelRatchetDH sess pf.inner mid coins := by
  obtain ⟨remIk, r2, mkGen, newPqrState, pqrKey, st', hRem, _, _, _, _, _, hBr⟩ :=
    prom_exec_branch_out hOut
  have hfound : ∀ ck : ChainKey,
      (ratchetStateOf sess.state).findReceiverChainKey pf.inner.senderRatchetKey = .ok (some ck) →
      mid = [] ∧ coins = 0#256 := by
    intro ck hFind
    have hdraw : pureDrawsCoins (cryptoOf' interpretation) sess.state pf.inner.senderRatchetKey = false := by
      unfold pureDrawsCoins
      change (sess.state.remoteIdentity.isSome &&
        (match (ratchetStateOf sess.state).findReceiverChainKey pf.inner.senderRatchetKey with
         | .ok none => _
         | _ => false)) = false
      rw [hFind, Bool.and_false]
    rcases hOut.hcoins with ⟨h0, hnil⟩ | ⟨_, _, _, _, hd⟩
    · exact ⟨hnil, h0⟩
    · rw [hdraw] at hd; cases hd
  cases hBr with
  | skipped ck hFind hLt _ _ =>
    obtain ⟨hmid, hcoins⟩ := hfound ck hFind
    obtain ⟨ci, rc, _, hrc, hsrk, hck⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    exact Or.inl ⟨ci, rc, ck, hmid, hcoins, hrc, hsrk, hck, hLt⟩
  | existing ck _ _ _ hFind hNotLt _ _ _ _ _ _ =>
    obtain ⟨hmid, hcoins⟩ := hfound ck hFind
    obtain ⟨ci, rc, _, hrc, hsrk, hck⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    exact Or.inr (Or.inl ⟨ci, rc, ck, hmid, hcoins, hrc, hsrk, hck, BitVec.not_lt.mp hNotLt⟩)
  | ratchet ck _ _ _ _ hFind hDh _ _ _ _ _ _ _ =>
    obtain ⟨sc, newRootKey, _, _, hsc, hcc, _, _⟩ :=
      Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
    have hdraw : pureDrawsCoins (cryptoOf' interpretation) sess.state pf.inner.senderRatchetKey = true := by
      unfold pureDrawsCoins
      have hsc' : sess.state.senderChain = some sc := hsc
      have hcc' : rootCreateChain (cryptoOf' interpretation) sess.state.rootKey
          pf.inner.senderRatchetKey sc.ratchetKey.privateKey = .ok (newRootKey, ck) := hcc
      change (sess.state.remoteIdentity.isSome &&
        (match (ratchetStateOf sess.state).findReceiverChainKey pf.inner.senderRatchetKey with
         | .ok none =>
           match sess.state.senderChain with
           | some sc =>
             match rootCreateChain (cryptoOf' interpretation) sess.state.rootKey
                 pf.inner.senderRatchetKey sc.ratchetKey.privateKey with
             | .ok _ => true
             | .error _ => false
           | none => false
         | _ => false)) = true
      rw [hRem, hFind, hsc']
      dsimp only []
      rw [hcc']
      rfl
    rcases hOut.hcoins with ⟨_, hnil⟩ | ⟨rb, hmid, hlen, hpin, _⟩
    · rw [hND hnil] at hdraw
      cases hdraw
    · exact Or.inr (Or.inr ⟨rb, hmid, hlen, hpin, prom_noChain_of_find_none hFind⟩)

end AdapterOut

end Symbolic.Swarm.CREF.CliPure
