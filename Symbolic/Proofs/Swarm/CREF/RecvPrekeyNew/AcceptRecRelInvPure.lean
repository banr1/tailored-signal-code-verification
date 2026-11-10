/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieAuxPure
public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.SR.SendSpecWPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SessionPrimsPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure
import Symbolic.Proofs.Swarm.CREF.Prelude

/-!
# Ratchet-Branch Inversion for Pre-Key Session Decryption

Inverts an accepting `tryDecryptWithStateW` execution on a fresh pre-key session state with no
existing receiver chains into the DH ratchet step, chain advance, MAC verification, and AES-CBC
decryption witnesses.
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
open DY.Libsignal.Refinement (sha256CompressFunction)
open DY.Libsignal.PQXDH
open Proofs.libsignal.SR (interpW)
open Symbolic.Swarm.CREF.CliPure (AcceptRecTie AcceptSt0ModelInvs pureSpqrEmptyAsNone)
open Symbolic.Swarm.CREF.CliPure.RpkCli (pureCoinsOf)

theorem rpkI_acceptTieD_ratchet_inv {interpretation : ExternInterpretation} {r : ProtocolSetup}
    {p : PreKeyFields} {d pt : HwBytes} {sm : StateAndMessage}
    (h : ∃ (st0 st' : SessionState HwBytes) (expected : Option HwBytes),
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
          expected p.inner .preKey (pureCoinsOf d)) st0 = (.ok pt, st')) :
    let C := Proofs.libsignal.Hooks2.cryptoOf' interpretation
    let F := sha256CompressFunction interpretation
    let their := p.inner.senderRatchetKey
    ∃ (st0 st' : SessionState HwBytes) (expected : Option HwBytes) (remIk : IdentityKey)
      (ck ck_adv ck_next : ChainKey) (r1 r_adv r2 : RatchetState) (newPqrState : HwBytes)
      (pqrKey : CryptoGames.HKDF.Salt) (f248 : BitVec 32),
      AcceptSt0ModelInvs interpretation r p st0 ∧
      (∀ sc, st0.senderChain = some sc → sc.ratchetKey.privateKey.bytes =
        List.Vector.ofFn (fun i =>
          (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)).getD i.val 0#8)) ∧
      st0.remoteIdentity = some remIk ∧
      (pureSpqrEmptyAsNone (sha256CompressFunction interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interpretation)).recv
        st0.pqRatchetState p.inner.pqRatchet = .ok (newPqrState, pqrKey) ∧
      (Proofs.libsignal.RngG.R3.ratchetStateOf st0).findReceiverChainKey their = .ok none ∧
      Mut.exec (RatchetState.dhRatchetStep C their (pureCoinsOf d))
        (Proofs.libsignal.RngG.R3.ratchetStateOf st0) = (.ok ck, r1) ∧
      ck.index = 0 ∧
      ¬ (p.inner.counter < ck.index) ∧
      (p.inner.counter - ck.index).toNat ≤ CryptoGames.LibsignalSession.maxForwardJumps ∧
      Mut.exec (RatchetState.advanceChain F their p.inner.counter
        (p.inner.counter - ck.index).toNat ck) r1 = (.ok ck_adv, r_adv) ∧
      ck_adv.nextChainKey F = .ok ck_next ∧
      Mut.exec (RatchetState.setReceiverChainKey their ck_next) r_adv = (.ok (), r2) ∧
      p.inner.verifyMacWithAddresses F expected remIk st0.localIdentity
        ((ck_adv.messageKeys F).generateKeys F pqrKey).macKey = true ∧
      (Proofs.libsignal.SR.interpW interpretation).dec
        ((ck_adv.messageKeys F).generateKeys F pqrKey).cipherKey
        ((ck_adv.messageKeys F).generateKeys F pqrKey).iv p.inner.ciphertext = some pt ∧
      st' = { st0 with
        rootKey := r2.rootKey, previousCounter := r2.previousCounter,
        senderChain := r2.senderChain, receiverChains := r2.receiverChains,
        pqRatchetState := newPqrState, pendingPreKey := false } ∧
      sm.state = CryptoVerification.E2E.Record.encodeRecord
        ⟨some { state := st', pendingPreKey := none, pendingKyberPreKey := none,
                aliceBaseKey := p.baseKey.take 33, remoteRegistrationId := f248,
                localRegistrationId := r.regIdB }⟩ := by
  obtain ⟨st0, st', expected, hrt, hinv, hsk, hdec⟩ := h
  obtain ⟨_, f248, _hscope, _hbin, hstate⟩ := hrt
  have ⟨_ct_wire, _hver, hrc_empty, _⟩ := hinv
  obtain ⟨remIk, tr_out, hRem, hTr, hSt2⟩ :=
    Proofs.libsignal.RngG.R3.tryDecryptWithStateW_ok_inv hdec
  obtain ⟨ck0, r1_0, r2, mkGen, newPqrState, pqrKey,
      hEnsure, hConsume, hSpqr, hMac, hDec, hTrOut⟩ :=
    Proofs.libsignal.RngG.R3.tripleRatchet_decryptW_ok_inv hTr
  have hSt' : st' = { st0 with
      rootKey := r2.rootKey, previousCounter := r2.previousCounter,
      senderChain := r2.senderChain, receiverChains := r2.receiverChains,
      pqRatchetState := newPqrState, pendingPreKey := false } := by
    rw [hSt2, hTrOut]
  have hBr :=
    Proofs.libsignal.RngG.R3.decryptOkBranch_of_ensure_consume hEnsure hConsume hMac
  cases hBr with
  | skipped ck' hFind _ _ _ =>
    obtain ⟨ci', rc', _, hrc', _, _⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    have hmem : rc' ∈ st0.receiverChains := List.mem_of_getElem? hrc'
    rw [hrc_empty] at hmem; cases hmem
  | existing ck' _ _ _ hFind _ _ _ _ _ _ _ =>
    obtain ⟨ci', rc', _, hrc', _, _⟩ :=
      Proofs.libsignal.RngG.CliPure.R3.findReceiverChainKey_ok_some _ _ _ hFind
    have hmem : rc' ∈ st0.receiverChains := List.mem_of_getElem? hrc'
    rw [hrc_empty] at hmem; cases hmem
  | ratchet ck ck_adv ck_next r1 r_adv hFind hDh hNotLt hJump hAdv hNext hSet hMkGen hMac' =>
    have hIdx0 : ck.index = 0 := Proofs.libsignal.RngG.R3.dhRatchetStep_ok_index_eq_zero hDh
    obtain ⟨_sc, _newRk, _finalRk, _senderCk, _, _, _, hr1_eq⟩ :=
      Proofs.libsignal.RngG.R3.dhRatchetStep_ok_inv hDh
    have hJump' : (p.inner.counter - ck.index).toNat ≤
        CryptoGames.LibsignalSession.maxForwardJumps := by
      have hmfj : r1.maxForwardJumps = CryptoGames.LibsignalSession.maxForwardJumps := by
        rw [hr1_eq]
      omega
    subst hMkGen
    exact ⟨st0, st', expected, remIk, ck, ck_adv, ck_next, r1, r_adv, r2,
      newPqrState, pqrKey, f248, hinv, hsk, hRem, hSpqr, hFind, hDh, hIdx0, hNotLt, hJump',
      hAdv, hNext, hSet, hMac', hDec, hSt', hstate⟩

end Symbolic.Swarm.CREF.CliPure.AcceptD

namespace Symbolic.Swarm.CREF.CliPure

export AcceptD (rpkI_acceptTieD_ratchet_inv)

end Symbolic.Swarm.CREF.CliPure
