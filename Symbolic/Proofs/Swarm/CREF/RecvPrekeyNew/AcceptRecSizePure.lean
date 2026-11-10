/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieNormPure
public import Symbolic.Proofs.Swarm.CREF.RelPure
import Symbolic.Proofs.Swarm.CREF.Grow.PqInit
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptRecRelT1PureA
import Symbolic.Proofs.Swarm.CREF.TR.RecordBytesInj
import Symbolic.Proofs.Swarm.SHARED.HmacLen
import Symbolic.Proofs.Swarm.TRREF.GrowthRecvPure.TopPure
import Symbolic.Proofs.Swarm.TRREF.MacFormBridge

/-!
# SPQR Out-of-Order Bound for Bob's New Session Record

Proves `SpqrOooBounded` for the post-decrypt SPQR state and returned session record `sm.state` of
an accepting `session_recv_prekey` call.
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
open Proofs.libsignal.SR (interpW)
open Symbolic.Swarm.CREF (SpqrOooBounded pqStateOf is1StateRaw_encodeRaw_length_lt_2_32)
open Symbolic.Swarm.CREF.CliPure (AcceptSt0ModelInvs pureSpqrEmptyAsNone
  rpkT1_recordBytes_of_binSessionInv)
open Symbolic.Swarm.CREF.CliPure.RpkCli (pureCoinsOf)

private theorem pqStateOf_recordBytes_aux (recR : RecordRec) :
    pqStateOf (recordBytes recR) = recR.current.pqRatchetState := by
  have hex : ∃ r' : RecordRec, recordBytes recR = recordBytes r' := ⟨recR, rfl⟩
  simp only [pqStateOf, hex, ↓reduceDIte]
  exact congrArg (fun r => r.current.pqRatchetState)
    (TR.recordBytes_injective (Classical.choose_spec hex).symm)

theorem spqrSemOf_spqrRecvB_of_spqrV1WithMacEmptyAsNone_recv_ok
    (F : ShaCompress) (K : CryptoVerification.LibsignalSpqrV1.MlKem)
    {mac : Symbolic.Swarm.SHARED.HookAuth.HmacFn}
    (hmac_len : ∀ k d t, mac k d = some t → t.length = 32)
    (st msg newPqrState : HwBytes) (pqrKey : CryptoGames.HKDF.Salt)
    (hspqr : (pureSpqrEmptyAsNone F K mac).recv st msg = .ok (newPqrState, pqrKey)) :
    ∃ key? : Option HwBytes,
      Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvB F K mac st msg = some (newPqrState, key?) := by
  unfold Symbolic.Swarm.TRREF.SpqrSemOf.spqrRecvB
    Symbolic.Swarm.TRREF.SpqrSemOf.spqrV1RecvWithMac
  rw [Symbolic.Swarm.TRREF.MacFormBridge.spqrDepsWithMac_spqrSemOf_eq_hookAuth F K hmac_len]
  unfold pureSpqrEmptyAsNone
    Symbolic.Swarm.SHARED.HookAuth.spqrV1RecvWithMac
    CryptoVerification.LibsignalSpqrV1.toSpqrRecvModel at hspqr
  unfold CryptoVerification.LibsignalSpqrV1.toSpqrRecvModel
  dsimp only at hspqr ⊢
  cases hraw : CryptoVerification.LibsignalSpqrV1.recv
      (Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac F K mac)
      (CryptoVerification.LibsignalSpqrV1.spqrHkdfWith F) st msg with
  | error e => rw [hraw] at hspqr; cases e <;> contradiction
  | ok out =>
    rw [hraw] at hspqr; dsimp only at hspqr ⊢
    injection hspqr with hpair
    obtain ⟨hst_eq, _⟩ := Prod.mk.inj hpair
    subst hst_eq
    exact ⟨out.key, rfl⟩

/-- `SpqrOooBounded` holds on `st'.pqRatchetState` after Bob's initial pre-key decrypt. -/
theorem spqrOoo_of_acceptDecrypt {interpretation : ExternInterpretation}
    (hCrypto : ExternCryptoLawsHold interpretation)
    {r : ProtocolSetup} {p : PreKeyFields} {st0 st' : SessionState HwBytes} {expected : Option HwBytes}
    {d pt : HwBytes}
    (hinv : AcceptSt0ModelInvs interpretation r p st0)
    (hdec : Mut.exec
      (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
        (Proofs.libsignal.Hooks2.cryptoOf' interpretation) (interpW interpretation)
        (pureSpqrEmptyAsNone (sha256CompressFunction interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interpretation)
          (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interpretation))
        expected p.inner .preKey (pureCoinsOf d)) st0 = (.ok pt, st')) :
    SpqrOooBounded st'.pqRatchetState := by
  obtain ⟨_remIk, tr_out, _, hTr, hSt'⟩ := Proofs.libsignal.RngG.R3.tryDecryptWithStateW_ok_inv hdec
  obtain ⟨_ck, _r1, _r2, _mkGen, newPqrState, pqrKey, _, _, hspqr, _, _, hTrOut⟩ :=
    Proofs.libsignal.RngG.R3.tripleRatchet_decryptW_ok_inv hTr
  dsimp only at hspqr
  have hmac_len := Symbolic.Swarm.SHARED.HmacLen.hmacLen_of_ceh hCrypto
  obtain ⟨key?, hB⟩ :=
    spqrSemOf_spqrRecvB_of_spqrV1WithMacEmptyAsNone_recv_ok
      _ _ hmac_len _ _ _ _ hspqr
  have hpq' : st'.pqRatchetState = newPqrState := by rw [hSt', hTrOut]
  rw [hpq']
  obtain ⟨ct_wire, _, _, _, _, _, _, _, _, _, _, hst0_pq⟩ := hinv
  let F := sha256CompressFunction interpretation
  let pqr := (TR.pqxdhKdfBytes F (TR.pqxdhIkmBytes
    (TR.dhAgreeBytes interpretation (secretBytes r 2) (pubBytes interpretation (secretBytes r 0)))
    (TR.dhAgreeBytes interpretation (secretBytes r 1) (TR.ekBytes p))
    (TR.dhAgreeBytes interpretation (secretBytes r 2) (TR.ekBytes p))
    (p.preKeyId.map (fun _ => TR.dhAgreeBytes interpretation (secretBytes r 6) (TR.ekBytes p)))
    ((kyberDecapsBytes interpretation r ct_wire).getD []))).2.2
  have hpqr32 : pqr.length = 32 := TR.length_hmacWith _ _ _
  refine (Symbolic.Swarm.TRREF.GrowthRecvPure.spqr_recv_growth _ _ _ _ _ _ _ ?_ ?_ hB).1
  · rw [hst0_pq, Grow.spqrInitOf_b2a_eq_is1StateRaw]
    exact Grow.spqrOooBounded_is1StateRaw F .b2a pqr (by omega)
  · rw [hst0_pq, Grow.spqrInitOf_b2a_eq_is1StateRaw]
    exact is1StateRaw_encodeRaw_length_lt_2_32 F .b2a pqr (by omega)

/-- `SpqrOooBounded` holds on `pqStateOf sm.state` for Bob's returned session record under
`AcceptTieD`. -/
theorem newOoo_of_acceptTieD {interpretation : ExternInterpretation}
    (hCrypto : ExternCryptoLawsHold interpretation)
    {r : ProtocolSetup} (_hwf : ProtocolSetupWF r) {p : PreKeyFields} {d pt : HwBytes} {sm : StateAndMessage}
    (_hbase : ((p.baseKey.take 33).drop 1).length = 32)
    (htie : AcceptTieD interpretation r p d pt sm) :
    SpqrOooBounded (pqStateOf sm.state) := by
  obtain ⟨st0, st', _expected, hrt, hinv, _hsk, hdec⟩ := htie
  obtain ⟨_, _f248, _hscope, hbin, hstate⟩ := hrt
  have hbytes := rpkT1_recordBytes_of_binSessionInv hbin hstate
  rw [hbytes, pqStateOf_recordBytes_aux]
  exact spqrOoo_of_acceptDecrypt hCrypto hinv hdec

end Symbolic.Swarm.CREF.CliPure.AcceptD
