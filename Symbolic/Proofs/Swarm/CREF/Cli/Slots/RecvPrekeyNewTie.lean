/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewWire
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptBinPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SessionPrimsPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewParams
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieAuxPure
import Symbolic.Proofs.RngG.R3ModelInv
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewDecrypt
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewModel
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewSpqrSalt
import Symbolic.Proofs.Swarm.CREF.Cli.Slots.RecvPrekeyNewTieCrypto
import Symbolic.Proofs.Swarm.CREF.Prelude
public import Symbolic.Proofs.Swarm.CREF.RecvPrekeyNew.AcceptTieNormPure -- shake: keep

/-!
# Fresh Pre-Key Receive Acceptance Tie Helpers

Connects Bob's accepting `pqRecvPrekeyModel` execution to `AcceptRecTie`, `RpkAcceptBin`,
`AcceptSt0ModelInvs`, and the MAC/AES-CBC cryptographic postconditions of a fresh pre-key decrypt.
-/

@[expose] public section

set_option autoImplicit false
cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.Cli.Slots
open Symbolic.Swarm.CREF.CliPure

open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.E2E CryptoVerification.E2E.RecordX CryptoVerification.SignalSession
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (StateAndMessage)
open DY.Libsignal.Refinement (sha256CompressFunction aesCbcDecryptSymbol)
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.Composed.Refinement.Cli
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure
open Symbolic.Swarm.CREF.Cli

/-- Derives `AcceptRecTie`, `RpkAcceptBin`, the `< 2^64` state length bound, and the
`opkRemovedIdx` event flag from `PqxdhPartyInSpecDomain` on Bob's post-accept party state. -/
theorem acceptRecTie_and_rpkAcceptBin_of_wfPq
    {P : PEParams} {r : ProtocolSetup} {stB' : PqParty} {me : LocalIdentity} {m : PreKeyMessageFields}
    {inner : SignalMessage} {st' : SessionState HwBytes}
    {x : RecordExtras} {g : GhostState HwBytes} {pt : HwBytes}
    (hwf_st' : PqxdhPartyInSpecDomain P stB') (hsess' : stB'.session = some (x, g))
    (hx : x = responderRecordExtras me m) (hregB : me.regId = r.regIdB)
    (hg : g = ⟨.B, st', 1, [1]⟩) (hppk : st'.pendingPreKey = false)
    (hcl' : ∀ sc, st'.senderChain = some sc →
      Ratchet.clampScalar sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) :
    let pf := rpkNew_preKeyFieldsOf m inner
    let sm : StateAndMessage := ⟨encodeRecordUnderExtras (fun _ => x) g, preKeyStoreEventsBytes m ++ pt⟩
    AcceptRecTie r pf (pf.baseKey.take 33) st' sm ∧
    RpkAcceptBin pf sm ∧ sm.state.length < 2 ^ 64 ∧
    (sm.message[opkRemovedIdx]?).any (· != 0#8) = pf.preKeyId.isSome := by
  intro pf sm
  have hppk_g : g.session.pendingPreKey = false := by rw [hg]; exact hppk
  obtain ⟨hscopeP, hbin, hlen31, henc_eq, _⟩ := rpkNew_record_facts_of_wfPq hwf_st' hsess' hppk_g
  have hbase_take : pf.baseKey.take 33 = djbKey m.baseKey := by
    have hb : pf.baseKey = djbKey m.baseKey := rfl
    have hlen33 : (djbKey m.baseKey).length = 33 := by simp [djbKey]
    rw [hb, List.take_of_length_le (Nat.le_of_eq hlen33)]
  have hpq_eq : pqSession x g = bobNewSession st' (pf.baseKey.take 33) m.regId r.regIdB := by
    have h1 := pqSession_pendingPreKey_of_false x g hppk_g
    have h2 := pqSession_pendingKyberPreKey_of_false x g hppk_g
    unfold bobNewSession
    cases hpq : pqSession x g
    rw [hpq] at h1 h2; dsimp only at h1 h2; subst h1 h2
    have hstate : (pqSession x g).state = st' := by rw [hg]; rfl
    have habk : (pqSession x g).aliceBaseKey = pf.baseKey.take 33 := by
      rw [pqSession_aliceBaseKey, hx, hbase_take]; rfl
    have hrreg : (pqSession x g).remoteRegistrationId = m.regId := by rw [hx]; rfl
    have hlreg : (pqSession x g).localRegistrationId = r.regIdB := by rw [hx, ← hregB]; rfl
    rw [hpq] at hstate habk hrreg hlreg; dsimp only at hstate habk hrreg hlreg
    subst hstate habk hrreg hlreg; rfl
  rw [hpq_eq] at hscopeP hbin henc_eq
  have hrecTie : AcceptRecTie r pf (pf.baseKey.take 33) st' sm := ⟨rfl, m.regId, hscopeP, hbin, henc_eq⟩
  have hkyb : (sm.message[kyberUsedIdx]?).any (· != 0#8) = true := eventsBytes_append_getElem?_zero m pt
  have hbk_slice : slice sm.message 9 33 = pf.baseKey.take 33 := by
    change ((preKeyStoreEventsBytes m ++ pt).drop 9).take 33 = pf.baseKey.take 33
    rw [eventsBytes_append_slice_9_33, hbase_take]
  have hopk_rem : (sm.message[opkRemovedIdx]?).any (· != 0#8) = pf.preKeyId.isSome :=
    eventsBytes_append_getElem?_42 m pt
  have hlen64 : sm.state.length < 2 ^ 64 := by change (encodeRecordUnderExtras (fun _ => x) g).length < 2 ^ 64; omega
  exact ⟨hrecTie, ⟨⟨st', m.regId, r.regIdB, hscopeP, hbin, hcl', henc_eq⟩, hkyb, hbk_slice⟩, hlen64, hopk_rem⟩

theorem vector_eq_ofFn_getD_of_toList_eq {n : Nat} (v : List.Vector (BitVec 8) n) (l : HwBytes)
    (h : v.toList = l) : v = List.Vector.ofFn (fun i => l.getD i.val 0#8) := by
  apply List.Vector.eq
  have hl : l.length = n := h ▸ v.2
  rw [h, List.Vector.toList_ofFn]
  apply List.ext_getElem
  · rw [List.length_ofFn, hl]
  · intro j hj1 _hj2
    rw [List.getElem_ofFn]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1, Option.getD_some]

theorem bobSaltSeedBytes_eq_of_kdf (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (pf : PreKeyFields) (ct_wire : HwBytes) :
    let F := sha256CompressFunction interp
    let ikABytes := pubBytes interp (secretBytes r 0)
    let ikBskBytes := secretBytes r 1
    let spkBytes := secretBytes r 2
    let ek := TR.ekBytes pf
    let dh1 := TR.dhAgreeBytes interp spkBytes ikABytes
    let dh2 := TR.dhAgreeBytes interp ikBskBytes ek
    let dh3 := TR.dhAgreeBytes interp spkBytes ek
    let dh4 := pf.preKeyId.map (fun _ => TR.dhAgreeBytes interp (secretBytes r 6) ek)
    let ss := (kyberDecapsBytes interp r ct_wire).getD []
    let kdf := TR.pqxdhKdfBytes F (TR.pqxdhIkmBytes dh1 dh2 dh3 dh4 ss)
    TR.bobSaltSeedBytes interp r S pf ct_wire =
      (TR.spqrSaltBytes S kdf.2.2 (preKeySpqrIndex pf),
       TR.recvSeedBytes F
         (TR.createChainKeyBytes interp kdf.1 pf.inner.senderRatchetKey.bytes.toList spkBytes)
         pf.inner.counter.toNat) := by
  dsimp only [TR.bobSaltSeedBytes]

/-- Combines `AcceptSt0ModelInvs` and `tryDecryptWithStateW_nil_unpack` to derive the cryptographic
postconditions for Bob's fresh pre-key decrypt. -/
theorem bobSaltSeed_keys_of_st0Invs
    {interp : ExternInterpretation} (hExt : ExternContractsHoldCli interp)
    {r : ProtocolSetup} (hspk_len : (secretBytes r 2).length = 32)
    {pf : PreKeyFields} {expected : Option HwBytes}
    {coins : BitVec 256} {st0 st' : SessionState HwBytes} {pt : HwBytes}
    (hinv : AcceptSt0ModelInvs interp r pf st0)
    (hok : Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
      (Proofs.libsignal.Hooks2.cryptoOf' interp) (Proofs.libsignal.SR.interpW interp)
      (Symbolic.Swarm.CREF.Cli.pureSpqrOf interp) expected pf.inner .preKey coins) st0 =
      (.ok pt, st')) :
    st'.pendingPreKey = false ∧
    (∀ sc1, st'.senderChain = some sc1 →
      Ratchet.clampScalar sc1.ratchetKey.privateKey.bytes = sc1.ratchetKey.privateKey.bytes) ∧
    pf.inner.counter.toNat ≤ DY.Libsignal.TripleRatchet.maxForwardJumps ∧
    pf.inner.pqRatchet ≠ [] ∧
    (((pf.baseKey.take 33).drop 1).length = 32 ∧
      DY.X25519.leValue (((pf.baseKey.take 33).drop 1).map BitVec.toNat) < DY.X25519.p25519 ∧
      DY.X25519.isLowOrderKey (((pf.baseKey.take 33).drop 1).map BitVec.toNat) = false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interp ((pf.baseKey.take 33).drop 1)) ∧
    DY.X25519.isLowOrderKey (pf.inner.senderRatchetKey.bytes.toList.map BitVec.toNat) = false ∧
    (pf.inner.serialized = pf.message ∧ pf.message.length ≥ 8) ∧
    ∃ ct_wire : HwBytes, pf.kyberCiphertext = some (kyberKey ct_wire) ∧ ct_wire.length = 1568 ∧
      (∀ S : OpaqueSymbolSemantics, S.chainKey = Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyOf interp →
        pf.inner.verifyMac (sha256CompressFunction interp)
          ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 0)).getD i.val 0#8)⟩⟩
          ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 1)).getD i.val 0#8)⟩⟩
          (CryptoGames.HKDF.bytesToKey32 (TR.trMacKeyBytes (sha256CompressFunction interp)
            (TR.bobSaltSeedBytes interp r S pf ct_wire).1
            (TR.bobSaltSeedBytes interp r S pf ct_wire).2)) = true) ∧
      (∀ S : OpaqueSymbolSemantics, S.chainKey = Symbolic.Swarm.SHARED.SpqrBytes.spqrChainKeyOf interp →
        interp aesCbcDecryptSymbol
          [pf.inner.ciphertext,
           TR.trCipherKeyBytes (sha256CompressFunction interp)
             (TR.bobSaltSeedBytes interp r S pf ct_wire).1 (TR.bobSaltSeedBytes interp r S pf ct_wire).2,
           (TR.trIvBytes (sha256CompressFunction interp)
             (TR.bobSaltSeedBytes interp r S pf ct_wire).1
             (TR.bobSaltSeedBytes interp r S pf ct_wire).2).take 16] = some pt) := by
  obtain ⟨ct_wire, _hver0, hr0, hct, hct_len, hbase, hmsg, hrem0, hloc0,
    hrk0, ⟨pubKp, hsc0_eq⟩, hpq0⟩ := hinv
  obtain ⟨hppk, hst'_cl, hctr_le, remIk, sc0, newRk, ck, newPqrState, pqrKey,
    hrem1, hsc0_1, hrc1, hspqr, hmac, hdec⟩ := tryDecryptWithStateW_nil_unpack hr0 hok
  have hrem_eq : remIk =
      ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 0)).getD i.val 0#8)⟩⟩ :=
    Option.some.inj (hrem1.symm.trans hrem0)
  have hsc0_val := Option.some.inj (hsc0_1.symm.trans hsc0_eq)
  set F := sha256CompressFunction interp
  set ikABytes := pubBytes interp (secretBytes r 0)
  set ikBskBytes := secretBytes r 1
  set spkBytes := secretBytes r 2
  set ek := TR.ekBytes pf
  set dh1 := TR.dhAgreeBytes interp spkBytes ikABytes
  set dh2 := TR.dhAgreeBytes interp ikBskBytes ek
  set dh3 := TR.dhAgreeBytes interp spkBytes ek
  set dh4 := pf.preKeyId.map (fun _ => TR.dhAgreeBytes interp (secretBytes r 6) ek)
  set ss := (kyberDecapsBytes interp r ct_wire).getD []
  set kdf := TR.pqxdhKdfBytes F (TR.pqxdhIkmBytes dh1 dh2 dh3 dh4 ss)
  have hrk_len : kdf.1.length = 32 := TR.length_hmacWith F _ _
  have hpqr_len : kdf.2.2.length = 32 := TR.length_hmacWith F _ _
  have hsc0_cl : (Ratchet.clampScalar sc0.ratchetKey.privateKey.bytes).toList =
      DY.Libsignal.TripleRatchet.Refinement.clamp spkBytes := by
    rw [hsc0_val]; dsimp only; exact clampScalar_ofFn_clamp_toList hspk_len
  rw [hrk0] at hrc1
  obtain ⟨hlow, hck_eq, hck0_len⟩ :=
    rootCreateChain_ok_bytes_and_not_lowOrder hExt hrk_len hspk_len hsc0_cl hrc1
  have hseed_eq :
      ((CryptoVerification.SessionModel.chainStepN F pf.inner.counter.toNat ck).messageKeys F).seed =
        TR.recvSeedBytes F
          (TR.createChainKeyBytes interp kdf.1 pf.inner.senderRatchetKey.bytes.toList spkBytes)
          pf.inner.counter.toNat := by
    rw [hck_eq]; exact chainStepN_messageKeys_seed_eq_recvSeedBytes F pf.inner.counter.toNat _ 0 hck0_len
  have hsm_eq := spqrModelOf_eq_hookAuth_of_ext hExt
  have hspqr' := hspqr
  rw [hpq0, hsm_eq] at hspqr'
  have hspqr_sem :
      (Symbolic.Swarm.SHARED.HookAuth.spqrV1WithMac (sha256CompressFunction interp)
          (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp)
          (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp)).recv
        (Symbolic.Swarm.SHARED.SpqrBytes.spqrInitB (sha256CompressFunction interp)
          (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp)
          (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp) kdf.2.2 [1#8])
        pf.inner.pqRatchet = .ok (newPqrState, pqrKey) := hspqr'
  have hpq_ne : pf.inner.pqRatchet ≠ [] :=
    spqrV1WithMac_recv_spqrInitB_ok_pqRatchet_ne_nil hpqr_len hspqr_sem
  refine ⟨hppk, hst'_cl, hctr_le, hpq_ne, hbase, hlow, hmsg, ct_wire, hct, hct_len, ?_, ?_⟩
  · intro S hS_ck
    have hprk := spqr_hkdfExtract_eq_hmacWith_spqrSaltBytes_sem interp S hS_ck pf
      kdf.2.2 newPqrState pqrKey
      (TR.recvSeedBytes F (TR.createChainKeyBytes interp kdf.1 pf.inner.senderRatchetKey.bytes.toList spkBytes)
        pf.inner.counter.toNat)
      hpqr_len hspqr_sem
    have hbss := bobSaltSeedBytes_eq_of_kdf interp r S pf ct_wire
    have hprk_bss :
        CryptoGames.HKDF.hkdfExtract F pqrKey
          ((CryptoVerification.SessionModel.chainStepN F pf.inner.counter.toNat ck).messageKeys F).seed =
        CryptoGames.HMAC.hmacWith F
          (TR.bobSaltSeedBytes interp r S pf ct_wire).1
          (TR.bobSaltSeedBytes interp r S pf ct_wire).2 := by
      rw [hbss, hseed_eq]; exact hprk
    obtain ⟨_, _, _, hm_key⟩ := generateKeys_eq_trMsgKeys_of_prk F _ pqrKey _ _ hprk_bss
    rw [← hm_key, ← hrem_eq, ← hloc0]; exact hmac
  · intro S hS_ck
    have hprk := spqr_hkdfExtract_eq_hmacWith_spqrSaltBytes_sem interp S hS_ck pf
      kdf.2.2 newPqrState pqrKey
      (TR.recvSeedBytes F (TR.createChainKeyBytes interp kdf.1 pf.inner.senderRatchetKey.bytes.toList spkBytes)
        pf.inner.counter.toNat)
      hpqr_len hspqr_sem
    have hbss := bobSaltSeedBytes_eq_of_kdf interp r S pf ct_wire
    have hprk_bss :
        CryptoGames.HKDF.hkdfExtract F pqrKey
          ((CryptoVerification.SessionModel.chainStepN F pf.inner.counter.toNat ck).messageKeys F).seed =
        CryptoGames.HMAC.hmacWith F
          (TR.bobSaltSeedBytes interp r S pf ct_wire).1
          (TR.bobSaltSeedBytes interp r S pf ct_wire).2 := by
      rw [hbss, hseed_eq]; exact hprk
    obtain ⟨hc_key, _, hiv_blk, _⟩ := generateKeys_eq_trMsgKeys_of_prk F _ pqrKey _ _ hprk_bss
    rw [← hc_key, ← hiv_blk]; exact hdec

theorem tryDecryptFromRecord_ok_to_emptyAsNone
    {interp : ExternInterpretation} {P : PEParams}
    (hExt : ExternContractsHoldCli interp) (hb : RpkModelHookBridge interp P)
    {expected : Option HwBytes} {msg : SignalMessage} {ty : MessageType}
    {coins : BitVec 256} {st0 st' : SessionState HwBytes} {pt : HwBytes}
    (hdec : SessionState.tryDecryptFromRecord P.C (pqxdhSpqrSession P)
      expected msg ty coins st0 = (.ok pt, st')) :
    st0.version.toNat = msg.messageVersion.toNat ∧
    Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
      (Proofs.libsignal.Hooks2.cryptoOf' interp) (Proofs.libsignal.SR.interpW interp)
      (Symbolic.Swarm.CREF.Cli.pureSpqrOf interp) expected msg ty coins) st0 = (.ok pt, st') ∧
    Mut.exec (Proofs.libsignal.SR.SessionState.tryDecryptWithStateW
      (Proofs.libsignal.Hooks2.cryptoOf' interp) (Proofs.libsignal.SR.interpW interp)
      (Symbolic.Swarm.CREF.CliPure.pureSpqrEmptyAsNone (sha256CompressFunction interp)
        (Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp)
        (Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp))
      expected msg ty coins) st0 = (.ok pt, st') := by
  rw [tryDecryptFromRecord_eq_tryDecryptFromRecordW_of_rpkBridge hb] at hdec
  obtain ⟨hver, hdecW⟩ := Proofs.libsignal.RngG.R3.tryDecryptFromRecordW_ok_inv hdec
  have hsm := spqrModelOf_eq_hookAuth_of_ext hExt
  refine ⟨hver, hdecW, tryDecryptWithStateW_emptyAsNone_of_spqrV1WithMac_ok hdecW ?_ ?_ rfl⟩
  · show _ = (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp).recvPanics
    rw [hsm]; rfl
  · show (Symbolic.Swarm.TRREF.SpqrSemOf.spqrModelOf interp).recv = _
    rw [hsm]

theorem signalMessage_tryFrom_ok_serialized_and_len
    {codec : SignalMessageProtoCodec} {value : HwBytes} {inner : SignalMessage}
    (hok : SignalMessage.tryFrom codec value = .ok inner) :
    inner.serialized = value ∧ value.length ≥ 8 := by
  unfold SignalMessage.tryFrom at hok
  dsimp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at hok
  split at hok
  · cases hok
  · rename_i hlen; have hm : macLength = 8 := rfl
    split at hok
    · cases hok
    · split at hok
      · cases hok
      · split at hok
        · split at hok
          · rcases hrk : PublicKey.deserialize _ with _ | v
            · rw [hrk] at hok; cases hok
            · rw [hrk] at hok; dsimp only at hok
              split at hok
              · split at hok
                · injection hok with h; subst h; exact ⟨rfl, by omega⟩
                · cases hok
              · cases hok
          · cases hok
        · cases hok

theorem verifyMac_true_eq_computeMac
    {F : CryptoGames.LibsignalSession.ShaCompress} {m : SignalMessage} {msg : HwBytes}
    {sender receiver : IdentityKey} {macKey : BitVec 256}
    (hser : m.serialized = msg) (hv : m.verifyMac F sender receiver macKey = true) :
    CryptoGames.LibsignalSession.computeMac F sender receiver macKey
      (msg.take (msg.length - 8)) = msg.drop (msg.length - 8) := by
  unfold SignalMessage.verifyMac at hv; rw [hser] at hv; exact beq_iff_eq.mp hv

theorem initializeRecipientSession_fields {PQ PQC : Type}
    (spqr : Spqr PQ PQC) (ourId theirId : IdentityKey) (ourSpk : KeyPair)
    (rk ck pqr : BitVec 256) :
    let st0 := initializeRecipientSession spqr ourId theirId ourSpk rk ck pqr
    st0.sessionVersion = 4#32 ∧ st0.receiverChains = [] ∧ st0.localIdentity = ourId ∧
    st0.remoteIdentity = some theirId ∧ st0.rootKey = rk ∧
    st0.senderChain = some ⟨ourSpk, ⟨ck, 0#32⟩⟩ ∧ st0.pqRatchetState = spqr.init .b2a pqr :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bobExpectedMacBytes_eq_computeMacBytes
    (interp : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (pf : PreKeyFields) (ct_wire : HwBytes) :
    TR.bobExpectedMacBytes interp r S pf ct_wire =
      TR.computeMacBytes (sha256CompressFunction interp)
        (TR.trMacKeyBytes (sha256CompressFunction interp)
          (TR.bobSaltSeedBytes interp r S pf ct_wire).1
          (TR.bobSaltSeedBytes interp r S pf ct_wire).2)
        (ecKey (pubBytes interp (secretBytes r 0)))
        (ecKey (pubBytes interp (secretBytes r 1)))
        (pf.message.take (pf.message.length - 8)) := by
  dsimp only [TR.bobExpectedMacBytes, TR.bobSaltSeedBytes]

theorem toList_ofFn_getD_32 {b : HwBytes} (hb : b.length = 32) :
    (List.Vector.ofFn (n := 32) (fun i => b.getD i.val 0#8)).toList = b := by
  rw [List.Vector.toList_ofFn]; apply List.ext_getElem
  · rw [List.length_ofFn, hb]
  · intro j hj1 hj2
    rw [List.getElem_ofFn, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some]

theorem identityKey_serialize_ofFn_getD {b : HwBytes} (hb : b.length = 32) :
    (IdentityKey.mk ⟨List.Vector.ofFn (n := 32) (fun i => b.getD i.val 0#8)⟩).serialize =
      0x05#8 :: b := by
  unfold IdentityKey.serialize PublicKey.serialize djbType; rw [toList_ofFn_getD_32 hb]; rfl

theorem serialize_ofFn_eq_ecKey {b : HwBytes} (hb : b.length = 32) :
    (IdentityKey.mk ⟨List.Vector.ofFn (n := 32) (fun i => b.getD i.val 0#8)⟩).serialize =
      ecKey b := by
  rw [identityKey_serialize_ofFn_getD hb]; rfl

private theorem macIds_toList (a b : IdentityKey) :
    (CryptoGames.LibsignalSession.macIds a b).toList = a.serialize ++ b.serialize := rfl

theorem verifyMac_true_imp_bobExpectedMacBytes
    {interp : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics}
    {pf : PreKeyFields} {ct_wire : HwBytes}
    (hp0 : (pubBytes interp (secretBytes r 0)).length = 32)
    (hp1 : (pubBytes interp (secretBytes r 1)).length = 32)
    (hser : pf.inner.serialized = pf.message)
    (hv : pf.inner.verifyMac (sha256CompressFunction interp)
      ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 0)).getD i.val 0#8)⟩⟩
      ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 1)).getD i.val 0#8)⟩⟩
      (CryptoGames.HKDF.bytesToKey32 (TR.trMacKeyBytes (sha256CompressFunction interp)
        (TR.bobSaltSeedBytes interp r S pf ct_wire).1
        (TR.bobSaltSeedBytes interp r S pf ct_wire).2)) = true) :
    TR.bobExpectedMacBytes interp r S pf ct_wire =
      pf.message.drop (pf.message.length - 8) := by
  have hm_eq := verifyMac_true_eq_computeMac hser hv
  set F := sha256CompressFunction interp
  set mk := TR.trMacKeyBytes F (TR.bobSaltSeedBytes interp r S pf ct_wire).1
    (TR.bobSaltSeedBytes interp r S pf ct_wire).2
  have hmk_len : mk.length = 32 := TR.length_hmacWith F _ _
  have hhmac_bs : CryptoGames.HMAC.hmacWith = ByteSpecs.hmacWith := rfl
  unfold CryptoGames.LibsignalSession.computeMac CryptoGames.HMAC.hmacSha256Trunc8 at hm_eq
  rw [macIds_toList,
      Proofs.libsignal.RngG.CliPure.DecCrypto.keyToBytes32_bytesToKey32_of_length_eq_32 mk hmk_len,
      serialize_ofFn_eq_ecKey hp0, serialize_ofFn_eq_ecKey hp1, hhmac_bs] at hm_eq
  rw [bobExpectedMacBytes_eq_computeMacBytes]
  simpa [TR.computeMacBytes, List.append_assoc] using hm_eq

theorem clampScalar_bytesToVec_eq_ofFn_clamp {b : HwBytes} (hb : b.length = 32) :
    Ratchet.clampScalar (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 b) =
      List.Vector.ofFn (fun i => (DY.Libsignal.TripleRatchet.Refinement.clamp b).getD i.val 0#8) := by
  apply vector_eq_ofFn_getD_of_toList_eq
  rw [Proofs.libsignal.RngG.CliPure.DecCrypto.clampScalar_toList_eq_clamp_toList, bytesToVec_toList_of_len hb]

theorem keyPairOf_bytesToVec_privateKey_eq_ofFn (C : Crypto) {b : HwBytes} (hb : b.length = 32) :
    (keyPairOf C (Symbolic.Swarm.TRREF.SpqrSemOf.bytesToVec 32 b)).privateKey.bytes =
      List.Vector.ofFn (fun i => (DY.Libsignal.TripleRatchet.Refinement.clamp b).getD i.val 0#8) :=
  clampScalar_bytesToVec_eq_ofFn_clamp hb

/-- Establishes `AcceptSt0ModelInvs` and the clamped sender-chain private-key invariant for
`initializeRecipientSession`. -/
theorem acceptSt0ModelInvs_of_initializeRecipientSession
    {PQC : Type} (spqr : Spqr HwBytes PQC)
    {interp : ExternInterpretation} {r : ProtocolSetup} {p : PreKeyFields}
    {ourId theirId : IdentityKey} {ourSpk : KeyPair}
    {rk0 ck0 pqr0 ct_wire : HwBytes}
    (hct : p.kyberCiphertext = some (kyberKey ct_wire)) (hct_len : ct_wire.length = 1568)
    (hbase : ((p.baseKey.take 33).drop 1).length = 32 ∧
      DY.X25519.leValue (((p.baseKey.take 33).drop 1).map BitVec.toNat) < DY.X25519.p25519 ∧
      DY.X25519.isLowOrderKey (((p.baseKey.take 33).drop 1).map BitVec.toNat) = false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interp ((p.baseKey.take 33).drop 1))
    (hmsg : p.inner.serialized = p.message ∧ p.message.length ≥ 8)
    (htheir : theirId =
      ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 0)).getD i.val 0#8)⟩⟩)
    (hour : ourId =
      ⟨⟨List.Vector.ofFn (fun i => (pubBytes interp (secretBytes r 1)).getD i.val 0#8)⟩⟩)
    (hspk_priv : ourSpk.privateKey.bytes =
      List.Vector.ofFn (fun i =>
        (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)).getD i.val 0#8))
    (hkdf :
      let F := sha256CompressFunction interp
      let dh1 := TR.dhAgreeBytes interp (secretBytes r 2) (pubBytes interp (secretBytes r 0))
      let dh2 := TR.dhAgreeBytes interp (secretBytes r 1) (TR.ekBytes p)
      let dh3 := TR.dhAgreeBytes interp (secretBytes r 2) (TR.ekBytes p)
      let dh4 := p.preKeyId.map (fun _ => TR.dhAgreeBytes interp (secretBytes r 6) (TR.ekBytes p))
      let ss := (kyberDecapsBytes interp r ct_wire).getD []
      let kdf := TR.pqxdhKdfBytes F (TR.pqxdhIkmBytes dh1 dh2 dh3 dh4 ss)
      rk0 = kdf.1 ∧ ck0 = kdf.2.1 ∧
      spqr.init .b2a (CryptoGames.HKDF.bytesToKey32 pqr0) =
        Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf interp kdf.2.2 [1#8]) :
    let st0 := initializeRecipientSession spqr ourId theirId ourSpk
      (CryptoGames.HKDF.bytesToKey32 rk0)
      (CryptoGames.HKDF.bytesToKey32 ck0)
      (CryptoGames.HKDF.bytesToKey32 pqr0)
    AcceptSt0ModelInvs interp r p st0 ∧
    (∀ sc, st0.senderChain = some sc →
      sc.ratchetKey.privateKey.bytes =
        List.Vector.ofFn (fun i =>
          (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)).getD i.val 0#8)) := by
  intro st0
  obtain ⟨hv, hrc, hloc, hrem, hrk_st0, hsc_st0, hpq_st0⟩ :=
    initializeRecipientSession_fields spqr ourId theirId ourSpk
      (CryptoGames.HKDF.bytesToKey32 rk0) (CryptoGames.HKDF.bytesToKey32 ck0)
      (CryptoGames.HKDF.bytesToKey32 pqr0)
  dsimp only at hkdf
  obtain ⟨hrk_eq, hck_eq, hpq_eq⟩ := hkdf
  refine ⟨⟨ct_wire, hv, hrc, hct, hct_len, hbase, hmsg, ?_, ?_, ?_⟩, ?_⟩
  · rw [hrem, htheir]
  · rw [hloc, hour]
  · dsimp only
    refine ⟨?_, ⟨ourSpk.publicKey, ?_⟩, ?_⟩
    · change st0.rootKey = _; rw [hrk_st0, hrk_eq]
    · change st0.senderChain = _
      rw [hsc_st0, hck_eq]
      cases ourSpk with | mk pub priv =>
      cases priv with | mk bytes =>
      dsimp only at hspk_priv; subst hspk_priv; rfl
    · change st0.pqRatchetState = _; rw [hpq_st0, hpq_eq]
  · intro sc hsc
    change st0.senderChain = some sc at hsc
    rw [hsc_st0] at hsc; injection hsc with hsc'; rw [← hsc']; exact hspk_priv

theorem spqrPq_init_b2a_eq_spqrInitOf
    {interp : ExternInterpretation} {P : PEParams} (hagree : ModelAgree interp P)
    (hmlkem : Symbolic.Swarm.SHARED.HookAuth.mlkemOf interp = P.Q.K)
    (hhmac : Symbolic.Swarm.SHARED.HookAuth.hmacFnOf interp =
      Symbolic.Swarm.SHARED.HookAuth.hmacFnOfSha P.C.F)
    {pqr : HwBytes} (hpqr : pqr.length = 32) :
    (pqxdhSpqrSession P).init .b2a (CryptoGames.HKDF.bytesToKey32 pqr) =
      Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf interp pqr [1#8] := by
  unfold pqxdhSpqrSession CryptoVerification.LibsignalSpqrV1.spqrV1Session
    CryptoVerification.LibsignalTripleRatchet.SpqrModel.spqrWith
    CryptoVerification.LibsignalSpqrV1.spqrV1Init
    CryptoVerification.LibsignalSpqrV1.spqrV1InitialStateFor
    Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf Symbolic.Swarm.SHARED.SpqrBytes.spqrInitB
  dsimp only
  have hdir : Symbolic.Swarm.SHARED.SpqrBytes.spqrDirOfParams? [1#8] = some .b2a := rfl
  have hkey : CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 pqr) = pqr :=
    Proofs.libsignal.RngG.CliPure.DecCrypto.keyToBytes32_bytesToKey32_of_length_eq_32 pqr hpqr
  rw [hdir, hhmac, hmlkem, ← hagree.1, Symbolic.Swarm.SHARED.HookAuth.spqrDepsWithMac_hmacFnOfSha]
  dsimp only [CryptoVerification.LibsignalSpqrV1.libsignalSpqrParams,
    CryptoVerification.LibsignalSpqrV1.Direction.ofSpqrDirection]
  rw [hkey]; rfl

end Symbolic.Swarm.CREF.Cli.Slots
