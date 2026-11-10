/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.GhostsPure
public import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
public import Symbolic.Proofs.Swarm.CREF.TR.PureSessionBounds
public import Symbolic.Proofs.Refinement.RecordBytesBridge
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredStatementDefs
public import Symbolic.Proofs.Swarm.SHARED.SpqrBytesDefs
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Prelude
public import Symbolic.Proofs.Refinement.LemmasPure -- shake: keep

/-!
# Pre-Decrypt Invariants and Initial `StateRel` for Pre-Key Accept

Defines `AcceptRecTie` and `AcceptSt0ModelInvs`, and proves `rpkTie_stateRel_init`, establishing
that Bob's pre-decrypt `SessionState HwBytes` is `TR.StateRel`-related to `bobInitSt`.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.CliPure

cref_open
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.Refinement (ExternCryptoLawsHold sha256CompressFunction x25519PublicKeySymbol)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec)
open ByteSpecs (hmacWith)

/-- Record-encoding and base-key invariants for an accepting pre-key output `sm`. -/
def AcceptRecTie (r : ProtocolSetup) (p : PreKeyFields) (baseKey : HwBytes)
    (st' : SessionState HwBytes) (sm : StateAndMessage) : Prop :=
  baseKey = p.baseKey.take 33 ∧
  ∃ f248 : BitVec 32,
    TR.Pure.slots_RecordInScopeP
      ⟨some { state := st', pendingPreKey := none, pendingKyberPreKey := none,
              aliceBaseKey := p.baseKey.take 33, remoteRegistrationId := f248,
              localRegistrationId := r.regIdB }⟩ ∧
    TR.Pure.BinSessionInv
      { state := st', pendingPreKey := none, pendingKyberPreKey := none,
        aliceBaseKey := p.baseKey.take 33, remoteRegistrationId := f248,
        localRegistrationId := r.regIdB } ∧
    sm.state = CryptoVerification.E2E.Record.encodeRecord
      ⟨some { state := st', pendingPreKey := none, pendingKyberPreKey := none,
              aliceBaseKey := p.baseKey.take 33, remoteRegistrationId := f248,
              localRegistrationId := r.regIdB }⟩

/-- Pre-decrypt `SessionState HwBytes` invariants entering `tryDecryptWithStateW` on a pre-key
message. -/
def AcceptSt0ModelInvs (interpretation : ExternInterpretation) (r : ProtocolSetup) (p : PreKeyFields)
    (st0 : SessionState HwBytes) : Prop :=
  let F := sha256CompressFunction interpretation
  let ikABytes := pubBytes interpretation (secretBytes r 0)
  let ikBskBytes := secretBytes r 1
  let spkBytes := secretBytes r 2
  let ek := TR.ekBytes p
  let dh1 := TR.dhAgreeBytes interpretation spkBytes ikABytes
  let dh2 := TR.dhAgreeBytes interpretation ikBskBytes ek
  let dh3 := TR.dhAgreeBytes interpretation spkBytes ek
  let dh4 := p.preKeyId.map (fun _ => TR.dhAgreeBytes interpretation (secretBytes r 6) ek)
  ∃ ct_wire : HwBytes,
    st0.sessionVersion = 4#32 ∧
    st0.receiverChains = [] ∧
    p.kyberCiphertext = some (kyberKey ct_wire) ∧
    ct_wire.length = 1568 ∧
    (((p.baseKey.take 33).drop 1).length = 32 ∧
      DY.X25519.leValue (((p.baseKey.take 33).drop 1).map BitVec.toNat) < DY.X25519.p25519 ∧
      DY.X25519.isLowOrderKey (((p.baseKey.take 33).drop 1).map BitVec.toNat) = false ∧
      DY.Libsignal.PQXDH.Refinement.X25519TorsionFree interpretation ((p.baseKey.take 33).drop 1)) ∧
    (p.inner.serialized = p.message ∧ p.message.length ≥ 8) ∧
    st0.remoteIdentity =
      some ⟨⟨List.Vector.ofFn (fun i => (pubBytes interpretation (secretBytes r 0)).getD i.val 0#8)⟩⟩ ∧
    st0.localIdentity =
      ⟨⟨List.Vector.ofFn (fun i => (pubBytes interpretation (secretBytes r 1)).getD i.val 0#8)⟩⟩ ∧
    (let ss := (kyberDecapsBytes interpretation r ct_wire).getD []
     let (rk, ck, pqr) := TR.pqxdhKdfBytes F (TR.pqxdhIkmBytes dh1 dh2 dh3 dh4 ss)
     st0.rootKey = CryptoGames.HKDF.bytesToKey32 rk ∧
       (∃ pubKp, st0.senderChain =
         some ⟨⟨pubKp, ⟨List.Vector.ofFn (fun i =>
           (DY.Libsignal.TripleRatchet.Refinement.clamp spkBytes).getD i.val 0#8)⟩⟩,
           ⟨CryptoGames.HKDF.bytesToKey32 ck, 0#32⟩⟩) ∧
       st0.pqRatchetState =
         Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf interpretation pqr [1#8])

unseal DY.Bytes in
private instance subSpqrInitAux (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_spqrInit_aux (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k d : DY.Bytes) :
    gamma interpretation S g (DY.Spqr.spqrInit k d) =
      S.init (gamma interpretation S g k) (gamma interpretation S g d) := by
  unfold gamma gamma'
  show ((({ authKey := k, params := d } : DY.Spqr.InitState.SubF DY.Bytes).pack).rec
    (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeSpqrInit S) (concretizeAll interpretation S g)]; rfl

theorem gamma_spqrParams_b2a_aux (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    gamma interpretation S g DY.Libsignal.TripleRatchet.spqrB2A = [1#8] := by
  unfold DY.Libsignal.TripleRatchet.spqrB2A DY.Spqr.encodeSpqrDirectionParams
  rw [TR.gamma_lit]
  rfl

private theorem tieAux_ofFn_getD_toList (l : List (BitVec 8)) (hl : l.length = 32) :
    (List.Vector.ofFn (n := 32) (fun i => l.getD i.val 0#8)).toList = l := by
  apply List.ext_getElem
  · simp [hl]
  · intro n _h1 h2
    simp only [List.Vector.toList_ofFn, List.getElem_ofFn]
    simp [List.getD_eq_getElem?_getD, h2]

private theorem pubBytes_eq_x25519 (interpretation : ExternInterpretation) (b : List (BitVec 8)) :
    pubBytes interpretation b =
      (interpretation x25519PublicKeySymbol [clamp b]).getD [] := rfl

private theorem identityKey_serialize_ofFn_eq_serializedKey_ecKey
    (interpretation : ExternInterpretation) (b : List (BitVec 8))
    (hb : (pubBytes interpretation b).length = 32) :
    IdentityKey.serialize ⟨⟨List.Vector.ofFn (fun i => (pubBytes interpretation b).getD i.val 0#8)⟩⟩ =
      TR.serializedKey ((ecKey (pubBytes interpretation b)).drop 1) := by
  unfold IdentityKey.serialize PublicKey.serialize TR.serializedKey ecKey
  dsimp only [List.drop]
  congr 1
  exact tieAux_ofFn_getD_toList (pubBytes interpretation b) hb

private theorem gamma_pqxdhKdf_eq (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {keys : PQXDH.HandshakeKeys} {ikm : DY.Bytes} {ikmB : HwBytes}
    (hkeys : keys = PQXDH.pqxdhKdf ikm)
    (hikm : gamma interpretation S g ikm = ikmB) :
    let F := sha256CompressFunction interpretation
    let prk := hmacWith F (List.replicate 32 0#8) ikmB
    gamma interpretation S g keys.rk = TR.hkdfBlock1Bytes F prk TR.pqxdhLabelBytes ∧
    gamma interpretation S g keys.ck = TR.hkdfBlock2Bytes F prk TR.pqxdhLabelBytes ∧
    gamma interpretation S g keys.pqr = TR.hkdfBlock3Bytes F prk TR.pqxdhLabelBytes := by
  subst hkeys hikm
  exact TR.gamma_pqxdhKdf interpretation S g ikm

private theorem stateRel_of_fields {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : DY.Libsignal.TripleRatchet.TRState}
    {s : Session (List (BitVec 8))}
    {st0 : SessionState HwBytes}
    {sc : SenderChain}
    (hs : s.state = st0)
    (hver : st0.sessionVersion = 4#32)
    (hpn : st.pn = 0)
    (hns : st.ns = 0)
    (hrecv : st.recv = [])
    (hpc : st0.previousCounter = 0)
    (hrc : st0.receiverChains = [])
    (hsc : st0.senderChain = some sc)
    (hck_idx : sc.chainKey.index = 0#32)
    (hloc : st0.localIdentity.serialize =
      TR.serializedKey ((gamma interpretation S g st.myIk).drop 1))
    (hrem : (st0.remoteIdentity.map IdentityKey.serialize).getD [] =
      TR.serializedKey ((gamma interpretation S g st.peerIk).drop 1))
    (hrk : CryptoGames.HMAC.keyToBytes32 st0.rootKey =
      gamma interpretation S g st.rk)
    (hpub : sc.ratchetKey.publicKey.serialize =
      TR.serializedKey ((interpretation x25519PublicKeySymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp
          (gamma interpretation S g st.dhs)]).getD []))
    (hpriv : sc.ratchetKey.privateKey.bytes.toList =
      DY.Libsignal.TripleRatchet.Refinement.clamp (gamma interpretation S g st.dhs))
    (hck : CryptoGames.HMAC.keyToBytes32 sc.chainKey.key =
      gamma interpretation S g st.cks)
    (hpq : st0.pqRatchetState = gamma interpretation S g st.spqr) :
    TR.StateRel interpretation S g st (sessionToRecordRec s) := by
  refine ⟨rfl, ?_⟩
  unfold sessionToRecordRec TR.eraseSkipped TR.eraseUnmodelled TR.sessionOf
    Swarm.Phase0WholeFunctionBridge.sessionToSessionRec
    Swarm.Phase0WholeFunctionBridge.senderChainToChainRec
  rw [hs, hver, hpn, hns, hrecv, hpc, hrc, hsc, hloc, hrem, hrk, hpq]
  dsimp only [Option.map_some, List.map_nil]
  rw [hpub, hpriv, hck_idx, hck]
  rfl

set_option maxHeartbeats 800000 in
/-- Bob's pre-decrypt `SessionState` satisfying `AcceptSt0ModelInvs` is `TR.StateRel`-related to the
symbolic `bobStart` initial state. -/
theorem rpkTie_stateRel_init {interpretation : ExternInterpretation}
    (hEq : ExternCryptoLawsHold interpretation)
    {r : ProtocolSetup} (hwf : ProtocolSetupWF r) {S : OpaqueSymbolSemantics}
    (hInit : S.init = Symbolic.Swarm.SHARED.SpqrBytes.spqrInitOf interpretation)
    {g : Ghost} (hCompat : GhostAndSemMatchSetup interpretation r S g)
    {b : HwBytes} {p : PreKeyFields}
    (hp : parsePreKeyWire b = some p)
    {ms : List Move} {x : PreKeyRep} (hx : x ∈ preKeyRepresentations interpretation r S g ms b)
    (hnk : ¬ KyberMismatch interpretation r p)
    {keys : PQXDH.HandshakeKeys} (hkeys : TR.bobKeys r p x = some keys)
    {st0 : SessionState HwBytes}
    (hinv : AcceptSt0ModelInvs interpretation r p st0)
    (hpub : ∀ sc, st0.senderChain = some sc →
      sc.ratchetKey.publicKey.serialize = TR.serializedKey ((interpretation
        x25519PublicKeySymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)]).getD []))
    (hpc : st0.previousCounter = 0)
    (rt : DY.Bytes) (s : Session (List (BitVec 8)))
    (hs : s.state = st0) :
    TR.StateRel interpretation S g
      { peer := r.alice, myIk := PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 1)),
        peerIk := PQXDH.serializedIk (setupPublic r 0), rk := keys.rk, dhs := setupSecret r 2,
        cks := keys.ck, ns := 0, pn := 0,
        sid := DY.Concat.concat (DY.X25519.normalizeX25519Key rt) keys.rk,
        initiator := false,
        rIdx := 0, recv := [],
        spqr := DY.Spqr.spqrInit keys.pqr DY.Libsignal.TripleRatchet.spqrB2A }
      (sessionToRecordRec s) := by
  have hNe : r.alice ≠ r.bob := hwf.1
  obtain ⟨ct_wire, hst0_ver, hst0_rc, hct_eq, hct_len, _hbase_ok, _hmsg_eq,
    hik_eq, hloc_eq, hst0_rk, ⟨pubKp, hst0_sc⟩, hst0_pq⟩ := hinv
  obtain ⟨hek_gamma, hct_gamma, _hFaith⟩ :=
    TR.rep_ek_ct_gamma interpretation r S g ms b p ct_wire x hp hct_eq hx
  obtain ⟨ss, hdec, hss_gamma⟩ :=
    TR.gamma_kemSS_of_not_implicitReject interpretation r S g p x ct_wire
      hCompat hNe hnk hct_eq hct_len hct_gamma
  obtain ⟨_, hs1, hs2, _, hs6⟩ := TR.gamma_setupSecret interpretation r S g hCompat hNe
  obtain ⟨hp0, _, _⟩ := TR.gamma_setupPublic_0_2_6 interpretation r S g hCompat hNe
  let opk : Option DY.Bytes := p.preKeyId.map (fun _ => setupSecret r 6)
  have hkeys_eq :
      keys = PQXDH.pqxdhKdf (PQXDH.pqxdhIkm
        (PQXDH.agree (setupPublic r 0) (setupSecret r 2))
        (PQXDH.agree x.ek (setupSecret r 1))
        (PQXDH.agree x.ek (setupSecret r 2))
        (opk.map (PQXDH.agree x.ek ·)) ss) ∧
      Option.map (gamma interpretation S g) (Option.map (PQXDH.agree x.ek ·) opk) =
        p.preKeyId.map (fun _ =>
          TR.dhAgreeBytes interpretation (secretBytes r 6) (TR.ekBytes p)) := by
    unfold TR.bobKeys at hkeys
    dsimp only [opk] at hkeys ⊢
    rw [hdec] at hkeys
    cases hid : p.preKeyId with
    | none =>
      simp only [hid, Option.map, Bind.bind, Option.bind, Pure.pure, Option.some.injEq] at hkeys ⊢
      exact ⟨hkeys.symm, trivial⟩
    | some kid =>
      rw [hid] at hkeys
      by_cases hcond : (r.withOpk && kid == r.opkId) = true
      · simp only [hcond, ↓reduceIte, Option.map, Bind.bind, Option.bind, Pure.pure,
          Option.some.injEq] at hkeys ⊢
        have hw : r.withOpk = true := (Bool.and_eq_true _ _).mp hcond |>.1
        refine ⟨hkeys.symm, ?_⟩
        rw [TR.gamma_agree interpretation hEq, hs6 hw, hek_gamma]
        rfl
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte, Bind.bind, Option.bind] at hkeys
        cases hkeys
  have hikm_gamma :
      gamma interpretation S g
        (PQXDH.pqxdhIkm
          (PQXDH.agree (setupPublic r 0) (setupSecret r 2))
          (PQXDH.agree x.ek (setupSecret r 1))
          (PQXDH.agree x.ek (setupSecret r 2))
          (opk.map (PQXDH.agree x.ek ·)) ss) =
      TR.pqxdhIkmBytes
        (TR.dhAgreeBytes interpretation (secretBytes r 2) (pubBytes interpretation (secretBytes r 0)))
        (TR.dhAgreeBytes interpretation (secretBytes r 1) (TR.ekBytes p))
        (TR.dhAgreeBytes interpretation (secretBytes r 2) (TR.ekBytes p))
        (p.preKeyId.map (fun _ => TR.dhAgreeBytes interpretation (secretBytes r 6) (TR.ekBytes p)))
        ((kyberDecapsBytes interpretation r ct_wire).getD []) := by
    rw [TR.gamma_pqxdhIkm, hkeys_eq.2,
      TR.gamma_agree interpretation hEq _ _ (setupPublic r 0) (setupSecret r 2),
      TR.gamma_agree interpretation hEq _ _ x.ek (setupSecret r 1),
      TR.gamma_agree interpretation hEq _ _ x.ek (setupSecret r 2),
      hp0, hs1, hs2, hek_gamma, hss_gamma]
    rfl
  obtain ⟨hrk_gamma, hck_gamma, hpqr_gamma⟩ :=
    gamma_pqxdhKdf_eq interpretation S g hkeys_eq.1 hikm_gamma
  rw [← hck_gamma] at hst0_sc
  have hpub0_len : (pubBytes interpretation (secretBytes r 0)).length = 32 :=
    hEq.x25519_public_key_length _
  have hpub1_len : (pubBytes interpretation (secretBytes r 1)).length = 32 :=
    hEq.x25519_public_key_length _
  have hsec2_len : (secretBytes r 2).length = 32 := by
    rw [(TR.secretBytes_eq r hNe).2.2.1]
    exact hwf.2.1 (10, 32) (by rw [TR.setupRandomsAt_eq r hNe]; cases r.withOpk <;> simp)
  have hclamp2_len : (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)).length = 32 := by
    unfold DY.Libsignal.TripleRatchet.Refinement.clamp; simp [hsec2_len]
  have hrk_len : (gamma interpretation S g keys.rk).length = 32 := by
    rw [hrk_gamma]; exact TR.length_hmacWith _ _ _
  have hck_len : (gamma interpretation S g keys.ck).length = 32 := by
    rw [hck_gamma]; exact TR.length_hmacWith _ _ _
  have hloc_ser :
      st0.localIdentity.serialize =
        TR.serializedKey ((gamma interpretation S g
          (PQXDH.serializedIk (DY.DiffieHellman.dhPk (setupSecret r 1)))).drop 1) := by
    rw [hloc_eq, TR.gamma_serializedIk, TR.gamma_dhPk, hs1, ← pubBytes_eq_x25519]
    exact identityKey_serialize_ofFn_eq_serializedKey_ecKey
      interpretation (secretBytes r 1) hpub1_len
  have hrem_ser :
      (st0.remoteIdentity.map IdentityKey.serialize).getD [] =
        TR.serializedKey ((gamma interpretation S g
          (PQXDH.serializedIk (setupPublic r 0))).drop 1) := by
    rw [hik_eq, Option.map_some, Option.getD_some, TR.gamma_serializedIk, hp0]
    exact identityKey_serialize_ofFn_eq_serializedKey_ecKey
      interpretation (secretBytes r 0) hpub0_len
  have hrk_ser :
      CryptoGames.HMAC.keyToBytes32 st0.rootKey =
        gamma interpretation S g keys.rk := by
    rw [hst0_rk, ← hrk_gamma,
      Proofs.libsignal.RngG.CliPure.DecCrypto.keyToBytes32_bytesToKey32_of_length_eq_32 _ hrk_len]
  have hpub_ser :
      pubKp.serialize =
        TR.serializedKey ((interpretation x25519PublicKeySymbol
          [DY.Libsignal.TripleRatchet.Refinement.clamp
            (gamma interpretation S g (setupSecret r 2))]).getD []) := by
    have hpub0 := hpub _ hst0_sc
    rw [hs2]
    exact hpub0
  have hpriv_ser :
      (List.Vector.ofFn (n := 32) (fun i =>
        (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)).getD i.val 0#8)).toList =
        DY.Libsignal.TripleRatchet.Refinement.clamp
          (gamma interpretation S g (setupSecret r 2)) := by
    rw [tieAux_ofFn_getD_toList (DY.Libsignal.TripleRatchet.Refinement.clamp (secretBytes r 2)) hclamp2_len,
      hs2]
  have hck_ser :
      CryptoGames.HMAC.keyToBytes32
        (CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g keys.ck)) =
        gamma interpretation S g keys.ck := by
    rw [Proofs.libsignal.RngG.CliPure.DecCrypto.keyToBytes32_bytesToKey32_of_length_eq_32 _ hck_len]
  have hpq_ser :
      st0.pqRatchetState =
        gamma interpretation S g
          (DY.Spqr.spqrInit keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) := by
    rw [hst0_pq, ← hpqr_gamma, gamma_spqrInit_aux, gamma_spqrParams_b2a_aux, hInit]
  exact stateRel_of_fields hs hst0_ver rfl rfl rfl hpc hst0_rc hst0_sc rfl
    hloc_ser hrem_ser hrk_ser hpub_ser hpriv_ser hck_ser hpq_ser

end Symbolic.Swarm.CREF.CliPure
