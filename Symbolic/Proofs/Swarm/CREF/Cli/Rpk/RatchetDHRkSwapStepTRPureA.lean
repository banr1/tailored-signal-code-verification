/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.R3StepExistingPure
public import Symbolic.Proofs.RngG.R3ModelInv
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.EquationalTheory.Literal
import Symbolic.Specifications.Model.EquationalTheory.X25519
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureA
import Symbolic.Proofs.Refinement.X25519Covered
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.SendRetCoinsCliPureB
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepSpqrPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.HonestPqNoTrWire -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic

/-!
# DH Ratchet Step Lemmas Under Ratchet-Key Swap

Transfers `findRecvChain = none`, `x25519LowOrder = false`, and `consumeMessageKey` across a
`gamma`-equivalent sender ratchet key `rk_c` in the DH ratchet branch.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure.TR.G1
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr SpqrSem at?_append_of_lt gamma_concat getLocalState_fst leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd uOf_leBytes uOf_lt
open Symbolic.Swarm.CREF.TR.G1 hiding gamma_kdfExtract_tr gamma_symEnc_tr

cref_open

open DY DY.Comparse DY.Literal DY.DiffieHellman DY.Libsignal
open DY.Libsignal.TripleRatchet
  (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder litByte)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (x25519AgreementSymbol ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Hooks2
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec)
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvRep hiding gamma_litOf
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState at?_append_of_lt)
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep (consumeMessageKey_eq_some_iff_tr)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.CliPure.TR.SendRetCoins (SpqrSem gamma_symEnc_tr gamma_kdfExtract_tr)

theorem knows_litOf (bs : HwBytes) (tr : ExecTrace) : (litOf bs).AttackerKnows tr :=
  Literal.attacker_knows_literalToBytes _ _

theorem length_gamma_hmac_tr (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (k m : DY.Bytes) :
    (gamma interpretation S g (DY.Libsignal.TripleRatchet.hmac k m)).length = 32 := by
  change (gamma interpretation S g (DY.KdfExtract.kdfExtract k m)).length = 32
  rw [gamma_kdfExtract_tr]
  exact Symbolic.Swarm.CREF.TR.length_hmacWith _ _ _

theorem their_and_pkLen_of_gamma_rkSwap
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {their : PublicKey} {rk_c : DY.Bytes} {msg₀ : TRSignalMsg}
    (hTheir₀ : their = ⟨vec32 (gamma interpretation S g msg₀.ratchetKey)⟩)
    (hPkLen₀ : (gamma interpretation S g msg₀.ratchetKey).length = 32)
    (hγ_rk_c : gamma interpretation S g rk_c = gamma interpretation S g msg₀.ratchetKey) :
    their = ⟨vec32 (gamma interpretation S g rk_c)⟩ ∧
    (gamma interpretation S g rk_c).length = 32 ∧
    their.bytes.toList = gamma interpretation S g rk_c := by
  have hTheir_c : their = ⟨vec32 (gamma interpretation S g rk_c)⟩ := by
    rw [hγ_rk_c]; exact hTheir₀
  have hPkLen_c : (gamma interpretation S g rk_c).length = 32 := by
    rw [hγ_rk_c]; exact hPkLen₀
  have hBytes_c : their.bytes.toList = gamma interpretation S g rk_c := by
    rw [hTheir_c]
    exact Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hPkLen_c
  exact ⟨hTheir_c, hPkLen_c, hBytes_c⟩

private theorem stateRel_sessionToRecordRec_iff_tr_rkSwap
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (st : TRState) (s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))) :
    StateRel interpretation S g st (sessionToRecordRec s) ↔
      eraseSkipped (eraseUnmodelled (sessionToSessionRec s)) =
        sessionOf interpretation (gamma interpretation S g) st := by
  simp [StateRel, sessionToRecordRec]

private theorem receiverChains_of_stateRel_tr_rkSwap
    {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s)) :
    (s.state.receiverChains.map eraseRecvChain).map recChainOfErased =
      (sessionOf interpretation (gamma interpretation S g) st).receiverChains := by
  rw [← congrArg SessionRec.receiverChains ((stateRel_sessionToRecordRec_iff_tr_rkSwap interpretation S g st s).mp hrel)]
  simp only [eraseSkipped, eraseUnmodelled, sessionToSessionRec, List.map_map]; rfl

private theorem senderRatchetKey_of_mem_recv_of_stateRel_tr_rkSwap
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    {c : RecvChain} (hc : c ∈ st.recv) :
    ∃ rc ∈ (ratchetStateOf s.state).receiverChains,
      rc.senderRatchetKey = ⟨vec32 (gamma interpretation S g c.ratchetKey)⟩ := by
  have hmap := congrArg (List.map ChainRec.senderRatchetKey) (receiverChains_of_stateRel_tr_rkSwap hrel)
  simp only [sessionOf, List.map_map, Function.comp_def, recChainOfErased, eraseRecvChain,
    PublicKey.serialize, CryptoGames.LibsignalSession.djbType,
    serializedKey, ecKey] at hmap
  have hmem : (0x05#8 :: gamma interpretation S g c.ratchetKey) ∈
      List.map (fun c => 0x05#8 :: gamma interpretation S g c.ratchetKey) st.recv :=
    List.mem_map_of_mem hc
  rw [← hmap] at hmem
  obtain ⟨rc, hrcMem, hrcEq⟩ := List.mem_map.mp hmem
  have htoList : rc.senderRatchetKey.bytes.toList = gamma interpretation S g c.ratchetKey :=
    (List.cons.inj hrcEq).2
  exact ⟨rc, hrcMem, (publicKey_eq_vec32_of_toList_eq htoList).1⟩

theorem findRecvChain_eq_none_of_dhRatchetStep_rkSwap
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    {their : PublicKey} {rk_c : DY.Bytes} {msg₀ : TRSignalMsg}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (_hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32)
    (hFindNone : (ratchetStateOf s.state).findReceiverChainKey their = .ok none)
    (hTheir₀ : their = ⟨vec32 (gamma interpretation S g msg₀.ratchetKey)⟩)
    (hγ_rk_c : gamma interpretation S g rk_c = gamma interpretation S g msg₀.ratchetKey) :
    findRecvChain st.recv rk_c = none ∧
    (∀ rc ∈ (ratchetStateOf s.state).receiverChains, rc.senderRatchetKey ≠ their) := by
  have hci : (ratchetStateOf s.state).findReceiverChainIndex their = none :=
    findReceiverChainKey_ok_none (ratchetStateOf s.state) their hFindNone
  have hNoRc : ∀ rc ∈ (ratchetStateOf s.state).receiverChains, rc.senderRatchetKey ≠ their := by
    intro rc hMem hEq
    unfold RatchetState.findReceiverChainIndex at hci
    rw [List.findIdx?_eq_none_iff] at hci
    have hFalse := hci rc hMem
    simp [hEq] at hFalse
  refine ⟨?_, hNoRc⟩
  unfold findRecvChain
  rw [List.find?_eq_none]
  intro c hc
  simp only [beq_iff_eq]
  intro hRkEq
  obtain ⟨rc, hrcMem, hSrk⟩ := senderRatchetKey_of_mem_recv_of_stateRel_tr_rkSwap interpretation S g hrel hc
  exact hNoRc rc hrcMem (by rw [hSrk, hRkEq, hγ_rk_c, hTheir₀])

unseal DY.Bytes in
private instance subLit_rkSwap (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant_rkSwap (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem gamma_literalToBytes_rkSwap
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (b : ByteArray) :
    gamma interpretation S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma gamma'
  show ((({lit := b} : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]; rfl

private theorem gamma_x25519Variant_raw_rkSwap
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (k : DY.Bytes) (v : Fin 4) (t : Fin 8 := 0) :
    gamma interpretation S g (({key := k, variation := v, torsion := t} : DY.X25519.Variant.SubF DY.Bytes).pack) =
      DY.Libsignal.Refinement.variantBytes
        (DY.Libsignal.Refinement.torsionShift interpretation (gamma interpretation S g k) t) v := by
  unfold gamma gamma'
  rw [DY.Bytes.rec_eq (concretizeVariant interpretation) (concretizeAll interpretation S g)]; rfl

private theorem agreement_gamma_x25519Key_rkSwap
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (hEquations : ExternCryptoLawsHold interpretation) (a : HwBytes) (pk : DY.Bytes) :
    interpretation x25519AgreementSymbol [a, gamma interpretation S g (DY.X25519.normalizeX25519Key pk)] =
      interpretation x25519AgreementSymbol [a, gamma interpretation S g pk] := by
  unfold DY.X25519.normalizeX25519Key
  split
  · rename_i x h
    have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
    simp only [h] at hv
    rw [← hv, gamma_x25519Variant_raw_rkSwap interpretation S g x.key x.variation x.torsion]
    have htl : (DY.Libsignal.Refinement.torsionShift interpretation
        (gamma interpretation S g x.key) x.torsion).length =
          (gamma interpretation S g x.key).length := by
      unfold DY.Libsignal.Refinement.torsionShift
      split
      · rfl
      · rename_i h
        have hlen : (gamma interpretation S g x.key).length = 32 := by revert h; simp
        split
        · split
          · rename_i q _ hq
            omega
          · rfl
        · rfl
    by_cases hl : (gamma interpretation S g x.key).length = 32
    · have hl' := htl.trans hl
      have hs := DY.Libsignal.Refinement.variantBytes_spec _ hl' x.variation
      rw [← hEquations.x25519_agreement_torsion_invariant a (gamma interpretation S g x.key) x.torsion]
      exact hEquations.x25519_agreement_reads_u_coordinate a _ _ hl' hs.1 hs.2.symm
    · have hts : DY.Libsignal.Refinement.torsionShift interpretation
          (gamma interpretation S g x.key) x.torsion = gamma interpretation S g x.key := by
        unfold DY.Libsignal.Refinement.torsionShift; simp [hl]
      rw [hts]
      unfold DY.Libsignal.Refinement.variantBytes
      simp only [hl, ↓reduceIte]
  · rfl

private theorem map_toNat_ofByteArray_data_rkSwap (ba : ByteArray) :
    (ofByteArray ba).map BitVec.toNat = ba.data.toList.map UInt8.toNat := by
  unfold ofByteArray; rw [List.map_map]; rfl

theorem x25519LowOrder_false_of_dhRatchetStep_rkSwap
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (hEq : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    {their : PublicKey} {coins : BitVec 256} {rk_c : DY.Bytes} {msg₀ : TRSignalMsg}
    (hTheir₀ : their = ⟨vec32 (gamma interpretation S g msg₀.ratchetKey)⟩)
    (hPkLen₀ : (gamma interpretation S g msg₀.ratchetKey).length = 32)
    (hγ_rk_c : gamma interpretation S g rk_c = gamma interpretation S g msg₀.ratchetKey)
    {r0 r1 : RatchetState} {ck : ChainKey}
    (hDh :
      Mut.exec (RatchetState.dhRatchetStep (cryptoOf' interpretation E D) their coins) r0 =
        (.ok ck, r1)) :
    x25519LowOrder rk_c = false := by
  have hTheir : their.bytes.toList = gamma interpretation S g rk_c :=
    (their_and_pkLen_of_gamma_rkSwap interpretation S g hTheir₀ hPkLen₀ hγ_rk_c).2.2
  obtain ⟨sc, newRootKey, finalRootKey, senderChainKey, hsc, hrc1, hrc2, hr1⟩ := dhRatchetStep_ok_inv hDh
  unfold x25519LowOrder
  rcases hb : DY.Literal.bytesToLiteral (DY.X25519.normalizeX25519Key rk_c) with _ | b
  · rfl
  · dsimp only
    cases hlow : DY.X25519.isLowOrderKey (b.data.toList.map (·.toNat))
    · rfl
    · exfalso
      have hlit : DY.X25519.normalizeX25519Key rk_c = DY.Literal.literalToBytes b := by
        have := DY.Literal.literalToBytes_bytesToLiteral (DY.X25519.normalizeX25519Key rk_c); rwa [hb] at this
      have hγ_key : gamma interpretation S g (DY.X25519.normalizeX25519Key rk_c) = ofByteArray b := by
        rw [hlit, gamma_literalToBytes_rkSwap]
      have hlow_len : (b.data.toList.map (·.toNat)).length = 32 := by
        unfold DY.X25519.isLowOrderKey at hlow; simp only [Bool.and_eq_true] at hlow
        exact beq_iff_eq.mp hlow.1
      have hlen_of : (ofByteArray b).length = 32 := by
        unfold ofByteArray; rw [List.length_map]; simpa [List.length_map] using hlow_len
      have hlow_of : DY.X25519.isLowOrderKey ((ofByteArray b).map BitVec.toNat) = true := by
        rw [map_toNat_ofByteArray_data_rkSwap]; exact hlow
      have hsec_len := (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList_length
      have hiff := hEq.x25519_agreement_zero_iff_low_order
        (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList
        (ofByteArray b) hsec_len hlen_of
      have hz0 := hiff.mpr hlow_of
      have hagr := agreement_gamma_x25519Key_rkSwap interpretation S g hEq
        (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList rk_c
      rw [hγ_key, ← hTheir] at hagr
      have hz :
          (interpretation x25519AgreementSymbol
            [(CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList,
              their.bytes.toList]).getD [] = List.replicate 32 0#8 := by
        rw [← hagr]; exact hz0
      have hlen := hEq.x25519_agreement_length
        (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList their.bytes.toList
      have hz' :
          ((cryptoOf' interpretation E D).X
            (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes) their.bytes).toList =
            List.replicate 32 0#8 := by
        dsimp only [cryptoOf']
        rw [Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hlen]; exact hz
      unfold rootCreateChain CryptoGames.Ratchet.createChain at hrc1
      simp only [hz', ite_true] at hrc1; nomatch hrc1

/-- Transfers `consumeMessageKey` on `trDhRatchetState` from `msg₀.ratchetKey` to any `rk_c` since
the fresh chain index is `0`. -/
theorem consumeMessageKey_trDhRatchetState_rkSwap_of_msg₀
    (st₀ : TRState) (msg₀ : TRSignalMsg) (rngIdx : Nat)
    (seed₀ : DY.Bytes) (c'₀ : RecvChain) (rk_c : DY.Bytes)
    (hcons₀ :
      consumeMessageKey (trDhRatchetState st₀ msg₀.ratchetKey rngIdx).2 msg₀.counter =
        some (seed₀, c'₀)) :
    let seed_c := (kdfCk (chainKeyAt (createChain st₀.rk rk_c st₀.dhs).2 msg₀.counter.toNat)).2
    let c'_c : RecvChain :=
      { ratchetKey := rk_c
        chainKey := (kdfCk (chainKeyAt (createChain st₀.rk rk_c st₀.dhs).2 msg₀.counter.toNat)).1
        index := msg₀.counter + 1
        rIdx := st₀.rIdx + 2 }
    consumeMessageKey (trDhRatchetState st₀ rk_c rngIdx).2 msg₀.counter = some (seed_c, c'_c) ∧
    seed₀ = (kdfCk (chainKeyAt (createChain st₀.rk msg₀.ratchetKey st₀.dhs).2 msg₀.counter.toNat)).2 ∧
    c'_c.ratchetKey = rk_c ∧
    c'_c.rIdx = st₀.rIdx + 2 := by
  intro seed_c c'_c
  obtain ⟨h1, h2, h3, hseed₀_eq, _⟩ :=
    (consumeMessageKey_eq_some_iff_tr (trDhRatchetState st₀ msg₀.ratchetKey rngIdx).2
      msg₀.counter seed₀ c'₀).mp hcons₀
  change ¬ msg₀.counter < 0 at h1
  change msg₀.counter.toNat - (0 : UInt32).toNat ≤ DY.Libsignal.TripleRatchet.maxForwardJumps at h2
  change seed₀ = (kdfCk (chainKeyAt (createChain st₀.rk msg₀.ratchetKey st₀.dhs).2
    (msg₀.counter.toNat - (0 : UInt32).toNat))).2 at hseed₀_eq
  have hcons_c :
      consumeMessageKey (trDhRatchetState st₀ rk_c rngIdx).2 msg₀.counter = some (seed_c, c'_c) :=
    (consumeMessageKey_eq_some_iff_tr (trDhRatchetState st₀ rk_c rngIdx).2
      msg₀.counter seed_c c'_c).mpr ⟨h1, h2, h3, rfl, rfl⟩
  exact ⟨hcons_c, hseed₀_eq, rfl, rfl⟩

theorem ratchetKey_attackerKnows_of_parseTrSignalMsg_step
    {tr : ExecTrace} {t : DY.Bytes} {msg : TRSignalMsg}
    (ht : t.AttackerKnows tr) (hparse : parseTrSignalMsg t = some msg) :
    msg.ratchetKey.AttackerKnows tr := by
  have hsp := Concat.attacker_knows_split t (t.length - Trunc.trunc8Length) tr ht
  unfold parseTrSignalMsg at hparse
  rcases hsplit : Concat.split t (t.length - Trunc.trunc8Length) with _ | ⟨w, m⟩
  · rw [hsplit] at hparse; cases hparse
  · rw [hsplit] at hsp hparse; dsimp only [Bind.bind, Option.bind] at hparse
    rcases hwf : DY.TrWire.trWireMsgFields? w with _ | x
    · rw [hwf] at hparse; cases hparse
    · rw [hwf] at hparse; injection hparse with hmsg; subst hmsg
      rw [DY.TrWire.trWireMsg_of_fields? hwf] at hsp
      exact (DY.TrWire.attacker_knows_trWireMsg_args x.version x.senderRatchetKey x.counter
        x.previousCounter x.ciphertext x.pqRatchet x.encodingVariation tr hsp.1).1

end Symbolic.Swarm.CREF.CliPure.TR.G1
