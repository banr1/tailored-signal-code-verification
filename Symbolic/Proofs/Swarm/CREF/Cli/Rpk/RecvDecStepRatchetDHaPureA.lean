/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel
public import Symbolic.Proofs.Swarm.CREF.TR.RecvDec
public import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaReach
public import Symbolic.Proofs.RngG.R3ModelInv
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.PinCoinsPure
import Init.Data.String.Defs
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Hooks2.BridgeXPure
public import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPureA
import Symbolic.Proofs.Refinement.LemmasPure
import Symbolic.Proofs.Refinement.X25519Covered
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.DecCryptoAPure
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigmaHead
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Fresh-Randomness Ghost Update and DH Ratchet State Relation Bridge

Proves `ratchetDH_sigma_bridge` for updating `g.σ` at a fresh timestamp without disturbing earlier
trace invariants, and relates `RatchetState.dhRatchetStep` to symbolic `trDhRatchetState` under
`gamma`.
-/

@[expose] public section

cref_hide_foreign_instances

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
open Symbolic.Swarm.CREF.TR hiding newRandoms_append_rnd runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.DiffieHellman DY.Libsignal
open DY.Libsignal.TripleRatchet
  (SessionInfo DRState KeyComponent KeyDir RecvChain findRecvChain setRecvChain recvChainFor consumeMessageKey chainKeyAt kdfCk kdfRk maxForwardJumps u32Max computeMac messageVersion createChain x25519LowOrder litByte hkdfBlock1 hkdfBlock2)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.Refinement (x25519PublicKeySymbol x25519AgreementSymbol sha256CompressFunction ExternCryptoLawsHold)
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Record
open CryptoVerification.SessionModel.AdvanceAndFrame
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.RngG Proofs.libsignal.Hooks2
open Symbolic.Swarm.CREF.CliPure.RpkCli (pinCoins)
open Swarm.Phase0WholeFunctionBridge (sessionToRecordRec sessionToSessionRec senderChainToChainRec)
open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3
open Proofs.libsignal.RngG.CliPure.DecCrypto (clampScalar_idem clampScalar_toList_eq_clamp clampScalar_toList_eq_clamp_toList rootCreateChain_of_rel_lowOrder hkdf_64_whisperRatchet)
open Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec (trDhRatchetState)
open Symbolic.Swarm.CREF.TR.FreshSigma

theorem ratchetDH_sigma_bridge
    (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (_hwf : ProtocolSetupWF r₀)
    (S : SpqrSem) (Z : PureTRSlots) {who : List Participant} (g : Ghost) (ms₁ : List Move) (τ : List MachineEvent)
    (records : Participant → Option HwBytes) (p : Participant) (stateIdx : Nat)
    (st : TRState) (rec : RecordRec) (t : DY.Bytes) (msg : TRSignalMsg)
    (ts : Nat) (rngBytes : HwBytes) (hts : (runTraceMoves r₀ ms₁).length ≤ ts)
    (hmp : DY.Libsignal.Composed.Refinement.MatchedPrefix interpretation r₀ S who g ms₁ τ)
    (hrsi : PureTRRecordStateInv interpretation r₀ S Z g ms₁ records)
    (hst : ((PersistentLocalState.getLocalState p stateIdx : Traceful TRState).run (runTraceMoves r₀ ms₁)).1 = some st)
    (hrel : StateRel interpretation S g st rec) (hks : TRKeyShape interpretation S g st)
    (ht_kn : t.AttackerKnows (runTraceMoves r₀ ms₁)) (hparse : parseTrSignalMsg t = some msg) :
    let g' : Ghost := { g with σ := updateFreshAt g.σ ts 32 rngBytes }
    g'.σ ts 32 = rngBytes ∧
    DY.Libsignal.Composed.Refinement.MatchedPrefix interpretation r₀ S who g' ms₁ τ ∧
    PureTRRecordStateInv interpretation r₀ S Z g' ms₁ records ∧
    StateRel interpretation S g' st rec ∧
    TRKeyShape interpretation S g' st ∧
    StateStampsLt interpretation S g ts st ∧
    TRSignalMsgStampsLt interpretation S g ts msg ∧
    gamma interpretation S g' t = gamma interpretation S g t ∧
    gamma interpretation S g' msg.wire = gamma interpretation S g msg.wire ∧
    gamma interpretation S g' msg.mac = gamma interpretation S g msg.mac ∧
    gamma interpretation S g' msg.ratchetKey = gamma interpretation S g msg.ratchetKey ∧
    gamma interpretation S g' msg.ciphertext = gamma interpretation S g msg.ciphertext ∧
    gamma interpretation S g' msg.pqRatchet = gamma interpretation S g msg.pqRatchet ∧
    gamma interpretation S g' st.spqr = gamma interpretation S g st.spqr ∧
    (∀ c ∈ st.recv,
      gamma interpretation S g' c.ratchetKey = gamma interpretation S g c.ratchetKey ∧
      gamma interpretation S g' c.chainKey = gamma interpretation S g c.chainKey) := by
  intro g'
  have htr_lt : TraceEntriesLt interpretation S g ts (runTraceMoves r₀ ms₁) :=
    traceEntriesLt_of_reachable interpretation S g ts hmp.2.1.2.2.1.1 hts
  have hat_st : ((runTraceMoves r₀ ms₁).at? stateIdx : Option StEntry) = some ⟨⟨p, st⟩⟩ :=
    at?_eq_some_of_getLocalState_some hst
  have hst_lt : StateStampsLt interpretation S g ts st := traceEntriesLt_at?_st htr_lt hat_st
  have ht_lt : StampsLt interpretation S g ts t := traceEntriesLt_knows htr_lt ht_kn
  have hmsg_lt : TRSignalMsgStampsLt interpretation S g ts msg := stampsLt_parseTrSignalMsg ht_lt hparse
  have hrsi' : PureTRRecordStateInv interpretation r₀ S Z g' ms₁ records := by
    intro q recBytes hrec
    obtain ⟨hq_mem, rec₀, st₀, idx₀, hrecB, hst₀, hcur₀, hrel₀, hsk₀, hcan₀, hks₀, hnd₀⟩ := hrsi q recBytes hrec
    have hst₀_lt := traceEntriesLt_at?_st htr_lt (at?_eq_some_of_getLocalState_some hst₀)
    refine ⟨hq_mem, rec₀, st₀, idx₀, hrecB, hst₀, hcur₀,
      (stateRel_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes st₀ rec₀ hst₀_lt).mpr hrel₀,
      fun c hc k hk => ?_, hcan₀, trKeyShape_updateFreshAt_of_stampsLt hst₀_lt hks₀, hnd₀⟩
    obtain ⟨pk, rIdx, srcIdx, skIdx, seed, hat, hused, hrused, hk2, hsrk, hfind⟩ := hsk₀ c hc k hk
    have hev := traceEntriesLt_at?_tr htr_lt ((Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1 _ _ _).mp hat)
    refine ⟨pk, rIdx, srcIdx, skIdx, seed, hat, hused, hrused, ?_, ?_, hfind⟩
    · rwa [gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes seed hev.1]
    · rwa [gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes pk hev.2]
  refine ⟨updateFreshAt_self g.σ ts 32 rngBytes,
    matchedPrefix_updateFreshAt hmp hts 32 rngBytes, hrsi',
    (stateRel_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes st rec hst_lt).mpr hrel,
    trKeyShape_updateFreshAt_of_stampsLt hst_lt hks, hst_lt, hmsg_lt,
    gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes t ht_lt,
    gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.wire hmsg_lt.1,
    gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.mac hmsg_lt.2.1,
    gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.ratchetKey hmsg_lt.2.2.1,
    gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.ciphertext hmsg_lt.2.2.2.1,
    gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes msg.pqRatchet hmsg_lt.2.2.2.2,
    gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes st.spqr hst_lt.2.2.2.2.2.1,
    fun c hc =>
      ⟨gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes c.ratchetKey (hst_lt.2.2.2.2.2.2 c hc).1,
       gamma_updateFreshAt_of_stampsLt interpretation S g ts 32 rngBytes c.chainKey (hst_lt.2.2.2.2.2.2 c hc).2⟩⟩

section GammaAndStateRelHelpers

variable (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)

unseal DY.Bytes in
private instance subLit : DY.Bytes.SubFunction concretizeLit (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subRandom : DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subConcat : DY.Bytes.SubFunction concretizeConcat (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhPk : DY.Bytes.SubFunction (concretizeDhPk interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDh : DY.Bytes.SubFunction (concretizeDh interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKdf : DY.Bytes.SubFunction (concretizeKdf interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant : DY.Bytes.SubFunction (concretizeVariant interpretation) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_randTerm32 (ts : Nat) :
    gamma interpretation S g (randTerm ts 32) = g.σ ts 32 := by
  unfold gamma gamma' randTerm
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]
  rfl
theorem gamma_literalToBytes_tr (b : ByteArray) :
    gamma interpretation S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma gamma'
  show ((({lit := b} : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll interpretation S g)]; rfl
private theorem gamma_lit_whisperRatchet_tr :
    gamma interpretation S g (DY.Libsignal.TripleRatchet.lit "WhisperRatchet") = Ratchet.whisperRatchetInfo := by
  unfold DY.Libsignal.TripleRatchet.lit
  rw [gamma_literalToBytes_tr, String.toUTF8_eq_toByteArray, ← String.ofList_toList (s := "WhisperRatchet"),
      String.toByteArray_ofList]
  decide
private theorem gamma_concat_tr (a b : DY.Bytes) :
    gamma interpretation S g (DY.Concat.concat a b) =
      gamma interpretation S g a ++ gamma interpretation S g b := by
  show (gamma' interpretation S g (({lhs := a, rhs := b} : DY.Concat.Concat.SubF DY.Bytes).pack)).bytes = _
  unfold gamma'; rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll interpretation S g)]; rfl
private theorem gamma_dhPk_tr (sk : DY.Bytes) :
    gamma interpretation S g (DY.DiffieHellman.dhPk sk) =
      (interpretation x25519PublicKeySymbol [clamp (gamma interpretation S g sk)]).getD [] := by
  unfold gamma gamma'
  show ((({sk := sk} : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeDhPk interpretation) (concretizeAll interpretation S g)]; rfl
private theorem gamma_dh_raw_tr (pk sk : DY.Bytes) :
    gamma interpretation S g (({pk := pk, sk := sk} : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
      (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk), gamma interpretation S g pk]).getD [] := by
  unfold gamma gamma'; rw [DY.Bytes.rec_eq (concretizeDh interpretation) (concretizeAll interpretation S g)]; rfl
private theorem gamma_dh_tr (hEquations : ExternCryptoLawsHold interpretation) (pk sk : DY.Bytes) :
    gamma interpretation S g (DY.DiffieHellman.dh pk sk) =
      (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk), gamma interpretation S g pk]).getD [] := by
  have hv := DY.Bytes.pack_view? DhPk.SubF pk
  simp only [DY.DiffieHellman.dh, CanDH.dh]
  split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    split
    · rw [gamma_dh_raw_tr]
    · rw [gamma_dh_raw_tr]
      show (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk2), gamma interpretation S g (dhPk sk)]).getD [] =
        (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk), gamma interpretation S g (dhPk sk2)]).getD []
      rw [gamma_dhPk_tr, gamma_dhPk_tr,
        hEquations.x25519_agreement_commutes (clamp (gamma interpretation S g sk2)) (clamp (gamma interpretation S g sk))]
  · rw [gamma_dh_raw_tr]
private theorem gamma_x25519Variant_raw_tr (k : DY.Bytes) (v : Fin 4) (t : Fin 8) :
    gamma interpretation S g (({key := k, variation := v, torsion := t} : DY.X25519.Variant.SubF DY.Bytes).pack) =
      DY.Libsignal.Refinement.variantBytes
        (DY.Libsignal.Refinement.torsionShift interpretation (gamma interpretation S g k) t) v := by
  unfold gamma gamma'; rw [DY.Bytes.rec_eq (concretizeVariant interpretation) (concretizeAll interpretation S g)]; rfl
private theorem torsionShift_length_tr (p : HwBytes) (t : Fin 8) :
    (DY.Libsignal.Refinement.torsionShift interpretation p t).length = p.length := by
  unfold DY.Libsignal.Refinement.torsionShift
  split
  · rfl
  · rename_i h
    have hlen : p.length = 32 := by revert h; simp
    split
    · split
      · rename_i q _ hq
        omega
      · rfl
    · rfl
theorem agreement_gamma_x25519Key_tr (hEquations : ExternCryptoLawsHold interpretation)
    (a : HwBytes) (pk : DY.Bytes) :
    interpretation x25519AgreementSymbol [a, gamma interpretation S g (DY.X25519.normalizeX25519Key pk)] =
      interpretation x25519AgreementSymbol [a, gamma interpretation S g pk] := by
  unfold DY.X25519.normalizeX25519Key
  split
  · rename_i x h; have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
    simp only [h] at hv; rw [← hv, gamma_x25519Variant_raw_tr _ _ _ x.key x.variation x.torsion]
    by_cases hl : (gamma interpretation S g x.key).length = 32
    · have hl' := (torsionShift_length_tr interpretation (gamma interpretation S g x.key) x.torsion).trans hl
      have hs := DY.Libsignal.Refinement.variantBytes_spec _ hl' x.variation
      rw [← hEquations.x25519_agreement_torsion_invariant a (gamma interpretation S g x.key) x.torsion]
      exact hEquations.x25519_agreement_reads_u_coordinate a _ _ hl' hs.1 hs.2.symm
    · have hts : DY.Libsignal.Refinement.torsionShift interpretation
          (gamma interpretation S g x.key) x.torsion = gamma interpretation S g x.key := by
        unfold DY.Libsignal.Refinement.torsionShift; simp [hl]
      rw [hts]
      unfold DY.Libsignal.Refinement.variantBytes; simp only [hl, ↓reduceIte]
  · rfl
private theorem gamma_dh_x25519Key_tr (hEquations : ExternCryptoLawsHold interpretation) (pk sk : DY.Bytes) :
    gamma interpretation S g (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key pk) sk) =
      (interpretation x25519AgreementSymbol [clamp (gamma interpretation S g sk), gamma interpretation S g pk]).getD [] := by
  rw [gamma_dh_tr interpretation S g hEquations, agreement_gamma_x25519Key_tr interpretation S g hEquations]
theorem length_gamma_createChain_snd_tr (rk pk sk : DY.Bytes) :
    (gamma interpretation S g (createChain rk pk sk).2).length = 32 := length_gamma_hmac_tr interpretation S g _ _
end GammaAndStateRelHelpers

theorem findReceiverChainKey_none_of_map_erase_tr
    {interpretation : ExternInterpretation} {S : SpqrSem} {g : Ghost}
    {r : RatchetState} {st : TRState} {their : PublicKey}
    (hMap : r.receiverChains.map eraseRecvChain = st.recv.map (modelRecvChainOfTr interpretation S g))
    (hNone : r.findReceiverChainKey their = .ok none) {pk : DY.Bytes}
    (hTheir : their = ⟨vec32 (gamma interpretation S g pk)⟩) :
    (∀ rc ∈ r.receiverChains, rc.senderRatchetKey ≠ their) ∧ findRecvChain st.recv pk = none := by
  have hci : r.findReceiverChainIndex their = none := findReceiverChainKey_ok_none r their hNone
  have hNoRc : ∀ rc ∈ r.receiverChains, rc.senderRatchetKey ≠ their := by
    intro rc hMem hEq; unfold RatchetState.findReceiverChainIndex at hci
    rw [List.findIdx?_eq_none_iff] at hci; have hFalse := hci rc hMem; simp [hEq] at hFalse
  refine ⟨hNoRc, ?_⟩
  unfold findRecvChain; rw [List.find?_eq_none]; intro c hc; simp only [beq_iff_eq]; intro hRkEq
  have hMemModel : modelRecvChainOfTr interpretation S g c ∈ st.recv.map (modelRecvChainOfTr interpretation S g) :=
    List.mem_map_of_mem hc
  rw [← hMap] at hMemModel; rcases List.mem_map.mp hMemModel with ⟨rc, hrcMem, hrcErase⟩
  have hSrk : rc.senderRatchetKey = ⟨vec32 (gamma interpretation S g c.ratchetKey)⟩ := by
    simpa [modelRecvChainOfTr] using congrArg ReceiverChain.senderRatchetKey hrcErase
  exact hNoRc rc hrcMem (by rw [hSrk, hRkEq, hTheir])
theorem setRecvChain_append_singleton_of_forall_ne_tr (ys : List RecvChain) (c c' : RecvChain)
    (hNo : ∀ y ∈ ys, y.ratchetKey ≠ c'.ratchetKey) (hEq : c.ratchetKey = c'.ratchetKey) :
    setRecvChain (ys ++ [c]) c' = ys ++ [c'] := by
  unfold setRecvChain; rw [List.map_append, List.map_singleton]
  simp only [hEq, beq_self_eq_true, ↓reduceIte]
  exact congrArg (· ++ [c']) (map_ite_ratchetKey_eq_self_tr hNo)

private theorem x25519_agreement_eq_gamma_dh_raw_tr
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (hEq : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    (their : PublicKey) (our : PrivateKey) (theirPk ourSk : DY.Bytes)
    (htheir : their.bytes.toList = gamma interpretation S g theirPk)
    (hour : (CryptoGames.Ratchet.clampScalar our.bytes).toList = clamp (gamma interpretation S g ourSk)) :
    ((cryptoOf' interpretation E D).X (CryptoGames.Ratchet.clampScalar our.bytes) their.bytes).toList =
      gamma interpretation S g (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key theirPk) ourSk) := by
  have hlen := hEq.x25519_agreement_length (CryptoGames.Ratchet.clampScalar our.bytes).toList their.bytes.toList
  dsimp only [cryptoOf']
  rw [Proofs.libsignal.RngG.CliPure.DecCrypto.vec32_toList_of_length_eq_32 _ hlen, hour, htheir,
    gamma_dh_x25519Key_tr interpretation S g hEq]
private theorem rootKdf_eq_gamma_kdfRk_tr
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (rk : CryptoGames.Ratchet.RootKey) (ikm : List (BitVec 8)) (rkSym dhSym : DY.Bytes)
    (hrk : CryptoGames.HMAC.keyToBytes32 rk = gamma interpretation S g rkSym)
    (hikm : ikm = gamma interpretation S g dhSym) :
    let F := sha256CompressFunction interpretation
    (CryptoGames.Ratchet.rootKdf F rk ikm).1 =
      CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (kdfRk rkSym dhSym).1) ∧
    CryptoGames.HMAC.keyToBytes32 (CryptoGames.Ratchet.rootKdf F rk ikm).1 =
      gamma interpretation S g (kdfRk rkSym dhSym).1 ∧
    (CryptoGames.Ratchet.rootKdf F rk ikm).2 =
      CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (kdfRk rkSym dhSym).2) ∧
    CryptoGames.HMAC.keyToBytes32 (CryptoGames.Ratchet.rootKdf F rk ikm).2 =
      gamma interpretation S g (kdfRk rkSym dhSym).2 ∧
    (gamma interpretation S g (kdfRk rkSym dhSym).1).length = 32 ∧
    (gamma interpretation S g (kdfRk rkSym dhSym).2).length = 32 := by
  intro F; obtain ⟨_, htake1, htake2⟩ := hkdf_64_whisperRatchet F (CryptoGames.Ratchet.rootSalt rk) ikm
  have hprk : hkdfExtract F (CryptoGames.Ratchet.rootSalt rk) ikm =
      gamma interpretation S g (DY.Libsignal.TripleRatchet.hmac rkSym dhSym) := by
    rw [gamma_hmac_tr, ← hrk, ← hikm]; rfl
  set prk := hkdfExtract F (CryptoGames.Ratchet.rootSalt rk) ikm
  have ht1 : HMAC.hmacWith F prk ([] ++ CryptoGames.Ratchet.whisperRatchetInfo ++ [1#8]) =
      gamma interpretation S g (kdfRk rkSym dhSym).1 := by
    dsimp only [kdfRk, hkdfBlock1]
    rw [gamma_hmac_tr, gamma_concat_tr, gamma_lit_whisperRatchet_tr, gamma_litByte_tr, ← hprk]; rfl
  have ht2 : HMAC.hmacWith F prk
      (HMAC.hmacWith F prk ([] ++ CryptoGames.Ratchet.whisperRatchetInfo ++ [1#8]) ++
        CryptoGames.Ratchet.whisperRatchetInfo ++ [2#8]) =
      gamma interpretation S g (kdfRk rkSym dhSym).2 := by
    dsimp only [kdfRk, hkdfBlock2]
    rw [gamma_hmac_tr, gamma_concat_tr, gamma_concat_tr, gamma_lit_whisperRatchet_tr, gamma_litByte_tr, ← hprk]
    change HMAC.hmacWith F prk (HMAC.hmacWith F prk ([] ++ CryptoGames.Ratchet.whisperRatchetInfo ++ [1#8]) ++
      CryptoGames.Ratchet.whisperRatchetInfo ++ [2#8]) =
      HMAC.hmacWith F prk (gamma interpretation S g (kdfRk rkSym dhSym).1 ++ (CryptoGames.Ratchet.whisperRatchetInfo ++ [2#8]))
    rw [← ht1, List.append_assoc]
  have hlen1 : (gamma interpretation S g (kdfRk rkSym dhSym).1).length = 32 := length_gamma_hmac_tr interpretation S g _ _
  have hlen2 : (gamma interpretation S g (kdfRk rkSym dhSym).2).length = 32 := length_gamma_hmac_tr interpretation S g _ _
  have hrk1 : (CryptoGames.Ratchet.rootKdf F rk ikm).1 =
      CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (kdfRk rkSym dhSym).1) := by
    dsimp only [CryptoGames.Ratchet.rootKdf]; rw [htake1, ht1]
  have hrk2 : (CryptoGames.Ratchet.rootKdf F rk ikm).2 =
      CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g (kdfRk rkSym dhSym).2) := by
    dsimp only [CryptoGames.Ratchet.rootKdf]; rw [htake2, ht2]
  exact ⟨hrk1, by rw [hrk1, keyToBytes32_bytesToKey32_tr _ hlen1],
    hrk2, by rw [hrk2, keyToBytes32_bytesToKey32_tr _ hlen2], hlen1, hlen2⟩
private theorem rootCreateChain_of_rel_not_lowOrder_raw_tr
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost) (hEq : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    (rk : CryptoGames.Ratchet.RootKey) (their : PublicKey) (our : PrivateKey) (rkSym theirPk ourSk : DY.Bytes)
    (hrk : CryptoGames.HMAC.keyToBytes32 rk = gamma interpretation S g rkSym)
    (htheir : their.bytes.toList = gamma interpretation S g theirPk)
    (hour : (CryptoGames.Ratchet.clampScalar our.bytes).toList = clamp (gamma interpretation S g ourSk))
    (hnot_zero : ((cryptoOf' interpretation E D).X (CryptoGames.Ratchet.clampScalar our.bytes)
      their.bytes).toList ≠ List.replicate 32 0#8) :
    let C := cryptoOf' interpretation E D
    let (rkSym', ckSym') := DY.Libsignal.TripleRatchet.createChain rkSym theirPk ourSk
    rootCreateChain C rk their our =
      .ok (CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g rkSym'),
           ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckSym'), 0⟩) ∧
    CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g rkSym')) =
      gamma interpretation S g rkSym' ∧
    CryptoGames.HMAC.keyToBytes32 (CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g ckSym')) =
      gamma interpretation S g ckSym' ∧
    (gamma interpretation S g rkSym').length = 32 ∧ (gamma interpretation S g ckSym').length = 32 := by
  intro C; dsimp only [DY.Libsignal.TripleRatchet.createChain, DY.X25519.agree]
  have hdh := x25519_agreement_eq_gamma_dh_raw_tr interpretation S g hEq E D their our theirPk ourSk htheir hour
  obtain ⟨hrk1, _, hrk2, _, hlen1, hlen2⟩ :=
    rootKdf_eq_gamma_kdfRk_tr interpretation S g rk
      ((cryptoOf' interpretation E D).X (CryptoGames.Ratchet.clampScalar our.bytes) their.bytes).toList
      rkSym (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key theirPk) ourSk) hrk hdh
  refine ⟨?_, keyToBytes32_bytesToKey32_tr _ hlen1,
    keyToBytes32_bytesToKey32_tr _ hlen2, hlen1, hlen2⟩
  unfold rootCreateChain CryptoGames.Ratchet.createChain; dsimp only [C]
  simp only [hnot_zero, ↓reduceIte, Proofs.libsignal.Hooks2.cryptoOf'_F]; rw [hrk1, hrk2]
private theorem uint32_sub_one_if_toBitVec_tr (ns : UInt32) :
    (if ns.toBitVec = 0 then (0 : BitVec 32) else ns.toBitVec - 1) =
      (if ns = 0 then (0 : UInt32) else ns - 1).toBitVec := by
  rcases ns with ⟨bv⟩
  by_cases h : bv = 0
  · subst h; rfl
  · have h' : (⟨bv⟩ : UInt32) ≠ 0 := fun hEq => h (congrArg UInt32.toBitVec hEq)
    simp only [h, h', ↓reduceIte]; rfl

theorem dhRatchetStep_ok_eq_gamma_trDhRatchetState
    (interpretation : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (hEquations : ExternCryptoLawsHold interpretation)
    (E D : CryptoGames.CBC.AesKey → CryptoGames.CBC.Block → CryptoGames.CBC.Block := fun _ b => b)
    {st : TRState} {s : CryptoGames.LibsignalSessionApi.Session (List (BitVec 8))}
    (hrel : StateRel interpretation S g st (sessionToRecordRec s))
    (hRkLen : (gamma interpretation S g st.rk).length = 32)
    (hDhsLen : (gamma interpretation S g st.dhs).length = 32)
    (hCkLens : ∀ c ∈ st.recv, (gamma interpretation S g c.chainKey).length = 32)
    {their : PublicKey} {pk : DY.Bytes}
    (hTheir : their = ⟨vec32 (gamma interpretation S g pk)⟩)
    (hPkLen : (gamma interpretation S g pk).length = 32)
    {rngIdx : Nat} {rngBytes : List (BitVec 8)}
    (hRng : g.σ rngIdx 32 = rngBytes) (hRngLen : rngBytes.length = 32)
    {ck_r : ChainKey} {r1 : RatchetState}
    (hStep :
      Mut.exec
        (RatchetState.dhRatchetStep (cryptoOf' interpretation E D) their (pinCoins (some rngBytes)))
        (ratchetStateOf s.state) = (.ok ck_r, r1)) :
    let (st1, c) := trDhRatchetState st pk rngIdx
    let sk' := CryptoGames.Ratchet.clampScalar (vec32 (gamma interpretation S g st1.dhs))
    ck_r = ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g c.chainKey), c.index.toBitVec⟩ ∧
    (gamma interpretation S g c.chainKey).length = 32 ∧
    (gamma interpretation S g st1.rk).length = 32 ∧
    (gamma interpretation S g st1.cks).length = 32 ∧
    r1.rootKey = CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g st1.rk) ∧
    CryptoGames.HMAC.keyToBytes32 r1.rootKey = gamma interpretation S g st1.rk ∧
    r1.previousCounter = st1.pn.toBitVec ∧
    r1.senderChain =
      some ⟨⟨⟨vec32 ((interpretation x25519PublicKeySymbol [sk'.toList]).getD [])⟩, ⟨sk'⟩⟩,
        ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g st1.cks), st1.ns.toBitVec⟩⟩ ∧
    r1.senderChain.map senderChainToChainRec =
      (sessionOf interpretation (gamma interpretation S g) st1).senderChain ∧
    r1.receiverChains =
      RatchetState.evictReceiverChains (s.state.receiverChains ++ [⟨their, some ck_r, []⟩]) ∧
    r1.receiverChains.length = st1.recv.length ∧
    r1.receiverChains[r1.receiverChains.length - 1]? =
      some (modelRecvChainOfTr interpretation S g c) ∧
    (∀ i < r1.receiverChains.length - 1,
      r1.receiverChains[i]? =
        s.state.receiverChains[(s.state.receiverChains.length + 1 -
          CryptoGames.LibsignalSession.maxReceiverChains) + i]?) ∧
    r1.receiverChains.map eraseRecvChain =
      st1.recv.map (modelRecvChainOfTr interpretation S g) := by
  let p := trDhRatchetState st pk rngIdx
  let sk' := CryptoGames.Ratchet.clampScalar (vec32 (gamma interpretation S g p.1.dhs))
  let dhsSym := randTerm rngIdx 32
  have hGammaDhs : gamma interpretation S g dhsSym = rngBytes := by rw [gamma_randTerm32, hRng]
  have hDhsSymLen : (gamma interpretation S g dhsSym).length = 32 := by rw [hGammaDhs, hRngLen]
  have hCoins : CryptoGames.HMAC.keyToBytes32 (pinCoins (some rngBytes)) =
      gamma interpretation S g dhsSym := by
    unfold pinCoins Symbolic.Swarm.CREF.CliPure.RpkCli.pureCoinsOf; dsimp only
    rw [List.take_append_of_le_length (Nat.le_of_eq hRngLen.symm),
        List.take_of_length_le (Nat.le_of_eq hRngLen), hGammaDhs]
    exact keyToBytes32_bytesToKey32_tr rngBytes hRngLen
  have hTheirList : their.bytes.toList = gamma interpretation S g pk := by
    rw [hTheir]; exact vec32_toList_of_length_eq_tr hPkLen
  let C := cryptoOf' interpretation E D
  let r0 : RatchetState := ratchetStateOf s.state
  obtain ⟨sc, newRootKey, finalRootKey, senderChainKey, hsc, hrc1, hrc2, hr1⟩ := dhRatchetStep_ok_inv hStep
  have hsc_s : s.state.senderChain = some sc := hsc
  have heq := (stateRel_sessionToRecordRec_iff_tr interpretation S g st s).mp hrel
  have hMap0 : s.state.receiverChains.map eraseRecvChain =
      st.recv.map (modelRecvChainOfTr interpretation S g) :=
    recvMap_of_stateRel_tr interpretation S g hrel hCkLens
  have hRoot0 : CryptoGames.HMAC.keyToBytes32 r0.rootKey = gamma interpretation S g st.rk := by
    have hrk := congrArg SessionRec.rootKey heq
    dsimp only [eraseSkipped, eraseUnmodelled, sessionToSessionRec, sessionOf, r0, ratchetStateOf] at hrk ⊢
    exact hrk
  have hScRec : s.state.senderChain.map senderChainToChainRec =
      (sessionOf interpretation (gamma interpretation S g) st).senderChain :=
    congrArg SessionRec.senderChain heq
  rw [hsc_s] at hScRec; dsimp only [Option.map_some, senderChainToChainRec, sessionOf] at hScRec
  injection hScRec with hcr
  have hPrivList : sc.ratchetKey.privateKey.bytes.toList =
      clamp (gamma interpretation S g st.dhs) :=
    congrArg ChainRec.senderRatchetKeyPrivate hcr
  have hScIdx : sc.chainKey.index = st.ns.toBitVec := by
    have hck := congrArg ChainRec.chainKey hcr
    dsimp only at hck; injection hck with hpair; exact congrArg Prod.fst hpair
  have hOur1 :
      (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes).toList =
        clamp (gamma interpretation S g st.dhs) := by
    rw [clampScalar_toList_eq_clamp_toList, hPrivList]
    exact DY.Libsignal.TripleRatchet.Refinement.clamp_clamp (gamma interpretation S g st.dhs)
  have hNotZero1 :
      (C.X (CryptoGames.Ratchet.clampScalar sc.ratchetKey.privateKey.bytes) their.bytes).toList ≠
        List.replicate 32 0#8 := by
    intro hZero
    have hErr := rootCreateChain_of_rel_lowOrder interpretation E D r0.rootKey their sc.ratchetKey.privateKey hZero
    rw [hrc1] at hErr; cases hErr
  obtain ⟨hrc1_ok, hNewRkBytes, _, _, hCkrLen⟩ :=
    rootCreateChain_of_rel_not_lowOrder_raw_tr interpretation S g hEquations E D r0.rootKey their
      sc.ratchetKey.privateKey st.rk pk st.dhs hRoot0 hTheirList hOur1 hNotZero1
  rw [hrc1] at hrc1_ok; injection hrc1_ok with hPair1; injection hPair1 with hNewRk hCk
  rw [← hNewRk] at hNewRkBytes
  have hCkEq : ck_r = ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g p.2.chainKey), 0⟩ := hCk
  have hkv : CryptoGames.Ratchet.keyToBytesVec32 (pinCoins (some rngBytes)) =
      vec32 (gamma interpretation S g dhsSym) := by
    apply Subtype.ext
    change CryptoGames.HMAC.keyToBytes32 (pinCoins (some rngBytes)) = (vec32 (gamma interpretation S g dhsSym)).toList
    rw [hCoins, vec32_toList_of_length_eq_tr hDhsSymLen]
  have hNewSkEq :
      KeyPair.generate C (pinCoins (some rngBytes)) =
        ⟨⟨vec32 ((interpretation x25519PublicKeySymbol [sk'.toList]).getD [])⟩, ⟨sk'⟩⟩ := by
    dsimp only [KeyPair.generate, C, cryptoOf', sk', p, trDhRatchetState, dhsSym]; rw [hkv]
  have hOur2 :
      (CryptoGames.Ratchet.clampScalar
        (KeyPair.generate C (pinCoins (some rngBytes))).privateKey.bytes).toList =
        clamp (gamma interpretation S g dhsSym) := by
    rw [hNewSkEq]; dsimp only [sk', p, trDhRatchetState, dhsSym]
    rw [Proofs.libsignal.RngG.CliPure.DecCrypto.clampScalar_idem]
    exact clampScalar_toList_eq_clamp (gamma interpretation S g dhsSym) hDhsSymLen
  have hNotZero2 :
      (C.X (CryptoGames.Ratchet.clampScalar
        (KeyPair.generate C (pinCoins (some rngBytes))).privateKey.bytes)
        their.bytes).toList ≠ List.replicate 32 0#8 := by
    intro hZero
    have hErr := rootCreateChain_of_rel_lowOrder interpretation E D
      newRootKey their (KeyPair.generate C (pinCoins (some rngBytes))).privateKey hZero
    rw [hrc2] at hErr; cases hErr
  obtain ⟨hrc2_ok, hFinalRkBytes, hSenderCkBytes, hFinalRkLen, hSenderCkLen⟩ :=
    rootCreateChain_of_rel_not_lowOrder_raw_tr interpretation S g hEquations E D
      newRootKey their (KeyPair.generate C (pinCoins (some rngBytes))).privateKey
      (createChain st.rk pk st.dhs).1 pk dhsSym hNewRkBytes hTheirList hOur2 hNotZero2
  rw [hrc2] at hrc2_ok; injection hrc2_ok with hPair2; injection hPair2 with hFinalRk hSenderCk
  have hCkrLen' : (gamma interpretation S g p.2.chainKey).length = 32 := hCkrLen
  have hFinalRkLen' : (gamma interpretation S g p.1.rk).length = 32 := hFinalRkLen
  have hSenderCkLen' : (gamma interpretation S g p.1.cks).length = 32 := hSenderCkLen
  subst hFinalRk hSenderCk
  have hP1Ns : p.1.ns = 0 := rfl
  have hP1Pn : p.1.pn = (if st.ns = 0 then 0 else st.ns - 1) := rfl
  have hSk'Eq : sk'.toList = clamp (gamma interpretation S g p.1.dhs) :=
    clampScalar_toList_eq_clamp (gamma interpretation S g dhsSym) hDhsSymLen
  let c : RecvChain := p.2
  have hNewRcEq :
      ({ senderRatchetKey := their
         chainKey := some ⟨CryptoGames.HKDF.bytesToKey32 (gamma interpretation S g p.2.chainKey), 0⟩
         messageKeys := [] } : ReceiverChain) =
      modelRecvChainOfTr interpretation S g c := by
    unfold modelRecvChainOfTr; dsimp only [c, p, trDhRatchetState]; rw [hTheir]; rfl
  have hLenRcEq : s.state.receiverChains.length = st.recv.length := by
    have h1 := congrArg List.length hMap0; simp only [List.length_map] at h1; exact h1
  have hMaxEq : CryptoGames.LibsignalSession.maxReceiverChains = DY.Libsignal.TripleRatchet.maxReceiverChains := rfl
  let dropCount := (s.state.receiverChains.length + 1) - CryptoGames.LibsignalSession.maxReceiverChains
  let rcs1 := (s.state.receiverChains ++ [modelRecvChainOfTr interpretation S g c]).drop dropCount
  have hDropCountEq : dropCount = (st.recv.length + 1) - DY.Libsignal.TripleRatchet.maxReceiverChains := by
    dsimp only [dropCount]; rw [hLenRcEq, hMaxEq]
  have hRcs1Map : rcs1.map eraseRecvChain = p.1.recv.map (modelRecvChainOfTr interpretation S g) := by
    dsimp only [rcs1, p, trDhRatchetState, c]
    rw [hDropCountEq, List.map_drop, List.map_append, hMap0, List.map_singleton,
      eraseRecvChain_modelRecvChainOfTr, List.map_drop, List.map_append, List.map_singleton]
  have hRcs1Len : rcs1.length = p.1.recv.length := by
    have h1 := congrArg List.length hRcs1Map; simp only [List.length_map] at h1; exact h1
  have hDropLt : dropCount < s.state.receiverChains.length + 1 := by
    dsimp only [dropCount]; change (s.state.receiverChains.length + 1) - 5 < s.state.receiverChains.length + 1; omega
  have hRcs1Last : rcs1[rcs1.length - 1]? = some (modelRecvChainOfTr interpretation S g c) := by
    dsimp only [rcs1]
    rw [List.getElem?_drop, List.length_drop, List.length_append, List.length_singleton]
    have hIdx : dropCount + (s.state.receiverChains.length + 1 - dropCount - 1) = s.state.receiverChains.length := by omega
    rw [hIdx, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self, List.getElem?_cons_zero]
  have hRcs1Prefix : ∀ i < rcs1.length - 1, rcs1[i]? = s.state.receiverChains[dropCount + i]? := by
    intro i hi; dsimp only [rcs1] at hi ⊢
    rw [List.length_drop, List.length_append, List.length_singleton] at hi
    rw [List.getElem?_drop, List.getElem?_append_left (by omega)]
  have hR1RcEq :
      RatchetState.evictReceiverChains (s.state.receiverChains ++ [⟨their, some ck_r, []⟩]) = rcs1 := by
    rw [hCkEq]; unfold RatchetState.evictReceiverChains
    rw [hNewRcEq, List.length_append, List.length_singleton]
  rw [hr1]; dsimp only [r0, ratchetStateOf]
  refine ⟨hCkEq, hCkrLen', hFinalRkLen', hSenderCkLen', rfl, hFinalRkBytes, ?_, ?_, ?_, rfl,
    hR1RcEq ▸ hRcs1Len, hR1RcEq ▸ hRcs1Last, hR1RcEq ▸ hRcs1Prefix, hR1RcEq ▸ hRcs1Map⟩
  · rw [hScIdx, hP1Pn, uint32_sub_one_if_toBitVec_tr st.ns]
  · rw [hNewSkEq, hP1Ns]; rfl
  · rw [hNewSkEq]
    have hPubLen : ((interpretation x25519PublicKeySymbol [sk'.toList]).getD []).length = 32 :=
      hEquations.x25519_public_key_length sk'.toList
    dsimp only [Option.map_some, senderChainToChainRec, PublicKey.serialize,
      CryptoGames.LibsignalSession.djbType, Symbolic.Swarm.CREF.TR.serializedKey, ecKey, sessionOf]
    rw [vec32_toList_of_length_eq_tr hPubLen, hSk'Eq, hP1Ns, hSenderCkBytes]; rfl

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep
