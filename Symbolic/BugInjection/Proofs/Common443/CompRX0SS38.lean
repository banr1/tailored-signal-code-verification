/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRX0Split38
public import Symbolic.BugInjection.Proofs.Common443.CompRPlantWire
public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompFitsNames
public import Symbolic.BugInjection.Proofs.Common443.Census443Defs
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupHighBitComp
public import Symbolic.BugInjection.Proofs.Fixtures.Cheval26SmallSubgroupTorsionComp

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0SS38
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
open DY.Libsignal.TripleRatchet.Refinement (wireWhisperTag)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol kyberDecapsSymbol)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompRPlantWire Symbolic.BugInjection.Proofs.Common443.CompRFaithfulInner Symbolic.BugInjection.Proofs.Common443.CompRX0Top
open Symbolic.BugInjection.Proofs.Common443.CompRX0Gamma (coinHeads)
private theorem eventBytes_rng (bs : HwBytes) : CompRPlantWire.eventBytes (.rng bs) = bs := rfl
private theorem eventBytes_pt (bs : HwBytes) : CompRPlantWire.eventBytes (.pt bs) = bs := rfl
def bunBytes : HwBytes := CompRPlantWire.eventBytes (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.headD (.recv []))
def b0Bytes : HwBytes := CompRPlantWire.eventBytes ((Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 1).headD (.rng []))
def rsT : List MachineEvent := (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 2).take 33
def ptB : HwBytes := CompRPlantWire.eventBytes ((Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 35).headD (.pt []))
def cB : HwBytes := CompRPlantWire.eventBytes ((Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 36).headD (.rng []))
theorem rsT_coinHeads_eq : coinHeads (rsT.take 32) = compKyberE0 := by decide +kernel
theorem clamp_b0_lookup : compLookupPub (clamp b0Bytes) = compEkAPub := by decide +kernel
attribute [local irreducible] Symbolic.BugInjection.hexBytes
theorem rsT_len : rsT.length = 33 := rfl
theorem rsT_kind : ∀ e ∈ (MachineEvent.rng b0Bytes :: rsT), eventKind e = .rng := by decide
def bunChars : List Char := chars_of_hex_def bunBytes
theorem bun_head_eq : Witnesses.Cheval26SmallSubgroupHighBitComp.trace.headD (.recv []) = .recv (hexBytes (str_of_hex_def bunBytes)) := rfl
theorem bunStr_eq : (str_of_hex_def bunBytes) = String.ofList bunChars := rfl
theorem bunBytes_eq : bunBytes = hexBytes.go hexDigit bunChars := by have h : bunBytes = hexBytes (str_of_hex_def bunBytes) := (congrArg CompRPlantWire.eventBytes bun_head_eq).trans (eventBytes_recv _); rw [h, bunStr_eq, hexBytes_ofList]
def bunFast : HwBytes := hexBytes.go hexDigit bunChars
theorem bunFast_getElem4_ne : bunFast[4]? ≠ some 1#8 := by decide +kernel
theorem bunBytes_getElem4_ne : bunBytes[4]? ≠ some 1#8 := by rw [bunBytes_eq]; exact bunFast_getElem4_ne
theorem bunBytes_eq_hex : bunBytes = hexBytes (str_of_hex_def bunBytes) := (congrArg CompRPlantWire.eventBytes bun_head_eq).trans (eventBytes_recv _)
theorem b0_head_eq : (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 1).headD (.rng []) = .rng (hexBytes (str_of_hex_def b0Bytes)) := rfl
theorem b0Bytes_eq_hex : b0Bytes = hexBytes (str_of_hex_def b0Bytes) := (congrArg CompRPlantWire.eventBytes b0_head_eq).trans (eventBytes_rng _)
theorem pt_head_eq : (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 35).headD (.pt []) = .pt (hexBytes (str_of_hex_def ptB)) := rfl
theorem ptB_eq_hex : ptB = hexBytes (str_of_hex_def ptB) := (congrArg CompRPlantWire.eventBytes pt_head_eq).trans (eventBytes_pt _)
theorem c_head_eq : (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 36).headD (.rng []) = .rng (hexBytes (str_of_hex_def cB)) := rfl
theorem cB_eq_hex : cB = hexBytes (str_of_hex_def cB) := (congrArg CompRPlantWire.eventBytes c_head_eq).trans (eventBytes_rng _)
theorem sentWireBytes_eq_hex : sentWireBytes = hexBytes (str_of_hex_def sentWireBytes) := (congrArg CompRPlantWire.eventBytes sentWire_head_eq).trans (CompRPlantWire.eventBytes_send _)
theorem highBitComp_take38_hex : Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38 = (.recv (hexBytes (str_of_hex_def bunBytes)) :: .rng (hexBytes (str_of_hex_def b0Bytes)) :: rsT) ++ [.pt (hexBytes (str_of_hex_def ptB)), .rng (hexBytes (str_of_hex_def cB)), .send (hexBytes (str_of_hex_def sentWireBytes))] := rfl
theorem torsionComp_take38_hex : Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38 = (.recv (hexBytes (str_of_hex_def bunBytes)) :: .rng (hexBytes (str_of_hex_def b0Bytes)) :: rsT) ++ [.pt (hexBytes (str_of_hex_def ptB)), .rng (hexBytes (str_of_hex_def cB)), .send (hexBytes (str_of_hex_def sentWireBytes))] := rfl
theorem highBitComp_take38 : Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38 = (.recv bunBytes :: .rng b0Bytes :: rsT) ++ [.pt ptB, .rng cB, .send sentWireBytes] := by rw [bunBytes_eq_hex, b0Bytes_eq_hex, ptB_eq_hex, cB_eq_hex, sentWireBytes_eq_hex]; exact highBitComp_take38_hex
theorem torsionComp_take38 : Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38 = (.recv bunBytes :: .rng b0Bytes :: rsT) ++ [.pt ptB, .rng cB, .send sentWireBytes] := by rw [bunBytes_eq_hex, b0Bytes_eq_hex, ptB_eq_hex, cB_eq_hex, sentWireBytes_eq_hex]; exact torsionComp_take38_hex
theorem sentWireFast_head_ne : sentWireFast.head? ≠ some wireWhisperTag := by decide +kernel
theorem sentWireBytes_head_ne : sentWireBytes.head? ≠ some wireWhisperTag := by rw [sentWireBytes_eq]; exact sentWireFast_head_ne
theorem sentWireFast_hasTag4 : CompRBobInit.hasTag4 sentWireFast = false := by decide +kernel
theorem sentWireBytes_hasTag4 : CompRBobInit.hasTag4 sentWireBytes = false := by rw [sentWireBytes_eq]; exact sentWireFast_hasTag4
theorem sentWireFast_len : sentWireFast.length < 2 ^ 63 := by decide +kernel
theorem sentWireBytes_len : sentWireBytes.length < 2 ^ 63 := by rw [sentWireBytes_eq]; exact sentWireFast_len
theorem sentWireFast_baseKey : (parsePreKeyWire sentWireFast).map (·.baseKey) = some (ecKey compEkAPub) := by decide +kernel
theorem sentWireFast_kyberCiphertext : (parsePreKeyWire sentWireFast).bind (·.kyberCiphertext) = some (kyberKey compKyberCt0) := by decide +kernel
theorem sentWireBytes_baseKey {q₀ : PreKeyFields} (hq₀ : parsePreKeyWire sentWireBytes = some q₀) : q₀.baseKey = ecKey (compLookupPub (clamp b0Bytes)) := by have h1 := sentWireFast_baseKey; rw [sentWireBytes_eq] at hq₀; change parsePreKeyWire sentWireFast = some q₀ at hq₀; rw [hq₀] at h1; rw [clamp_b0_lookup]; exact Option.some.inj h1
theorem sentWireBytes_kyberCiphertext {q₀ : PreKeyFields} (hq₀ : parsePreKeyWire sentWireBytes = some q₀) : q₀.kyberCiphertext = some (kyberKey compKyberCt0) := by have h1 := sentWireFast_kyberCiphertext; rw [sentWireBytes_eq] at hq₀; change parsePreKeyWire sentWireFast = some q₀ at hq₀; rw [hq₀] at h1; exact h1
theorem compKyberEncaps_e0_take1568 : (compKyberEncaps compKyberE0).take 1568 = compKyberCt0 := by decide +kernel
theorem compI0_kyberEncaps_rsT (pk : CryptoProofLib.Refinement.ByteString) : ((compI0 kyberEncapsSymbol [pk, coinHeads (rsT.take 32)]).getD []).take 1568 = compKyberCt0 := by have h0 : compI0 kyberEncapsSymbol [pk, coinHeads (rsT.take 32)] = some (compKyberEncaps (coinHeads (rsT.take 32))) := rfl; rw [h0, Option.getD_some, rsT_coinHeads_eq, compKyberEncaps_e0_take1568]
def wirePairOk (w b : HwBytes) (bk : HwBytes) : Bool :=
  match parsePreKeyWire w, parsePreKeyWire b with
  | some q, some p =>
    decide (p.baseKey.take 33 = ecKey bk) && decide (p.kyberCiphertext = q.kyberCiphertext) &&
      decide (p.message = q.message) && decide (p.preKeyId = none) && decide (spqrIdx p = 1)
  | _, _ => false
theorem wirePairOk_spec {w b bk : HwBytes} (h : wirePairOk w b bk = true) {q p : PreKeyFields} (hq : parsePreKeyWire w = some q) (hp : parsePreKeyWire b = some p) : p.baseKey.take 33 = ecKey bk ∧ p.kyberCiphertext = q.kyberCiphertext ∧ p.message = q.message ∧ p.preKeyId = none ∧ spqrIdx p = 1 := by unfold wirePairOk at h; rw [hq, hp] at h; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
theorem wirePairOk_highBitFast : wirePairOk sentWireFast highBitWireFast (variantBytes compEkAPub 1) = true := by decide +kernel
theorem wirePairOk_torsionFast : wirePairOk sentWireFast torsionWireFast compEkATorsion = true := by decide +kernel
theorem wirePairOk_highBit : wirePairOk sentWireBytes highBitWireBytes (variantBytes compEkAPub 1) = true := by rw [sentWireBytes_eq, highBitWireBytes_eq]; exact wirePairOk_highBitFast
theorem wirePairOk_torsion : wirePairOk sentWireBytes torsionWireBytes compEkATorsion = true := by rw [sentWireBytes_eq, torsionWireBytes_eq]; exact wirePairOk_torsionFast
theorem checkOuter_highBitFast : CompFitsNames.checkPreKeyOuter Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 highBitWireFast = true := by decide +kernel
theorem checkOuter_torsionFast : CompFitsNames.checkPreKeyOuter Witnesses.Cheval26SmallSubgroupTorsionComp.setup compI0 torsionWireFast = true := by decide +kernel
theorem outer_highBit {r : Records} {p : PreKeyFields} (hf : compFits Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r) (hp : parsePreKeyWire highBitWireBytes = some p) : CompRPreKeyWire.PreKeyOuterMatches compI0 r highBitWireBytes p := by rw [highBitWireBytes_eq] at hp ⊢; exact CompFitsNames.preKeyOuterMatches_of_check hf hp checkOuter_highBitFast
theorem outer_torsion {r : Records} {p : PreKeyFields} (hf : compFits Witnesses.Cheval26SmallSubgroupTorsionComp.setup compI0 r) (hp : parsePreKeyWire torsionWireBytes = some p) : CompRPreKeyWire.PreKeyOuterMatches compI0 r torsionWireBytes p := by rw [torsionWireBytes_eq] at hp ⊢; exact CompFitsNames.preKeyOuterMatches_of_check hf hp checkOuter_torsionFast
theorem highBitComp_compSecretIdx_bobId : compSecretIdx (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.bobId) = some ⟨4, by decide⟩ := by decide +kernel
theorem highBitComp_compSecretIdx_spk : compSecretIdx (clamp Witnesses.Cheval26SmallSubgroupHighBitComp.setup.spk) = some ⟨3, by decide⟩ := by decide +kernel
theorem torsionComp_compSecretIdx_bobId : compSecretIdx (clamp Witnesses.Cheval26SmallSubgroupTorsionComp.setup.bobId) = some ⟨4, by decide⟩ := by decide +kernel
theorem torsionComp_compSecretIdx_spk : compSecretIdx (clamp Witnesses.Cheval26SmallSubgroupTorsionComp.setup.spk) = some ⟨3, by decide⟩ := by decide +kernel
theorem torsionShift_compEkAPub_one : DY.Libsignal.Refinement.torsionShift compI0 compEkAPub 1 = compEkATorsion := by decide +kernel
open DY.Libsignal.Refinement (torsionShift) in
theorem gamma_x25519TorsionVariant' (S : Sem) (g : Ghost) (k : DY.Bytes) (v : Fin 4) (t : Fin 8) (hvt : ¬ (v = 0 ∧ t = 0)) : gamma compI0 S g (DY.X25519.x25519TorsionVariant k v t) = variantBytes (torsionShift compI0 (gamma compI0 S g (DY.X25519.x25519Key k)) t) v := by
  have hdef : DY.X25519.x25519TorsionVariant k v t = ({ key := DY.X25519.x25519Key k, variation := v, torsion := t } :
        DY.X25519.Variant.SubF DY.Bytes).pack := by
    unfold DY.X25519.x25519TorsionVariant; simp only [hvt, ite_false]
  rw [hdef]; unfold gamma gamma'
  show ((({ key := DY.X25519.x25519Key k, variation := v, torsion := t } : DY.X25519.Variant.SubF DY.Bytes).pack).rec (gAll compI0 S g)).val = _
  rw [DY.Bytes.rec_eq (gVariant0 compI0) (gAll compI0 S g)]; rfl
theorem census_highBitWireBytes : Census443Defs.highBitWireBytes = highBitWireBytes := by
  unfold Census443Defs.highBitWireBytes highBitWireBytes; generalize (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.drop 38).headD (.recv []) = ev
  cases ev <;> rfl
theorem census_torsionWireBytes : Census443Defs.torsionWireBytes = torsionWireBytes := by
  unfold Census443Defs.torsionWireBytes torsionWireBytes; generalize (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.drop 38).headD (.recv []) = ev
  cases ev <;> rfl
theorem census_iniAliceOut : Census443Defs.iniAliceOut = Symbolic.Swarm.COMPOSED.CompTrace.aliceOut := rfl
theorem census_iniAliceStartState : Census443Defs.iniAliceStartState = CompPrefixInvBundle.aliceStartState := rfl
theorem census_iniAliceStartTr : Census443Defs.iniAliceStartTr = CompPrefixInvBundle.aliceStartTrOfOut := rfl
theorem census_encOut : Census443Defs.encOut = CompPrefixInvEnc.encOut := rfl
theorem census_invisibleNoEffect {tr : ExecTrace} {m : Move}
    (hnb : CompRX0Top.NoBrkTr (m.next tr))
    (h : Symbolic.Swarm.CREF.InvisibleNoEffect tr m) : Census443Defs.InvisibleNoEffect tr m := by
  refine ⟨h.1, fun i hi => ⟨(h.2 i hi).1, ?_, (h.2 i hi).2.2.1, (h.2 i hi).2.2.2⟩⟩
  cases heq : ((m.next tr).at? i : Option Symbolic.Swarm.COMPOSED.CompTrace.PQXDHEntry) with
  | none => rfl
  | some e =>
    have htrue := (h.2 i hi).2.1 e heq
    have hfalse := hnb i e heq
    rw [htrue] at hfalse; cases hfalse
theorem movesFrom_to_census443 {tr : ExecTrace} {δ : List Move}
    (hnb : CompRX0Top.NoBrkTr (runMoves δ tr).1)
    (h : Symbolic.Swarm.CREF.MovesFrom Symbolic.Swarm.CREF.InvisibleNoEffect tr δ) :
    Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect tr δ := by
  induction δ generalizing tr with
  | nil => trivial
  | cons m δ ih =>
    exact ⟨census_invisibleNoEffect (CompRX0Top.noBrkTr_of_le (Symbolic.Swarm.CREF.runMoves_le δ (m.next tr)) hnb) h.1,
      ih hnb h.2⟩
def Split38DecompSwapRep' (setup : PQXDHSpqrSetup) (who : List Participant) (ok : Nat → Bool) (τ₁ : List MachineEvent) (recvMsg38 : HwBytes) (v : Fin 4) (t : Fin 8) : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned setup compI0 r → CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S who ok g ms τ₁ → parsePreKeyWire recvMsg38 = some p → ∃ (pre mid post : List Move) (hb : DY.Libsignal.PQXDH.BundleHandles) (shown cl e c' : Nat),
      let tr₁ := (runMoves pre (setupTrace r)).1; let o := Census443Defs.iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let stA := Census443Defs.iniAliceStartState tr₁ r.bob o; let ms₀ := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c')) :: post; let ms' := pre ++ m₀ :: mid ++ .encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, Census443Defs.encOut tr₂ stA cl (tr₂.length + 2)⟩;
      Compat compI0 r S g ∧ ModelRun r ms₀ ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) τ₁ (runVis r ms₀) ∧
      Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect (setupTrace r) pre ∧ Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect (m₀.next tr₁) mid ∧
      Census443Defs.MovesFrom Census443Defs.InvisibleNoEffect
        ((Move.encrypt r.alice (tr₁.length + 8) cl (tr₂.length + 2) (some (e, c'))).next tr₂) post ∧
      m₀.next tr₁ = Census443Defs.iniAliceStartTr tr₁ r.alice r.bob o ∧ bobDoneBaseKeys (runTraceMoves r ms₀) = [] ∧
      ExplainsMoves compI0 r S who ok g ms' τ₁ ∧ x₀ ∈ preKeyRepresentations compI0 r S g ms' recvMsg38
def NoBsc38HB' : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned Witnesses.Cheval26SmallSubgroupHighBitComp.setup compI0 r → CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S Witnesses.Cheval26SmallSubgroupHighBitComp.who Witnesses.Cheval26SmallSubgroupHighBitComp.ok g ms (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) → parsePreKeyWire Census443Defs.highBitWireBytes = some p → ∃ g' ms', ExplainsMoves compI0 r S Witnesses.Cheval26SmallSubgroupHighBitComp.who Witnesses.Cheval26SmallSubgroupHighBitComp.ok g' ms' (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' Census443Defs.highBitWireBytes, ¬ BobStartCollision compI0 r S g' ms' p x
def NoBsc38TC' : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (p : PreKeyFields), compFitsPinned Witnesses.Cheval26SmallSubgroupTorsionComp.setup compI0 r → CompSetupSecrecy.NoBrk r ms → ExplainsMoves compI0 r S Witnesses.Cheval26SmallSubgroupTorsionComp.who Witnesses.Cheval26SmallSubgroupTorsionComp.ok g ms (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) → parsePreKeyWire Census443Defs.torsionWireBytes = some p → ∃ g' ms', ExplainsMoves compI0 r S Witnesses.Cheval26SmallSubgroupTorsionComp.who Witnesses.Cheval26SmallSubgroupTorsionComp.ok g' ms' (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) ∧ ∃ x ∈ preKeyRepresentations compI0 r S g' ms' Census443Defs.torsionWireBytes, ¬ BobStartCollision compI0 r S g' ms' p x
theorem noBsc38HB_of' (hNbsc : Census443Defs.NbscHighBitComp') (hDecomp : Split38DecompSwapRep' Witnesses.Cheval26SmallSubgroupHighBitComp.setup Witnesses.Cheval26SmallSubgroupHighBitComp.who Witnesses.Cheval26SmallSubgroupHighBitComp.ok (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) Census443Defs.highBitWireBytes 1 0) : NoBsc38HB' := by intro r S g ms p hfits hnb hex hp; obtain ⟨pre, mid, post, hb, shown, cl, e, c', hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hx₀⟩ := hDecomp r S g ms p hfits hnb hex hp; exact ⟨g, _, hex', _, hx₀, hNbsc compI0 r S hfits g p hp pre mid post hb shown cl e c' hc hmr hvis hpre hmid hpost hm₀ hnil⟩
theorem noBsc38TC_of' (hNbsc : Census443Defs.NbscTorsionComp') (hDecomp : Split38DecompSwapRep' Witnesses.Cheval26SmallSubgroupTorsionComp.setup Witnesses.Cheval26SmallSubgroupTorsionComp.who Witnesses.Cheval26SmallSubgroupTorsionComp.ok (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) Census443Defs.torsionWireBytes 0 1) : NoBsc38TC' := by intro r S g ms p hfits hnb hex hp; obtain ⟨pre, mid, post, hb, shown, cl, e, c', hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hx₀⟩ := hDecomp r S g ms p hfits hnb hex hp; exact ⟨g, _, hex', _, hx₀, hNbsc compI0 r S hfits g p hp pre mid post hb shown cl e c' hc hmr hvis hpre hmid hpost hm₀ hnil⟩
theorem split38DecompSwapRep_highBitComp : Split38DecompSwapRep' Witnesses.Cheval26SmallSubgroupHighBitComp.setup Witnesses.Cheval26SmallSubgroupHighBitComp.who Witnesses.Cheval26SmallSubgroupHighBitComp.ok (Witnesses.Cheval26SmallSubgroupHighBitComp.trace.take 38) Census443Defs.highBitWireBytes 1 0 := by
  intro r S g ms p hfits hnb hex hp; rw [census_highBitWireBytes] at hp ⊢; rw [census_iniAliceOut, census_iniAliceStartState, census_iniAliceStartTr, census_encOut]
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hb, hs, -, -, -, -, hEq, -, -⟩
  have hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩ := by rw [hb]; exact highBitComp_compSecretIdx_bobId
  have hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩ := by rw [hs]; exact highBitComp_compSecretIdx_spk
  obtain ⟨q₀, hq₀, -⟩ := sentWireBytes_innerWireCanonical.1; have hcan : InnerWireCanonical p := highBitWireBytes_innerWireCanonical.2 p hp; obtain ⟨hpbk, hkc, hpm, -, -⟩ := wirePairOk_spec wirePairOk_highBit hq₀ hp
  obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hmem'⟩ := CompRX0Top.split38_decomp_swap_rep_top (v := 1) (t := 0) hwf.1 hnb hEq hs1 hs2 highBitComp_take38 rsT_len rsT_kind bunBytes_getElem4_ne sentWireBytes_head_ne sentWireBytes_hasTag4 sentWireBytes_len hq₀ (sentWireBytes_baseKey hq₀)
      (fun _ => by rw [sentWireBytes_kyberCiphertext hq₀, compI0_kyberEncaps_rsT])
      hp
      (fun k hk hγ => by
        rw [gamma_x25519TorsionVariant' S g k 1 0 (by decide), hk, hγ, clamp_b0_lookup]
        exact hpbk)
      hkc hpm hcan (outer_highBit hfits.1 hp) (CompRX0Split38.attackerKnows_torsionVariant 1 0) hex
  obtain ⟨hnb_pre, hnb_mid, hnb_post⟩ := CompRX0Top.noBrkTr_split38 (hms_eq ▸ hnb)
  exact ⟨pre, mid, post, hb_eq, shown, cl, e, c', hc, hmr, hvis, movesFrom_to_census443 hnb_pre hpre, movesFrom_to_census443 hnb_mid hmid, movesFrom_to_census443 hnb_post hpost, hm₀, hnil, hex', hmem'⟩
theorem split38DecompSwapRep_torsionComp : Split38DecompSwapRep' Witnesses.Cheval26SmallSubgroupTorsionComp.setup Witnesses.Cheval26SmallSubgroupTorsionComp.who Witnesses.Cheval26SmallSubgroupTorsionComp.ok (Witnesses.Cheval26SmallSubgroupTorsionComp.trace.take 38) Census443Defs.torsionWireBytes 0 1 := by
  intro r S g ms p hfits hnb hex hp; rw [census_torsionWireBytes] at hp ⊢; rw [census_iniAliceOut, census_iniAliceStartState, census_iniAliceStartTr, census_encOut]
  rcases hfits.1 with ⟨hwf, -, -, -, -, -, -, hb, hs, -, -, -, -, hEq, -, -⟩
  have hs1 : compSecretIdx (clamp (secretBytes r 1)) = some ⟨4, by decide⟩ := by rw [hb]; exact torsionComp_compSecretIdx_bobId
  have hs2 : compSecretIdx (clamp (secretBytes r 2)) = some ⟨3, by decide⟩ := by rw [hs]; exact torsionComp_compSecretIdx_spk
  obtain ⟨q₀, hq₀, -⟩ := sentWireBytes_innerWireCanonical.1; have hcan : InnerWireCanonical p := torsionWireBytes_innerWireCanonical.2 p hp; obtain ⟨hpbk, hkc, hpm, -, -⟩ := wirePairOk_spec wirePairOk_torsion hq₀ hp
  have hv0 : variantBytes compEkATorsion 0 = compEkATorsion := by decide +kernel
  obtain ⟨pre, mid, post, hb_eq, shown, cl, e, c', hms_eq, hc, hmr, hvis, hpre, hmid, hpost, hm₀, hnil, hex', hmem'⟩ := CompRX0Top.split38_decomp_swap_rep_top (v := 0) (t := 1) hwf.1 hnb hEq hs1 hs2 torsionComp_take38 rsT_len rsT_kind bunBytes_getElem4_ne sentWireBytes_head_ne sentWireBytes_hasTag4 sentWireBytes_len hq₀ (sentWireBytes_baseKey hq₀)
      (fun _ => by rw [sentWireBytes_kyberCiphertext hq₀, compI0_kyberEncaps_rsT])
      hp
      (fun k hk hγ => by
        rw [gamma_x25519TorsionVariant' S g k 0 1 (by decide), hk, hγ, clamp_b0_lookup, torsionShift_compEkAPub_one, hv0]
        exact hpbk)
      hkc hpm hcan (outer_torsion hfits.1 hp) (CompRX0Split38.attackerKnows_torsionVariant 0 1) hex
  obtain ⟨hnb_pre, hnb_mid, hnb_post⟩ := CompRX0Top.noBrkTr_split38 (hms_eq ▸ hnb)
  exact ⟨pre, mid, post, hb_eq, shown, cl, e, c', hc, hmr, hvis, movesFrom_to_census443 hnb_pre hpre, movesFrom_to_census443 hnb_mid hmid, movesFrom_to_census443 hnb_post hpost, hm₀, hnil, hex', hmem'⟩
end Symbolic.BugInjection.Proofs.Common443.CompRX0SS38
