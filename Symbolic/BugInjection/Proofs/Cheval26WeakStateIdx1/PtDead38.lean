/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35
public import Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
import Symbolic.DYBridge.DY.Bytes.Basic

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38
open CryptoProofLib.Refinement (ExternInterpretation)
open ByteSpecs DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop hiding compI0
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
attribute [local irreducible] Symbolic.BugInjection.hexBytes
def PtAvoid (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : HwBytes) (t : DY.Bytes) : Prop := ∀ x ∈ (gamma' i S g t).memo, assumedInjective x.1 = true → x.2.2 ≠ b
def PtAvoidFull (i : ExternInterpretation) (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (b : HwBytes) (t : DY.Bytes) : Prop := ∀ x ∈ (gamma' i S g t).memo, x.1 ∉ ptAtoms (runVis r ms) → assumedInjective x.1 = true → ¬ x.1.AttackerKnows (runTraceMoves r ms) → x.2.2 ≠ b
theorem PtAvoid.full {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {t : DY.Bytes} (h : PtAvoid i S g b t) : PtAvoidFull i r S g ms b t := fun x hx _ hinj _ => h x hx hinj
theorem ptAvoid_of_memoInjGt {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : Nat} {b : HwBytes} {t : DY.Bytes} (hk : b.length ≤ k) (h : MemoInjGt i S g k t) : PtAvoid i S g b t := by
  intro x hx hinj heq; have hgt := h x hx hinj; rw [heq] at hgt; omega
theorem ptAvoidFull_of_memoInjGt {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {k : Nat} {b : HwBytes} {t : DY.Bytes} (hk : b.length ≤ k) (h : MemoInjGt i S g k t) : PtAvoidFull i r S g ms b t := (ptAvoid_of_memoInjGt hk h).full
section Nodes
variable {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes}
theorem ptAvoidFull_lit (bs : ByteArray) : PtAvoidFull i r S g ms b (({ lit := bs } : DY.Literal.Literal.SubF DY.Bytes).pack) := ptAvoidFull_of_memoInjGt (k := b.length) (Nat.le_refl _) (memoInjGt_lit i S g _ bs)
theorem ptAvoidFull_literalToBytes (bs : ByteArray) : PtAvoidFull i r S g ms b (DY.Literal.literalToBytes bs) := ptAvoidFull_lit bs
theorem ptAvoidFull_randTerm_ptAtom {idx sz : Nat} (hpt : randTerm idx sz ∈ ptAtoms (runVis r ms)) : PtAvoidFull i r S g ms b (randTerm idx sz) := by
  intro x hx hnpt _ _; unfold gamma' randTerm at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx; dsimp only [gRandom, concretizeRandom] at hx
  split_ifs at hx with hsz; cases hx; rcases List.mem_singleton.mp hx with rfl; exact absurd hpt hnpt
theorem ptAvoidFull_randTerm_ne {idx sz : Nat} (h : sz = 0 ∨ g.σ idx sz ≠ b) : PtAvoidFull i r S g ms b (randTerm idx sz) := by
  intro x hx _ _ _; unfold gamma' randTerm at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx; dsimp only [gRandom, concretizeRandom] at hx
  split_ifs at hx with hsz; cases hx; rcases List.mem_singleton.mp hx with rfl; exact h.resolve_left hsz
theorem ptAvoidFull_randTerm_of_pin {idx sz : Nat} {c : HwBytes} (hpin : [gamma i S g (randTerm idx sz)] = [c]) (hlt : b.length < c.length) : PtAvoidFull i r S g ms b (randTerm idx sz) := by
  by_cases hsz : sz = 0
  · exact ptAvoidFull_randTerm_ne (.inl hsz)
  · have hγ := (List.cons.inj hpin).1; unfold gamma at hγ; rw [gamma'_randTerm i S g idx sz hsz] at hγ; dsimp only at hγ
    exact ptAvoidFull_randTerm_ne (.inr fun h => by rw [h] at hγ; rw [hγ] at hlt; exact Nat.lt_irrefl _ hlt)
theorem ptAvoidFull_concat {a c : DY.Bytes} (ha : PtAvoidFull i r S g ms b a) (hc : PtAvoidFull i r S g ms b c) : PtAvoidFull i r S g ms b (DY.Concat.concat a c) := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show DY.Concat.concat a c = ({ lhs := a, rhs := c } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gConcat0 (gAll i S g)] at hx
  simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxc
  · rw [show (({ lhs := a, rhs := c } : DY.Concat.Concat.SubF DY.Bytes).pack) = DY.Concat.concat a c from rfl,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq] at hinj
    cases hinj
  · exact ha x hxa hnpt hinj hnk
  · exact hc x hxc hnpt hinj hnk
theorem ptAvoidFull_prefixTerms (hsend : ∀ v ∈ runVis r ms, v.kind = .send → ∀ u ∈ v.terms, PtAvoidFull i r S g ms b u) (hstates : ∀ ls ∈ storedStates r (runTraceMoves r ms), PtAvoidFull i r S g ms b (Comparse.serialize ls)) (hsecrets : ∀ u ∈ storedSecrets (runTraceMoves r ms), PtAvoidFull i r S g ms b u) (hpt : ∀ v ∈ runVis r ms, v.kind = .pt → ∀ u ∈ v.terms, PtAvoidFull i r S g ms b u) : ∀ u ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), PtAvoidFull i r S g ms b u := by
  intro u hu; unfold prefixTerms principalTerms plaintextTerms at hu; simp only [List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_map, beq_iff_eq] at hu
  rcases hu with ((⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩ | ⟨ls, hls, rfl⟩) | hsec) | ⟨v, ⟨hv_mem, hv_kind⟩, hu_v⟩
  · exact hsend v hv_mem hv_kind u hu_v
  · exact hstates ls hls
  · exact hsecrets u hsec
  · exact hpt v hv_mem hv_kind u hu_v
theorem ptAvoidFull_kdfExtract_of_lt32 {salt ikm : DY.Bytes} (hb : b.length < 32) (hs : PtAvoidFull i r S g ms b salt) (hm : PtAvoidFull i r S g ms b ikm) : PtAvoidFull i r S g ms b (DY.KdfExtract.kdfExtract salt ikm) := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show DY.KdfExtract.kdfExtract salt ikm = ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)] at hx
  simp only [gKdf0, concretizeKdf, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxs | hxm
  · intro heq; have hlen := congrArg List.length heq; dsimp only [ByteSpecs.hmacWith] at hlen; rw [Common443.CompRTag.sha256With_length] at hlen; omega
  · exact hs x hxs hnpt hinj hnk
  · exact hm x hxm hnpt hinj hnk
theorem ptAvoidFull_hmac {a c : DY.Bytes} (hb : b.length < 32) (ha : PtAvoidFull i r S g ms b a) (hc : PtAvoidFull i r S g ms b c) : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.hmac a c) := ptAvoidFull_kdfExtract_of_lt32 hb ha hc
theorem ptAvoidFull_dhPk_compI0 {sk : DY.Bytes} (hb : b.length < 32) (hsk : PtAvoidFull compI0 r S g ms b sk) : PtAvoidFull compI0 r S g ms b (DY.DiffieHellman.dhPk sk) := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (gDhPk compI0) (gAll compI0 S g)] at hx
  simp only [gDhPk, concretizeDhPk, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hxsk
  · intro heq; have hlen := congrArg List.length heq; change (compLookupPub _).length = b.length at hlen; rw [compLookupPub_length] at hlen; omega
  · exact hsk x hxsk hnpt hinj hnk
theorem gamma_hmac (i : ExternInterpretation) (S : Sem) (g : Ghost) (k m : DY.Bytes) : gamma i S g (DY.Libsignal.TripleRatchet.hmac k m) = ByteSpecs.hmacWith (DY.Libsignal.Refinement.sha256CompressFunction i) (gamma i S g k) (gamma i S g m) := by
  unfold gamma gamma' DY.Libsignal.TripleRatchet.hmac
  rw [show DY.KdfExtract.kdfExtract k m = ({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)]; rfl
theorem ptAvoidFull_trunc8_of_len {a : DY.Bytes} (hb : b.length < 8) (hlen : 8 ≤ (gamma i S g a).length) (ha : PtAvoidFull i r S g ms b a) : PtAvoidFull i r S g ms b (DY.Trunc.trunc8 a) := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gTrunc0 (gAll i S g)] at hx
  simp only [gTrunc0, concretizeTrunc, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa
  · intro heq; have ht : ((gamma i S g a).take 8).length = 8 := by rw [List.length_take, Nat.min_eq_left hlen]
    change (gamma i S g a).take 8 = b at heq; rw [heq] at ht; omega
  · exact ha x hxa hnpt hinj hnk
theorem ptAvoidFull_trunc8_hmac {k m : DY.Bytes} (hb : b.length < 8) (hk : PtAvoidFull i r S g ms b k) (hm : PtAvoidFull i r S g ms b m) : PtAvoidFull i r S g ms b (DY.Trunc.trunc8 (DY.Libsignal.TripleRatchet.hmac k m)) := by
  refine ptAvoidFull_trunc8_of_len hb ?_ (ptAvoidFull_hmac (by omega) hk hm)
  rw [gamma_hmac]; dsimp only [ByteSpecs.hmacWith]; rw [Common443.CompRTag.sha256With_length]; omega
theorem ptAvoidFull_trWire {w : DY.TrWire.TrWireMsg.SubF DY.Bytes} (hrk : PtAvoidFull i r S g ms b w.senderRatchetKey) (hct : PtAvoidFull i r S g ms b w.ciphertext) (hpq : PtAvoidFull i r S g ms b w.pqRatchet) : PtAvoidFull i r S g ms b w.pack := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx; rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)] at hx; simp only [gTrWire0, concretizeTrWire, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxrk | hxct | hxpq
  · rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_trWire_pack_eq] at hinj
    cases hinj
  · exact hrk x hxrk hnpt hinj hnk
  · exact hct x hxct hnpt hinj hnk
  · exact hpq x hxpq hnpt hinj hnk
theorem ptAvoidFull_trWireMsg {v : UInt8} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes} {ev : DY.TrWire.EncodingVariation} (hrk : PtAvoidFull i r S g ms b rk) (hct : PtAvoidFull i r S g ms b ct) (hpq : PtAvoidFull i r S g ms b pq) : PtAvoidFull i r S g ms b (DY.TrWire.trWireMsg v rk c pc ct pq ev) := ptAvoidFull_trWire hrk hct hpq
theorem ptAvoidFull_spqrInit {a p : DY.Bytes} (ha : PtAvoidFull i r S g ms b a) (hp : PtAvoidFull i r S g ms b p) : PtAvoidFull i r S g ms b (DY.Spqr.spqrInit a p) := by
  intro x hx hnpt hinj hnk; unfold gamma' DY.Spqr.spqrInit at hx; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)] at hx; simp only [gSpqrInit, concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  exact hx.elim (fun h => ha x h hnpt hinj hnk) (fun h => hp x h hnpt hinj hnk)
theorem ptAvoidFull_spqrInit_elim {s : DY.Spqr.InitState.SubF DY.Bytes} (h : PtAvoidFull i r S g ms b s.pack) : PtAvoidFull i r S g ms b s.authKey ∧ PtAvoidFull i r S g ms b s.params := by
  refine ⟨fun x hx hnpt hinj hnk => h x ?_ hnpt hinj hnk, fun x hx hnpt hinj hnk => h x ?_ hnpt hinj hnk⟩ <;>
    (unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)]; simp only [gSpqrInit, concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll])
  · exact Or.inl hx
  · exact Or.inr hx
theorem ptAvoidFull_spqrChainKey {a p idx : DY.Bytes} (ha : PtAvoidFull i r S g ms b a) (hp : PtAvoidFull i r S g ms b p) (hi : PtAvoidFull i r S g ms b idx) : PtAvoidFull i r S g ms b (DY.Spqr.spqrChainKey a p idx) := by
  intro x hx hnpt hinj hnk; unfold gamma' DY.Spqr.spqrChainKey at hx; rw [DY.Bytes.rec_eq (gSpqrChainKey S) (gAll i S g)] at hx; simp only [gSpqrChainKey, concretizeSpqrChainKey, spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with hxa | hxp | hxi; exact ha x hxa hnpt hinj hnk; exact hp x hxp hnpt hinj hnk; exact hi x hxi hnpt hinj hnk
theorem ptAvoidFull_spqrSendState {st c : DY.Bytes} (hst : PtAvoidFull i r S g ms b st) (hc : PtAvoidFull i r S g ms b c) : PtAvoidFull i r S g ms b (DY.Spqr.spqrSend st c).1 := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show (DY.Spqr.spqrSend st c).1 = ({ st := st, coins := c } : DY.Spqr.SendState.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (gSpqrSendState S) (gAll i S g)] at hx
  simp only [gSpqrSendState, concretizeSpqrSendState, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  exact hx.elim (fun h => hst x h hnpt hinj hnk) (fun h => hc x h hnpt hinj hnk)
theorem ptAvoidFull_spqrSendKey_pack {st c : DY.Bytes} (hst : PtAvoidFull i r S g ms b st) (hc : PtAvoidFull i r S g ms b c) : PtAvoidFull i r S g ms b (({ st := st, coins := c } : DY.Spqr.SendKey.SubF DY.Bytes).pack) := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx; rw [DY.Bytes.rec_eq (gSpqrSendKey S) (gAll i S g)] at hx; simp only [gSpqrSendKey, concretizeSpqrSendKey, spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  exact hx.elim (fun h => hst x h hnpt hinj hnk) (fun h => hc x h hnpt hinj hnk)
theorem ptAvoidFull_spqrSendKey {st c : DY.Bytes} (hst : PtAvoidFull i r S g ms b st) (hc : PtAvoidFull i r S g ms b c) : PtAvoidFull i r S g ms b (DY.Spqr.spqrSend st c).2.1 := by
  unfold DY.Spqr.spqrSend; dsimp only; have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  cases hv : st.view? DY.Spqr.InitState.SubF with
  | none => exact ptAvoidFull_spqrSendKey_pack hst hc
  | some x =>
    rw [hv] at hp; rw [← hp] at hst; obtain ⟨hk, hpar⟩ := ptAvoidFull_spqrInit_elim hst; exact ptAvoidFull_spqrChainKey hk hpar (ptAvoidFull_literalToBytes _)
theorem ptAvoidFull_spqrSendMsg {st c : DY.Bytes} (hst : PtAvoidFull i r S g ms b st) (hc : PtAvoidFull i r S g ms b c) : PtAvoidFull i r S g ms b (DY.Spqr.spqrSend st c).2.2 := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show (DY.Spqr.spqrSend st c).2.2 = ({ st := st, coins := c } : DY.Spqr.SendMsg.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (gSpqrSendMsg S) (gAll i S g)] at hx
  simp only [gSpqrSendMsg, concretizeSpqrSendMsg, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  exact hx.elim (fun h => hst x h hnpt hinj hnk) (fun h => hc x h hnpt hinj hnk)
theorem ptAvoidFull_hkdfBlock1 {prk info : DY.Bytes} (hb : b.length < 32) (hprk : PtAvoidFull i r S g ms b prk) (hinfo : PtAvoidFull i r S g ms b info) : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := ptAvoidFull_hmac hb hprk (ptAvoidFull_concat hinfo (ptAvoidFull_lit _))
theorem ptAvoidFull_hkdfBlock2 {prk info : DY.Bytes} (hb : b.length < 32) (hprk : PtAvoidFull i r S g ms b prk) (hinfo : PtAvoidFull i r S g ms b info) : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) := ptAvoidFull_hmac hb hprk (ptAvoidFull_concat (ptAvoidFull_hkdfBlock1 hb hprk hinfo) (ptAvoidFull_concat hinfo (ptAvoidFull_lit _)))
theorem ptAvoidFull_hkdfBlock3 {prk info : DY.Bytes} (hb : b.length < 32) (hprk : PtAvoidFull i r S g ms b prk) (hinfo : PtAvoidFull i r S g ms b info) : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := ptAvoidFull_hmac hb hprk (ptAvoidFull_concat (ptAvoidFull_hkdfBlock2 hb hprk hinfo) (ptAvoidFull_concat hinfo (ptAvoidFull_lit _)))
theorem ptAvoidFull_trMsgKeys {salt seed : DY.Bytes} (hb : b.length < 32)
    (hsalt : PtAvoidFull i r S g ms b salt) (hseed : PtAvoidFull i r S g ms b seed) :
    let keys := DY.Libsignal.TripleRatchet.trMsgKeys salt seed
    PtAvoidFull i r S g ms b keys.cipherKey ∧ PtAvoidFull i r S g ms b keys.macKey ∧ PtAvoidFull i r S g ms b keys.iv := by
  have hprk := ptAvoidFull_hmac hb hsalt hseed; have hinfo : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys") := ptAvoidFull_lit _; exact ⟨ptAvoidFull_hkdfBlock1 hb hprk hinfo, ptAvoidFull_hkdfBlock2 hb hprk hinfo, ptAvoidFull_hkdfBlock3 hb hprk hinfo⟩
theorem ptAvoidFull_kdfCk {ck : DY.Bytes} (hb : b.length < 32) (hck : PtAvoidFull i r S g ms b ck) : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.kdfCk ck).1 ∧ PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.kdfCk ck).2 := ⟨ptAvoidFull_hmac hb hck (ptAvoidFull_lit _), ptAvoidFull_hmac hb hck (ptAvoidFull_lit _)⟩
theorem ptAvoidFull_kdfCk_fst {ck : DY.Bytes} (hb : b.length < 32) (hck : PtAvoidFull i r S g ms b ck) : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.kdfCk ck).1 := (ptAvoidFull_kdfCk hb hck).1
theorem ptAvoidFull_kdfCk_snd {ck : DY.Bytes} (hb : b.length < 32) (hck : PtAvoidFull i r S g ms b ck) : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.kdfCk ck).2 := (ptAvoidFull_kdfCk hb hck).2
theorem ptAvoidFull_computeMac {mk myIk peerIk wire : DY.Bytes} (hb : b.length < 8) (hmk : PtAvoidFull i r S g ms b mk) (hmy : PtAvoidFull i r S g ms b myIk) (hpeer : PtAvoidFull i r S g ms b peerIk) (hwire : PtAvoidFull i r S g ms b wire) : PtAvoidFull i r S g ms b (DY.Libsignal.TripleRatchet.computeMac mk myIk peerIk wire) := ptAvoidFull_trunc8_hmac hb hmk (ptAvoidFull_concat hmy (ptAvoidFull_concat hpeer hwire))
theorem ptAvoidFull_of_litConcatTree {t : DY.Bytes} (h : LitConcatTree t) : PtAvoidFull i r S g ms b t := ptAvoidFull_of_memoInjGt (k := b.length) (Nat.le_refl _) (memoInjGt_of_litConcatTree h)
theorem ptAvoidFull_mem_slowNat (n : Nat) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowNat.serialize n) : PtAvoidFull i r S g ms b p := ptAvoidFull_of_memoInjGt (k := b.length) (Nat.le_refl _) (memoInjGt_mem_slowNat i S g b.length n hp)
theorem ptAvoidFull_mem_uint32 (n : UInt32) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize n) : PtAvoidFull i r S g ms b p := ptAvoidFull_of_memoInjGt (k := b.length) (Nat.le_refl _) (memoInjGt_mem_uint32 i S g b.length n hp)
theorem ptAvoidFull_mem_bool (v : Bool) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.bool.serialize v) : PtAvoidFull i r S g ms b p := ptAvoidFull_of_memoInjGt (k := b.length) (Nat.le_refl _) (memoInjGt_mem_bool i S g b.length v hp)
theorem ptAvoidFull_mem_slowString (s : String) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowString.serialize s) : PtAvoidFull i r S g ms b p := ptAvoidFull_of_memoInjGt (k := b.length) (Nat.le_refl _) (memoInjGt_mem_slowString i S g b.length s hp)
theorem ptAvoidFull_mem_slowBytes {u : DY.Bytes} (hu : PtAvoidFull i r S g ms b u) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowBytes.serialize u) : PtAvoidFull i r S g ms b p := by
  have hser : Comparse.NonExtensibleMessageFormat.slowBytes.serialize u = Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length u) ++ [u] :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq u
  rw [hser, List.mem_append, List.mem_singleton] at hp; exact hp.elim (ptAvoidFull_mem_slowNat _) (· ▸ hu)
theorem ptAvoidFull_serialize_local_tr {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hmyIk : PtAvoidFull i r S g ms b ls.state.myIk) (hpeerIk : PtAvoidFull i r S g ms b ls.state.peerIk) (hrk : PtAvoidFull i r S g ms b ls.state.rk) (hdhs : PtAvoidFull i r S g ms b ls.state.dhs) (hcks : PtAvoidFull i r S g ms b ls.state.cks) (hsid : PtAvoidFull i r S g ms b ls.state.sid) (hspqr : PtAvoidFull i r S g ms b ls.state.spqr) (hrecv : ∀ d ∈ ls.state.recv, PtAvoidFull i r S g ms b d.ratchetKey ∧ PtAvoidFull i r S g ms b d.chainKey) : PtAvoidFull i r S g ms b (Comparse.serialize ls) := by
  intro x hx hnpt hinj hnk
  rcases memo_serialize_local_tr_decomp hx with ⟨p, hp, hxp⟩ | ⟨d, hd, p, hp, hxp⟩ | ⟨hfalse, _⟩
  · unfold trStatePrefixes at hp; simp only [List.mem_append] at hp
    rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
    · exact ptAvoidFull_mem_slowString _ h1 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowString _ h2 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowBytes hmyIk h3 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowBytes hpeerIk h4 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowBytes hrk h5 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowBytes hdhs h6 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowBytes hcks h7 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_uint32 _ h8 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_uint32 _ h9 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowBytes hsid h10 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_bool _ h11 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowNat _ h12 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowBytes hspqr h13 x hxp hnpt hinj hnk
  · have hser : (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d =
        Comparse.NonExtensibleMessageFormat.slowBytes.serialize d.ratchetKey ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize d.chainKey ++ (Comparse.NonExtensibleMessageFormat.uint32.serialize d.index ++ Comparse.NonExtensibleMessageFormat.slowNat.serialize d.rIdx)) :=
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq d
    rw [hser] at hp; simp only [List.mem_append] at hp; rcases hp with h1 | h2 | h3 | h4
    · exact ptAvoidFull_mem_slowBytes (hrecv d hd).1 h1 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowBytes (hrecv d hd).2 h2 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_uint32 _ h3 x hxp hnpt hinj hnk
    · exact ptAvoidFull_mem_slowNat _ h4 x hxp hnpt hinj hnk
  · rw [hfalse] at hinj; cases hinj
end Nodes
def rng36Chars : List Char := chars_of_hex (rngAt 36)
theorem rngAt36_eq_hex : rngAt 36 = hexBytes (str_of_hex (rngAt 36)) := rfl
theorem rng36Str_eq : (str_of_hex (rngAt 36)) = String.ofList rng36Chars := rfl
theorem rngAt36_length : (rngAt 36).length = 64 := by
  have h : rngAt 36 = hexBytes.go hexDigit rng36Chars := by rw [rngAt36_eq_hex, rng36Str_eq, hexBytes_ofList]
  rw [h]; rfl
def pt38Chars : List Char := chars_of_hex (ptAt 38)
theorem ptAt38_eq_hex : ptAt 38 = hexBytes (str_of_hex (ptAt 38)) := rfl
theorem pt38Str_eq : (str_of_hex (ptAt 38)) = String.ofList pt38Chars := rfl
theorem ptAt38_eq_fast : ptAt 38 = hexBytes.go hexDigit pt38Chars := by rw [ptAt38_eq_hex, pt38Str_eq, hexBytes_ofList]
theorem ptAt38_length : (ptAt 38).length = 6 := by rw [ptAt38_eq_fast]; rfl
def pt78Chars : List Char := chars_of_hex (ptAt 78)
theorem ptAt78_eq_hex : ptAt 78 = hexBytes (str_of_hex (ptAt 78)) := rfl
theorem pt78Str_eq : (str_of_hex (ptAt 78)) = String.ofList pt78Chars := rfl
theorem ptAt78_eq_fast : ptAt 78 = hexBytes.go hexDigit pt78Chars := by rw [ptAt78_eq_hex, pt78Str_eq, hexBytes_ofList]
theorem ptAt78_length : (ptAt 78).length = 5 := by rw [ptAt78_eq_fast]; rfl
theorem ptAt35_eq_fast : ptAt 35 = hexBytes.go hexDigit pt35Chars := by rw [ptAt35_eq_hex, pt35Str_eq, hexBytes_ofList]
theorem ptAt35_eq_compAesPt1 : ptAt 35 = compAesPt1 := by rw [ptAt35_eq_fast]; decide +kernel
theorem ptAt38_eq_compAesPt2 : ptAt 38 = compAesPt2 := by rw [ptAt38_eq_fast]; decide +kernel
theorem ptAt78_eq_compAesPt3 : ptAt 78 = compAesPt3 := by rw [ptAt78_eq_fast]; decide +kernel
theorem ptAt38_or_ptAt78_len {b : HwBytes} (hb : b = ptAt 38 ∨ b = ptAt 78) :
    b.length ≤ 6 ∧ b.length < 8 ∧ b.length < 32 := by rcases hb with rfl | rfl <;> [rw [ptAt38_length]; rw [ptAt78_length]] <;> decide
theorem call0Rng_take_1_gt_6 : ∀ e ∈ call0Rng.take 1, 6 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he; rw [call0Rng_take_1_eq, List.mem_singleton] at he; subst he; show 6 < (rngAt 1).length; rw [rngAt1_length]; decide
theorem call0Rng_drop_33_gt_6 : ∀ e ∈ call0Rng.drop 33, 6 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he; rw [call0Rng_drop_33_eq, List.mem_singleton] at he; subst he; show 6 < (rngAt 34).length; rw [rngAt34_length]; decide
theorem compAesPt1_ne_pt38_pt78 {b : HwBytes} (hb : b = ptAt 38 ∨ b = ptAt 78) : compAesPt1 ≠ b := by
  have h1 : compAesPt1 ≠ compAesPt2 ∧ compAesPt1 ≠ compAesPt3 := by decide +kernel
  rcases hb with rfl | rfl; rw [ptAt38_eq_compAesPt2]; exact h1.1; rw [ptAt78_eq_compAesPt3]; exact h1.2
theorem compAesPerm_compAesPt1_ne (k iv : HwBytes) {b : HwBytes} (hb : b = ptAt 38 ∨ b = ptAt 78) : compAesPerm k iv compAesPt1 ≠ b := by
  intro h; have h16 := compAesPerm_length_ge_16 k iv compAesPt1; have hb6 := (ptAt38_or_ptAt78_len hb).1; rw [h] at h16; omega
theorem ptAvoidFull_symEnc_compI0_of_perm_ne {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {key iv msg : DY.Bytes} (hperm : ∀ k iv_b : HwBytes, compAesPerm k iv_b (gamma compI0 S g msg) ≠ b) (hk : PtAvoidFull compI0 r S g ms b key) (hiv : PtAvoidFull compI0 r S g ms b iv) (hm : PtAvoidFull compI0 r S g ms b msg) : PtAvoidFull compI0 r S g ms b (DY.SymEnc.symEnc key iv msg) := by
  intro x hx hnpt hinj hnk; unfold gamma' at hx
  rw [show DY.SymEnc.symEnc key iv msg = ({ key := key, iv := iv, msg := msg } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl,
    DY.Bytes.rec_eq (gSym0 compI0) (gAll compI0 S g)] at hx
  simp only [gSym0, concretizeSym, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxk | hxiv | hxm; exact hperm _ _; exact hk x hxk hnpt hinj hnk; exact hiv x hxiv hnpt hinj hnk; exact hm x hxm hnpt hinj hnk
def PqxdhSecretsInv (r : Records) (tr : ExecTrace) : Prop := ∀ j : Nat, ∀ e : PQXDHStEntry, (tr.at? j : Option PQXDHStEntry) = some e → e.st.state.sk = setupSecret r 0 ∨ e.st.state.sk = setupSecret r 1 ∨ e.st.state.sk = setupSecret r 2 ∨ e.st.state.sk = setupSecret r 4 ∨ (r.withOpk = true ∧ e.st.state.sk = randTerm 22 32)
def PtVisRandTermsInv (vis : List VisEntry) : Prop := ∀ v ∈ vis, v.kind = .pt → ∀ u ∈ v.terms, ∃ idx sz : Nat, u = randTerm idx sz
theorem ptAvoidFull_ptVis_of_randTermsInv {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hpt : PtVisRandTermsInv (runVis r ms)) : ∀ v ∈ runVis r ms, v.kind = .pt → ∀ u ∈ v.terms, PtAvoidFull i r S g ms b u := by intro v hv hk u hu; obtain ⟨idx, sz, rfl⟩ := hpt v hv hk u hu; exact ptAvoidFull_randTerm_ptAtom (List.mem_flatMap.mpr ⟨v, List.mem_filter.mpr ⟨hv, beq_iff_eq.mpr hk⟩, hu⟩)
theorem ptAvoidFull_storedSecrets_of_inv {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (hcompat : Compat i r S g) (hwf : RecordsWF r) (hb : b.length < 32) (hsec : PqxdhSecretsInv r (runTraceMoves r ms)) : ∀ u ∈ storedSecrets (runTraceMoves r ms), PtAvoidFull i r S g ms b u := fun u hu => ptAvoidFull_of_memoInjGt (Nat.le_refl b.length) (memoInjGt_storedSecrets_of_inv hcompat hwf hb hsec u hu)
section AliceStatesAndEncOut
attribute [local irreducible] setupPublic setupSecret
theorem ptAvoidFull_iniAliceStartState_of_aliceVis {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {tr₁ : ExecTrace} {a : Participant} {ikA : DY.Bytes} {hb_h : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} {b : HwBytes} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb : b.length < 32) (hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) (hm₀_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb_h)) (hrs_ek : ∀ e ∈ rs.take 1, b.length < (Common443.Census443Defs.eventBytes e).length) (hrs_dhs : ∀ e ∈ rs.drop 33, b.length < (Common443.Census443Defs.eventBytes e).length) : PtAvoidFull compI0 r S g ms b (Comparse.serialize (⟨a, iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := ptAvoidFull_of_memoInjGt (Nat.le_refl _) (memoInjGt_iniAliceStartState_of_aliceVis hcompat hwf hb hid hm₀_vis hrs_ek hrs_dhs)
theorem ptAvoidFull_encSt_iniAliceStartState {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (tr₁ tr₂ : ExecTrace) (a pB : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) (hb : b.length < 32) (hikA : MemoInjGt compI0 S g b.length o.ikA) (hikB : MemoInjGt compI0 S g b.length o.ikB) (hspk : MemoInjGt compI0 S g b.length o.spk) (hspk_key : MemoInjGt compI0 S g b.length (DY.X25519.x25519Key o.spk)) (hrk : MemoInjGt compI0 S g b.length o.keys.rk) (hck : MemoInjGt compI0 S g b.length o.keys.ck) (hpqr : MemoInjGt compI0 S g b.length o.keys.pqr) (hdhsA : MemoInjGt compI0 S g b.length (randTerm (tr₁.length + 2) 32)) (hcoin : PtAvoidFull compI0 r S g ms b (randTerm (tr₂.length + 1) cl)) : PtAvoidFull compI0 r S g ms b (Comparse.serialize (⟨a, encSt tr₂ (iniAliceStartState tr₁ pB o) cl⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
  have hcc := memoInjGt_createChain hb hrk hspk_key hdhsA; have lift : ∀ {t : DY.Bytes}, MemoInjGt compI0 S g b.length t → PtAvoidFull compI0 r S g ms b t := ptAvoidFull_of_memoInjGt (Nat.le_refl _)
  refine ptAvoidFull_serialize_local_tr (lift (memoInjGt_serializedIk hikA)) (lift (memoInjGt_serializedIk hikB)) (lift hcc.1) (lift hdhsA) (ptAvoidFull_kdfCk_fst hb (lift hcc.2)) (lift (memoInjGt_concat (memoInjGt_dhPk_compI0 hb hdhsA) hrk)) (ptAvoidFull_spqrSendState (lift (memoInjGt_spqrInit hpqr (memoInjGt_lit compI0 S g _ _))) hcoin)
    (fun d hd => by simp only [encSt, iniAliceStartState, List.mem_singleton] at hd; subst hd; exact ⟨lift hspk, lift hck⟩)
theorem aliceOut_fields_memoInjGt
    {r : Records} {S : Sem} {g : Ghost} {k : Nat} {tr₁ : ExecTrace} {a : Participant} {ikA : DY.Bytes}
    {hb_h : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent}
    (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hk : k < 32) (hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1)
    (hm₀_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb_h))
    (hrs_ek : ∀ e ∈ rs.take 1, k < (Common443.Census443Defs.eventBytes e).length)
    (hrs_dhs : ∀ e ∈ rs.drop 33, k < (Common443.Census443Defs.eventBytes e).length) :
    let o := iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
    MemoInjGt compI0 S g k o.ikA ∧ MemoInjGt compI0 S g k o.ikB ∧ MemoInjGt compI0 S g k o.spk ∧
    MemoInjGt compI0 S g k (DY.X25519.x25519Key o.spk) ∧ MemoInjGt compI0 S g k o.keys.rk ∧
    MemoInjGt compI0 S g k o.keys.ck ∧ MemoInjGt compI0 S g k o.keys.pqr ∧ MemoInjGt compI0 S g k (randTerm (tr₁.length + 2) 32) := by
  have hNe : r.alice ≠ r.bob := hwf.1
  obtain ⟨hek_draw, hent_draw, hdhs_draw⟩ := memoInjGt_draws_of_aliceVis hk hm₀_vis (fun b' hb' => hrs_ek (.rng b') hb') (fun b' hb' => hrs_dhs (.rng b') hb')
  have hsec := memoInjGt_setupSecret hcompat hwf hk
  have hikA_gt : MemoInjGt compI0 S g k ikA := hid.elim (· ▸ hsec 0) (· ▸ hsec 1)
  have hikB_pk : MemoInjGt compI0 S g k (setupPublic r 2) := by rw [Common443.CompSetupSecrecy.setupPublic_2 hNe, ← Common443.CompSetupSecrecy.setupSecret_1 hNe]; exact memoInjGt_dhPk_compI0 hk (hsec 1)
  have hspk_pk : MemoInjGt compI0 S g k (setupPublic r 4) := by rw [Common443.CompSetupSecrecy.setupPublic_4 hNe, ← Common443.CompSetupSecrecy.setupSecret_2 hNe]; exact memoInjGt_dhPk_compI0 hk (hsec 2)
  have hspk_key : MemoInjGt compI0 S g k (DY.X25519.x25519Key (setupPublic r 4)) := by unfold DY.X25519.x25519Key; rw [Common443.CompSetupSecrecy.setupPublic_4 hNe, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq, ← Common443.CompSetupSecrecy.setupSecret_2 hNe]; exact memoInjGt_dhPk_compI0 hk (hsec 2)
  have hikB_key : MemoInjGt compI0 S g k (DY.X25519.x25519Key (setupPublic r 2)) := by unfold DY.X25519.x25519Key; rw [Common443.CompSetupSecrecy.setupPublic_2 hNe, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq, ← Common443.CompSetupSecrecy.setupSecret_1 hNe]; exact memoInjGt_dhPk_compI0 hk (hsec 1)
  have hpq_pk : MemoInjGt compI0 S g k (setupPublic r 6) := by rw [Common443.CompSetupSecrecy.setupPublic_6 hNe, ← Common443.CompSetupSecrecy.setupSecret_4 hNe]; exact memoInjGt_kemPk (hsec 4)
  have hkdf := memoInjGt_pqxdhKdf_none hk (memoInjGt_dh_compI0 hk hspk_key hikA_gt) (memoInjGt_dh_compI0 hk hikB_key hek_draw) (memoInjGt_dh_compI0 hk hspk_key hek_draw) (memoInjGt_kemEncap_snd_compI0 hk hpq_pk hent_draw); exact ⟨memoInjGt_dhPk_compI0 hk hikA_gt, hikB_pk, hspk_pk, hspk_key, hkdf.1, hkdf.2.1, hkdf.2.2, hdhs_draw⟩
theorem ptAvoidFull_encSt_of_aliceVis {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {tr₁ tr₂ : ExecTrace} {a : Participant} {ikA : DY.Bytes} {hb_h : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} {cl : Nat} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb : b.length < 32) (hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) (hm₀_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb_h)) (hrs_ek : ∀ e ∈ rs.take 1, b.length < (Common443.Census443Defs.eventBytes e).length) (hrs_dhs : ∀ e ∈ rs.drop 33, b.length < (Common443.Census443Defs.eventBytes e).length) (hcoin : PtAvoidFull compI0 r S g ms b (randTerm (tr₂.length + 1) cl)) : PtAvoidFull compI0 r S g ms b (Comparse.serialize (⟨a, encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by obtain ⟨hikA, hikB, hspk, hspk_key, hrk, hck, hpqr, hdhs⟩ := aliceOut_fields_memoInjGt hcompat hwf hb hid hm₀_vis hrs_ek hrs_dhs; exact ptAvoidFull_encSt_iniAliceStartState tr₁ tr₂ a r.bob _ cl hb hikA hikB hspk hspk_key hrk hck hpqr hdhs hcoin
theorem ptAvoidFull_encOut_iniAliceStartState {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (tr₁ tr₂ : ExecTrace) (pB : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) (hb8 : b.length < 8) (hikA : MemoInjGt compI0 S g b.length o.ikA) (hikB : MemoInjGt compI0 S g b.length o.ikB) (hspk_key : MemoInjGt compI0 S g b.length (DY.X25519.x25519Key o.spk)) (hrk : MemoInjGt compI0 S g b.length o.keys.rk) (hpqr : MemoInjGt compI0 S g b.length o.keys.pqr) (hdhsA : MemoInjGt compI0 S g b.length (randTerm (tr₁.length + 2) 32)) (hcoin : PtAvoidFull compI0 r S g ms b (randTerm (tr₂.length + 1) cl)) (hmsg : PtAvoidFull compI0 r S g ms b (randTerm tr₂.length 32)) (hperm : ∀ k iv_b : HwBytes, compAesPerm k iv_b (gamma compI0 S g (randTerm tr₂.length 32)) ≠ b) : PtAvoidFull compI0 r S g ms b (encOut tr₂ (iniAliceStartState tr₁ pB o) cl (tr₂.length + 2)) := by
  have hb32 : b.length < 32 := by omega
  have hcc := memoInjGt_createChain hb32 hrk hspk_key hdhsA; have lift : ∀ {t : DY.Bytes}, MemoInjGt compI0 S g b.length t → PtAvoidFull compI0 r S g ms b t := ptAvoidFull_of_memoInjGt (Nat.le_refl _); have hspqr : PtAvoidFull compI0 r S g ms b (iniAliceStartState tr₁ pB o).spqr := lift (memoInjGt_spqrInit hpqr (memoInjGt_lit compI0 S g _ _)); have hcks : PtAvoidFull compI0 r S g ms b (iniAliceStartState tr₁ pB o).cks := lift hcc.2
  have hkeys := ptAvoidFull_trMsgKeys hb32 (ptAvoidFull_spqrSendKey hspqr hcoin) (ptAvoidFull_kdfCk_snd hb32 hcks)
  have hwire : PtAvoidFull compI0 r S g ms b (encWire tr₂ (iniAliceStartState tr₁ pB o) cl (tr₂.length + 2)) := by unfold encWire; rw [encSalt_self]; exact ptAvoidFull_trWireMsg (ptAvoidFull_dhPk_compI0 hb32 (lift hdhsA)) (ptAvoidFull_symEnc_compI0_of_perm_ne hperm hkeys.1 hkeys.2.2 hmsg) (ptAvoidFull_spqrSendMsg hspqr hcoin)
  unfold encOut; refine ptAvoidFull_concat hwire ?_; unfold encMac; rw [encSalt_self]
  exact ptAvoidFull_computeMac hb8 hkeys.2.1 (lift (memoInjGt_serializedIk hikA)) (lift (memoInjGt_serializedIk hikB)) hwire
theorem gamma_randTerm_eq_σ {i : ExternInterpretation} {S : Sem} {g : Ghost} (idx sz : Nat) (hsz : sz ≠ 0) :
    gamma i S g (randTerm idx sz) = g.σ idx sz := by unfold gamma; rw [gamma'_randTerm i S g idx sz hsz]
theorem ptAvoidFull_encOut_of_aliceVis {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {tr₁ tr₂ : ExecTrace} {a : Participant} {ikA : DY.Bytes} {hb_h : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} {cl : Nat} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb : b = ptAt 38 ∨ b = ptAt 78) (hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) (hm₀_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb_h)) (hrs_ek : ∀ e ∈ rs.take 1, b.length < (Common443.Census443Defs.eventBytes e).length) (hrs_dhs : ∀ e ∈ rs.drop 33, b.length < (Common443.Census443Defs.eventBytes e).length) (hcoin : PtAvoidFull compI0 r S g ms b (randTerm (tr₂.length + 1) cl)) (hpt_pin : gamma compI0 S g (randTerm tr₂.length 32) = ptAt 35) : PtAvoidFull compI0 r S g ms b (encOut tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl (tr₂.length + 2)) := by
  obtain ⟨_, hb8, hb32⟩ := ptAt38_or_ptAt78_len hb; obtain ⟨hikA, hikB, _, hspk_key, hrk, _, hpqr, hdhs⟩ := aliceOut_fields_memoInjGt hcompat hwf hb32 hid hm₀_vis hrs_ek hrs_dhs
  have hmsg : PtAvoidFull compI0 r S g ms b (randTerm tr₂.length 32) := by
    refine ptAvoidFull_randTerm_ne (.inr ?_)
    rw [← gamma_randTerm_eq_σ (i := compI0) (S := S) tr₂.length 32 (by decide), hpt_pin, ptAt35_eq_compAesPt1]
    exact compAesPt1_ne_pt38_pt78 hb
  refine ptAvoidFull_encOut_iniAliceStartState tr₁ tr₂ r.bob _ cl hb8 hikA hikB hspk_key hrk hpqr hdhs hcoin hmsg (fun k iv_b => ?_)
  rw [hpt_pin, ptAt35_eq_compAesPt1]; exact compAesPerm_compAesPt1_ne k iv_b hb
end AliceStatesAndEncOut
def badAes38_78 : List HwBytes :=
  [compAesPt2, compAesCt2, xorHeadD7 compAesPt2, compAesPt3, compAesCt3, xorHeadD7 compAesPt3]
theorem mem_badAes38_78 {b : HwBytes} (hb : b = ptAt 38 ∨ b = ptAt 78) : b ∈ badAes38_78 := by
  rcases hb with rfl | rfl
  · rw [ptAt38_eq_compAesPt2]; simp [badAes38_78]
  · rw [ptAt78_eq_compAesPt3]; simp [badAes38_78]
theorem rngAt36_inits_not_mem_badAes38_78 : ∀ c ∈ (rngAt 36).inits, c ∉ badAes38_78 := by
  have h : rngAt 36 = hexBytes.go hexDigit rng36Chars := by rw [rngAt36_eq_hex, rng36Str_eq, hexBytes_ofList]
  rw [h]; decide +kernel
theorem mem_rng36_inits_ne_and_perm_ne {b c : HwBytes} (hb : b = ptAt 38 ∨ b = ptAt 78) (hc : c ∈ (rngAt 36).inits) :
    c ≠ b ∧ ∀ k iv : HwBytes, compAesPerm k iv c ≠ b := by
  have hnot := rngAt36_inits_not_mem_badAes38_78 c hc
  refine ⟨fun heq => hnot (heq ▸ mem_badAes38_78 hb), fun k iv heq => ?_⟩
  have h16 := compAesPerm_length_ge_16 k iv c
  have hb6 := (ptAt38_or_ptAt78_len hb).1
  rw [heq] at h16; omega
theorem ptAvoidFull_randTerm_of_mem_rng36_inits {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {idx sz : Nat}
    (hb : b = ptAt 38 ∨ b = ptAt 78) (h : sz = 0 ∨ gamma compI0 S g (randTerm idx sz) ∈ (rngAt 36).inits) :
    PtAvoidFull compI0 r S g ms b (randTerm idx sz) := by
  by_cases hsz : sz = 0
  · exact ptAvoidFull_randTerm_ne (.inl hsz)
  · have hc := h.resolve_left hsz
    rw [gamma_randTerm_eq_σ idx sz hsz] at hc
    exact ptAvoidFull_randTerm_ne (.inr (mem_rng36_inits_ne_and_perm_ne hb hc).1)
def Pre38PrefixInv (r : Records) (S : Sem) (g : Ghost) (ms : List Move) (b : HwBytes) : Prop := PqxdhSecretsInv r (runTraceMoves r ms) ∧ (∀ ls ∈ storedStates r (runTraceMoves r ms), ∃ (tr₁ : ExecTrace) (a : Participant) (ikA : DY.Bytes) (hb : DY.Libsignal.PQXDH.BundleHandles), (ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bundle0 :: call0Rng) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb) ∧ (ls = ⟨a, iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)⟩ ∨ ∃ (tr₂ : ExecTrace) (cl₁ : Nat), (cl₁ = 0 ∨ gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (rngAt 36).inits) ∧ ls = ⟨a, encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁⟩)) ∧ (∀ v ∈ runVis r ms, v.kind = .send → ∀ u ∈ v.terms, PtAvoidFull compI0 r S g ms b u ∨ ∃ (tr₁ tr₂ : ExecTrace) (a : Participant) (ikA : DY.Bytes) (hb : DY.Libsignal.PQXDH.BundleHandles) (cl₁ : Nat), (ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bundle0 :: call0Rng) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb) ∧ gamma compI0 S g (randTerm tr₂.length 32) = ptAt 35 ∧ (cl₁ = 0 ∨ gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (rngAt 36).inits) ∧ u = encOut tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2)) ∧ PtVisRandTermsInv (runVis r ms)
theorem ptAvoidFull_prefixTerms_of_pre38PrefixInv {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent} {b : HwBytes} (hwf : RecordsWF r) (hmp : MatchedPrefix compI0 r S who₀ g ms τ) (hb : b = ptAt 38 ∨ b = ptAt 78) (hinv : Pre38PrefixInv r S g ms b) : ∀ u ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), PtAvoidFull compI0 r S g ms b u := by
  have hcompat : Compat compI0 r S g := hmp.1; obtain ⟨hb6, _, hb32⟩ := ptAt38_or_ptAt78_len hb
  have hrs_ek : ∀ e ∈ call0Rng.take 1, b.length < (Common443.Census443Defs.eventBytes e).length := fun e he => Nat.lt_of_le_of_lt hb6 (call0Rng_take_1_gt_6 e he)
  have hrs_dhs : ∀ e ∈ call0Rng.drop 33, b.length < (Common443.Census443Defs.eventBytes e).length := fun e he => Nat.lt_of_le_of_lt hb6 (call0Rng_drop_33_gt_6 e he)
  refine ptAvoidFull_prefixTerms ?_ ?_ (ptAvoidFull_storedSecrets_of_inv hcompat hwf hb32 hinv.1) (ptAvoidFull_ptVis_of_randTermsInv hinv.2.2.2)
  · intro v hv hk u hu
    rcases hinv.2.2.1 v hv hk u hu with hav | ⟨tr₁, tr₂, a, ikA, hb_h, cl₁, hid, hm₀_vis, hpt_pin, hcpin, rfl⟩
    · exact hav
    · exact ptAvoidFull_encOut_of_aliceVis hcompat hwf hb hid hm₀_vis hrs_ek hrs_dhs (ptAvoidFull_randTerm_of_mem_rng36_inits hb hcpin) hpt_pin
  · intro ls hls
    obtain ⟨tr₁, a, ikA, hb_h, hid, hm₀_vis, rfl | ⟨tr₂, cl₁, hcpin, rfl⟩⟩ := hinv.2.1 ls hls
    · exact ptAvoidFull_iniAliceStartState_of_aliceVis hcompat hwf hb32 hid hm₀_vis hrs_ek hrs_dhs
    · exact ptAvoidFull_encSt_of_aliceVis hcompat hwf hb32 hid hm₀_vis hrs_ek hrs_dhs (ptAvoidFull_randTerm_of_mem_rng36_inits hb hcpin)
theorem ptDeadAt38_of (hinv : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms (trace.take 38) → Common443.CompSetupSecrecy.NoBrk r ms → Pre38PrefixInv r S g ms (ptAt 38)) : PtDeadAt 38 := by intro r S g ms hfits hnb hexp hem hcol; exact not_pt_collision_of_ne_bytes_full hem (ptAvoidFull_prefixTerms_of_pre38PrefixInv hfits.1.1 hexp.1 (.inl rfl) (hinv r S g ms hfits hexp hnb)) (hcol g ⟨rfl, hexp.1⟩)
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38
