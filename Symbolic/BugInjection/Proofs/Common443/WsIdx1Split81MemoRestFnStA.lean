/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HBA
public import Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HB
public import Symbolic.BugInjection.Proofs.Common443.CompExcuse
import Init.Data.String
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStA
open CryptoProofLib.Refinement (ExternInterpretation) open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 (rngAt)
open ByteSpecs DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPlant Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRX0Top Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape Symbolic.BugInjection.Proofs.Common443.CompRNonInj38Census Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HBA Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead78 Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
private theorem toUTF8_eq_ofList (s : String) : s.toUTF8 = List.utf8Encode s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
def rng44Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng44Chars
def rng77Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng77Chars
def rng79Fast : HwBytes := hexBytes.go Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop.hexDigit rng79Chars
def rVals81W : List HwBytes := rVals40 ++ ([bobRng41Bytes, rng44Fast, compKyberE2, rng77Fast, compAesPt3, compAesCt3, compKyberCt2, compKyberSs2] ++ (List.inits rng79Fast).tail)
abbrev RvW (v : HwBytes) : Prop := v ∈ rVals81W
set_option maxRecDepth 200000 in
theorem rVals81W_props :
    (rVals81W.all fun v =>
      (v.length == 5) || (v.length == 6) || (v.length == 16) || (v.length == 32) ||
      (v.length == 64) || (v.length == 1568) ||
      (decide (1 ≤ v.length) && decide (v.length ≤ 63) &&
        ((v.take 1 == [110#8]) || (v.take 1 == [82#8]) || (v.take 1 == [103#8])) &&
        (decide (v.length < 32) || decide (KdfFree (v.take 32))))) = true ∧
    (rVals81W.all fun v => !(decide (65 ≤ v.length)) || (v.length == 1568)) = true := by decide +kernel
theorem not_rvW_of_len_head {v : HwBytes} (h5 : v.length ≠ 5) (h6 : v.length ≠ 6) (h16 : v.length ≠ 16) (h32 : v.length ≠ 32) (h64 : v.length ≠ 64) (h1568 : v.length ≠ 1568) (h178 : v.take 1 ≠ [110#8]) (h24 : v.take 1 ≠ [82#8]) (h103 : v.take 1 ≠ [103#8]) : ¬ RvW v := by
  intro hv; have hall := List.all_eq_true.mp rVals81W_props.1 v hv
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hall
  rcases hall with (((((h | h) | h) | h) | h) | h) | ⟨⟨⟨_, _⟩, (h | h) | h⟩, _⟩
  · exact h5 h
  · exact h6 h
  · exact h16 h
  · exact h32 h
  · exact h64 h
  · exact h1568 h
  · exact h178 h
  · exact h24 h
  · exact h103 h
theorem not_rvW_of_kdf_prefix {k suf : HwBytes} (hk : ¬ KdfFree k) (hkL : k.length = 32) (h5 : k.length + suf.length ≠ 5) (h6 : k.length + suf.length ≠ 6) (h16 : k.length + suf.length ≠ 16) (h32 : k.length + suf.length ≠ 32) (h64 : k.length + suf.length ≠ 64) (h1568 : k.length + suf.length ≠ 1568) : ¬ RvW (k ++ suf) := by
  intro hv; have hall := List.all_eq_true.mp rVals81W_props.1 (k ++ suf) hv
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.length_append] at hall
  rcases hall with (((((h | h) | h) | h) | h) | h) | ⟨⟨⟨_, _⟩, _⟩, hlt | hkf⟩
  · exact h5 h
  · exact h6 h
  · exact h16 h
  · exact h32 h
  · exact h64 h
  · exact h1568 h
  · omega
  · rw [← hkL, List.take_left] at hkf; exact hk hkf
theorem not_rvW_of_len_ge65 {v : HwBytes} (h : 65 ≤ v.length) (h1568 : v.length ≠ 1568) : ¬ RvW v := by
  intro hv; have hall := List.all_eq_true.mp rVals81W_props.2 v hv
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hall
  rcases hall with hlt | hL <;> [exact hlt h; exact h1568 hL]
def ShortHeadOK (v : HwBytes) : Prop :=
  1 ≤ v.length ∧ v.take 1 ∈ ([[0#8], [1#8], [2#8], [97#8], [98#8]] : List HwBytes)
set_option maxRecDepth 200000 in
theorem rVals81W_short_head :
    (rVals81W.all fun v =>
      !(decide (v.length < 9)) ||
      !(decide (v.take 1 ∈ ([[0#8], [1#8], [2#8], [97#8], [98#8]] : List HwBytes)))) = true := by decide +kernel
theorem not_rvW_of_short_head {v : HwBytes} (hL : v.length < 9) (hH : ShortHeadOK v) : ¬ RvW v := by
  intro hv; have hall := List.all_eq_true.mp rVals81W_short_head v hv
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hall
  exact hall.elim (· hL) (· hH.2)
theorem not_rvW_of_short_append_head {a b : HwBytes} (hL : (a ++ b).length < 9) (ha : ShortHeadOK a) : ¬ RvW (a ++ b) := by
  refine not_rvW_of_short_head hL ⟨by rw [List.length_append]; exact Nat.le_trans ha.1 (Nat.le_add_right _ _), ?_⟩
  rw [List.take_append_of_le_length ha.1]; exact ha.2
set_option maxRecDepth 200000 in
theorem rVals81W_tail38_kdfFree :
    (rVals81W.all fun v =>
      decide (v.length < 38) || decide (KdfFree ((v.drop (v.length - 38)).take 32))) = true := by decide +kernel
theorem not_rvW_of_kdf_tail6 {pref k suf : HwBytes} (hk : ¬ KdfFree k) (hkL : k.length = 32) (hsufL : suf.length = 6) : ¬ RvW (pref ++ (k ++ suf)) := by
  intro hv; have hall := List.all_eq_true.mp rVals81W_tail38_kdfFree _ hv; simp only [Bool.or_eq_true, decide_eq_true_eq] at hall
  have hL : (pref ++ (k ++ suf)).length = pref.length + 38 := by rw [List.length_append, List.length_append, hkL, hsufL]
  rcases hall with hlt | hkf
  · omega
  · rw [hL, Nat.add_sub_cancel, List.drop_left, ← hkL, List.take_left] at hkf; exact hk hkf
theorem kdfTail6_not_rvW {v : HwBytes} (h : KdfTail6 v) : ¬ RvW v := by obtain ⟨pre, ck, tail, rfl, hk, hkL, htL⟩ := h; exact not_rvW_of_kdf_tail6 hk hkL htL
def KdfTail7 (v : HwBytes) : Prop := ∃ pre ck tail, v = pre ++ (ck ++ tail) ∧ ¬ KdfFree ck ∧ ck.length = 32 ∧ tail.length = 7
theorem KdfTail7.append_left {v : HwBytes} (h : KdfTail7 v) (p : HwBytes) : KdfTail7 (p ++ v) := by
  obtain ⟨pre, ck, tail, rfl, hk, hkL, htL⟩ := h; exact ⟨p ++ pre, ck, tail, by simp [List.append_assoc], hk, hkL, htL⟩
set_option maxRecDepth 200000 in
theorem rVals81W_tail39_kdfFree :
    (rVals81W.all fun v =>
      decide (v.length < 39) || decide (KdfFree ((v.drop (v.length - 39)).take 32))) = true := by decide +kernel
theorem not_rvW_of_kdf_tail7 {pref k suf : HwBytes} (hk : ¬ KdfFree k) (hkL : k.length = 32) (hsufL : suf.length = 7) : ¬ RvW (pref ++ (k ++ suf)) := by
  intro hv; have hall := List.all_eq_true.mp rVals81W_tail39_kdfFree _ hv; simp only [Bool.or_eq_true, decide_eq_true_eq] at hall
  have hL : (pref ++ (k ++ suf)).length = pref.length + 39 := by rw [List.length_append, List.length_append, hkL, hsufL]
  rcases hall with hlt | hkf
  · omega
  · rw [hL, Nat.add_sub_cancel, List.drop_left, ← hkL, List.take_left] at hkf; exact hk hkf
theorem kdfTail7_not_rvW {v : HwBytes} (h : KdfTail7 v) : ¬ RvW v := by obtain ⟨pre, ck, tail, rfl, hk, hkL, htL⟩ := h; exact not_rvW_of_kdf_tail7 hk hkL htL
set_option maxRecDepth 200000 in
theorem rVals81W_ge33_not_x25519_prefix :
    (rVals81W.all fun v =>
      (decide (v.length < 33)) || (x25519Vals.all fun w => !(v.take 4 == w.take 4))) = true := by decide +kernel
theorem not_rvW_of_x25519_append {a b : HwBytes} (ha : a ∈ x25519Vals) (hb : b.length = 32) : ¬ RvW (a ++ b) := by
  have haL : a.length = 32 := x25519Vals_length a ha; intro hm; have hall := List.all_eq_true.mp rVals81W_ge33_not_x25519_prefix (a ++ b) hm; simp only [Bool.or_eq_true, decide_eq_true_eq] at hall
  rcases hall with hlt | hx
  · rw [List.length_append, haL] at hlt; omega
  · have hwx := List.all_eq_true.mp hx a ha
    rw [Bool.not_eq_true', beq_eq_false_iff_ne] at hwx
    exact hwx (List.take_append_of_le_length (by omega))
set_option maxRecDepth 200000 in theorem not_rvW_zeroDh : ¬ RvW CompRI0Census.zeroDh := by decide +kernel
set_option maxRecDepth 200000 in theorem not_rvW_ff32 : ¬ RvW (List.replicate 32 0xff#8) := by decide +kernel
def FnOKW (allT rT : List DY.Bytes) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := (assumedInjective x.1 = false → ¬ RvW x.2.2) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → x.1 ∈ allT) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → ¬ IsX x.1 → ¬ IsTrunc8 x.1 → x.1 ∈ rT)
abbrev FnCensusW (allT rT : List DY.Bytes) (S : Sem) (g : Ghost) (t : DY.Bytes) : Prop := MemoOK compI0 S g (FnOKW allT rT) t
section NRPrim
variable {allT rT : List DY.Bytes} {S : Sem} {g : Ghost}
theorem fnokW_of_ni {b : DY.Bytes} (hb : assumedInjective b = false)
    {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) (hnr : ¬ RvW x.2.2) : FnOKW allT rT x :=
  ⟨fun _ => hnr, fun hai _ => (by rw [hx, hb] at hai; cases hai), fun hai _ _ _ => (by rw [hx, hb] at hai; cases hai)⟩
theorem fnokW_of_isKdf {b : DY.Bytes} (hb : IsKdf b) (hai : assumedInjective b = true)
    {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) : FnOKW allT rT x :=
  ⟨fun h => (by rw [hx, hai] at h; cases h), fun _ hK => absurd (hx ▸ hb) hK, fun _ hK _ _ => absurd (hx ▸ hb) hK⟩
theorem fnokW_of_isX {b : DY.Bytes} (hb : IsX b) (hai : assumedInjective b = true)
    (hm : b ∈ allT) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) : FnOKW allT rT x :=
  ⟨fun h => (by rw [hx, hai] at h; cases h), fun _ _ => hx ▸ hm, fun _ _ hX _ => absurd (hx ▸ hb) hX⟩
theorem fnokW_of_isTrunc8 {b : DY.Bytes} (hb : IsTrunc8 b) (hai : assumedInjective b = true)
    (hm : b ∈ allT) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) : FnOKW allT rT x :=
  ⟨fun h => (by rw [hx, hai] at h; cases h), fun _ _ => hx ▸ hm, fun _ _ _ hT => absurd (hx ▸ hb) hT⟩
theorem fnokW_of_r {b : DY.Bytes} (hai : assumedInjective b = true) (hmA : b ∈ allT) (hmR : b ∈ rT)
    {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x.1 = b) : FnOKW allT rT x :=
  ⟨fun h => (by rw [hx, hai] at h; cases h), fun _ _ => hx ▸ hmA, fun _ _ _ _ => hx ▸ hmR⟩
theorem nrcensusW_lit (bs : ByteArray) (h : ¬ RvW (gamma compI0 S g (DY.Literal.literalToBytes bs))) : FnCensusW allT rT S g (DY.Literal.literalToBytes bs) := by
  intro x hx; have hv := (CompRPreMemoSound.memo_sound compI0 S g _ hx).2; unfold gamma' at hx
  rw [show DY.Literal.literalToBytes bs = ({ lit := bs } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq gLit0 (gAll compI0 S g)] at hx
  rcases List.mem_singleton.mp hx with rfl
  exact fnokW_of_ni (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_lit_pack_eq bs) rfl (by rw [hv]; exact h)
theorem nrcensusW_lit_ofBA {bs : ByteArray} (h : ¬ RvW (ofByteArray bs)) :
    FnCensusW allT rT S g (DY.Literal.literalToBytes bs) :=
  nrcensusW_lit bs (by
    rw [show DY.Literal.literalToBytes bs = ({ lit := bs } : DY.Literal.Literal.SubF DY.Bytes).pack from rfl,
        CompFreshDistinct.gamma_lit]; exact h)
theorem nrcensusW_lit_size (bs : ByteArray)
    (h5 : bs.size ≠ 5) (h6 : bs.size ≠ 6) (h16 : bs.size ≠ 16) (h32 : bs.size ≠ 32)
    (h64 : bs.size ≠ 64) (h1568 : bs.size ≠ 1568)
    (h178 : (ofByteArray bs).take 1 ≠ [110#8]) (h24 : (ofByteArray bs).take 1 ≠ [82#8])
    (h103 : (ofByteArray bs).take 1 ≠ [103#8]) :
    FnCensusW allT rT S g (DY.Literal.literalToBytes bs) :=
  nrcensusW_lit bs (not_rvW_of_len_head
    (by rw [CompPlant.gamma_literalToBytes_length]; exact h5) (by rw [CompPlant.gamma_literalToBytes_length]; exact h6)
    (by rw [CompPlant.gamma_literalToBytes_length]; exact h16) (by rw [CompPlant.gamma_literalToBytes_length]; exact h32)
    (by rw [CompPlant.gamma_literalToBytes_length]; exact h64) (by rw [CompPlant.gamma_literalToBytes_length]; exact h1568)
    (by rw [gamma_literalToBytes_eq]; exact h178) (by rw [gamma_literalToBytes_eq]; exact h24)
    (by rw [gamma_literalToBytes_eq]; exact h103))
theorem nrcensusW_litByte (b : UInt8) (hb178 : b.toBitVec ≠ 110#8) (hb24 : b.toBitVec ≠ 82#8) (hb103 : b.toBitVec ≠ 103#8) : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.litByte b) :=
  nrcensusW_lit_size _ (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by simp [ByteArray.size])
    (by simp [ByteArray.size]) (by simp [ByteArray.size]) (by simp [ByteArray.size])
    (by simp [ofByteArray, hb178]) (by simp [ofByteArray, hb24]) (by simp [ofByteArray, hb103])
theorem nrcensusW_lit_participant {s : String} (hs : s = "alice" ∨ s = "bob") : FnCensusW allT rT S g (DY.Literal.literalToBytes s.toUTF8) := by refine nrcensusW_lit _ ?_; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; rcases hs with rfl | rfl <;> decide +kernel
theorem nrcensusW_concat {a c : DY.Bytes} (h : ¬ RvW (gamma compI0 S g a ++ gamma compI0 S g c)) (ha : FnCensusW allT rT S g a) (hc : FnCensusW allT rT S g c) : FnCensusW allT rT S g (DY.Concat.concat a c) := by
  intro x hx; unfold gamma' at hx
  rw [show DY.Concat.concat a c = ({ lhs := a, rhs := c } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq gConcat0 (gAll compI0 S g)] at hx
  simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, CompPlant.bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxc <;> [exact fnokW_of_ni (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq a c) rfl h; exact ha x hxa; exact hc x hxc]
theorem nrcensusW_concat_len_head {a c : DY.Bytes}
    (h5 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 5)
    (h6 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 6)
    (h16 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 16)
    (h32 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 32)
    (h64 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 64)
    (h1568 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 1568)
    (ha1 : 1 ≤ (gamma compI0 S g a).length)
    (ha178 : (gamma compI0 S g a).take 1 ≠ [110#8])
    (ha24 : (gamma compI0 S g a).take 1 ≠ [82#8])
    (ha103 : (gamma compI0 S g a).take 1 ≠ [103#8])
    (ha : FnCensusW allT rT S g a) (hc : FnCensusW allT rT S g c) : FnCensusW allT rT S g (DY.Concat.concat a c) :=
  nrcensusW_concat (not_rvW_of_len_head (by simpa using h5) (by simpa using h6) (by simpa using h16)
    (by simpa using h32) (by simpa using h64) (by simpa using h1568)
    (by rw [List.take_append_of_le_length ha1]; exact ha178)
    (by rw [List.take_append_of_le_length ha1]; exact ha24)
    (by rw [List.take_append_of_le_length ha1]; exact ha103)) ha hc
theorem nrcensusW_concat_kdf {a c : DY.Bytes}
    (hk : ¬ KdfFree (gamma compI0 S g a)) (haL : (gamma compI0 S g a).length = 32)
    (h5 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 5)
    (h6 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 6)
    (h16 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 16)
    (h32 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 32)
    (h64 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 64)
    (h1568 : (gamma compI0 S g a).length + (gamma compI0 S g c).length ≠ 1568)
    (ha : FnCensusW allT rT S g a) (hc : FnCensusW allT rT S g c) : FnCensusW allT rT S g (DY.Concat.concat a c) :=
  nrcensusW_concat (not_rvW_of_kdf_prefix hk haL h5 h6 h16 h32 h64 h1568) ha hc
theorem nrcensusW_randTerm {ts sz : Nat} (hmA : randTerm ts sz ∈ allT) (hmR : randTerm ts sz ∈ rT) : FnCensusW allT rT S g (randTerm ts sz) := by
  intro x hx; unfold gamma' randTerm at hx
  rw [DY.Bytes.rec_eq (gRandom g) (gAll compI0 S g)] at hx; dsimp only [gRandom, concretizeRandom] at hx; split_ifs at hx with hsz
  · cases hx
  · rcases List.mem_singleton.mp hx with rfl
    exact fnokW_of_r ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by unfold randTerm; simp [DY.BytesView.view_pack, hsz])) hmA hmR rfl
theorem nrcensusW_randTerm_zero (ts : Nat) : FnCensusW allT rT S g (randTerm ts 0) := by
  intro x hx; unfold gamma' randTerm at hx
  rw [DY.Bytes.rec_eq (gRandom g) (gAll compI0 S g)] at hx; dsimp only [gRandom, concretizeRandom] at hx; split_ifs at hx with hsz
  · cases hx
  · exact absurd rfl hsz
theorem nrcensusW_randTerm_coin {tr : ExecTrace} {cl : Nat}
    (hm : cl ≠ 0 → randTerm (tr.length + 1) cl ∈ rT) (hr_sub : ∀ u ∈ rT, u ∈ allT) :
    FnCensusW allT rT S g (randTerm (tr.length + 1) cl) := by
  by_cases h0 : cl = 0
  · exact h0 ▸ nrcensusW_randTerm_zero (tr.length + 1)
  · exact nrcensusW_randTerm (hr_sub _ (hm h0)) (hm h0)
theorem nrcensusW_dhPk {sk : DY.Bytes} (hmA : DY.DiffieHellman.dhPk sk ∈ allT) (hsk : FnCensusW allT rT S g sk) : FnCensusW allT rT S g (DY.DiffieHellman.dhPk sk) :=
  memoOK_dhPk (fun _ hx => fnokW_of_isX (.inl ⟨sk, rfl⟩) ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack])) hmA hx) hsk
theorem nrcensusW_dh_pack {pk sk : DY.Bytes}
    (hmA : (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) ∈ allT)
    (hpk : FnCensusW allT rT S g pk) (hsk : FnCensusW allT rT S g sk) :
    FnCensusW allT rT S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) :=
  memoOK_dh_pack (fun _ hx => fnokW_of_isX (.inr ⟨pk, sk, rfl⟩) ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [DY.BytesView.view_pack])) hmA hx) hpk hsk
theorem nrcensusW_kdfExtract {k m : DY.Bytes} (hk : FnCensusW allT rT S g k) (hm : FnCensusW allT rT S g m) : FnCensusW allT rT S g (DY.KdfExtract.kdfExtract k m) :=
  memoOK_kdfExtract (fun _ hx => fnokW_of_isKdf ⟨k, m, rfl⟩ (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_kdfExtract_eq k m) hx) hk hm
theorem nrcensusW_symEnc {k iv m : DY.Bytes} (hmA : DY.SymEnc.symEnc k iv m ∈ allT) (hmR : DY.SymEnc.symEnc k iv m ∈ rT) (hk : FnCensusW allT rT S g k) (hiv : FnCensusW allT rT S g iv) (hm : FnCensusW allT rT S g m) : FnCensusW allT rT S g (DY.SymEnc.symEnc k iv m) :=
  memoOK_symEnc (fun _ hx => fnokW_of_r ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack])) hmA hmR hx) hk hiv hm
theorem nrcensusW_trunc8 {a : DY.Bytes} (hmA : DY.Trunc.trunc8 a ∈ allT) (ha : FnCensusW allT rT S g a) : FnCensusW allT rT S g (DY.Trunc.trunc8 a) :=
  memoOK_trunc8 (fun _ hx => fnokW_of_isTrunc8 ⟨a, rfl⟩ ((Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack])) hmA hx) ha
theorem nrcensusW_agree_dhPk {q sk : DY.Bytes} (hag : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk q) sk ∈ allT) (hpk_sk : DY.DiffieHellman.dhPk sk ∈ allT) (hpk : FnCensusW allT rT S g (DY.DiffieHellman.dhPk q)) (hsk : FnCensusW allT rT S g sk) : FnCensusW allT rT S g (DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk q) sk) := by
  have hv : (DY.DiffieHellman.dhPk q).view? DY.DiffieHellman.DhPk.SubF = some { sk := q } := by dsimp only [DY.DiffieHellman.dhPk, DY.DiffieHellman.CanDH.dhPk]; rw [DY.BytesView.view_pack]
  simp only [DY.Libsignal.PQXDH.agree, CompPlant.x25519Key_dhPk, DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, hv] at hag ⊢
  split_ifs at hag ⊢
  · exact nrcensusW_dh_pack hag hpk hsk
  · exact nrcensusW_dh_pack hag (nrcensusW_dhPk hpk_sk hsk) (memoOK_dhPk_elim hpk)
theorem nrcensusW_hmac {a b : DY.Bytes} (ha : FnCensusW allT rT S g a) (hb : FnCensusW allT rT S g b) : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.hmac a b) := nrcensusW_kdfExtract ha hb
theorem nrcensusW_hkdf3 {prk info : DY.Bytes} (h4 : (gamma compI0 S g info).length ≠ 4) (h5 : (gamma compI0 S g info).length ≠ 5) (h15 : (gamma compI0 S g info).length ≠ 15) (h31 : (gamma compI0 S g info).length ≠ 31) (h63 : (gamma compI0 S g info).length ≠ 63) (hinfo1 : 1 ≤ (gamma compI0 S g info).length) (hinfoU : (gamma compI0 S g info).length < 1500) (hinfo102 : (gamma compI0 S g info).take 1 ≠ [110#8]) (hinfo111 : (gamma compI0 S g info).take 1 ≠ [82#8]) (hinfo103 : (gamma compI0 S g info).take 1 ≠ [103#8]) (hprk : FnCensusW allT rT S g prk) (hinfo : FnCensusW allT rT S g info) : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) ∧ FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) ∧ FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := by
  have hb1 : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := by
    unfold DY.Libsignal.TripleRatchet.hkdfBlock1
    refine nrcensusW_hmac hprk (nrcensusW_concat_len_head ?_ ?_ ?_ ?_ ?_ ?_ hinfo1 hinfo102 hinfo111 hinfo103 hinfo (nrcensusW_litByte _ (by decide) (by decide) (by decide))) <;>
      rw [gamma_litByte_length] <;> omega
  have hb2 : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) := by
    unfold DY.Libsignal.TripleRatchet.hkdfBlock2
    refine nrcensusW_hmac hprk (nrcensusW_concat_kdf (not_kdfFree_kdfExtract _ _) (CompFreshDistinct.gamma_hmac_length S g _ _) ?_ ?_ ?_ ?_ ?_ ?_ hb1
      (nrcensusW_concat_len_head ?_ ?_ ?_ ?_ ?_ ?_ hinfo1 hinfo102 hinfo111 hinfo103 hinfo (nrcensusW_litByte _ (by decide) (by decide) (by decide)))) <;>
      simp only [gamma_concat, List.length_append, gamma_litByte_length,
        DY.Libsignal.TripleRatchet.hkdfBlock1, CompFreshDistinct.gamma_hmac_length] <;> omega
  have hb3 : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := by
    unfold DY.Libsignal.TripleRatchet.hkdfBlock3
    refine nrcensusW_hmac hprk (nrcensusW_concat_kdf (not_kdfFree_kdfExtract _ _) (CompFreshDistinct.gamma_hmac_length S g _ _) ?_ ?_ ?_ ?_ ?_ ?_ hb2
      (nrcensusW_concat_len_head ?_ ?_ ?_ ?_ ?_ ?_ hinfo1 hinfo102 hinfo111 hinfo103 hinfo (nrcensusW_litByte _ (by decide) (by decide) (by decide)))) <;>
      simp only [gamma_concat, List.length_append, gamma_litByte_length,
        DY.Libsignal.TripleRatchet.hkdfBlock2, CompFreshDistinct.gamma_hmac_length] <;> omega
  exact ⟨hb1, hb2, hb3⟩
theorem nrcensusW_zeroSalt : FnCensusW allT rT S g DY.Libsignal.TripleRatchet.zeroSalt := nrcensusW_lit_ofBA not_rvW_zeroDh
theorem nrcensusW_discontinuity : FnCensusW allT rT S g DY.Libsignal.PQXDH.discontinuity := nrcensusW_lit_ofBA not_rvW_ff32
set_option maxRecDepth 200000 in
theorem nrcensusW_spqrA2B : FnCensusW allT rT S g DY.Libsignal.TripleRatchet.spqrA2B :=
  nrcensusW_lit_ofBA (by decide +kernel)
set_option maxRecDepth 200000 in
theorem nrcensusW_spqrB2A : FnCensusW allT rT S g DY.Libsignal.TripleRatchet.spqrB2A :=
  nrcensusW_lit_ofBA (by decide +kernel)
set_option maxRecDepth 200000 in
theorem nrcensusW_spqrIdx_one : FnCensusW allT rT S g (DY.Spqr.spqrIdx 1) :=
  nrcensusW_lit_ofBA (by decide +kernel)
theorem nrcensusW_spqrSendKey {st c : DY.Bytes} (hst : FnCensusW allT rT S g st) (hc : FnCensusW allT rT S g c) : FnCensusW allT rT S g (DY.Spqr.spqrSend st c).2.1 := by
  unfold DY.Spqr.spqrSend; dsimp only; have hp := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st
  cases hv : st.view? DY.Spqr.InitState.SubF with
  | none => exact memoOK_spqrSendKey_pack hst hc
  | some x =>
    rw [hv] at hp; rw [← hp] at hst; obtain ⟨hk, hpar⟩ := memoOK_spqrInit_elim hst; exact memoOK_spqrChainKey hk hpar nrcensusW_spqrIdx_one
theorem nrcensusW_trWire_of_len {ver : UInt8} {rk ct pq : DY.Bytes} {c pc : UInt32} {ev : DY.TrWire.EncodingVariation} (h65 : 65 ≤ (gamma compI0 S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev)).length) (h1568 : (gamma compI0 S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev)).length ≠ 1568) (hrk : FnCensusW allT rT S g rk) (hct : FnCensusW allT rT S g ct) (hpq : FnCensusW allT rT S g pq) : FnCensusW allT rT S g (DY.TrWire.trWireMsg ver rk c pc ct pq ev) := by
  rw [show DY.TrWire.trWireMsg ver rk c pc ct pq ev =
        ({ version := ver, senderRatchetKey := rk, counter := c, previousCounter := pc,
           ciphertext := ct, pqRatchet := pq, encodingVariation := ev } :
           DY.TrWire.TrWireMsg.SubF DY.Bytes).pack from rfl] at h65 h1568 ⊢
  intro x hx
  refine memoOK_trWire (P := fun y => y.2.2 = gamma compI0 S g y.1 → FnOKW allT rT y)
    (fun y hy hs => fnokW_of_ni (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_trWire_pack_eq _) hy (by rw [hs, hy]; exact not_rvW_of_len_ge65 h65 h1568))
    (fun y hy _ => hrk y hy) (fun y hy _ => hct y hy) (fun y hy _ => hpq y hy)
    x hx (CompRPreMemoSound.memo_sound compI0 S g _ hx).2
set_option maxRecDepth 200000 in
theorem nrcensusW_createChain_dhPk {rk q sk : DY.Bytes} (hag : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk q) sk ∈ allT) (hpk_sk : DY.DiffieHellman.dhPk sk ∈ allT) (hrk : FnCensusW allT rT S g rk) (hpk : FnCensusW allT rT S g (DY.DiffieHellman.dhPk q)) (hsk : FnCensusW allT rT S g sk) : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.createChain rk (DY.DiffieHellman.dhPk q) sk).1 ∧ FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.createChain rk (DY.DiffieHellman.dhPk q) sk).2 := by
  have h := nrcensusW_hkdf3 (info := DY.Libsignal.TripleRatchet.lit "WhisperRatchet")
    (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (nrcensusW_hmac hrk (nrcensusW_agree_dhPk hag hpk_sk hpk hsk))
    (nrcensusW_lit_ofBA (by rw [toUTF8_eq_ofList]; decide +kernel))
  exact ⟨h.1, h.2.1⟩
theorem nrcensusW_kdfCk {ck : DY.Bytes} (hck : FnCensusW allT rT S g ck) : FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.kdfCk ck).1 ∧ FnCensusW allT rT S g (DY.Libsignal.TripleRatchet.kdfCk ck).2 := ⟨nrcensusW_hmac hck (nrcensusW_litByte _ (by decide) (by decide) (by decide)), nrcensusW_hmac hck (nrcensusW_litByte _ (by decide) (by decide) (by decide))⟩
set_option maxRecDepth 200000 in
theorem nrcensusW_trMsgKeys {salt seed : DY.Bytes}
    (hsalt : FnCensusW allT rT S g salt) (hseed : FnCensusW allT rT S g seed) :
    let mk := DY.Libsignal.TripleRatchet.trMsgKeys salt seed
    FnCensusW allT rT S g mk.cipherKey ∧ FnCensusW allT rT S g mk.macKey ∧ FnCensusW allT rT S g mk.iv :=
  nrcensusW_hkdf3 (info := DY.Libsignal.TripleRatchet.lit "WhisperMessageKeys")
    (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide) (by rw [gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (nrcensusW_hmac hsalt hseed)
    (nrcensusW_lit_ofBA (by rw [toUTF8_eq_ofList]; decide +kernel))
theorem nrcensusW_serializedIk {ik : DY.Bytes} (hikL : (gamma compI0 S g ik).length = 32) (hik : FnCensusW allT rT S g ik) : FnCensusW allT rT S g (DY.Libsignal.PQXDH.serializedIk ik) := by
  unfold DY.Libsignal.PQXDH.serializedIk DY.Libsignal.PQXDH.encodeEC
  refine nrcensusW_concat_len_head ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ (nrcensusW_litByte _ (by decide) (by decide) (by decide)) hik <;>
    first | (rw [gamma_litByte_length, hikL]; decide) | rw [gamma_litByte_length] | (unfold DY.Libsignal.TripleRatchet.litByte; rw [gamma_literalToBytes_eq]; decide)
set_option maxRecDepth 200000 in
theorem nrcensusW_pqxdhKdf_none {dh1 dh2 dh3 ss : DY.Bytes}
    (hdh1L : (gamma compI0 S g dh1).length = 32) (hdh2L : (gamma compI0 S g dh2).length = 32)
    (hdh3L : (gamma compI0 S g dh3).length = 32) (hssL : (gamma compI0 S g ss).length = 32)
    (hdh3X : gamma compI0 S g dh3 ∈ x25519Vals)
    (hdh1 : FnCensusW allT rT S g dh1) (hdh2 : FnCensusW allT rT S g dh2)
    (hdh3 : FnCensusW allT rT S g dh3) (hss : FnCensusW allT rT S g ss) :
    let keys := DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss)
    FnCensusW allT rT S g keys.rk ∧ FnCensusW allT rT S g keys.ck ∧ FnCensusW allT rT S g keys.pqr := by
  have hc3 : FnCensusW allT rT S g (DY.Concat.concat dh3 ss) := nrcensusW_concat (not_rvW_of_x25519_append hdh3X hssL) hdh3 hss
  have hc2 : FnCensusW allT rT S g (DY.Concat.concat dh2 (DY.Concat.concat dh3 ss)) := by
    refine nrcensusW_concat (not_rvW_of_len_ge65 ?_ ?_) hdh2 hc3 <;>
      · rw [List.length_append, gamma_concat, List.length_append, hdh2L, hdh3L, hssL]; decide
  have hc1 : FnCensusW allT rT S g (DY.Concat.concat dh1 (DY.Concat.concat dh2 (DY.Concat.concat dh3 ss))) := by
    refine nrcensusW_concat (not_rvW_of_len_ge65 ?_ ?_) hdh1 hc2 <;>
      · rw [List.length_append, gamma_concat, gamma_concat, List.length_append, List.length_append, hdh1L, hdh2L, hdh3L, hssL]; decide
  have hikm : FnCensusW allT rT S g (DY.Libsignal.PQXDH.pqxdhIkm dh1 dh2 dh3 none ss) := by
    refine nrcensusW_concat (not_rvW_of_len_ge65 ?_ ?_) nrcensusW_discontinuity hc1 <;>
      · rw [List.length_append, DY.Libsignal.PQXDH.discontinuity, CompPlant.gamma_literalToBytes_length, gamma_concat,
          gamma_concat, gamma_concat, List.length_append, List.length_append, List.length_append,
          hdh1L, hdh2L, hdh3L, hssL]; decide
  exact nrcensusW_hkdf3 (info := DY.Libsignal.PQXDH.pqxdhLabel)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by rw [DY.Libsignal.PQXDH.pqxdhLabel, gamma_trLit_length, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.PQXDH.pqxdhLabel DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.PQXDH.pqxdhLabel DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (by unfold DY.Libsignal.PQXDH.pqxdhLabel DY.Libsignal.TripleRatchet.lit; rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]; decide)
    (nrcensusW_hmac nrcensusW_zeroSalt hikm)
    (nrcensusW_lit_ofBA (by rw [toUTF8_eq_ofList]; decide +kernel))
end NRPrim
section Run81
variable {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
abbrev FnC81 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (t : DY.Bytes) : Prop := FnCensusW (allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) (rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) S g t
theorem fnOK81_of_W (hR : ∀ v, Rv81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ v → RvW v) {x : DY.Bytes × DY.Bytes × HwBytes} (h : FnOKW (allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) (rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) x) : FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x := ⟨fun hai hv => h.1 hai (hR _ hv), h.2.1, h.2.2⟩
theorem fnCensus81_of_W (hR : ∀ v, Rv81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ v → RvW v) {t : DY.Bytes} (h : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ t) : FnCensus81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ t := fun x hx => fnOK81_of_W hR (h x hx)
theorem nrcensusW_randTerm81 {ts sz : Nat} (hmR : randTerm ts sz ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (randTerm ts sz) := nrcensusW_randTerm (mem_allTerms81_of_r hmR) hmR
theorem nrcensusW_dhPk81 {sk : DY.Bytes} (hmX : DY.DiffieHellman.dhPk sk ∈ xTerms81 tr₁ tr_bob tr₄) (hsk : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ sk) : FnC81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ (DY.DiffieHellman.dhPk sk) := nrcensusW_dhPk (mem_allTerms81_of_x hmX) hsk
end Run81
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStA
