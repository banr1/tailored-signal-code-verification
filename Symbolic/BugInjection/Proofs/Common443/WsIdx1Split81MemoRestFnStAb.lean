/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStA
import Init.Data.String
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStAb
open CryptoProofLib.Refinement (ExternInterpretation)
open ByteSpecs DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPlant Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown Symbolic.BugInjection.Proofs.Common443.CompRX0Top Symbolic.BugInjection.Proofs.Common443.CompRI0TermInj Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape Symbolic.BugInjection.Proofs.Common443.CompC3RestFn38HBA Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnTbl Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81DrawPins Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStA Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
private theorem toUTF8_eq_ofList (s : String) : s.toUTF8 = List.utf8Encode s.toList := by
  conv_lhs => rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
section NRSer
variable {allT rT : List DY.Bytes} {S : Sem} {g : Ghost}
theorem nrcensusW_concatPrefixes_kdfTail6 :
    ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FnCensusW allT rT S g p) → FnCensusW allT rT S g s → KdfTail6 (gamma compI0 S g s) → FnCensusW allT rT S g (Comparse.concatPrefixes ps s) ∧ KdfTail6 (gamma compI0 S g (Comparse.concatPrefixes ps s))
  | [], _, _, hs, hT => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact ⟨hs, hT⟩
  | p :: ps, s, hps, hs, hT => by
    obtain ⟨ih, ihT⟩ := nrcensusW_concatPrefixes_kdfTail6 ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs hT
    have hT' : KdfTail6 (gamma compI0 S g p ++ gamma compI0 S g (Comparse.concatPrefixes ps s)) := ihT.append_left _
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat]
    exact ⟨nrcensusW_concat (kdfTail6_not_rvW hT') (hps p (List.mem_cons_self ..)) ih, hT'⟩
theorem nrcensusW_concatPrefixes_kdfTail7 :
    ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FnCensusW allT rT S g p) → FnCensusW allT rT S g s → KdfTail7 (gamma compI0 S g s) → FnCensusW allT rT S g (Comparse.concatPrefixes ps s) ∧ KdfTail7 (gamma compI0 S g (Comparse.concatPrefixes ps s))
  | [], _, _, hs, hT => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact ⟨hs, hT⟩
  | p :: ps, s, hps, hs, hT => by
    obtain ⟨ih, ihT⟩ := nrcensusW_concatPrefixes_kdfTail7 ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs hT
    have hT' : KdfTail7 (gamma compI0 S g p ++ gamma compI0 S g (Comparse.concatPrefixes ps s)) := ihT.append_left _
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat]
    exact ⟨nrcensusW_concat (kdfTail7_not_rvW hT') (hps p (List.mem_cons_self ..)) ih, hT'⟩
theorem nrcensusW_concatPrefixes_ge65 :
    ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FnCensusW allT rT S g p) → FnCensusW allT rT S g s → 65 ≤ (gamma compI0 S g s).length → (gamma compI0 S g (Comparse.concatPrefixes ps s)).length < 1568 → FnCensusW allT rT S g (Comparse.concatPrefixes ps s) ∧ 65 ≤ (gamma compI0 S g (Comparse.concatPrefixes ps s)).length
  | [], _, _, hs, hL, _ => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact ⟨hs, hL⟩
  | p :: ps, s, hps, hs, hL, hU => by
    have hlen : (gamma compI0 S g (Comparse.concatPrefixes (p :: ps) s)).length = (gamma compI0 S g p).length + (gamma compI0 S g (Comparse.concatPrefixes ps s)).length := by
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat, List.length_append]
    obtain ⟨ih, ihL⟩ := nrcensusW_concatPrefixes_ge65 ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs hL (by omega)
    refine ⟨?_, by omega⟩
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    refine nrcensusW_concat (not_rvW_of_len_ge65 ?_ ?_) (hps p (List.mem_cons_self ..)) ih <;> · rw [List.length_append]; omega
private theorem shortHeadOK_ne178 {v : HwBytes} (h : ShortHeadOK v) : v.take 1 ≠ [110#8] :=
  fun heq => absurd (heq ▸ h.2) (by decide)
private theorem shortHeadOK_ne24 {v : HwBytes} (h : ShortHeadOK v) : v.take 1 ≠ [82#8] :=
  fun heq => absurd (heq ▸ h.2) (by decide)
private theorem shortHeadOK_ne103 {v : HwBytes} (h : ShortHeadOK v) : v.take 1 ≠ [103#8] :=
  fun heq => absurd (heq ▸ h.2) (by decide)
theorem nrcensusW_concatPrefixes_33_lt64 :
    ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FnCensusW allT rT S g p ∧ ShortHeadOK (gamma compI0 S g p)) → FnCensusW allT rT S g s → 33 ≤ (gamma compI0 S g s).length → (gamma compI0 S g (Comparse.concatPrefixes ps s)).length < 64 → FnCensusW allT rT S g (Comparse.concatPrefixes ps s) ∧ 33 ≤ (gamma compI0 S g (Comparse.concatPrefixes ps s)).length
  | [], _, _, hs, h33, _ => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact ⟨hs, h33⟩
  | p :: ps, s, hps, hs, h33, h64 => by
    have hlen : (gamma compI0 S g (Comparse.concatPrefixes (p :: ps) s)).length = (gamma compI0 S g p).length + (gamma compI0 S g (Comparse.concatPrefixes ps s)).length := by
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat, List.length_append]
    obtain ⟨ih, ih33⟩ := nrcensusW_concatPrefixes_33_lt64 ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs h33 (by omega)
    obtain ⟨hpC, hpH⟩ := hps p (List.mem_cons_self ..)
    refine ⟨?_, by omega⟩
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    exact nrcensusW_concat_len_head (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hpH.1 (shortHeadOK_ne178 hpH) (shortHeadOK_ne24 hpH) (shortHeadOK_ne103 hpH) hpC ih
theorem nrcensusW_concatPrefixes_lt9_head :
    ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, FnCensusW allT rT S g p ∧ ShortHeadOK (gamma compI0 S g p)) → FnCensusW allT rT S g s → (gamma compI0 S g (Comparse.concatPrefixes ps s)).length < 9 → FnCensusW allT rT S g (Comparse.concatPrefixes ps s)
  | [], _, _, hs, _ => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact hs
  | p :: ps, s, hps, hs, hL => by
    have hlen : (gamma compI0 S g (Comparse.concatPrefixes (p :: ps) s)).length = (gamma compI0 S g p).length + (gamma compI0 S g (Comparse.concatPrefixes ps s)).length := by
      rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons, gamma_concat, List.length_append]
    have ih := nrcensusW_concatPrefixes_lt9_head ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs (by omega)
    obtain ⟨hpC, hpH⟩ := hps p (List.mem_cons_self ..)
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    refine nrcensusW_concat (not_rvW_of_short_append_head ?_ hpH) hpC ih
    rw [List.length_append]; omega
set_option maxRecDepth 200000 in
theorem nrcensusW_mem_bool_short_head (b : Bool) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.bool.serialize b) : FnCensusW allT rT S g p ∧ ShortHeadOK (gamma compI0 S g p) := by
  obtain ⟨ba, hba_sz, hba_hd, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.bool_serialize_singleton_head b
  rw [hser] at hp; rcases List.mem_singleton.mp hp with rfl
  have hsh : ShortHeadOK (gamma compI0 S g (DY.Literal.literalToBytes ba)) := by
    refine ⟨?_, ?_⟩
    · rw [CompPlant.gamma_literalToBytes_length]; omega
    · rw [gamma_literalToBytes_eq, hba_hd]; cases b <;> decide
  refine ⟨?_, hsh⟩
  refine nrcensusW_lit _ (not_rvW_of_len_head ?_ ?_ ?_ ?_ ?_ ?_
    (shortHeadOK_ne178 hsh) (shortHeadOK_ne24 hsh) (shortHeadOK_ne103 hsh)) <;>
    rw [CompPlant.gamma_literalToBytes_length] <;> omega
theorem nrcensusW_mem_bool (b : Bool) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.bool.serialize b) : FnCensusW allT rT S g p :=
  (nrcensusW_mem_bool_short_head b hp).1
theorem nrcensusW_mem_slowNat :
    ∀ (n : Nat) {p : DY.Bytes}, p ∈ Comparse.NonExtensibleMessageFormat.slowNat.serialize n → FnCensusW allT rT S g p
  | 0, _, hp => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_zero] at hp
    exact nrcensusW_mem_bool false hp
  | n + 1, _, hp => by
    have hstep := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_succ n
    rw [hstep, List.mem_append] at hp; exact hp.elim (nrcensusW_mem_bool true) (nrcensusW_mem_slowNat n)
theorem nrcensusW_mem_slowNat_short_head :
    ∀ (n : Nat) {p : DY.Bytes}, p ∈ Comparse.NonExtensibleMessageFormat.slowNat.serialize n → FnCensusW allT rT S g p ∧ ShortHeadOK (gamma compI0 S g p)
  | 0, _, hp => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_zero] at hp
    exact nrcensusW_mem_bool_short_head false hp
  | n + 1, _, hp => by
    have hstep := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_succ n
    rw [hstep, List.mem_append] at hp; exact hp.elim (nrcensusW_mem_bool_short_head true) (nrcensusW_mem_slowNat_short_head n)
private theorem nrcensusW_mem_uint32_012_short_head {n : UInt32} (hn : n = 0 ∨ n = 1 ∨ n = 2) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize n) : FnCensusW allT rT S g p ∧ ShortHeadOK (gamma compI0 S g p) := by
  obtain ⟨ba, hba_sz, hba_hd, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.uint32_serialize_singleton_head n hn
  rw [hser] at hp; rcases List.mem_singleton.mp hp with rfl
  have hsh : ShortHeadOK (gamma compI0 S g (DY.Literal.literalToBytes ba)) := by
    refine ⟨?_, ?_⟩
    · rw [CompPlant.gamma_literalToBytes_length]; omega
    · rw [gamma_literalToBytes_eq]; rcases hba_hd with rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  refine ⟨?_, hsh⟩
  refine nrcensusW_lit _ (not_rvW_of_len_head ?_ ?_ ?_ ?_ ?_ ?_
    (shortHeadOK_ne178 hsh) (shortHeadOK_ne24 hsh) (shortHeadOK_ne103 hsh)) <;>
    rw [CompPlant.gamma_literalToBytes_length] <;> omega
theorem nrcensusW_mem_uint32_012 {n : UInt32} (hn : n = 0 ∨ n = 1 ∨ n = 2) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize n) : FnCensusW allT rT S g p :=
  (nrcensusW_mem_uint32_012_short_head hn hp).1
theorem nrcensusW_mem_uint32_zero_short_head {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize 0) : FnCensusW allT rT S g p ∧ ShortHeadOK (gamma compI0 S g p) :=
  nrcensusW_mem_uint32_012_short_head (Or.inl rfl) hp
theorem nrcensusW_mem_uint32_two_short_head {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize 2) : FnCensusW allT rT S g p ∧ ShortHeadOK (gamma compI0 S g p) :=
  nrcensusW_mem_uint32_012_short_head (Or.inr (Or.inr rfl)) hp
theorem nrcensusW_mem_slowBytes {b : DY.Bytes} (hb : FnCensusW allT rT S g b) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowBytes.serialize b) : FnCensusW allT rT S g p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq b
  rw [hser, List.mem_append, List.mem_singleton] at hp; exact hp.elim (nrcensusW_mem_slowNat _) (· ▸ hb)
theorem nrcensusW_mem_slowString_participant {s : String} (hs : s = "alice" ∨ s = "bob") {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowString.serialize s) : FnCensusW allT rT S g p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s
  rw [hser, List.mem_append, List.mem_singleton] at hp
  rcases hp with hnat | rfl <;> [exact nrcensusW_mem_slowNat _ hnat; exact nrcensusW_lit_participant hs]
set_option maxRecDepth 200000 in
theorem nrcensusW_mem_slowString_participant_short_head {s : String} (hs : s = "alice" ∨ s = "bob") {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowString.serialize s) : FnCensusW allT rT S g p ∧ ShortHeadOK (gamma compI0 S g p) := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s
  rw [hser, List.mem_append, List.mem_singleton] at hp
  rcases hp with hnat | rfl
  · exact nrcensusW_mem_slowNat_short_head _ hnat
  · refine ⟨nrcensusW_lit_participant hs, ?_, ?_⟩
    · change 1 ≤ (gamma compI0 S g (DY.Literal.literalToBytes s.toUTF8)).length
      rw [CompPlant.gamma_literalToBytes_length, toUTF8_eq_ofList]; rcases hs with rfl | rfl <;> decide
    · change (gamma compI0 S g (DY.Literal.literalToBytes s.toUTF8)).take 1 ∈ _
      rw [gamma_literalToBytes_eq, toUTF8_eq_ofList]
      rcases hs with rfl | rfl <;> decide +kernel
theorem nrcensusW_serialize_recv1 {rk ck : DY.Bytes}
    (hrk : FnCensusW allT rT S g rk) (hck : FnCensusW allT rT S g ck)
    (hck_kf : ¬ KdfFree (gamma compI0 S g ck)) (hckL : (gamma compI0 S g ck).length = 32) :
    let l := (Comparse.ExtensibleMessageFormat.list
      (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize
      [{ ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 }]
    FnCensusW allT rT S g l ∧ KdfTail6 (gamma compI0 S g l) := by
  intro l
  let t0 : DY.Bytes := Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize 0 ++ Comparse.NonExtensibleMessageFormat.slowNat.serialize 1) (DY.Literal.literalToBytes .empty)
  let t_ck : DY.Bytes := Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length ck)) (DY.Concat.concat ck t0)
  have hl : l = Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize rk ++ Comparse.NonExtensibleMessageFormat.slowBytes.serialize ck) t0 := by
    have hnil := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_nil
    have h1 := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons { ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 } []
    have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq { ratchetKey := rk, chainKey := ck, index := 0, rIdx := 1 }
    dsimp only [l]; rw [h1, hser, hnil, ← List.append_assoc, ← CompExcuse.concatPrefixes_append, ← CompExcuse.concatPrefixes_append]
  have hT0 : FnCensusW allT rT S g t0 ∧ (gamma compI0 S g t0).length = 6 := by
    have hL : (gamma compI0 S g t0).length = 6 := by
      dsimp only [t0]; rw [gamma_concatPrefixes_length, List.flatMap_append, List.length_append, CompPlant.gamma_uint32_serialize_length, CompPlant.gamma_slowNat_serialize_length, CompPlant.gamma_literalToBytes_length]; rfl
    refine ⟨nrcensusW_concatPrefixes_lt9_head _ ?_
      (nrcensusW_lit_size _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by change (gamma compI0 S g t0).length < 9; omega), hL⟩
    exact fun _ hp => (List.mem_append.mp hp).elim nrcensusW_mem_uint32_zero_short_head (nrcensusW_mem_slowNat_short_head 1)
  have hsplit_ck := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq ck
  have hsplit_rk := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq rk
  have hckT' : KdfTail6 (gamma compI0 S g ck ++ gamma compI0 S g t0) := ⟨[], _, _, rfl, hck_kf, hckL, hT0.2⟩
  obtain ⟨hs_ck, hs_ckT⟩ := nrcensusW_concatPrefixes_kdfTail6 _
    (fun _ hp => nrcensusW_mem_slowNat _ hp) (nrcensusW_concat (kdfTail6_not_rvW hckT') hck hT0.1) (by rw [gamma_concat]; exact hckT')
  have hT2T' : KdfTail6 (gamma compI0 S g rk ++ gamma compI0 S g t_ck) := hs_ckT.append_left _
  rw [hl, ← CompExcuse.concatPrefixes_append, hsplit_ck, ← CompExcuse.concatPrefixes_append, concatPrefixes_singleton, hsplit_rk, ← CompExcuse.concatPrefixes_append, concatPrefixes_singleton]
  exact nrcensusW_concatPrefixes_kdfTail6 _ (fun _ hp => nrcensusW_mem_slowNat _ hp)
    (nrcensusW_concat (kdfTail6_not_rvW hT2T') hrk hs_ck) (by rw [gamma_concat]; exact hT2T')
theorem nrcensusW_serialize_recv2 {rk ck : DY.Bytes}
    (hrk : FnCensusW allT rT S g rk) (hck : FnCensusW allT rT S g ck)
    (hck_kf : ¬ KdfFree (gamma compI0 S g ck)) (hckL : (gamma compI0 S g ck).length = 32) :
    let l := (Comparse.ExtensibleMessageFormat.list
      (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize
      [{ ratchetKey := rk, chainKey := ck, index := 2, rIdx := 2 }]
    FnCensusW allT rT S g l ∧ KdfTail7 (gamma compI0 S g l) := by
  intro l
  let t0 : DY.Bytes := Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize 2 ++ Comparse.NonExtensibleMessageFormat.slowNat.serialize 2) (DY.Literal.literalToBytes .empty)
  let t_ck : DY.Bytes := Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length ck)) (DY.Concat.concat ck t0)
  have hl : l = Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize rk ++ Comparse.NonExtensibleMessageFormat.slowBytes.serialize ck) t0 := by
    have hnil := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_nil
    have h1 := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons { ratchetKey := rk, chainKey := ck, index := 2, rIdx := 2 } []
    have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq { ratchetKey := rk, chainKey := ck, index := 2, rIdx := 2 }
    dsimp only [l]; rw [h1, hser, hnil, ← List.append_assoc, ← CompExcuse.concatPrefixes_append, ← CompExcuse.concatPrefixes_append]
  have hT0 : FnCensusW allT rT S g t0 ∧ (gamma compI0 S g t0).length = 7 := by
    have hL : (gamma compI0 S g t0).length = 7 := by
      dsimp only [t0]; rw [gamma_concatPrefixes_length, List.flatMap_append, List.length_append, CompPlant.gamma_uint32_serialize_length, CompPlant.gamma_slowNat_serialize_length, CompPlant.gamma_literalToBytes_length]; rfl
    refine ⟨nrcensusW_concatPrefixes_lt9_head _ ?_
      (nrcensusW_lit_size _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by change (gamma compI0 S g t0).length < 9; omega), hL⟩
    exact fun _ hp => (List.mem_append.mp hp).elim nrcensusW_mem_uint32_two_short_head (nrcensusW_mem_slowNat_short_head 2)
  have hsplit_ck := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq ck
  have hsplit_rk := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq rk
  have hckT' : KdfTail7 (gamma compI0 S g ck ++ gamma compI0 S g t0) := ⟨[], _, _, rfl, hck_kf, hckL, hT0.2⟩
  obtain ⟨hs_ck, hs_ckT⟩ := nrcensusW_concatPrefixes_kdfTail7 _
    (fun _ hp => nrcensusW_mem_slowNat _ hp) (nrcensusW_concat (kdfTail7_not_rvW hckT') hck hT0.1) (by rw [gamma_concat]; exact hckT')
  have hT2T' : KdfTail7 (gamma compI0 S g rk ++ gamma compI0 S g t_ck) := hs_ckT.append_left _
  rw [hl, ← CompExcuse.concatPrefixes_append, hsplit_ck, ← CompExcuse.concatPrefixes_append, concatPrefixes_singleton, hsplit_rk, ← CompExcuse.concatPrefixes_append, concatPrefixes_singleton]
  exact nrcensusW_concatPrefixes_kdfTail7 _ (fun _ hp => nrcensusW_mem_slowNat _ hp)
    (nrcensusW_concat (kdfTail7_not_rvW hT2T') hrk hs_ck) (by rw [gamma_concat]; exact hT2T')
theorem nrcensusW_concatPrefixes_bool (b : Bool) {s : DY.Bytes} (hs : FnCensusW allT rT S g s) (hL : (gamma compI0 S g s).length = 32 ∨ (gamma compI0 S g s).length = 64) : FnCensusW allT rT S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.bool.serialize b) s) ∧ ((gamma compI0 S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.bool.serialize b) s)).length = 33 ∨ 65 ≤ (gamma compI0 S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.bool.serialize b) s)).length) := by
  obtain ⟨ba, _, hx⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bool_serialize_singleton b
  let x : DY.Bytes := DY.Literal.literalToBytes ba
  obtain ⟨hxC, hxH⟩ : FnCensusW allT rT S g x ∧ ShortHeadOK (gamma compI0 S g x) :=
    nrcensusW_mem_bool_short_head b (by rw [hx]; exact List.mem_singleton_self x)
  have hxL : (gamma compI0 S g x).length = 1 := by
    have h := CompPlant.gamma_bool_serialize_length compI0 S g b; rw [hx] at h; simpa using h
  rw [hx, concatPrefixes_singleton, gamma_concat, List.length_append, hxL]
  refine ⟨nrcensusW_concat_len_head (by rw [hxL]; omega) (by rw [hxL]; omega) (by rw [hxL]; omega)
    (by rw [hxL]; omega) (by rw [hxL]; omega) (by rw [hxL]; omega) hxH.1 (shortHeadOK_ne178 hxH) (shortHeadOK_ne24 hxH) (shortHeadOK_ne103 hxH) hxC hs, by omega⟩
theorem nrcensusW_serialize_local_pqxdh {ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState} (hpa : ls.participant = "alice" ∨ ls.participant = "bob") (hsk : FnCensusW allT rT S g ls.state.sk) (hskL : (gamma compI0 S g ls.state.sk).length = 32 ∨ (gamma compI0 S g ls.state.sk).length = 64) : FnCensusW allT rT S g (Comparse.serialize ls : DY.Bytes) := by
  rw [CompRX0NBSC38Parts.serialize_local_pqxdh_eq, ← CompExcuse.concatPrefixes_append, ← CompExcuse.concatPrefixes_append]; obtain ⟨h2, h2L⟩ := nrcensusW_concatPrefixes_bool (allT := allT) (rT := rT) (S := S) (g := g) ls.state.kind.toBits.2 hsk hskL
  have hps : ∀ p ∈ (Comparse.NonExtensibleMessageFormat.slowString (Bytes := DY.Bytes)).serialize ls.participant ++
      (Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize ls.state.kind.toBits.1,
      FnCensusW allT rT S g p ∧ ShortHeadOK (gamma compI0 S g p) := fun _ hp =>
    (List.mem_append.mp hp).elim (nrcensusW_mem_slowString_participant_short_head hpa) (nrcensusW_mem_bool_short_head _)
  rw [CompExcuse.concatPrefixes_append]
  rcases h2L with h33 | h65
  · refine (nrcensusW_concatPrefixes_33_lt64 _ hps h2 (by omega) ?_).1
    rw [gamma_concatPrefixes_length, List.flatMap_append, List.length_append, gamma_slowString_serialize_length, CompPlant.gamma_bool_serialize_length, h33]
    rcases hpa with hpA | hpB
    · rw [hpA, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.2]; decide
    · rw [hpB, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.2]; decide
  · refine (nrcensusW_concatPrefixes_ge65 _ (fun p hp => (hps p hp).1) h2 h65 ?_).1
    have hpartU : ls.participant.utf8ByteSize + 1 + ls.participant.toUTF8.size < 20 := by
      rcases hpa with hpA | hpB
      · rw [hpA, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.alice_utf8_sizes.2]; decide
      · rw [hpB, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.1, Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bob_utf8_sizes.2]; decide
    simp only [gamma_concatPrefixes_length, List.flatMap_append, List.length_append, gamma_slowString_serialize_length, CompPlant.gamma_bool_serialize_length]
    rcases hskL with h | h <;> omega
end NRSer
section TRStateSer
variable {allT rT : List DY.Bytes} {S : Sem} {g : Ghost}
structure TRStateNRC (allT rT : List DY.Bytes) (S : Sem) (g : Ghost)
    (st : DY.Libsignal.TripleRatchet.TRState) : Prop where
  peer : st.peer = "alice" ∨ st.peer = "bob"
  myIk : FnCensusW allT rT S g st.myIk
  peerIk : FnCensusW allT rT S g st.peerIk
  rk : FnCensusW allT rT S g st.rk
  dhs : FnCensusW allT rT S g st.dhs
  cks : FnCensusW allT rT S g st.cks
  sid : FnCensusW allT rT S g st.sid
  spqr : FnCensusW allT rT S g st.spqr
  recv : FnCensusW allT rT S g ((Comparse.ExtensibleMessageFormat.list
    (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize st.recv)
  recvT : KdfTail6 (gamma compI0 S g ((Comparse.ExtensibleMessageFormat.list
      (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize st.recv)) ∨
    KdfTail7 (gamma compI0 S g ((Comparse.ExtensibleMessageFormat.list
      (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize st.recv))
  myIkL : (gamma compI0 S g st.myIk).length = 33
  peerIkL : (gamma compI0 S g st.peerIk).length = 33
  ns_val : st.ns = 0 ∨ st.ns = 1 ∨ st.ns = 2
  pn_val : st.pn = 0
theorem nrcensusW_mem_trStatePrefixes {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hpa : ls.participant = "alice" ∨ ls.participant = "bob") (hst : TRStateNRC allT rT S g ls.state) {p : DY.Bytes} (hp : p ∈ trStatePrefixes ls) : FnCensusW allT rT S g p := by
  unfold trStatePrefixes at hp; simp only [List.mem_append] at hp
  rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact nrcensusW_mem_slowString_participant hpa h1
  · exact nrcensusW_mem_slowString_participant hst.peer h2
  · exact nrcensusW_mem_slowBytes hst.myIk h3
  · exact nrcensusW_mem_slowBytes hst.peerIk h4
  · exact nrcensusW_mem_slowBytes hst.rk h5
  · exact nrcensusW_mem_slowBytes hst.dhs h6
  · exact nrcensusW_mem_slowBytes hst.cks h7
  · exact nrcensusW_mem_uint32_012 hst.ns_val h8
  · exact nrcensusW_mem_uint32_012 (Or.inl hst.pn_val) h9
  · exact nrcensusW_mem_slowBytes hst.sid h10
  · exact nrcensusW_mem_bool _ h11
  · exact nrcensusW_mem_slowNat _ h12
  · exact nrcensusW_mem_slowBytes hst.spqr h13
theorem nrcensusW_serialize_local_tr {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hpa : ls.participant = "alice" ∨ ls.participant = "bob") (hst : TRStateNRC allT rT S g ls.state) : FnCensusW allT rT S g (Comparse.serialize ls : DY.Bytes) := by
  have hser : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes (trStatePrefixes ls) ((Comparse.ExtensibleMessageFormat.list
        (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize ls.state.recv) := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_tr_eq_bridge ls]
    simp only [trStatePrefixes, ← CompExcuse.concatPrefixes_append]
  rw [hser]
  rcases hst.recvT with hT6 | hT7
  · exact (nrcensusW_concatPrefixes_kdfTail6 _ (fun _ hp => nrcensusW_mem_trStatePrefixes hpa hst hp) hst.recv hT6).1
  · exact (nrcensusW_concatPrefixes_kdfTail7 _ (fun _ hp => nrcensusW_mem_trStatePrefixes hpa hst hp) hst.recv hT7).1
end TRStateSer
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnStAb
