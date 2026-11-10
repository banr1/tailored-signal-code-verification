/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 200000
namespace Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead78
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompI0Laws Symbolic.BugInjection.Proofs.Common443.CompMemoInjGt Symbolic.BugInjection.Proofs.Common443.CompRSchedBSalts
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.SpecTop hiding compI0
open Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead35 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38 Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy
attribute [local irreducible] Symbolic.BugInjection.hexBytes
export Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead38 ( PtAvoid PtAvoidFull ptAvoid_of_memoInjGt ptAvoidFull_of_memoInjGt ptAvoidFull_lit ptAvoidFull_literalToBytes ptAvoidFull_randTerm_ptAtom ptAvoidFull_randTerm_ne ptAvoidFull_randTerm_of_pin ptAvoidFull_randTerm_of_mem_rng36_inits mem_rng36_inits_ne_and_perm_ne ptAvoidFull_concat ptAvoidFull_prefixTerms ptAvoidFull_hmac ptAvoidFull_dhPk_compI0 gamma_hmac ptAvoidFull_trunc8_of_len ptAvoidFull_trunc8_hmac ptAvoidFull_trWire ptAvoidFull_trWireMsg ptAvoidFull_spqrInit_elim ptAvoidFull_spqrChainKey ptAvoidFull_spqrSendState ptAvoidFull_spqrSendKey_pack ptAvoidFull_spqrSendKey ptAvoidFull_spqrSendMsg ptAvoidFull_hkdfBlock1 ptAvoidFull_hkdfBlock2 ptAvoidFull_hkdfBlock3 ptAvoidFull_trMsgKeys ptAvoidFull_kdfCk ptAvoidFull_kdfCk_fst ptAvoidFull_kdfCk_snd ptAvoidFull_computeMac ptAvoidFull_of_litConcatTree ptAvoidFull_mem_slowNat ptAvoidFull_mem_uint32 ptAvoidFull_mem_bool ptAvoidFull_mem_slowString ptAvoidFull_mem_slowBytes ptAvoidFull_serialize_local_tr rng36Chars rngAt36_eq_hex rng36Str_eq rngAt36_length pt38Chars ptAt38_eq_hex pt38Str_eq ptAt38_eq_fast pt78Chars ptAt78_eq_hex pt78Str_eq ptAt78_eq_fast ptAt78_length call0Rng_take_1_gt_6 call0Rng_drop_33_gt_6 ptAt35_eq_fast ptAt35_eq_compAesPt1 ptAt38_eq_compAesPt2 ptAt78_eq_compAesPt3 ptAvoidFull_symEnc_compI0_of_perm_ne PqxdhSecretsInv PtVisRandTermsInv ptAvoidFull_ptVis_of_randTermsInv ptAvoidFull_storedSecrets_of_inv ptAvoidFull_iniAliceStartState_of_aliceVis ptAvoidFull_encSt_iniAliceStartState aliceOut_fields_memoInjGt ptAvoidFull_encSt_of_aliceVis ptAvoidFull_encOut_iniAliceStartState gamma_randTerm_eq_σ)
def call4Rng : List MachineEvent := ((trace.drop 43).take 35).tail
def rng44Chars : List Char := chars_of_hex (rngAt 44)
theorem rngAt44_eq_hex : rngAt 44 = hexBytes (str_of_hex (rngAt 44)) := rfl
theorem rng44Str_eq : (str_of_hex (rngAt 44)) = String.ofList rng44Chars := rfl
theorem rngAt44_length : (rngAt 44).length = 32 := by
  have h : rngAt 44 = hexBytes.go hexDigit rng44Chars := by rw [rngAt44_eq_hex, rng44Str_eq, hexBytes_ofList]
  rw [h]; rfl
def rng77Chars : List Char := chars_of_hex (rngAt 77)
theorem rngAt77_eq_hex : rngAt 77 = hexBytes (str_of_hex (rngAt 77)) := rfl
theorem rng77Str_eq : (str_of_hex (rngAt 77)) = String.ofList rng77Chars := rfl
theorem rngAt77_length : (rngAt 77).length = 32 := by
  have h : rngAt 77 = hexBytes.go hexDigit rng77Chars := by rw [rngAt77_eq_hex, rng77Str_eq, hexBytes_ofList]
  rw [h]; rfl
theorem call4Rng_take_1_eq : call4Rng.take 1 = [.rng (rngAt 44)] := rfl
theorem call4Rng_drop_33_eq : call4Rng.drop 33 = [.rng (rngAt 77)] := rfl
theorem call4Rng_take_1_gt_6 : ∀ e ∈ call4Rng.take 1, 6 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he; rw [call4Rng_take_1_eq, List.mem_singleton] at he; subst he; show 6 < (rngAt 44).length; rw [rngAt44_length]; decide
theorem call4Rng_drop_33_gt_6 : ∀ e ∈ call4Rng.drop 33, 6 < (Common443.Census443Defs.eventBytes e).length := by
  intro e he; rw [call4Rng_drop_33_eq, List.mem_singleton] at he; subst he; show 6 < (rngAt 77).length; rw [rngAt77_length]; decide
theorem compAesPt1_ne_pt78 : compAesPt1 ≠ ptAt 78 := by rw [ptAt78_eq_compAesPt3]; decide +kernel
theorem compAesPt2_ne_pt78 : compAesPt2 ≠ ptAt 78 := by rw [ptAt78_eq_compAesPt3]; decide +kernel
theorem compAesPerm_compAesPt1_ne_pt78 (k iv : HwBytes) : compAesPerm k iv compAesPt1 ≠ ptAt 78 := by
  intro h; have h16 := compAesPerm_length_ge_16 k iv compAesPt1; have h5 := ptAt78_length; rw [h, h5] at h16; omega
theorem compAesPerm_compAesPt2_ne_pt78 (k iv : HwBytes) : compAesPerm k iv compAesPt2 ≠ ptAt 78 := by
  intro h; have h16 := compAesPerm_length_ge_16 k iv compAesPt2; have h5 := ptAt78_length; rw [h, h5] at h16; omega
theorem ptAvoidFull_encSt2_iniAliceStartState {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (tr₁ tr₂ tr₃ : ExecTrace) (a pB : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl₁ cl₂ : Nat) (hb : b.length < 32) (hikA : MemoInjGt compI0 S g b.length o.ikA) (hikB : MemoInjGt compI0 S g b.length o.ikB) (hspk : MemoInjGt compI0 S g b.length o.spk) (hspk_key : MemoInjGt compI0 S g b.length (DY.X25519.x25519Key o.spk)) (hrk : MemoInjGt compI0 S g b.length o.keys.rk) (hck : MemoInjGt compI0 S g b.length o.keys.ck) (hpqr : MemoInjGt compI0 S g b.length o.keys.pqr) (hdhsA : MemoInjGt compI0 S g b.length (randTerm (tr₁.length + 2) 32)) (hcoin₁ : PtAvoidFull compI0 r S g ms b (randTerm (tr₂.length + 1) cl₁)) (hcoin₂ : PtAvoidFull compI0 r S g ms b (randTerm (tr₃.length + 1) cl₂)) : PtAvoidFull compI0 r S g ms b (Comparse.serialize (⟨a, encSt tr₃ (encSt tr₂ (iniAliceStartState tr₁ pB o) cl₁) cl₂⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by
  have hcc := memoInjGt_createChain hb hrk hspk_key hdhsA; have lift : ∀ {t : DY.Bytes}, MemoInjGt compI0 S g b.length t → PtAvoidFull compI0 r S g ms b t := ptAvoidFull_of_memoInjGt (Nat.le_refl _)
  refine ptAvoidFull_serialize_local_tr (lift (memoInjGt_serializedIk hikA)) (lift (memoInjGt_serializedIk hikB)) (lift hcc.1) (lift hdhsA) (ptAvoidFull_kdfCk_fst hb (ptAvoidFull_kdfCk_fst hb (lift hcc.2))) (lift (memoInjGt_concat (memoInjGt_dhPk_compI0 hb hdhsA) hrk)) (ptAvoidFull_spqrSendState (ptAvoidFull_spqrSendState (lift (memoInjGt_spqrInit hpqr (memoInjGt_lit compI0 S g _ _))) hcoin₁) hcoin₂)
    (fun d hd => by simp only [encSt, iniAliceStartState, List.mem_singleton] at hd; subst hd; exact ⟨lift hspk, lift hck⟩)
theorem ptAvoidFull_encSt2_of_aliceVis {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} {tr₁ tr₂ tr₃ : ExecTrace} {a : Participant} {ikA : DY.Bytes} {hb_h : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} {cl₁ cl₂ : Nat} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hb : b.length < 32) (hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) (hm₀_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb_h)) (hrs_ek : ∀ e ∈ rs.take 1, b.length < (Common443.Census443Defs.eventBytes e).length) (hrs_dhs : ∀ e ∈ rs.drop 33, b.length < (Common443.Census443Defs.eventBytes e).length) (hcoin₁ : PtAvoidFull compI0 r S g ms b (randTerm (tr₂.length + 1) cl₁)) (hcoin₂ : PtAvoidFull compI0 r S g ms b (randTerm (tr₃.length + 1) cl₂)) : PtAvoidFull compI0 r S g ms b (Comparse.serialize (⟨a, encSt tr₃ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState)) := by obtain ⟨hikA, hikB, hspk, hspk_key, hrk, hck, hpqr, hdhs⟩ := aliceOut_fields_memoInjGt hcompat hwf hb hid hm₀_vis hrs_ek hrs_dhs; exact ptAvoidFull_encSt2_iniAliceStartState tr₁ tr₂ tr₃ a r.bob _ cl₁ cl₂ hb hikA hikB hspk hspk_key hrk hck hpqr hdhs hcoin₁ hcoin₂
theorem ptAvoidFull_encOut2_iniAliceStartState {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {b : HwBytes} (tr₁ tr₂ tr₃ : ExecTrace) (pB : Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl₁ cl₂ : Nat) (hb8 : b.length < 8) (hikA : MemoInjGt compI0 S g b.length o.ikA) (hikB : MemoInjGt compI0 S g b.length o.ikB) (hspk_key : MemoInjGt compI0 S g b.length (DY.X25519.x25519Key o.spk)) (hrk : MemoInjGt compI0 S g b.length o.keys.rk) (hpqr : MemoInjGt compI0 S g b.length o.keys.pqr) (hdhsA : MemoInjGt compI0 S g b.length (randTerm (tr₁.length + 2) 32)) (hcoin₁ : PtAvoidFull compI0 r S g ms b (randTerm (tr₂.length + 1) cl₁)) (hcoin₂ : PtAvoidFull compI0 r S g ms b (randTerm (tr₃.length + 1) cl₂)) (hmsg : PtAvoidFull compI0 r S g ms b (randTerm tr₃.length 32)) (hperm : ∀ k iv_b : HwBytes, compAesPerm k iv_b (gamma compI0 S g (randTerm tr₃.length 32)) ≠ b) : PtAvoidFull compI0 r S g ms b (encOut tr₃ (encSt tr₂ (iniAliceStartState tr₁ pB o) cl₁) cl₂ (tr₃.length + 2)) := by
  have hb32 : b.length < 32 := by omega
  have hcc := memoInjGt_createChain hb32 hrk hspk_key hdhsA; have lift : ∀ {t : DY.Bytes}, MemoInjGt compI0 S g b.length t → PtAvoidFull compI0 r S g ms b t := ptAvoidFull_of_memoInjGt (Nat.le_refl _); have hspqr : PtAvoidFull compI0 r S g ms b (iniAliceStartState tr₁ pB o).spqr := lift (memoInjGt_spqrInit hpqr (memoInjGt_lit compI0 S g _ _)); have hspqr₁ := ptAvoidFull_spqrSendState hspqr hcoin₁
  have hkeys := ptAvoidFull_trMsgKeys hb32 (ptAvoidFull_spqrSendKey hspqr₁ hcoin₂) (ptAvoidFull_kdfCk_snd hb32 (ptAvoidFull_kdfCk_fst hb32 (lift hcc.2)))
  have hwire : PtAvoidFull compI0 r S g ms b (encWire tr₃ (encSt tr₂ (iniAliceStartState tr₁ pB o) cl₁) cl₂ (tr₃.length + 2)) := by unfold encWire; rw [encSalt_self]; exact ptAvoidFull_trWireMsg (ptAvoidFull_dhPk_compI0 hb32 (lift hdhsA)) (ptAvoidFull_symEnc_compI0_of_perm_ne hperm hkeys.1 hkeys.2.2 hmsg) (ptAvoidFull_spqrSendMsg hspqr₁ hcoin₂)
  unfold encOut; refine ptAvoidFull_concat hwire ?_; unfold encMac; rw [encSalt_self]
  exact ptAvoidFull_computeMac hb8 hkeys.2.1 (lift (memoInjGt_serializedIk hikA)) (lift (memoInjGt_serializedIk hikB)) hwire
theorem ptAvoidFull_encOut_of_aliceVis_pt78 {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {tr₁ tr₂ : ExecTrace} {a : Participant} {ikA : DY.Bytes} {hb_h : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} {cl : Nat} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) (hm₀_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb_h)) (hrs_ek : ∀ e ∈ rs.take 1, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length) (hrs_dhs : ∀ e ∈ rs.drop 33, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length) (hcoin : PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm (tr₂.length + 1) cl)) (hpt_pin : gamma compI0 S g (randTerm tr₂.length 32) = ptAt 35) : PtAvoidFull compI0 r S g ms (ptAt 78) (encOut tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl (tr₂.length + 2)) := by
  have hb8 : (ptAt 78).length < 8 := by rw [ptAt78_length]; decide
  have hb32 : (ptAt 78).length < 32 := by rw [ptAt78_length]; decide
  obtain ⟨hikA, hikB, _, hspk_key, hrk, _, hpqr, hdhs⟩ := aliceOut_fields_memoInjGt hcompat hwf hb32 hid hm₀_vis hrs_ek hrs_dhs
  have hmsg : PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm tr₂.length 32) := by
    refine ptAvoidFull_randTerm_ne (.inr ?_)
    rw [← gamma_randTerm_eq_σ (i := compI0) (S := S) tr₂.length 32 (by decide), hpt_pin, ptAt35_eq_compAesPt1]
    exact compAesPt1_ne_pt78
  refine ptAvoidFull_encOut_iniAliceStartState tr₁ tr₂ r.bob _ cl hb8 hikA hikB hspk_key hrk hpqr hdhs hcoin hmsg (fun k iv_b => ?_)
  rw [hpt_pin, ptAt35_eq_compAesPt1]; exact compAesPerm_compAesPt1_ne_pt78 k iv_b
theorem ptAvoidFull_encOut2_of_aliceVis_pt78 {r : Records} {S : Sem} {g : Ghost} {ms : List Move} {tr₁ tr₂ tr₃ : ExecTrace} {a : Participant} {ikA : DY.Bytes} {hb_h : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} {cl₁ cl₂ : Nat} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hid : ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) (hm₀_vis : List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb_h)) (hrs_ek : ∀ e ∈ rs.take 1, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length) (hrs_dhs : ∀ e ∈ rs.drop 33, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length) (hcoin₁ : PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm (tr₂.length + 1) cl₁)) (hcoin₂ : PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm (tr₃.length + 1) cl₂)) (hpt_pin : gamma compI0 S g (randTerm tr₃.length 32) = ptAt 38) : PtAvoidFull compI0 r S g ms (ptAt 78) (encOut tr₃ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2)) := by
  have hb8 : (ptAt 78).length < 8 := by rw [ptAt78_length]; decide
  have hb32 : (ptAt 78).length < 32 := by rw [ptAt78_length]; decide
  obtain ⟨hikA, hikB, _, hspk_key, hrk, _, hpqr, hdhs⟩ := aliceOut_fields_memoInjGt hcompat hwf hb32 hid hm₀_vis hrs_ek hrs_dhs
  have hmsg : PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm tr₃.length 32) := by
    refine ptAvoidFull_randTerm_ne (.inr ?_)
    rw [← gamma_randTerm_eq_σ (i := compI0) (S := S) tr₃.length 32 (by decide), hpt_pin, ptAt38_eq_compAesPt2]
    exact compAesPt2_ne_pt78
  refine ptAvoidFull_encOut2_iniAliceStartState tr₁ tr₂ tr₃ r.bob _ cl₁ cl₂ hb8 hikA hikB hspk_key hrk hpqr hdhs hcoin₁ hcoin₂ hmsg (fun k iv_b => ?_)
  rw [hpt_pin, ptAt38_eq_compAesPt2]; exact compAesPerm_compAesPt2_ne_pt78 k iv_b
def Pre78PrefixInv (r : Records) (S : Sem) (g : Ghost) (ms : List Move) : Prop := PqxdhSecretsInv r (runTraceMoves r ms) ∧ (∀ ls ∈ storedStates r (runTraceMoves r ms), PtAvoidFull compI0 r S g ms (ptAt 78) (Comparse.serialize ls) ∨ ∃ (tr₁ : ExecTrace) (a : Participant) (ikA : DY.Bytes) (hb : DY.Libsignal.PQXDH.BundleHandles) (bun : HwBytes) (rs : List MachineEvent), (ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) ∧ (rs = call0Rng ∨ rs = call4Rng) ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bun :: rs) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb) ∧ (ls = ⟨a, iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)⟩ ∨ ∃ (tr₂ : ExecTrace) (cl₁ : Nat), (cl₁ = 0 ∨ gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (rngAt 36).inits) ∧ (ls = ⟨a, encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁⟩ ∨ ∃ (tr₃ : ExecTrace) (cl₂ : Nat), (cl₂ = 0 ∨ PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm (tr₃.length + 1) cl₂)) ∧ ls = ⟨a, encSt tr₃ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂⟩))) ∧ (∀ v ∈ runVis r ms, v.kind = .send → ∀ u ∈ v.terms, PtAvoidFull compI0 r S g ms (ptAt 78) u ∨ ∃ (tr₁ tr₂ : ExecTrace) (a : Participant) (ikA : DY.Bytes) (hb : DY.Libsignal.PQXDH.BundleHandles) (cl₁ : Nat), (ikA = setupSecret r 0 ∨ ikA = setupSecret r 1) ∧ List.Forall₂ (EventMatchesEntry compI0 r S g) (.recv bundle0 :: call0Rng) (aliceVis tr₁ (iniAliceStartTr tr₁ a r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) hb) ∧ (cl₁ = 0 ∨ gamma compI0 S g (randTerm (tr₂.length + 1) cl₁) ∈ (rngAt 36).inits) ∧ ((gamma compI0 S g (randTerm tr₂.length 32) = ptAt 35 ∧ u = encOut tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁ (tr₂.length + 2)) ∨ ∃ (tr₃ : ExecTrace) (cl₂ : Nat), (cl₂ = 0 ∨ PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm (tr₃.length + 1) cl₂)) ∧ gamma compI0 S g (randTerm tr₃.length 32) = ptAt 38 ∧ u = encOut tr₃ (encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ ikA (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl₁) cl₂ (tr₃.length + 2))) ∧ PtVisRandTermsInv (runVis r ms)
theorem ptAvoidFull_prefixTerms_of_pre78PrefixInv {r : Records} {S : Sem} {who₀ : List Participant} {g : Ghost} {ms : List Move} {τ : List MachineEvent} (hwf : RecordsWF r) (hmp : MatchedPrefix compI0 r S who₀ g ms τ) (hinv : Pre78PrefixInv r S g ms) : ∀ u ∈ prefixTerms r (runTraceMoves r ms) (runVis r ms), PtAvoidFull compI0 r S g ms (ptAt 78) u := by
  have hcompat : Compat compI0 r S g := hmp.1
  have hb6 : (ptAt 78).length ≤ 6 := by rw [ptAt78_length]; decide
  have hb32 : (ptAt 78).length < 32 := by rw [ptAt78_length]; decide
  have hrs0_ek : ∀ e ∈ call0Rng.take 1, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length :=
    fun e he => Nat.lt_of_le_of_lt hb6 (call0Rng_take_1_gt_6 e he)
  have hrs0_dhs : ∀ e ∈ call0Rng.drop 33, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length :=
    fun e he => Nat.lt_of_le_of_lt hb6 (call0Rng_drop_33_gt_6 e he)
  have hrs_both_ek : ∀ {rs : List MachineEvent}, (rs = call0Rng ∨ rs = call4Rng) → ∀ e ∈ rs.take 1, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length := by
    rintro rs (rfl | rfl) e he; exact hrs0_ek e he; exact Nat.lt_of_le_of_lt hb6 (call4Rng_take_1_gt_6 e he)
  have hrs_both_dhs : ∀ {rs : List MachineEvent}, (rs = call0Rng ∨ rs = call4Rng) → ∀ e ∈ rs.drop 33, (ptAt 78).length < (Common443.Census443Defs.eventBytes e).length := by
    rintro rs (rfl | rfl) e he; exact hrs0_dhs e he; exact Nat.lt_of_le_of_lt hb6 (call4Rng_drop_33_gt_6 e he)
  have hcoin2_of : ∀ {tr₃ : ExecTrace} {cl₂ : Nat}, (cl₂ = 0 ∨ PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm (tr₃.length + 1) cl₂)) → PtAvoidFull compI0 r S g ms (ptAt 78) (randTerm (tr₃.length + 1) cl₂) := by
    rintro tr₃ cl₂ (rfl | hc₂); exact ptAvoidFull_randTerm_ne (.inl rfl); exact hc₂
  refine ptAvoidFull_prefixTerms ?_ ?_ (ptAvoidFull_storedSecrets_of_inv hcompat hwf hb32 hinv.1) (ptAvoidFull_ptVis_of_randTermsInv hinv.2.2.2)
  · intro v hv hk u hu
    rcases hinv.2.2.1 v hv hk u hu with hav | ⟨tr₁, tr₂, a, ikA, hb_h, cl₁, hid, hm₀_vis, hcpin₁, ⟨hpt_pin, rfl⟩ | ⟨tr₃, cl₂, hc₂, hpt_pin, rfl⟩⟩
    · exact hav
    · exact ptAvoidFull_encOut_of_aliceVis_pt78 hcompat hwf hid hm₀_vis hrs0_ek hrs0_dhs (ptAvoidFull_randTerm_of_mem_rng36_inits (.inr rfl) hcpin₁) hpt_pin
    · exact ptAvoidFull_encOut2_of_aliceVis_pt78 hcompat hwf hid hm₀_vis hrs0_ek hrs0_dhs (ptAvoidFull_randTerm_of_mem_rng36_inits (.inr rfl) hcpin₁) (hcoin2_of hc₂) hpt_pin
  · intro ls hls
    rcases hinv.2.1 ls hls with hav | ⟨tr₁, a, ikA, hb_h, bun, rs, hid, hrs_cases, hm₀_vis, rfl | ⟨tr₂, cl₁, hcpin₁, rfl | ⟨tr₃, cl₂, hc₂, rfl⟩⟩⟩
    · exact hav
    · exact ptAvoidFull_iniAliceStartState_of_aliceVis hcompat hwf hb32 hid hm₀_vis (hrs_both_ek hrs_cases) (hrs_both_dhs hrs_cases)
    · exact ptAvoidFull_encSt_of_aliceVis hcompat hwf hb32 hid hm₀_vis (hrs_both_ek hrs_cases) (hrs_both_dhs hrs_cases) (ptAvoidFull_randTerm_of_mem_rng36_inits (.inr rfl) hcpin₁)
    · exact ptAvoidFull_encSt2_of_aliceVis hcompat hwf hb32 hid hm₀_vis (hrs_both_ek hrs_cases) (hrs_both_dhs hrs_cases) (ptAvoidFull_randTerm_of_mem_rng36_inits (.inr rfl) hcpin₁) (hcoin2_of hc₂)
theorem ptDeadAt78_of (hinv : ∀ (r : Records) (S : Sem) (g : Ghost) (ms : List Move), compFitsPinned setup compI0 r → ExplainsMoves compI0 r S who ok g ms (trace.take 78) → Common443.CompSetupSecrecy.NoBrk r ms → Pre78PrefixInv r S g ms) : PtDeadAt 78 := by intro r S g ms hfits hnb hexp hem hcol; exact not_pt_collision_of_ne_bytes_full hem (ptAvoidFull_prefixTerms_of_pre78PrefixInv hfits.1.1 hexp.1 (hinv r S g ms hfits hexp hnb)) (hcol g ⟨rfl, hexp.1⟩)
end Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.PtDead78
