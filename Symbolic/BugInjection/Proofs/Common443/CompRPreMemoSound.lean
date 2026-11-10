/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common.DefsCompI0

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement
section Unfold
variable (i : ExternInterpretation) (S : Sem) (g : Ghost)
theorem ms_pack_random (x : DY.Random.Random DY.Bytes) : gamma' i S g x.pack = gRandom g x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)]
theorem ms_pack_lit (x : DY.Literal.Literal.SubF DY.Bytes) : gamma' i S g x.pack = gLit0 x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq gLit0 (gAll i S g)]
theorem ms_pack_concat (x : DY.Concat.Concat.SubF DY.Bytes) : gamma' i S g x.pack = gConcat0 x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq gConcat0 (gAll i S g)]
theorem ms_pack_dhPk (x : DY.DiffieHellman.DhPk.SubF DY.Bytes) : gamma' i S g x.pack = gDhPk i x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (gDhPk i) (gAll i S g)]
theorem ms_pack_dh (x : DY.DiffieHellman.Dh.SubF DY.Bytes) : gamma' i S g x.pack = gDh i x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (gDh i) (gAll i S g)]
theorem ms_pack_kdf (x : DY.KdfExtract.KdfExtract.SubF DY.Bytes) : gamma' i S g x.pack = gKdf0 i x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)]
theorem ms_pack_sym (x : DY.SymEnc.Enc.SubF DY.Bytes) : gamma' i S g x.pack = gSym0 i x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (gSym0 i) (gAll i S g)]
theorem ms_pack_trunc (x : DY.Trunc.Trunc8.SubF DY.Bytes) : gamma' i S g x.pack = gTrunc0 x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq gTrunc0 (gAll i S g)]
theorem ms_pack_variant (x : DY.X25519.Variant.SubF DY.Bytes) : gamma' i S g x.pack = gVariant0 i x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (gVariant0 i) (gAll i S g)]
theorem ms_pack_trWire (x : DY.TrWire.TrWireMsg.SubF DY.Bytes) : gamma' i S g x.pack = gTrWire0 g x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)]
theorem ms_pack_kemEncap (x : DY.PQKem.Encap.SubF DY.Bytes) : gamma' i S g x.pack = gKemEncap i x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (gKemEncap i) (gAll i S g)]
theorem ms_pack_kemSS (x : DY.PQKem.SharedSecret.SubF DY.Bytes) : gamma' i S g x.pack = gKemSS i S x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (gKemSS i S) (gAll i S g)]
theorem ms_pack_kemRej (x : DY.PQKem.RejKey.SubF DY.Bytes) : gamma' i S g x.pack = concretizeKemRej S x (fun y _ => gamma' i S g y) := by unfold gamma'; rw [DY.Bytes.rec_eq (concretizeKemRej S) (gAll i S g)]
end Unfold
structure MemoRowClosed (i : ExternInterpretation) (S : Sem) (g : Ghost) (P : G → Prop) : Prop where
  hnode : ∀ {v : HwBytes} {self sh : DY.Bytes} {cs : List G}, gamma' i S g self = node v self sh cs → (∀ c ∈ cs, P c) → P (node v self sh cs)
  hopq : ∀ {v : HwBytes} {cs : List G}, (∀ c ∈ cs, P c) → P (opaqueNode v cs)
  hempty : P { bytes := [], shape := litOf [], memo := [] }
theorem ms_all_nil {P : G → Prop} : ∀ c ∈ ([] : List G), P c :=
  fun _ hc => by cases hc
theorem ms_all_cons {P : G → Prop} {a : G} {l : List G} (ha : P a) (hl : ∀ c ∈ l, P c) : ∀ c ∈ a :: l, P c := fun c hc => by
  rcases List.mem_cons.mp hc with h | h
  · exact h ▸ ha
  · exact hl c h
local macro "ms_sz" : tactic => `(tactic| simp +arith [DY.ALaCarte.FunctorSizeOf.sizeOf])
local macro "ms_kids " ih:ident : tactic =>
  `(tactic| (repeat' first
    | exact ms_all_nil
    | refine ms_all_cons ($ih _ (by ms_sz)) ?_))
section Rows
variable (i : ExternInterpretation) (S : Sem) (g : Ghost) {P : G → Prop} (H : MemoRowClosed i S g P)
include H
theorem ms_random_pp1 : DY.Bytes.PartialProof1 (gRandom g) (gamma' i S g) P := by
  intro x _
  by_cases h0 : x.size = 0
  · dsimp only [gRandom, concretizeRandom]; simp only [h0, ↓reduceIte]; exact H.hempty
  · have hp := ms_pack_random i S g x; dsimp only [gRandom, concretizeRandom] at hp ⊢; simp only [h0, ↓reduceIte] at hp ⊢; exact H.hnode hp (fun _ hc => by cases hc)
theorem ms_lit_pp1 : DY.Bytes.PartialProof1 gLit0 (gamma' i S g) P := by intro x _; exact H.hnode (ms_pack_lit i S g x) (fun _ hc => by cases hc)
theorem ms_concat_pp1 : DY.Bytes.PartialProof1 gConcat0 (gamma' i S g) P := by intro ⟨l, r⟩ ih; exact H.hnode (ms_pack_concat i S g ⟨l, r⟩) (by ms_kids ih)
theorem ms_dhPk_pp1 : DY.Bytes.PartialProof1 (gDhPk i) (gamma' i S g) P := by intro ⟨sk⟩ ih; exact H.hnode (ms_pack_dhPk i S g ⟨sk⟩) (by ms_kids ih)
theorem ms_dh_pp1 : DY.Bytes.PartialProof1 (gDh i) (gamma' i S g) P := by intro ⟨pk, sk⟩ ih; exact H.hnode (ms_pack_dh i S g ⟨pk, sk⟩) (by ms_kids ih)
theorem ms_kdf_pp1 : DY.Bytes.PartialProof1 (gKdf0 i) (gamma' i S g) P := by intro ⟨s, k⟩ ih; exact H.hnode (ms_pack_kdf i S g ⟨s, k⟩) (by ms_kids ih)
theorem ms_sym_pp1 : DY.Bytes.PartialProof1 (gSym0 i) (gamma' i S g) P := by intro ⟨k, iv, m⟩ ih; exact H.hnode (ms_pack_sym i S g ⟨k, iv, m⟩) (by ms_kids ih)
theorem ms_trunc_pp1 : DY.Bytes.PartialProof1 gTrunc0 (gamma' i S g) P := by intro ⟨x⟩ ih; exact H.hnode (ms_pack_trunc i S g ⟨x⟩) (by ms_kids ih)
theorem ms_variant_pp1 : DY.Bytes.PartialProof1 (gVariant0 i) (gamma' i S g) P := by intro ⟨k, w, t⟩ ih; exact H.hnode (ms_pack_variant i S g ⟨k, w, t⟩) (by ms_kids ih)
theorem ms_trWire_pp1 : DY.Bytes.PartialProof1 (gTrWire0 g) (gamma' i S g) P := by intro ⟨v, rk, c, pc, ct, pq, ev⟩ ih; exact H.hnode (ms_pack_trWire i S g ⟨v, rk, c, pc, ct, pq, ev⟩) (by ms_kids ih)
theorem ms_kemPk_pp1 : DY.Bytes.PartialProof1 (gKemPk S) (gamma' i S g) P := by intro ⟨a⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_kemEncap_pp1 : DY.Bytes.PartialProof1 (gKemEncap i) (gamma' i S g) P := by
  intro ⟨a, b⟩ ih
  by_cases h32 : (gamma' i S g b).bytes.length = 32
  · have hp := ms_pack_kemEncap i S g ⟨a, b⟩; dsimp only [gKemEncap, concretizeKemEncap] at hp ⊢; simp only [h32, ↓reduceIte] at hp ⊢; exact H.hnode hp (by ms_kids ih)
  · dsimp only [gKemEncap, concretizeKemEncap]; simp only [h32, ↓reduceIte]; exact H.hopq (by ms_kids ih)
theorem ms_kemSS_pp1 : DY.Bytes.PartialProof1 (gKemSS i S) (gamma' i S g) P := by
  intro ⟨a, b⟩ ih
  by_cases h32 : (gamma' i S g b).bytes.length = 32
  · have hp := ms_pack_kemSS i S g ⟨a, b⟩; dsimp only [gKemSS, concretizeKemSS] at hp ⊢; simp only [h32, ↓reduceIte] at hp ⊢; exact H.hnode hp (by ms_kids ih)
  · dsimp only [gKemSS, concretizeKemSS]; simp only [h32, ↓reduceIte]; exact H.hopq (by ms_kids ih)
theorem ms_kemRej_pp1 : DY.Bytes.PartialProof1 (concretizeKemRej S) (gamma' i S g) P := by intro ⟨a, b⟩ ih; exact H.hnode (ms_pack_kemRej i S g ⟨a, b⟩) (by ms_kids ih)
theorem ms_vk_pp1 : DY.Bytes.PartialProof1 (gVk S) (gamma' i S g) P := by intro ⟨a⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_sign_pp1 : DY.Bytes.PartialProof1 (gSign S) (gamma' i S g) P := by intro ⟨a, b, c⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_spqrInit_pp1 : DY.Bytes.PartialProof1 (gSpqrInit S) (gamma' i S g) P := by intro ⟨a, b⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_spqrSendState_pp1 : DY.Bytes.PartialProof1 (gSpqrSendState S) (gamma' i S g) P := by intro ⟨a, b⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_spqrSendKey_pp1 : DY.Bytes.PartialProof1 (gSpqrSendKey S) (gamma' i S g) P := by intro ⟨a, b⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_spqrSendMsg_pp1 : DY.Bytes.PartialProof1 (gSpqrSendMsg S) (gamma' i S g) P := by intro ⟨a, b⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_spqrRecvState_pp1 : DY.Bytes.PartialProof1 (gSpqrRecvState S) (gamma' i S g) P := by intro ⟨a, b⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_spqrRecvKey_pp1 : DY.Bytes.PartialProof1 (gSpqrRecvKey S) (gamma' i S g) P := by intro ⟨a, b⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_spqrChainKey_pp1 : DY.Bytes.PartialProof1 (gSpqrChainKey S) (gamma' i S g) P := by intro ⟨a, b, c⟩ ih; exact H.hopq (by ms_kids ih)
theorem ms_allFuns_pp1 (id : Fin 12) : DY.Bytes.PartialProof1 (allFuns i S g id) (gamma' i S g) P := by
  match id with
  | ⟨0, _⟩ => exact ms_random_pp1 i S g H
  | ⟨1, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro ⟨0, _⟩; exact ms_lit_pp1 i S g H
  | ⟨2, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro ⟨0, _⟩; exact ms_concat_pp1 i S g H
  | ⟨3, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact ms_dhPk_pp1 i S g H
    | ⟨1, _⟩ => exact ms_dh_pp1 i S g H
  | ⟨4, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro ⟨0, _⟩; exact ms_kdf_pp1 i S g H
  | ⟨5, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro ⟨0, _⟩; exact ms_sym_pp1 i S g H
  | ⟨6, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro ⟨0, _⟩; exact ms_trunc_pp1 i S g H
  | ⟨7, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro ⟨0, _⟩; exact ms_variant_pp1 i S g H
  | ⟨8, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact ms_kemPk_pp1 i S g H
    | ⟨1, _⟩ => exact ms_kemEncap_pp1 i S g H
    | ⟨2, _⟩ => exact ms_kemSS_pp1 i S g H
    | ⟨3, _⟩ => exact ms_kemRej_pp1 i S g H
  | ⟨9, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact ms_vk_pp1 i S g H
    | ⟨1, _⟩ => exact ms_sign_pp1 i S g H
  | ⟨10, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro id2
    match id2 with
    | ⟨0, _⟩ => exact ms_spqrInit_pp1 i S g H
    | ⟨1, _⟩ => exact ms_spqrSendState_pp1 i S g H
    | ⟨2, _⟩ => exact ms_spqrSendKey_pp1 i S g H
    | ⟨3, _⟩ => exact ms_spqrSendMsg_pp1 i S g H
    | ⟨4, _⟩ => exact ms_spqrRecvState_pp1 i S g H
    | ⟨5, _⟩ => exact ms_spqrRecvKey_pp1 i S g H
    | ⟨6, _⟩ => exact ms_spqrChainKey_pp1 i S g H
  | ⟨11, _⟩ =>
    dsimp only [allFuns]; apply DY.Bytes.PartialProof1.combine; intro ⟨0, _⟩; exact ms_trWire_pp1 i S g H
theorem gamma'_ind (t : DY.Bytes) : P (gamma' i S g t) := by have hpf : DY.Bytes.Proof1 (gAll i S g) P := DY.Bytes.PartialProof1.combine (ms_allFuns_pp1 i S g H); exact hpf.prove t
end Rows
section Memo
variable (i : ExternInterpretation) (S : Sem) (g : Ghost)
def EntrySound (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := x.2.1 = (gamma' i S g x.1).shape ∧ x.2.2 = gamma i S g x.1
theorem memoRowClosed_sound : MemoRowClosed i S g (fun res => ∀ x ∈ res.memo, EntrySound i S g x) := by
  refine ⟨fun {v self sh cs} hself hcs => ?_, fun {v cs} hcs => ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · unfold EntrySound gamma; rw [hself]; exact ⟨rfl, rfl⟩
    · obtain ⟨c, hc, hmc⟩ := List.mem_flatMap.mp hx; exact hcs c hc x hmc
  · intro x hx; obtain ⟨c, hc, hmc⟩ := List.mem_flatMap.mp hx; exact hcs c hc x hmc
  · intro x hx; cases hx
theorem memo_sound (t : DY.Bytes) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g t).memo) : x.2.1 = (gamma' i S g x.1).shape ∧ x.2.2 = gamma i S g x.1 := gamma'_ind i S g (memoRowClosed_sound i S g) t x hx
theorem memoRowClosed_trans : MemoRowClosed i S g (fun res => ∀ x ∈ res.memo, ∀ e ∈ (gamma' i S g x.1).memo, e ∈ res.memo) := by
  refine ⟨fun {v self sh cs} hself hcs => ?_, fun {v cs} hcs => ?_, ?_⟩
  · intro x hx e he
    rcases List.mem_cons.mp hx with rfl | hx
    · rw [hself] at he; exact he
    · obtain ⟨c, hc, hmc⟩ := List.mem_flatMap.mp hx; exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨c, hc, hcs c hc x hmc e he⟩)
  · intro x hx e he; obtain ⟨c, hc, hmc⟩ := List.mem_flatMap.mp hx; exact List.mem_flatMap.mpr ⟨c, hc, hcs c hc x hmc e he⟩
  · intro x hx; cases hx
theorem memo_trans (t : DY.Bytes) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g t).memo) : ∀ e ∈ (gamma' i S g x.1).memo, e ∈ (gamma' i S g t).memo := gamma'_ind i S g (memoRowClosed_trans i S g) t x hx
end Memo
end Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
