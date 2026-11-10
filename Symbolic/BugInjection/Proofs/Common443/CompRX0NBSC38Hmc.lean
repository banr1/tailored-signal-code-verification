/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh
public import Symbolic.BugInjection.Proofs.Common443.CompRNbsc38VTDefs
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompRNoBSC Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38 Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompSetupSecrecy Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
theorem mem_memo_lit_assumedInjective_false (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : ByteArray) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack)).memo) : assumedInjective x.1 = false := by unfold gamma' at hx; rw [DY.Bytes.rec_eq gLit0 (gAll i S g)] at hx; simp only [gLit0, concretizeLit, node, List.flatMap_nil, List.mem_singleton] at hx; subst hx; exact Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_lit_pack_eq b
theorem mem_memo_concat_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {a b : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Concat.concat a b)).memo) : x.1 = DY.Concat.concat a b ∨ x ∈ (gamma' i S g a).memo ∨ x ∈ (gamma' i S g b).memo := by
  unfold gamma' at hx; rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gConcat0 (gAll i S g)] at hx; simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxb; exacts [Or.inl rfl, Or.inr (Or.inl hxa), Or.inr (Or.inr hxb)]
theorem mem_memo_hmac_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {a b : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac a b)).memo) : x.1 = DY.Libsignal.TripleRatchet.hmac a b ∨ x ∈ (gamma' i S g a).memo ∨ x ∈ (gamma' i S g b).memo := by
  unfold gamma' DY.Libsignal.TripleRatchet.hmac at hx; rw [show DY.KdfExtract.kdfExtract a b = ({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)] at hx; simp only [gKdf0, concretizeKdf, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxb; exacts [Or.inl rfl, Or.inr (Or.inl hxa), Or.inr (Or.inr hxb)]
theorem mem_memo_trunc8_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {a : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Trunc.trunc8 a)).memo) : x.1 = DY.Trunc.trunc8 a ∨ x ∈ (gamma' i S g a).memo := by
  unfold gamma' at hx; rw [show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gTrunc0 (gAll i S g)] at hx; simp only [gTrunc0, concretizeTrunc, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, Census443Memo.bytes_rec_gAll] at hx
  rcases hx with rfl | hxa; exacts [Or.inl rfl, Or.inr hxa]
theorem mem_memo_variant_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {k : DY.Bytes} {v : Fin 4} {t : Fin 8} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.X25519.x25519TorsionVariant k v t)).memo) : assumedInjective x.1 = false ∨ x ∈ (gamma' i S g (DY.X25519.x25519Key k)).memo := by
  unfold DY.X25519.x25519TorsionVariant at hx; split at hx; · exact Or.inr hx
  unfold gamma' at hx; rw [DY.Bytes.rec_eq (gVariant0 i) (gAll i S g)] at hx; simp only [gVariant0, concretizeVariant, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, Census443Memo.bytes_rec_gAll] at hx
  rcases hx with rfl | hxk
  · left
    let w : DY.X25519.Variant.SubF DY.Bytes := { key := DY.X25519.normalizeX25519Key k, variation := v, torsion := t }
    have hnone : ∀ (F : Type → Type) [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F]
        [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.SubBytesTag F],
        Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.SubBytesTag.tag DY.X25519.Variant.SubF ≠
          Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.SubBytesTag.tag F →
        w.pack.view? F = none :=
      fun _ _ _ _ hne => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.view_pack_none w hne
    unfold assumedInjective
    simp only [Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    exact ⟨⟨⟨⟨⟨⟨⟨by dsimp only [w] at hnone; rw [hnone DY.Random.Random (by decide)]; rfl,
      hnone _ (by decide)⟩, hnone _ (by decide)⟩,
      hnone _ (by decide)⟩, hnone _ (by decide)⟩, hnone _ (by decide)⟩, hnone _ (by decide)⟩,
      hnone _ (by decide)⟩
  · exact Or.inr hxk
theorem mem_memo_concat_left {i : ExternInterpretation} {S : Sem} {g : Ghost} {a b : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g a).memo) : x ∈ (gamma' i S g (DY.Concat.concat a b)).memo := by unfold gamma' at hx ⊢; rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gConcat0 (gAll i S g)]; simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inr (Or.inl hx)
theorem mem_memo_concat_right {i : ExternInterpretation} {S : Sem} {g : Ghost} {a b : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g b).memo) : x ∈ (gamma' i S g (DY.Concat.concat a b)).memo := by unfold gamma' at hx ⊢; rw [show DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gConcat0 (gAll i S g)]; simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inr (Or.inr hx)
theorem mem_memo_concatPrefixes_mem {i : ExternInterpretation} {S : Sem} {g : Ghost} : ∀ {ps : List DY.Bytes} {s p : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes}, p ∈ ps → x ∈ (gamma' i S g p).memo → x ∈ (gamma' i S g (Comparse.concatPrefixes ps s)).memo
  | _ :: _, _, _, _, hp, hx => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    exact (List.mem_cons.mp hp).elim (fun h => h ▸ mem_memo_concat_left hx) (fun hp' => mem_memo_concat_right (mem_memo_concatPrefixes_mem hp' hx))
theorem mem_memo_concatPrefixes_tail {i : ExternInterpretation} {S : Sem} {g : Ghost} : ∀ (ps : List DY.Bytes) {s : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes}, x ∈ (gamma' i S g s).memo → x ∈ (gamma' i S g (Comparse.concatPrefixes ps s)).memo
  | [], _, _, hx => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact hx
  | _ :: ps, _, _, hx => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    exact mem_memo_concat_right (mem_memo_concatPrefixes_tail ps hx)
theorem mem_memo_hmac_left {i : ExternInterpretation} {S : Sem} {g : Ghost} {a b : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g a).memo) : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac a b)).memo := by unfold DY.Libsignal.TripleRatchet.hmac; unfold gamma' at hx ⊢; rw [show DY.KdfExtract.kdfExtract a b = ({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)]; simp only [gKdf0, concretizeKdf, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inr (Or.inl hx)
theorem mem_memo_hmac_right {i : ExternInterpretation} {S : Sem} {g : Ghost} {a b : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g b).memo) : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac a b)).memo := by unfold DY.Libsignal.TripleRatchet.hmac; unfold gamma' at hx ⊢; rw [show DY.KdfExtract.kdfExtract a b = ({ salt := a, ikm := b } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)]; simp only [gKdf0, concretizeKdf, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inr (Or.inr hx)
theorem mem_memo_trunc8 {i : ExternInterpretation} {S : Sem} {g : Ghost} {a : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g a).memo) : x ∈ (gamma' i S g (DY.Trunc.trunc8 a)).memo := by unfold gamma' at hx ⊢; rw [show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq gTrunc0 (gAll i S g)]; simp only [gTrunc0, concretizeTrunc, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, Census443Memo.bytes_rec_gAll]; exact Or.inr hx
theorem mem_memo_symEnc_key {i : ExternInterpretation} {S : Sem} {g : Ghost} {k iv m : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g k).memo) : x ∈ (gamma' i S g (DY.SymEnc.symEnc k iv m)).memo := by unfold gamma' at hx ⊢; rw [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gSym0 i) (gAll i S g)]; simp only [gSym0, concretizeSym, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inr (Or.inl hx)
theorem mem_memo_symEnc_iv {i : ExternInterpretation} {S : Sem} {g : Ghost} {k iv m : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g iv).memo) : x ∈ (gamma' i S g (DY.SymEnc.symEnc k iv m)).memo := by unfold gamma' at hx ⊢; rw [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gSym0 i) (gAll i S g)]; simp only [gSym0, concretizeSym, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inr (Or.inr (Or.inl hx))
theorem mem_memo_symEnc_msg {i : ExternInterpretation} {S : Sem} {g : Ghost} {k iv m : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g m).memo) : x ∈ (gamma' i S g (DY.SymEnc.symEnc k iv m)).memo := by unfold gamma' at hx ⊢; rw [show DY.SymEnc.symEnc k iv m = ({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gSym0 i) (gAll i S g)]; simp only [gSym0, concretizeSym, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inr (Or.inr (Or.inr hx))
theorem mem_memo_trWire_ct {i : ExternInterpretation} {S : Sem} {g : Ghost} {v : UInt8} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes} {ev : DY.TrWire.EncodingVariation} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g ct).memo) : x ∈ (gamma' i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev)).memo := by unfold gamma' at hx ⊢; dsimp only [DY.TrWire.trWireMsg, DY.TrWire.CanTrWireMsg.trWireMsg, DY.TrWire.instCanTrWireMsgBytes]; rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)]; simp only [gTrWire0, concretizeTrWire, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inr (Or.inr (Or.inl hx))
theorem mem_memo_trWire_pq {i : ExternInterpretation} {S : Sem} {g : Ghost} {v : UInt8} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes} {ev : DY.TrWire.EncodingVariation} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g pq).memo) : x ∈ (gamma' i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev)).memo := by unfold gamma' at hx ⊢; dsimp only [DY.TrWire.trWireMsg, DY.TrWire.CanTrWireMsg.trWireMsg, DY.TrWire.instCanTrWireMsgBytes]; rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)]; simp only [gTrWire0, concretizeTrWire, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inr (Or.inr (Or.inr hx))
theorem mem_memo_spqrSendMsg_left {i : ExternInterpretation} {S : Sem} {g : Ghost} {st coins : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g st).memo) : x ∈ (gamma' i S g (DY.Spqr.spqrSend st coins).2.2).memo := by unfold DY.Spqr.spqrSend; dsimp only; unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gSpqrSendMsg S) (gAll i S g)]; simp only [gSpqrSendMsg, concretizeSpqrSendMsg, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inl hx
theorem mem_memo_spqrInit_left {i : ExternInterpretation} {S : Sem} {g : Ghost} {a p : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g a).memo) : x ∈ (gamma' i S g (DY.Spqr.spqrInit a p)).memo := by unfold DY.Spqr.spqrInit; unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)]; simp only [gSpqrInit, concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, Census443Memo.bytes_rec_gAll]; exact Or.inl hx
theorem mem_memo_encWire_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encWire tr₂ stA cl pq)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_concat_left hx
theorem mem_memo_encMac_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encMac tr₂ stA cl pq)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_concat_right hx
theorem mem_memo_encCiphertext_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encCiphertext tr₂ stA cl pq)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_encWire_of_encOut (mem_memo_trWire_ct hx)
theorem mem_memo_encPqMsg_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encPqMsg tr₂ stA cl)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_encWire_of_encOut (mem_memo_trWire_pq hx)
theorem mem_memo_akeys_cipherKey_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encMsgKeys tr₂ stA cl pq).cipherKey).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_encCiphertext_of_encOut (mem_memo_symEnc_key hx)
theorem mem_memo_akeys_iv_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encMsgKeys tr₂ stA cl pq).iv).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_encCiphertext_of_encOut (mem_memo_symEnc_iv hx)
theorem mem_memo_pt_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (randTerm tr₂.length 32)).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_encCiphertext_of_encOut (mem_memo_symEnc_msg hx)
theorem mem_memo_akeys_macKey_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (encMsgKeys tr₂ stA cl pq).macKey).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_encMac_of_encOut (mem_memo_trunc8 (mem_memo_hmac_left hx))
theorem mem_memo_macInput_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr₂ stA cl pq)))).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_encMac_of_encOut (mem_memo_trunc8 (mem_memo_hmac_right hx))
theorem mem_memo_seed_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_akeys_cipherKey_of_encOut (mem_memo_hmac_left (mem_memo_hmac_right hx))
theorem mem_memo_cks_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g stA.cks).memo) : x ∈ (gamma' i S g (encOut tr₂ stA cl pq)).memo := mem_memo_seed_of_encOut (mem_memo_hmac_left hx)
theorem mem_memo_rk_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₁ tr₂ : ExecTrace} {b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g o.keys.rk).memo) : x ∈ (gamma' i S g (encOut tr₂ (iniAliceStartState tr₁ b o) cl pq)).memo := mem_memo_cks_of_encOut (mem_memo_hmac_left (mem_memo_hmac_left hx))
theorem mem_memo_pqr_of_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} {tr₁ tr₂ : ExecTrace} {b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl pq : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g o.keys.pqr).memo) : x ∈ (gamma' i S g (encOut tr₂ (iniAliceStartState tr₁ b o) cl pq)).memo := mem_memo_encPqMsg_of_encOut (mem_memo_spqrSendMsg_left (mem_memo_spqrInit_left hx))
theorem self_mem_slowBytes_serialize (b : DY.Bytes) : b ∈ Comparse.NonExtensibleMessageFormat.slowBytes.serialize b := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq]
  exact List.mem_append_right _ (List.mem_singleton_self _)
theorem cks_mem_trStatePrefixes (ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : ls.state.cks ∈ trStatePrefixes ls := by unfold trStatePrefixes; simp only [List.mem_append]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (self_mem_slowBytes_serialize ls.state.cks)))))))
theorem mem_memo_cks_of_serialize_local_tr {i : ExternInterpretation} {S : Sem} {g : Ghost} (ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g ls.state.cks).memo) : x ∈ (gamma' i S g (Comparse.serialize ls : DY.Bytes)).memo := by
  have hser : (Comparse.serialize ls : DY.Bytes) =
      Comparse.concatPrefixes (trStatePrefixes ls) ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize ls.state.recv) :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_tr_eq_bridge ls
  rw [hser]; exact mem_memo_concatPrefixes_mem (cks_mem_trStatePrefixes ls) hx
theorem chainKey_mem_serialize_recvChain (d : DY.Libsignal.TripleRatchet.RecvChain) : d.chainKey ∈ (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq]
  exact List.mem_append_right _ (List.mem_append_left _ (self_mem_slowBytes_serialize d.chainKey))
theorem mem_memo_chainKey_of_serialize_recvList {i : ExternInterpretation} {S : Sem} {g : Ghost} (d : DY.Libsignal.TripleRatchet.RecvChain) (cs : List DY.Libsignal.TripleRatchet.RecvChain) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g d.chainKey).memo) : x ∈ (gamma' i S g ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize (d :: cs))).memo := by
  rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons]
  exact mem_memo_concatPrefixes_mem (chainKey_mem_serialize_recvChain d) hx
theorem mem_memo_ck_of_serialize_encSt {i : ExternInterpretation} {S : Sem} {g : Ghost} (me b : Participant) (tr₁ tr₂ : ExecTrace) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (cl : Nat) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g o.keys.ck).memo) : x ∈ (gamma' i S g (Comparse.serialize (⟨me, encSt tr₂ (iniAliceStartState tr₁ b o) cl⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes)).memo := by
  let ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState := ⟨me, encSt tr₂ (iniAliceStartState tr₁ b o) cl⟩;
  have hser : (Comparse.serialize ls : DY.Bytes) =
      Comparse.concatPrefixes (trStatePrefixes ls) ((Comparse.ExtensibleMessageFormat.list (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize ls.state.recv) :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_tr_eq_bridge ls
  rw [hser]; exact mem_memo_concatPrefixes_tail (trStatePrefixes ls) (mem_memo_chainKey_of_serialize_recvList _ [] hx)
theorem mem_memo_concat_lit_lit_assumedInjective_false (i : ExternInterpretation) (S : Sem) (g : Ghost) (b₁ b₂ : ByteArray) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Concat.concat (({ lit := b₁ } : DY.Literal.Literal.SubF DY.Bytes).pack) (({ lit := b₂ } : DY.Literal.Literal.SubF DY.Bytes).pack))).memo) : assumedInjective x.1 = false := by
  rcases mem_memo_concat_cases hx with hx1 | hx_l | hx_r
  · rw [hx1]; exact Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _
  · exact mem_memo_lit_assumedInjective_false i S g b₁ hx_l
  · exact mem_memo_lit_assumedInjective_false i S g b₂ hx_r
theorem mem_memo_hmac_zeroKey_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {seed : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac DY.Spqr.zeroKey seed)).memo) : x.1 = DY.Libsignal.TripleRatchet.hmac DY.Spqr.zeroKey seed ∨ assumedInjective x.1 = false ∨ x ∈ (gamma' i S g seed).memo := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_zero | hx_seed
  exacts [Or.inl hx1, Or.inr (Or.inl (mem_memo_lit_assumedInjective_false i S g _ hx_zero)), Or.inr (Or.inr hx_seed)]
theorem mem_memo_trMsgKeys_cipherKey_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt seed : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey).memo) : x.1 = (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac salt seed)).memo ∨ assumedInjective x.1 = false := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_prk | hx_info
  exacts [Or.inl hx1, Or.inr (Or.inl hx_prk), Or.inr (Or.inr (mem_memo_concat_lit_lit_assumedInjective_false i S g _ _ hx_info))]
theorem mem_memo_trMsgKeys_macKey_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt seed : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).memo) : x.1 = (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac salt seed)).memo ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).cipherKey).memo ∨ assumedInjective x.1 = false := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_prk | hx_rhs
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_prk)
  · rcases mem_memo_concat_cases hx_rhs with hx1 | hx_ck | hx_info
    · rw [hx1]; exact Or.inr (Or.inr (Or.inr (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _)))
    · exact Or.inr (Or.inr (Or.inl hx_ck))
    · exact Or.inr (Or.inr (Or.inr (mem_memo_concat_lit_lit_assumedInjective_false i S g _ _ hx_info)))
theorem mem_memo_trMsgKeys_iv_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {salt seed : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).iv).memo) : x.1 = (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).iv ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.hmac salt seed)).memo ∨ x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys salt seed).macKey).memo ∨ assumedInjective x.1 = false := by
  rcases mem_memo_hmac_cases hx with hx1 | hx_prk | hx_rhs
  · exact Or.inl hx1
  · exact Or.inr (Or.inl hx_prk)
  · rcases mem_memo_concat_cases hx_rhs with hx1 | hx_mk | hx_info
    · rw [hx1]; exact Or.inr (Or.inr (Or.inr (Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_concat_eq _ _)))
    · exact Or.inr (Or.inr (Or.inl hx_mk))
    · exact Or.inr (Or.inr (Or.inr (mem_memo_concat_lit_lit_assumedInjective_false i S g _ _ hx_info)))
theorem mem_memo_computeMac_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {mk myIk peerIk wire : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.computeMac mk myIk peerIk wire)).memo) : x.1 = DY.Libsignal.TripleRatchet.computeMac mk myIk peerIk wire ∨ x.1 = DY.Libsignal.TripleRatchet.hmac mk (DY.Concat.concat myIk (DY.Concat.concat peerIk wire)) ∨ x ∈ (gamma' i S g mk).memo ∨ x ∈ (gamma' i S g (DY.Concat.concat myIk (DY.Concat.concat peerIk wire))).memo := by
  rcases mem_memo_trunc8_cases hx with hx1 | hx_full
  · exact Or.inl hx1
  · rcases mem_memo_hmac_cases hx_full with hx1 | hx_mk | hx_in
    exacts [Or.inr (Or.inl hx1), Or.inr (Or.inr (Or.inl hx_mk)), Or.inr (Or.inr (Or.inr hx_in))]
theorem mem_prefixTerms_of_send_vis {r : Records} {tr : ExecTrace} {vis : List VisEntry} {v : VisEntry} {u : DY.Bytes} (hv : v ∈ vis) (hkind : v.kind = .send) (hu : u ∈ v.terms) : u ∈ prefixTerms r tr vis := List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨v, List.mem_filter.mpr ⟨hv, beq_iff_eq.mpr hkind⟩, hu⟩)))
theorem mem_prefixTerms_of_storedStates {r : Records} {tr : ExecTrace} {vis : List VisEntry} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hls : ls ∈ storedStates r tr) : (Comparse.serialize ls : DY.Bytes) ∈ prefixTerms r tr vis := List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨ls, hls, rfl⟩)))
theorem length_le_of_trace_le {tr₁ tr₂ : ExecTrace} (h : tr₁ ≤ tr₂) : tr₁.length ≤ tr₂.length :=
  Trace.length_le _ _ h
theorem lt_length_of_at?_some {E : Type} [ExecTraceTypes.Has E] {tr : ExecTrace} {j : Nat} {x : E} (h : (tr.at? j : Option E) = some x) : j < tr.length :=
  XplSteps.xlt_of_at?_some h
private theorem mem_memo_zkeys_macKey_zeroKey {i : ExternInterpretation} {S : Sem} {g : Ghost} {seed macIn : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (gamma' i S g (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed).macKey).memo) : let zprk := DY.Libsignal.TripleRatchet.hmac DY.Spqr.zeroKey seed;
    let zkeys := DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed; let zmac_full := DY.Libsignal.TripleRatchet.hmac zkeys.macKey macIn; let zmac := DY.Trunc.trunc8 zmac_full;
    x ∈ (gamma' i S g seed).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ [zprk, zkeys.cipherKey, zkeys.macKey, zkeys.iv, zmac_full, zmac] := by
  intro zprk zkeys zmac_full zmac
  rcases mem_memo_trMsgKeys_macKey_cases hx with hx1 | hx_prk | hx_ck | hinj
  · exact Or.inr (Or.inr (by rw [hx1]; simp [zkeys]))
  · rcases mem_memo_hmac_zeroKey_cases hx_prk with hx1 | hinj | hx_seed
    exacts [Or.inr (Or.inr (by rw [hx1]; simp [zprk])), Or.inr (Or.inl hinj), Or.inl hx_seed]
  · rcases mem_memo_trMsgKeys_cipherKey_cases hx_ck with hx1 | hx_prk | hinj
    · exact Or.inr (Or.inr (by rw [hx1]; simp [zkeys]))
    · rcases mem_memo_hmac_zeroKey_cases hx_prk with hx1 | hinj | hx_seed
      exacts [Or.inr (Or.inr (by rw [hx1]; simp [zprk])), Or.inr (Or.inl hinj), Or.inl hx_seed]
    · exact Or.inr (Or.inl hinj)
  · exact Or.inr (Or.inl hinj)
private theorem mem_memo_bobTerm_cases {i : ExternInterpretation} {S : Sem} {g : Ghost} {me b : Participant} {tr₁ tr₂ : ExecTrace} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {cl : Nat} {u : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hu : u ∈ [o.keys.rk, o.keys.ck, o.keys.pqr, (iniAliceStartState tr₁ b o).cks, (encSt tr₂ (iniAliceStartState tr₁ b o) cl).cks, (encMsgKeys tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)).cipherKey, (encMsgKeys tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)).macKey, (encMsgKeys tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2)).iv, encMac tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2), randTerm tr₂.length 32, (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ b o).cks).2).cipherKey, (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ b o).cks).2).macKey, (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ b o).cks).2).iv, DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey (DY.Libsignal.TripleRatchet.kdfCk (iniAliceStartState tr₁ b o).cks).2).macKey (iniAliceStartState tr₁ b o).myIk (iniAliceStartState tr₁ b o).peerIk (encWire tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))]) (hx : x ∈ (gamma' i S g u).memo) : x ∈ (gamma' i S g (encOut tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2))).memo ∨ x ∈ (gamma' i S g (Comparse.serialize (⟨me, encSt tr₂ (iniAliceStartState tr₁ b o) cl⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes)).memo ∨ assumedInjective x.1 = false ∨ x.1 ∈ zeroSaltedTermsStA tr₂ (iniAliceStartState tr₁ b o) cl (tr₂.length + 2) := by
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inl (mem_memo_rk_of_encOut hx)
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inr (Or.inl (mem_memo_ck_of_serialize_encSt me b tr₁ tr₂ o cl hx))
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inl (mem_memo_pqr_of_encOut hx)
  generalize iniAliceStartState tr₁ b o = stA, tr₂.length + 2 = pq at hu ⊢; let macIn := DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr₂ stA cl pq));
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inl (mem_memo_cks_of_encOut hx)
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inr (Or.inl (mem_memo_cks_of_serialize_local_tr ⟨me, encSt tr₂ stA cl⟩ hx))
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inl (mem_memo_akeys_cipherKey_of_encOut hx)
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inl (mem_memo_akeys_macKey_of_encOut hx)
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inl (mem_memo_akeys_iv_of_encOut hx)
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inl (mem_memo_encMac_of_encOut hx)
  rcases List.mem_cons.mp hu with rfl | hu; · exact Or.inl (mem_memo_pt_of_encOut hx)
  rcases List.mem_cons.mp hu with rfl | hu
  · rcases mem_memo_trMsgKeys_cipherKey_cases hx with hx1 | hx_prk | hinj
    · exact Or.inr (Or.inr (Or.inr (by rw [hx1]; simp [zeroSaltedTermsStA])))
    · rcases mem_memo_hmac_zeroKey_cases hx_prk with hx1 | hinj | hx_seed
      exacts [Or.inr (Or.inr (Or.inr (by rw [hx1]; simp [zeroSaltedTermsStA]))), Or.inr (Or.inr (Or.inl hinj)), Or.inl (mem_memo_seed_of_encOut hx_seed)]
    · exact Or.inr (Or.inr (Or.inl hinj))
  rcases List.mem_cons.mp hu with rfl | hu
  · rcases mem_memo_zkeys_macKey_zeroKey (macIn := macIn) hx with hx_seed | hinj | hz
    exacts [Or.inl (mem_memo_seed_of_encOut hx_seed), Or.inr (Or.inr (Or.inl hinj)), Or.inr (Or.inr (Or.inr hz))]
  rcases List.mem_cons.mp hu with rfl | hu
  · rcases mem_memo_trMsgKeys_iv_cases hx with hx1 | hx_prk | hx_mk | hinj
    · exact Or.inr (Or.inr (Or.inr (by rw [hx1]; simp [zeroSaltedTermsStA])))
    · rcases mem_memo_hmac_zeroKey_cases hx_prk with hx1 | hinj | hx_seed
      exacts [Or.inr (Or.inr (Or.inr (by rw [hx1]; simp [zeroSaltedTermsStA]))), Or.inr (Or.inr (Or.inl hinj)), Or.inl (mem_memo_seed_of_encOut hx_seed)]
    · rcases mem_memo_zkeys_macKey_zeroKey (macIn := macIn) hx_mk with hx_seed | hinj | hz
      exacts [Or.inl (mem_memo_seed_of_encOut hx_seed), Or.inr (Or.inr (Or.inl hinj)), Or.inr (Or.inr (Or.inr hz))]
    · exact Or.inr (Or.inr (Or.inl hinj))
  rcases List.mem_singleton.mp hu with rfl
  rcases mem_memo_computeMac_cases hx with hx1 | hx1_full | hx_mk | hx_in
  · exact Or.inr (Or.inr (Or.inr (by rw [hx1]; simp [zeroSaltedTermsStA, DY.Libsignal.TripleRatchet.computeMac])))
  · exact Or.inr (Or.inr (Or.inr (by rw [hx1_full]; simp [zeroSaltedTermsStA])))
  · rcases mem_memo_zkeys_macKey_zeroKey (macIn := macIn) hx_mk with hx_seed | hinj | hz
    exacts [Or.inl (mem_memo_seed_of_encOut hx_seed), Or.inr (Or.inr (Or.inl hinj)), Or.inr (Or.inr (Or.inr hz))]
  · exact Or.inl (mem_memo_macInput_of_encOut hx_in)
private theorem send_terms_mem_prefixTerms_split38 {r : Records} (hNe : r.alice ≠ r.bob) {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    o.ek ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧ o.ct ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') ∧
    encOut tr₂ stA cl pq ∈ prefixTerms r (runTraceMoves r ms') (runVis r ms') := by
  intro tr₁ o m₀ tr₂ pq stA ms'; let wrap := some (tr₁.length + 3, tr₁.length + 4); let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl pq wrap;
  have henc : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA cl pq := encrypt_next_split38_eq wrap hm₀ hmid rfl
  have hek_net : NetMsgAt o.ek (tr₁.length + 3) tr₂ := (hm₀ ▸ netMsgAt_ek_iniAliceStartTr tr₁ r.alice r.bob o).mono (CompPrefixInvEnc.runMoves_le mid (m₀.next tr₁)); have hct_net : NetMsgAt o.ct (tr₁.length + 4) tr₂ := (hm₀ ▸ netMsgAt_ct_iniAliceStartTr tr₁ r.alice r.bob o).mono (CompPrefixInvEnc.runMoves_le mid (m₀.next tr₁)); have hrec : received tr₂ [tr₁.length + 3, tr₁.length + 4] = [o.ek, o.ct] := (by unfold received; simp only [List.filterMap_cons, List.filterMap_nil, CompRX0NBSC38Parts.getMessageSentAt_of_netMsgAt hek_net, CompRX0NBSC38Parts.getMessageSentAt_of_netMsgAt hct_net]); let v_send : VisEntry := ⟨.send, [o.ek, o.ct, encOut tr₂ stA cl pq], .preKeySend, none⟩; have hv_send : v_send ∈ runVis r ms' := (by dsimp only [ms']; rw [runVis_split38_eq hNe hpre hmid hpost, encrypt_vis_eq, henc]; refine List.mem_append_right _ (List.mem_append_right _ ?_); unfold encSend; rw [lastSent_encNextTr]; dsimp only [wrap]; rw [hrec]; exact List.mem_singleton_self _)
  exact ⟨mem_prefixTerms_of_send_vis hv_send rfl (by simp [v_send]), mem_prefixTerms_of_send_vis hv_send rfl (by simp [v_send]),
         mem_prefixTerms_of_send_vis hv_send rfl (by simp [v_send])⟩
private theorem serialize_encSt_mem_prefixTerms_split38 {r : Records} {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} (_hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post;
    (Comparse.serialize (⟨r.alice, encSt tr₂ stA cl⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∈
      prefixTerms r (runTraceMoves r ms') (runVis r ms') := by
  intro tr₁ o m₀ tr₂ pq stA ms'; let wrap := some (tr₁.length + 3, tr₁.length + 4); let m₁ := Move.encrypt r.alice (tr₁.length + 8) cl pq wrap;
  have henc : m₁.next tr₂ = encNextTr tr₂ r.alice (tr₁.length + 8) stA cl pq := encrypt_next_split38_eq wrap hm₀ hmid rfl
  have htr : runTraceMoves r ms' = (runMoves post (m₁.next tr₂)).1 := by dsimp only [ms', m₁]; rw [xpl_runTrace_eq]; simp only [runMoves_append_fst, runMoves]; rfl
  have hat : ((runTraceMoves r ms').at? (tr₂.length + 5) : Option TRStEntry) = some (TRStE r.alice (encSt tr₂ stA cl)) := (by rw [htr, at?_trSt_of_movesFrom_invisibleNoEffect hpost (tr₂.length + 5), henc]; exact trStateStoredAt_encNextTr tr₂ r.alice (tr₁.length + 8) stA cl pq)
  have hlen_setup : (setupTrace r).length ≤ tr₂.length := length_le_of_trace_le (Trace.le_trans _ _ _ (CompPrefixInvEnc.runMoves_le pre (setupTrace r))
      (Trace.le_trans _ _ _ (m₀.le_next tr₁) (CompPrefixInvEnc.runMoves_le mid (m₀.next tr₁))))
  exact mem_prefixTerms_of_storedStates (mem_storedStates_iff.mpr ⟨tr₂.length + 5, by omega, lt_length_of_at?_some hat, hat⟩)
private theorem mem_newTerms_memo_of_parts {r : Records} {S : Sem} {g : Ghost} {v : Fin 4} {t : Fin 8} {p : PreKeyFields} {tr₁ tr₂ : ExecTrace} {cl : Nat} {salts preTerms : List DY.Bytes} {x₀ : PreKeyRep} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) (hx₀ : x₀ = ⟨DY.X25519.x25519TorsionVariant (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek v t, (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct, encOut tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl (tr₂.length + 2)⟩) (hek_pre : (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek ∈ preTerms) (hct_pre : (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct ∈ preTerms) (hout_pre : encOut tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl (tr₂.length + 2) ∈ preTerms) (hser_pre : (Comparse.serialize (⟨r.alice, encSt tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∈ preTerms) (hsalts : salts = [DY.Spqr.zeroKey, DY.Spqr.spqrChainKey (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).keys.pqr DY.Libsignal.TripleRatchet.spqrA2B (DY.Spqr.spqrIdx 1)]) {x : DY.Bytes × DY.Bytes × HwBytes} (hx : x ∈ (([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r salts p x₀).flatMap fun u => (gamma' compI0 S g u).memo)) : x ∈ preTerms.flatMap (fun u => (gamma' compI0 S g u).memo) ∨ assumedInjective x.1 = false ∨ x.1 ∈ zeroSaltedTermsStA tr₂ (iniAliceStartState tr₁ r.bob (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl (tr₂.length + 2) := by
  have hek_key : DY.X25519.x25519Key x₀.ek = (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek := (by rw [hx₀]; exact x25519Key_torsionVariant_aliceOut_ek tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none v t)
  have hct_eq : x₀.ct = (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ct := by rw [hx₀]
  have hmsg_eq : x₀.msg = encOut tr₂ (iniAliceStartState tr₁ r.bob
      (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) cl (tr₂.length + 2) := by rw [hx₀]
  obtain ⟨u, hu, hx_u⟩ := List.mem_flatMap.mp hx; simp only [List.cons_append, List.nil_append, List.mem_cons] at hu
  rcases hu with rfl | rfl | rfl | hu_bob
  · rw [hx₀] at hx_u; rcases mem_memo_variant_cases hx_u with hinj | hx_ek
    · exact Or.inr (Or.inl hinj)
    · unfold DY.X25519.x25519Key at hx_ek
      rw [show (iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none).ek =
          DY.DiffieHellman.dhPk (randTerm tr₁.length 32) from rfl,
        Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.x25519Key_dhPk_eq] at hx_ek
      exact Or.inl (List.mem_flatMap.mpr ⟨_, hek_pre, hx_ek⟩)
  · rw [hct_eq] at hx_u; exact Or.inl (List.mem_flatMap.mpr ⟨_, hct_pre, hx_u⟩)
  · rw [hmsg_eq] at hx_u; exact Or.inl (List.mem_flatMap.mpr ⟨_, hout_pre, hx_u⟩)
  · rw [hsalts] at hu_bob; have hu_cases := mem_bobTerms_x0_iff (tr₁ := tr₁) (tr₂ := tr₂) (cl := cl) hNe hopk hek_key hct_eq hmsg_eq u hu_bob
    rcases mem_memo_bobTerm_cases (me := r.alice) hu_cases hx_u with hx_out | hx_ser | hinj | hz
    exacts [Or.inl (List.mem_flatMap.mpr ⟨_, hout_pre, hx_out⟩), Or.inl (List.mem_flatMap.mpr ⟨_, hser_pre, hx_ser⟩), Or.inr (Or.inl hinj), Or.inr (Or.inr hz)]
theorem mem_newTerms_memo_split38 {r : Records} {S : Sem} {g : Ghost} {v : Fin 4} {t : Fin 8} {p : PreKeyFields} {pre mid post : List Move} {hb : DY.Libsignal.PQXDH.BundleHandles} {shown cl : Nat} (hNe : r.alice ≠ r.bob) (hopk : p.preKeyId = none) (hpre : MovesFrom InvisibleNoEffect (setupTrace r) pre) (hmid : MovesFrom InvisibleNoEffect ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1) mid) (hpost : MovesFrom InvisibleNoEffect ((Move.encrypt r.alice ((runMoves pre (setupTrace r)).1.length + 8) cl ((runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1.length + 2) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4))).next (runMoves mid ((Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1)).1) post) (hm₀ : (Move.aliceStart r.alice r.bob 4 6 hb shown).next (runMoves pre (setupTrace r)).1 = iniAliceStartTr (runMoves pre (setupTrace r)).1 r.alice r.bob (iniAliceOut (runMoves pre (setupTrace r)).1 (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none)) : let tr₁ := (runMoves pre (setupTrace r)).1;
    let o := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none; let m₀ := Move.aliceStart r.alice r.bob 4 6 hb shown; let tr₂ := (runMoves mid (m₀.next tr₁)).1; let pq := tr₂.length + 2; let stA := iniAliceStartState tr₁ r.bob o; let ms' := pre ++ m₀ :: mid ++ Move.encrypt r.alice (tr₁.length + 8) cl pq (some (tr₁.length + 3, tr₁.length + 4)) :: post; let x₀ : PreKeyRep := ⟨DY.X25519.x25519TorsionVariant o.ek v t, o.ct, encOut tr₂ stA cl pq⟩; let seed := (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2; let zprk := DY.Libsignal.TripleRatchet.hmac DY.Spqr.zeroKey seed; let zkeys := DY.Libsignal.TripleRatchet.trMsgKeys DY.Spqr.zeroKey seed; let zmac_full := DY.Libsignal.TripleRatchet.hmac zkeys.macKey (DY.Concat.concat stA.myIk (DY.Concat.concat stA.peerIk (encWire tr₂ stA cl pq))); let zmac := DY.Libsignal.TripleRatchet.computeMac zkeys.macKey stA.myIk stA.peerIk (encWire tr₂ stA cl pq);
    ∀ x ∈ (([x₀.ek, x₀.ct, x₀.msg] ++ bobTerms r (honestSalts r ms') p x₀).flatMap fun u => (gamma' compI0 S g u).memo),
      x ∈ (prefixTerms r (runTraceMoves r ms') (runVis r ms')).flatMap (fun u => (gamma' compI0 S g u).memo) ∨
      assumedInjective x.1 = false ∨ x.1 ∈ [zprk, zkeys.cipherKey, zkeys.macKey, zkeys.iv, zmac_full, zmac] := by
  obtain ⟨hek_pre, hct_pre, hout_pre⟩ := send_terms_mem_prefixTerms_split38 hNe hpre hmid hpost hm₀; have hser_pre := serialize_encSt_mem_prefixTerms_split38 hpre hmid hpost hm₀; have henc := encrypt_next_split38_eq (cl := cl) (some ((runMoves pre (setupTrace r)).1.length + 3, (runMoves pre (setupTrace r)).1.length + 4)) hm₀ hmid rfl; have hsalts := honestSalts_split_eq rfl rfl hpre hmid hpost henc; dsimp only; intro x hx; exact mem_newTerms_memo_of_parts hNe hopk rfl hek_pre hct_pre hout_pre hser_pre hsalts hx
end Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Hmc
