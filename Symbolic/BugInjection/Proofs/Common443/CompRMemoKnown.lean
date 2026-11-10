/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.Statement
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
public import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
public import Symbolic.BugInjection.Proofs.Common443.Census443Memo
public import Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
theorem bytes_rec_gAll {i : ExternInterpretation} {S : Sem} {g : Ghost} (x : DY.Bytes) : x.rec (gAll i S g) = gamma' i S g x := rfl
export Symbolic.BugInjection.Proofs.Common443.Census443Memo (MemoOK memoOK_lit memoOK_concat memoOK_dhPk memoOK_dhPk_elim memoOK_dh_pack memoOK_kdfExtract memoOK_symEnc memoOK_trunc8 memoOK_variant_elim memoOK_x25519Key memoOK_kemPk memoOK_spqrInit memoOK_spqrInit_elim memoOK_spqrChainKey memoOK_spqrSendState memoOK_spqrSendKey_pack memoOK_spqrSendMsg memoOK_spqrRecvState_pack memoOK_trWire)
def Good (i : ExternInterpretation) (S : Sem) (g : Ghost) (P : DY.Bytes × DY.Bytes × HwBytes → Prop) (tr : ExecTrace) (t : DY.Bytes) : Prop := t.AttackerKnows tr ∧ MemoOK i S g P t
section Memo
variable {i : ExternInterpretation} {S : Sem} {g : Ghost} {P : DY.Bytes × DY.Bytes × HwBytes → Prop}
theorem memoOK_concat_elim {a c : DY.Bytes} (h : MemoOK i S g P (DY.Concat.concat a c)) : MemoOK i S g P a ∧ MemoOK i S g P c := by
  constructor <;> intro x hx <;> apply h x <;> unfold gamma' at hx ⊢ <;>
    rw [show DY.Concat.concat a c = ({ lhs := a, rhs := c } : DY.Concat.Concat.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq gConcat0 (gAll i S g)] <;>
    simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
      List.mem_append, bytes_rec_gAll] <;> simp [gamma', hx]
theorem assumedInjective_lit (bs : ByteArray) : assumedInjective (DY.Literal.literalToBytes bs) = false :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.ai_lit_eq bs
theorem memoOK_lit_ni (bs : ByteArray) (hNI : ∀ x : DY.Bytes × DY.Bytes × HwBytes, assumedInjective x.1 = false → P x) : MemoOK i S g P (DY.Literal.literalToBytes bs) :=
  memoOK_lit (fun x hx => hNI x (hx ▸ assumedInjective_lit bs))
theorem memoOK_symEnc_elim {e : DY.SymEnc.Enc.SubF DY.Bytes} (h : MemoOK i S g P e.pack) : MemoOK i S g P e.msg := by intro x hx; apply h x; unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gSym0 i) (gAll i S g)]; simp only [gSym0, concretizeSym, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll]; exact Or.inr (Or.inr (Or.inr hx))
theorem memoOK_variant_pack {v : DY.X25519.Variant.SubF DY.Bytes} (hP : ∀ x : DY.Bytes × DY.Bytes × HwBytes, x.1 = v.pack → P x) (hk : MemoOK i S g P v.key) : MemoOK i S g P v.pack := by
  intro x hx; unfold gamma' at hx; rw [DY.Bytes.rec_eq (gVariant0 i) (gAll i S g)] at hx; simp only [gVariant0, concretizeVariant, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hxk; exacts [hP _ rfl, hk x hxk]
theorem memoOK_kemEncap_fst {pk e : DY.Bytes} (hP : ∀ x : DY.Bytes × DY.Bytes × HwBytes, x.1 = (DY.PQKem.kemEncap pk e).1 → P x) (hpk : MemoOK i S g P pk) (he : MemoOK i S g P e) : MemoOK i S g P (DY.PQKem.kemEncap pk e).1 := by
  intro x hx; unfold gamma' at hx; rw [show (DY.PQKem.kemEncap pk e).1 = ({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gKemEncap i) (gAll i S g)] at hx; dsimp only [gKemEncap, concretizeKemEncap] at hx; split_ifs at hx
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
    rcases hx with rfl | hxpk | hxe; exacts [hP _ rfl, hpk x hxpk, he x hxe]
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
    rcases hx with hxpk | hxe; exacts [hpk x hxpk, he x hxe]
theorem memoOK_kemEncap_fst_elim {c : DY.PQKem.Encap.SubF DY.Bytes} (h : MemoOK i S g P c.pack) : MemoOK i S g P c.pk ∧ MemoOK i S g P c.entropy := by
  constructor <;> intro x hx <;> apply h x <;> unfold gamma' at hx ⊢ <;>
    rw [DY.Bytes.rec_eq (gKemEncap i) (gAll i S g)] <;> dsimp only [gKemEncap, concretizeKemEncap] <;> split_ifs <;>
    simp only [node, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] <;>
    simp [gamma', hx]
theorem memoOK_kemEncap_snd {pk e : DY.Bytes} (hP : ∀ x : DY.Bytes × DY.Bytes × HwBytes, x.1 = (DY.PQKem.kemEncap pk e).2 → P x) (hpk : MemoOK i S g P pk) (he : MemoOK i S g P e) : MemoOK i S g P (DY.PQKem.kemEncap pk e).2 := by
  intro x hx; unfold gamma' at hx; rw [show (DY.PQKem.kemEncap pk e).2 = ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gKemSS i S) (gAll i S g)] at hx; dsimp only [gKemSS, concretizeKemSS] at hx; split_ifs at hx
  · simp only [node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
    rcases hx with rfl | hxpk | hxe; exacts [hP _ rfl, hpk x hxpk, he x hxe]
  · simp only [opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
    rcases hx with hxpk | hxe; exacts [hpk x hxpk, he x hxe]
theorem memoOK_kemRejKey {sk ct : DY.Bytes} (hP : ∀ x : DY.Bytes × DY.Bytes × HwBytes, x.1 = DY.PQKem.kemRejKey sk ct → P x) (hsk : MemoOK i S g P sk) (hct : MemoOK i S g P ct) : MemoOK i S g P (DY.PQKem.kemRejKey sk ct) := by
  intro x hx; unfold gamma' at hx; rw [show DY.PQKem.kemRejKey sk ct = ({ sk := sk, cipher := ct } : DY.PQKem.RejKey.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gKemRej S) (gAll i S g)] at hx; simp only [gKemRej, concretizeKemRej, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxsk | hxct; exacts [hP _ rfl, hsk x hxsk, hct x hxct]
theorem memoOK_vk {sk : DY.Bytes} (hsk : MemoOK i S g P sk) : MemoOK i S g P (DY.Signature.vk sk) := by intro x hx; unfold gamma' at hx; rw [show DY.Signature.vk sk = ({ sk := sk } : DY.Signature.Vk.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gVk S) (gAll i S g)] at hx; simp only [gVk, concretizeVk, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, bytes_rec_gAll] at hx; exact hsk x hx
theorem memoOK_sign {sk n m : DY.Bytes} (hsk : MemoOK i S g P sk) (hn : MemoOK i S g P n) (hm : MemoOK i S g P m) : MemoOK i S g P (DY.Signature.sign sk n m) := by
  intro x hx; unfold gamma' at hx; rw [show DY.Signature.sign sk n m = ({ sk := sk, nonce := n, msg := m } : DY.Signature.Sign.SubF DY.Bytes).pack from rfl, DY.Bytes.rec_eq (gSign S) (gAll i S g)] at hx; simp only [gSign, concretizeSign, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with hxsk | hxn | hxm; exacts [hsk x hxsk, hn x hxn, hm x hxm]
theorem memoOK_spqrSendState_elim {s : DY.Spqr.SendState.SubF DY.Bytes} (h : MemoOK i S g P s.pack) : MemoOK i S g P s.st ∧ MemoOK i S g P s.coins := by
  constructor <;> intro x hx <;> apply h x <;> unfold gamma' at hx ⊢ <;>
    rw [DY.Bytes.rec_eq (gSpqrSendState S) (gAll i S g)] <;>
    simp only [gSpqrSendState, concretizeSpqrSendState, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] <;>
    simp [gamma', hx]
theorem memoOK_spqrRecvState_elim {s : DY.Spqr.RecvState.SubF DY.Bytes} (h : MemoOK i S g P s.pack) : MemoOK i S g P s.st ∧ MemoOK i S g P s.msg := by
  constructor <;> intro x hx <;> apply h x <;> unfold gamma' at hx ⊢ <;>
    rw [DY.Bytes.rec_eq (gSpqrRecvState S) (gAll i S g)] <;>
    simp only [gSpqrRecvState, concretizeSpqrRecvState, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] <;>
    simp [gamma', hx]
theorem memoOK_spqrRecvKey_pack {st m : DY.Bytes} (hst : MemoOK i S g P st) (hm : MemoOK i S g P m) : MemoOK i S g P (({ st := st, msg := m } : DY.Spqr.RecvKey.SubF DY.Bytes).pack) := by
  intro x hx; unfold gamma' at hx; rw [DY.Bytes.rec_eq (gSpqrRecvKey S) (gAll i S g)] at hx; simp only [gSpqrRecvKey, concretizeSpqrRecvKey, spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with hxst | hxm; exacts [hst x hxst, hm x hxm]
theorem memoOK_trWire_elim {w : DY.TrWire.TrWireMsg.SubF DY.Bytes} (h : MemoOK i S g P w.pack) : MemoOK i S g P w.senderRatchetKey ∧ MemoOK i S g P w.ciphertext ∧ MemoOK i S g P w.pqRatchet := by
  refine ⟨?_, ?_, ?_⟩ <;> intro x hx <;> apply h x <;> unfold gamma' at hx ⊢ <;>
    rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)] <;>
    simp only [gTrWire0, concretizeTrWire, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] <;>
    simp [gamma', hx]
end Memo
theorem memoOK_of_attackerKnows {i : ExternInterpretation} {S : Sem} {g : Ghost} {P : DY.Bytes × DY.Bytes × HwBytes → Prop} {tr : ExecTrace} (hPak : ∀ x : DY.Bytes × DY.Bytes × HwBytes, x.1.AttackerKnows tr → P x) (hNI : ∀ x : DY.Bytes × DY.Bytes × HwBytes, assumedInjective x.1 = false → P x) (hbase : ∀ t : DY.Bytes, tr.BaseAttackerKnows t → MemoOK i S g P t) {t : DY.Bytes} (ht : t.AttackerKnows tr) : MemoOK i S g P t := by
  exact Symbolic.Proofs.Tests.CliNonvacuity.PtNoCollisionAuxBase.composed_attackerKnows_ind
    (Q := MemoOK i S g P)
    (fun bs hak => memoOK_lit (fun x hx => hPak x (hx ▸ hak)))
    (fun a c hak ha hc => memoOK_concat (fun x hx => hPak x (hx ▸ hak)) ha hc)
    (fun _ _ => memoOK_concat_elim)
    (fun sk hak hsk => memoOK_dhPk (fun x hx => hPak x (hx ▸ hak)) hsk)
    (fun pk sk hak hpk hsk => memoOK_dh_pack (fun x hx => hPak x (hx ▸ hak)) hpk hsk)
    (fun _ => memoOK_dhPk_elim)
    (fun salt ikm hak hs hm => memoOK_kdfExtract (fun x hx => hPak x (hx ▸ hak)) hs hm)
    (fun k iv msg hak hk hiv hmsg => memoOK_symEnc (fun x hx => hPak x (hx ▸ hak)) hk hiv hmsg)
    (fun _ => memoOK_symEnc_elim)
    (fun m hak hm => memoOK_trunc8 (fun x hx => hPak x (hx ▸ hak)) hm)
    (fun _ => memoOK_x25519Key)
    (fun v hak hk => memoOK_variant_pack (fun x hx => hPak x (hx ▸ hak)) hk)
    (fun _ => memoOK_variant_elim)
    (fun _ => memoOK_kemPk)
    (fun pk e hak hpk he => memoOK_kemEncap_fst (fun x hx => hPak x (hx ▸ hak)) hpk he)
    (fun _ => memoOK_kemEncap_fst_elim)
    (fun pk e hak hpk he => memoOK_kemEncap_snd (fun x hx => hPak x (hx ▸ hak)) hpk he)
    (fun sk ct hak hsk hct => memoOK_kemRejKey (fun x hx => hPak x (hx ▸ hak)) hsk hct)
    (fun _ => memoOK_vk)
    (fun _ _ _ => memoOK_sign)
    (fun _ _ => memoOK_spqrInit)
    (fun _ => memoOK_spqrInit_elim)
    (fun _ _ _ => memoOK_spqrChainKey)
    (fun _ _ => memoOK_spqrSendState)
    (fun _ => memoOK_spqrSendState_elim)
    (fun _ _ => memoOK_spqrSendKey_pack)
    (fun _ _ => memoOK_spqrSendMsg)
    (fun _ _ => memoOK_spqrRecvState_pack)
    (fun _ => memoOK_spqrRecvState_elim)
    (fun _ _ => memoOK_spqrRecvKey_pack)
    (fun bs => memoOK_lit_ni bs hNI)
    (fun v rk c pc ct pq ev hak hrk hct hpq => memoOK_trWire (fun x hx => hPak x (hx ▸ hak)) hrk hct hpq)
    (fun _ => memoOK_trWire_elim)
    hbase ht
end Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown
