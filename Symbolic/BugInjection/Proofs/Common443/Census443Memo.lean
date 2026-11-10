/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common.DefsCompI0
public import Symbolic.BugInjection.Proofs.Common443.CompRGamma
public import Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
public import Symbolic.BugInjection.Proofs.Common443.CompRTag
public import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.Census443Memo
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY.X25519 (isLowOrderKey)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Proofs.Common443.CompRGamma Symbolic.BugInjection.Proofs.Common443.CompRPreMemoSound
open DY.Literal (literalToBytes) open DY.Concat (concat) open DY.KdfExtract (kdfExtract)
open DY.DiffieHellman DY.SymEnc DY.Trunc DY.X25519 DY.PQKem DY.Spqr DY.TrWire Comparse.NonExtensibleMessageFormat
theorem bytes_rec_gAll {i : ExternInterpretation} {S : Sem} {g : Ghost} (t : Bytes) : Bytes.rec (gAll i S g) t = gamma' i S g t := rfl
def MemoOK (i : ExternInterpretation) (S : Sem) (g : Ghost) (P : Bytes × Bytes × HwBytes → Prop) (t : Bytes) : Prop := ∀ x ∈ (gamma' i S g t).memo, P x
section Memo
variable {i : ExternInterpretation} {S : Sem} {g : Ghost} {P : Bytes × Bytes × HwBytes → Prop}
theorem memoOK_lit {bs : ByteArray} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = literalToBytes bs → P x) : MemoOK i S g P (literalToBytes bs) := by
  intro x hx; unfold gamma' at hx; rw [show literalToBytes bs = ({ lit := bs } : Literal.Literal.SubF Bytes).pack from rfl, Bytes.rec_eq gLit0 (gAll i S g)] at hx
  rcases List.mem_singleton.mp hx with rfl; exact hP _ rfl
theorem memoOK_concat {a c : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = concat a c → P x) (ha : MemoOK i S g P a) (hc : MemoOK i S g P c) : MemoOK i S g P (concat a c) := by
  intro x hx; unfold gamma' at hx; rw [show concat a c = ({ lhs := a, rhs := c } : Concat.Concat.SubF Bytes).pack from rfl, Bytes.rec_eq gConcat0 (gAll i S g)] at hx; simp only [gConcat0, concretizeConcat, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa | hxc <;> [exact hP _ rfl; exact ha x hxa; exact hc x hxc]
theorem memoOK_dhPk {sk : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = dhPk sk → P x) (hsk : MemoOK i S g P sk) : MemoOK i S g P (dhPk sk) := by
  intro x hx; unfold gamma' at hx; rw [show dhPk sk = ({ sk := sk } : DhPk.SubF Bytes).pack from rfl, Bytes.rec_eq (gDhPk i) (gAll i S g)] at hx; simp only [gDhPk, concretizeDhPk, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hxsk <;> [exact hP _ rfl; exact hsk x hxsk]
theorem memoOK_dhPk_elim {sk : Bytes} (h : MemoOK i S g P (dhPk sk)) : MemoOK i S g P sk := by intro x hx; apply h x; unfold gamma' at hx ⊢; rw [show dhPk sk = ({ sk := sk } : DhPk.SubF Bytes).pack from rfl, Bytes.rec_eq (gDhPk i) (gAll i S g)]; simp only [gDhPk, concretizeDhPk, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, bytes_rec_gAll]; exact Or.inr hx
theorem memoOK_dh_pack {pk sk : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = ({ pk := pk, sk := sk } : Dh.SubF Bytes).pack → P x) (hpk : MemoOK i S g P pk) (hsk : MemoOK i S g P sk) : MemoOK i S g P (({ pk := pk, sk := sk } : Dh.SubF Bytes).pack) := by
  intro x hx; unfold gamma' at hx; rw [Bytes.rec_eq (gDh i) (gAll i S g)] at hx; simp only [gDh, concretizeDh, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxpk | hxsk <;> [exact hP _ rfl; exact hpk x hxpk; exact hsk x hxsk]
theorem memoOK_kdfExtract {salt ikm : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = kdfExtract salt ikm → P x) (hs : MemoOK i S g P salt) (hm : MemoOK i S g P ikm) : MemoOK i S g P (kdfExtract salt ikm) := by
  intro x hx; unfold gamma' at hx; rw [show kdfExtract salt ikm = ({ salt := salt, ikm := ikm } : KdfExtract.KdfExtract.SubF Bytes).pack from rfl, Bytes.rec_eq (gKdf0 i) (gAll i S g)] at hx; simp only [gKdf0, concretizeKdf, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxs | hxm <;> [exact hP _ rfl; exact hs x hxs; exact hm x hxm]
theorem memoOK_symEnc {k iv m : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = symEnc k iv m → P x) (hk : MemoOK i S g P k) (hiv : MemoOK i S g P iv) (hm : MemoOK i S g P m) : MemoOK i S g P (symEnc k iv m) := by
  intro x hx; unfold gamma' at hx; rw [show symEnc k iv m = ({ key := k, iv := iv, msg := m } : Enc.SubF Bytes).pack from rfl, Bytes.rec_eq (gSym0 i) (gAll i S g)] at hx; simp only [gSym0, concretizeSym, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | hxk | hxiv | hxm <;> [exact hP _ rfl; exact hk x hxk; exact hiv x hxiv; exact hm x hxm]
theorem memoOK_trunc8 {a : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = trunc8 a → P x) (ha : MemoOK i S g P a) : MemoOK i S g P (trunc8 a) := by
  intro x hx; unfold gamma' at hx; rw [show trunc8 a = ({ input := a } : Trunc8.SubF Bytes).pack from rfl, Bytes.rec_eq gTrunc0 (gAll i S g)] at hx; simp only [gTrunc0, concretizeTrunc, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, bytes_rec_gAll] at hx
  rcases hx with rfl | hxa <;> [exact hP _ rfl; exact ha x hxa]
theorem memoOK_variant_elim {v : Variant.SubF Bytes} (h : MemoOK i S g P v.pack) : MemoOK i S g P v.key := by intro x hx; apply h x; unfold gamma' at hx ⊢; rw [Bytes.rec_eq (gVariant0 i) (gAll i S g)]; simp only [gVariant0, concretizeVariant, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, bytes_rec_gAll]; exact Or.inr hx
theorem memoOK_x25519Key {pk : Bytes} (h : MemoOK i S g P pk) : MemoOK i S g P (x25519Key pk) := by
  unfold x25519Key normalizeX25519Key; have hp := Bytes.pack_view? Variant.SubF pk
  cases hv : pk.view? Variant.SubF with
  | none => exact h
  | some x => rw [hv] at hp; rw [← hp] at h; exact memoOK_variant_elim h
theorem memoOK_kemPk {sk : Bytes} (hsk : MemoOK i S g P sk) : MemoOK i S g P (kemPk sk) := by intro x hx; unfold gamma' at hx; rw [show kemPk sk = ({ sk := sk } : Pk.SubF Bytes).pack from rfl, Bytes.rec_eq (gKemPk S) (gAll i S g)] at hx; simp only [gKemPk, concretizeKemPk, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, bytes_rec_gAll] at hx; exact hsk x hx
theorem memoOK_kemEncap_fst' {pk e : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = (kemEncap pk e).1 → x.2.2 = ((i kyberEncapsSymbol [gamma i S g pk, gamma i S g e]).getD []).take 1568 → (gamma i S g e).length = 32 → P x) (hpk : MemoOK i S g P pk) (he : MemoOK i S g P e) : MemoOK i S g P (kemEncap pk e).1 := by
  intro x hx; rw [show (kemEncap pk e).1 = ({ pk := pk, entropy := e } : Encap.SubF Bytes).pack from rfl, ms_pack_kemEncap i S g ⟨pk, e⟩] at hx; dsimp only [gKemEncap, concretizeKemEncap] at hx
  by_cases h32 : (gamma' i S g e).bytes.length = 32
  · simp only [h32, ↓reduceIte, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hxpk | hxe <;> [exact hP _ rfl rfl h32; exact hpk x hxpk; exact he x hxe]
  · simp only [h32, ↓reduceIte, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx; exact hx.elim (hpk x) (he x)
theorem memoOK_kemEncap_fst {pk e : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = (kemEncap pk e).1 → P x) (hpk : MemoOK i S g P pk) (he : MemoOK i S g P e) : MemoOK i S g P (kemEncap pk e).1 :=
  memoOK_kemEncap_fst' (fun x hx _ _ => hP x hx) hpk he
theorem memoOK_kemEncap_snd' {pk e : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = (kemEncap pk e).2 → x.2.2 = ((i kyberEncapsSymbol [gamma i S g pk, gamma i S g e]).getD []).drop 1568 → (gamma i S g e).length = 32 → P x) (hpk : MemoOK i S g P pk) (he : MemoOK i S g P e) : MemoOK i S g P (kemEncap pk e).2 := by
  intro x hx; rw [show (kemEncap pk e).2 = ({ pk := pk, entropy := e } : SharedSecret.SubF Bytes).pack from rfl, ms_pack_kemSS i S g ⟨pk, e⟩] at hx; dsimp only [gKemSS, concretizeKemSS] at hx
  by_cases h32 : (gamma' i S g e).bytes.length = 32
  · simp only [h32, ↓reduceIte, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hxpk | hxe <;> [exact hP _ rfl rfl h32; exact hpk x hxpk; exact he x hxe]
  · simp only [h32, ↓reduceIte, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append] at hx; exact hx.elim (hpk x) (he x)
theorem memoOK_kemEncap_snd {pk e : Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = (kemEncap pk e).2 → P x) (hpk : MemoOK i S g P pk) (he : MemoOK i S g P e) : MemoOK i S g P (kemEncap pk e).2 :=
  memoOK_kemEncap_snd' (fun x hx _ _ => hP x hx) hpk he
theorem gamma_kemEncap_fst_eq {pk e : Bytes} (he : (gamma i S g e).length = 32) : gamma i S g (kemEncap pk e).1 = ((i kyberEncapsSymbol [gamma i S g pk, gamma i S g e]).getD []).take 1568 := by unfold gamma; rw [show (kemEncap pk e).1 = ({ pk := pk, entropy := e } : Encap.SubF Bytes).pack from rfl, ms_pack_kemEncap i S g ⟨pk, e⟩]; have he' : (gamma' i S g e).bytes.length = 32 := he; simp only [gKemEncap, concretizeKemEncap, he', ↓reduceIte, node]
theorem gamma_kemEncap_snd_eq {pk e : Bytes} (he : (gamma i S g e).length = 32) : gamma i S g (kemEncap pk e).2 = ((i kyberEncapsSymbol [gamma i S g pk, gamma i S g e]).getD []).drop 1568 := by unfold gamma; rw [show (kemEncap pk e).2 = ({ pk := pk, entropy := e } : SharedSecret.SubF Bytes).pack from rfl, ms_pack_kemSS i S g ⟨pk, e⟩]; have he' : (gamma' i S g e).bytes.length = 32 := he; simp only [gKemSS, concretizeKemSS, he', ↓reduceIte, node]
theorem memoOK_spqrInit {a p : Bytes} (ha : MemoOK i S g P a) (hp : MemoOK i S g P p) : MemoOK i S g P (spqrInit a p) := by intro x hx; unfold gamma' spqrInit at hx; rw [Bytes.rec_eq (gSpqrInit S) (gAll i S g)] at hx; simp only [gSpqrInit, concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx; exact hx.elim (ha x) (hp x)
theorem memoOK_spqrInit_elim {s : InitState.SubF Bytes} (h : MemoOK i S g P s.pack) : MemoOK i S g P s.authKey ∧ MemoOK i S g P s.params := by
  constructor <;> intro x hx <;> apply h x <;> unfold gamma' at hx ⊢ <;>
    rw [Bytes.rec_eq (gSpqrInit S) (gAll i S g)] <;>
    simp only [gSpqrInit, concretizeSpqrInit, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.mem_append, bytes_rec_gAll] <;> simp [gamma', hx]
theorem memoOK_spqrChainKey {a p idx : Bytes} (ha : MemoOK i S g P a) (hp : MemoOK i S g P p) (hi : MemoOK i S g P idx) : MemoOK i S g P (spqrChainKey a p idx) := by
  intro x hx; unfold gamma' spqrChainKey at hx; rw [Bytes.rec_eq (gSpqrChainKey S) (gAll i S g)] at hx; simp only [gSpqrChainKey, concretizeSpqrChainKey, spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with hxa | hxp | hxi <;> [exact ha x hxa; exact hp x hxp; exact hi x hxi]
theorem memoOK_spqrSendState {st c : Bytes} (hst : MemoOK i S g P st) (hc : MemoOK i S g P c) : MemoOK i S g P (spqrSend st c).1 := by intro x hx; unfold gamma' spqrSend at hx; dsimp only at hx; rw [Bytes.rec_eq (gSpqrSendState S) (gAll i S g)] at hx; simp only [gSpqrSendState, concretizeSpqrSendState, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx; exact hx.elim (hst x) (hc x)
theorem memoOK_spqrSendKey_pack {st c : Bytes} (hst : MemoOK i S g P st) (hc : MemoOK i S g P c) : MemoOK i S g P (({ st := st, coins := c } : SendKey.SubF Bytes).pack) := by intro x hx; unfold gamma' at hx; rw [Bytes.rec_eq (gSpqrSendKey S) (gAll i S g)] at hx; simp only [gSpqrSendKey, concretizeSpqrSendKey, spqrKeyNode, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx; exact hx.elim (hst x) (hc x)
theorem memoOK_spqrSendMsg {st c : Bytes} (hst : MemoOK i S g P st) (hc : MemoOK i S g P c) : MemoOK i S g P (spqrSend st c).2.2 := by intro x hx; unfold gamma' spqrSend at hx; dsimp only at hx; rw [Bytes.rec_eq (gSpqrSendMsg S) (gAll i S g)] at hx; simp only [gSpqrSendMsg, concretizeSpqrSendMsg, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx; exact hx.elim (hst x) (hc x)
theorem memoOK_spqrRecvState_pack {st m : Bytes} (hst : MemoOK i S g P st) (hm : MemoOK i S g P m) : MemoOK i S g P (({ st := st, msg := m } : RecvState.SubF Bytes).pack) := by intro x hx; unfold gamma' at hx; rw [Bytes.rec_eq (gSpqrRecvState S) (gAll i S g)] at hx; simp only [gSpqrRecvState, concretizeSpqrRecvState, opaqueNode, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_append, bytes_rec_gAll] at hx; exact hx.elim (hst x) (hm x)
theorem memoOK_trWire {w : TrWireMsg.SubF Bytes} (hP : ∀ x : Bytes × Bytes × HwBytes, x.1 = w.pack → P x) (hrk : MemoOK i S g P w.senderRatchetKey) (hct : MemoOK i S g P w.ciphertext) (hpq : MemoOK i S g P w.pqRatchet) : MemoOK i S g P w.pack := by
  intro x hx; unfold gamma' at hx; rw [Bytes.rec_eq (gTrWire0 g) (gAll i S g)] at hx; simp only [gTrWire0, concretizeTrWire, node, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons, List.mem_append, bytes_rec_gAll] at hx
  rcases hx with rfl | h1 | h2 | h3 <;> [exact hP _ rfl; exact hrk x h1; exact hct x h2; exact hpq x h3]
end Memo
def kyberCtVals : List HwBytes := [compKyberCt0, compKyberCt1, compKyberCt2, compDefaultKyberCt]
theorem kyberCtVals_lengths : compKyberCt0.length = 1568 ∧ compKyberCt1.length = 1568 ∧ compKyberCt2.length = 1568 ∧ compDefaultKyberCt.length = 1568 := ⟨length_leBytes 1568 _, length_leBytes 1568 _, length_leBytes 1568 _, List.length_replicate⟩
theorem compKyberEncaps_take1568_mem (ent : HwBytes) : (compKyberEncaps ent).take 1568 ∈ kyberCtVals := by
  obtain ⟨h0, h1, h2, hd⟩ := kyberCtVals_lengths; unfold compKyberEncaps kyberCtVals
  split_ifs <;> [rw [List.take_left' h0]; rw [List.take_left' h1]; rw [List.take_left' h2];
    rw [List.take_left' hd]] <;> simp
theorem compI0_kyberEncaps_take1568_mem (pk ent : HwBytes) : ((compI0 kyberEncapsSymbol [pk, ent]).getD []).take 1568 ∈ kyberCtVals := compKyberEncaps_take1568_mem ent
theorem length_of_mem_kyberCtVals {v : HwBytes} (hv : v ∈ kyberCtVals) : v.length = 1568 := by
  obtain ⟨h0, h1, h2, hd⟩ := kyberCtVals_lengths; simp only [kyberCtVals, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h <;> rw [h] <;> [exact h0; exact h1; exact h2; exact hd]
def NotVariant (b : Bytes) : Prop := b.view? Variant.SubF = none
def VariantFree (i : ExternInterpretation) (S : Sem) (g : Ghost) (t : Bytes) : Prop :=
  MemoOK i S g (fun x => NotVariant x.1) t
theorem nv_lit (bs : ByteArray) : (literalToBytes bs : Bytes).view? Variant.SubF = none :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.view_pack_none ({ lit := bs } : Literal.Literal.SubF Bytes) (by decide)
section VFPrim
variable {i : ExternInterpretation} {S : Sem} {g : Ghost}
theorem variantFree_lit (bs : ByteArray) : VariantFree i S g (literalToBytes bs) :=
  memoOK_lit (fun _ hx => hx ▸ nv_lit bs)
theorem variantFree_mem_bool (b : Bool) {p : Bytes} (hp : p ∈ bool.serialize b) : VariantFree i S g p := by
  obtain ⟨ba, _, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bool_serialize_singleton b
  rw [hser] at hp
  rcases List.mem_singleton.mp hp with rfl; exact variantFree_lit _
theorem variantFree_mem_slowNat : ∀ (n : Nat) {p : Bytes}, p ∈ slowNat.serialize n → VariantFree i S g p
  | 0, _, hp => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_zero] at hp
    exact variantFree_mem_bool false hp
  | n + 1, _, hp => by
    have hstep := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_succ n
    rw [hstep, List.mem_append] at hp; exact hp.elim (variantFree_mem_bool true) (variantFree_mem_slowNat n)
theorem variantFree_mem_slowString (s : String) {p : Bytes} (hp : p ∈ slowString.serialize s) : VariantFree i S g p := by
  have hser := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s
  rw [hser, List.mem_append, List.mem_singleton] at hp
  rcases hp with hnat | rfl <;> [exact variantFree_mem_slowNat _ hnat; exact variantFree_lit _]
end VFPrim
end Symbolic.BugInjection.Proofs.Common443.Census443Memo
