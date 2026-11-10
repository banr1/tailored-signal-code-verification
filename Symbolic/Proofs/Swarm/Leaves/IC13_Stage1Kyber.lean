/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Refinement.TraceExplanation
import DY.ALaCarte.Basic
import DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil

/-!
# Kyber `Encap` and `SharedSecret` Concretization and Shape Inversion

Concretization, memo-membership, and 13-functor `.shape` inversion lemmas for `DY.PQKem.kemEncap`,
`DY.PQKem.kemPk`, and `DY.PQKem.kemRejKey`, together with concretization of Bob's KEM share
(`gamma_bobKemShare`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber

open DY
open DY.Libsignal (HwBytes)
open ByteSpecs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal.PQXDH.Refinement (kyberEncapsSymbol)
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement

/-! ## `PQKem` Term-Algebra Pack, View, and Injectivity Lemmas -/

theorem kemEncap_fst_eq_pack (pk e : DY.Bytes) :
    (DY.PQKem.kemEncap pk e).1 = ({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack :=
  rfl

theorem kemEncap_snd_eq_pack (pk e : DY.Bytes) :
    (DY.PQKem.kemEncap pk e).2 =
      ({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack := rfl

@[simp]
theorem view_kemEncap_pack (x : DY.PQKem.Encap.SubF DY.Bytes) :
    x.pack.view? DY.PQKem.Encap.SubF = some x :=
  DY.BytesView.view_pack x

@[simp]
theorem view_kemSS_pack (x : DY.PQKem.SharedSecret.SubF DY.Bytes) :
    x.pack.view? DY.PQKem.SharedSecret.SubF = some x :=
  DY.BytesView.view_pack x

theorem kemEncap_pack_inj {x y : DY.PQKem.Encap.SubF DY.Bytes} (h : x.pack = y.pack) : x = y := by
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.PQKem.Encap.SubF) h
  simpa using hv

theorem kemSS_pack_inj {x y : DY.PQKem.SharedSecret.SubF DY.Bytes} (h : x.pack = y.pack) :
    x = y := by
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.PQKem.SharedSecret.SubF) h
  simpa using hv

theorem kemEncap_fst_inj {pk₁ e₁ pk₂ e₂ : DY.Bytes}
    (h : (DY.PQKem.kemEncap pk₁ e₁).1 = (DY.PQKem.kemEncap pk₂ e₂).1) :
    pk₁ = pk₂ ∧ e₁ = e₂ := by
  cases kemEncap_pack_inj h; exact ⟨rfl, rfl⟩

theorem kemEncap_snd_inj {pk₁ e₁ pk₂ e₂ : DY.Bytes}
    (h : (DY.PQKem.kemEncap pk₁ e₁).2 = (DY.PQKem.kemEncap pk₂ e₂).2) :
    pk₁ = pk₂ ∧ e₁ = e₂ := by
  cases kemSS_pack_inj h; exact ⟨rfl, rfl⟩

theorem randTerm_inj {ts₁ sz₁ ts₂ sz₂ : Nat} (h : randTerm ts₁ sz₁ = randTerm ts₂ sz₂) :
    ts₁ = ts₂ ∧ sz₁ = sz₂ := by
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.Random.Random) h
  dsimp only [randTerm] at hv
  rw [DY.BytesView.view_pack, DY.BytesView.view_pack] at hv
  injection hv with hr; cases hr; exact ⟨rfl, rfl⟩

@[simp]
theorem kemDecap_kemEncap (sk e : DY.Bytes) :
    DY.PQKem.kemDecap sk (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).1 =
      some (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).2 := by
  simp only [DY.PQKem.kemDecap, DY.PQKem.CanPQKem.kemDecap,
    DY.PQKem.kemEncap, DY.PQKem.CanPQKem.kemEncap,
    DY.PQKem.kemPk, DY.PQKem.CanPQKem.kemPk, DY.BytesView.view_pack, ↓reduceIte]

/-- Exact destructor inversion for `DY.PQKem.kemDecap`. -/
theorem kemDecap_eq_some_iff {sk ct ss : DY.Bytes} :
    DY.PQKem.kemDecap sk ct = some ss ↔
      ∃ e : DY.Bytes,
        ct = (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).1 ∧
        ss = (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).2 := by
  constructor
  · intro h
    dsimp only [DY.PQKem.kemDecap, DY.PQKem.CanPQKem.kemDecap] at h
    have hct_pack := DY.Bytes.pack_view? DY.PQKem.Encap.SubF ct
    rcases hct : ct.view? DY.PQKem.Encap.SubF with _ | ⟨pk, e⟩
    · rw [hct] at h; cases h
    · rw [hct] at h hct_pack; dsimp only at h
      have hpk_pack := DY.Bytes.pack_view? DY.PQKem.Pk.SubF pk
      rcases hpk : pk.view? DY.PQKem.Pk.SubF with _ | ⟨sk'⟩
      · rw [hpk] at h; cases h
      · rw [hpk] at h hpk_pack; dsimp only at h
        split at h
        · rename_i hsk; subst hsk; injection h with hss
          exact ⟨e, by rw [← hct_pack, ← hpk_pack]; rfl, by rw [← hss, ← hpk_pack]; rfl⟩
        · cases h
  · rintro ⟨e, rfl, rfl⟩; exact kemDecap_kemEncap sk e

theorem errToOption_kemDecap_eq_some_iff {sk ct ss : DY.Bytes} :
    DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap sk ct) = some ss ↔
      ∃ e : DY.Bytes,
        ct = (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).1 ∧
        ss = (DY.PQKem.kemEncap (DY.PQKem.kemPk sk) e).2 :=
  kemDecap_eq_some_iff

unseal DY.Bytes in
@[simp]
theorem view_litOf_kemPk_eq_none (v : HwBytes) :
    (litOf v).view? DY.PQKem.Pk.SubF = none := by
  unfold litOf
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Pk.SubF _

unseal DY.Bytes in
@[simp]
theorem view_litOf_kemEncap_eq_none (v : HwBytes) :
    (litOf v).view? DY.PQKem.Encap.SubF = none := by
  unfold litOf
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF _

unseal DY.Bytes in
@[simp]
theorem view_litOf_kemSS_eq_none (v : HwBytes) :
    (litOf v).view? DY.PQKem.SharedSecret.SubF = none := by
  unfold litOf
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF _

unseal DY.Bytes in
@[simp]
theorem view_litOf_random_eq_none (v : HwBytes) :
    (litOf v).view? DY.Random.Random = none := by
  unfold litOf
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _

theorem litOf_ne_kemEncap_pack (v : HwBytes) (x : DY.PQKem.Encap.SubF DY.Bytes) :
    litOf v ≠ x.pack := by
  intro h
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.PQKem.Encap.SubF) h
  simp at hv

theorem litOf_ne_kemSS_pack (v : HwBytes) (x : DY.PQKem.SharedSecret.SubF DY.Bytes) :
    litOf v ≠ x.pack := by
  intro h
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.PQKem.SharedSecret.SubF) h
  simp at hv

theorem kemPk_eq_pack (sk : DY.Bytes) :
    DY.PQKem.kemPk sk = ({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes).pack := rfl

theorem kemRejKey_eq_pack (sk ct : DY.Bytes) :
    DY.PQKem.kemRejKey sk ct =
      ({ sk := sk, cipher := ct } : DY.PQKem.RejKey.SubF DY.Bytes).pack := rfl

@[simp]
theorem view_kemRejKey_pack (x : DY.PQKem.RejKey.SubF DY.Bytes) :
    x.pack.view? DY.PQKem.RejKey.SubF = some x :=
  DY.BytesView.view_pack x

theorem kemRejKey_pack_inj {x y : DY.PQKem.RejKey.SubF DY.Bytes} (h : x.pack = y.pack) :
    x = y := by
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.PQKem.RejKey.SubF) h
  simpa using hv

theorem kemRejKey_inj {sk₁ ct₁ sk₂ ct₂ : DY.Bytes}
    (h : DY.PQKem.kemRejKey sk₁ ct₁ = DY.PQKem.kemRejKey sk₂ ct₂) :
    sk₁ = sk₂ ∧ ct₁ = ct₂ := by
  cases kemRejKey_pack_inj h; exact ⟨rfl, rfl⟩

unseal DY.Bytes in
@[simp]
theorem view_litOf_kemRejKey_eq_none (v : HwBytes) :
    (litOf v).view? DY.PQKem.RejKey.SubF = none := by
  unfold litOf
  exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.RejKey.SubF _

theorem litOf_ne_kemRejKey_pack (v : HwBytes) (x : DY.PQKem.RejKey.SubF DY.Bytes) :
    litOf v ≠ x.pack := by
  intro h
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.PQKem.RejKey.SubF) h
  simp at hv

unseal DY.Bytes in
@[simp]
theorem rejKey_length_eq_32 (sk ct : DY.Bytes) :
    (DY.PQKem.kemRejKey sk ct).length = 32 := by
  rw [kemRejKey_eq_pack, Symbolic.DYBridge.DY.Bytes.length_eq_1,
      DY.Bytes.rec_eq DY.PQKem.RejKey.SubF.length DY.BytesLength.funs]
  rfl

unseal DY.Bytes in
/-- Constructor disjointness for `DY.PQKem.kemRejKey`: its `.view?` projection on every other
functor of the composed term algebra is `none`. -/
theorem view?_kemRejKey_disjoint (sk ct : DY.Bytes) :
    (DY.PQKem.kemRejKey sk ct).view? DY.Concat.Concat.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.DiffieHellman.DhPk.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.DiffieHellman.Dh.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.KdfExtract.KdfExtract.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.SymEnc.Enc.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.Trunc.Trunc8.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.Random.Random = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.PQKem.Pk.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.PQKem.Encap.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.PQKem.SharedSecret.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.X25519.Variant.SubF = none ∧
    (DY.PQKem.kemRejKey sk ct).view? DY.TrWire.TrWireMsg.SubF = none := by
  rw [kemRejKey_eq_pack]
  exact ⟨Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Concat.Concat.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Pk.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.X25519.Variant.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.TrWire.TrWireMsg.SubF _⟩

/-! ## `SubFunction` Instances and `gamma'` / `gamma` Unfold Lemmas -/

section SubFunctions

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

unseal DY.Bytes in
private instance subRandom : DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subLit : DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subConcat : DY.Bytes.SubFunction concretizeConcat (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, concatFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhPk : DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDh : DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKdf : DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSym : DY.Bytes.SubFunction (concretizeSym i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, symFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subTrunc : DY.Bytes.SubFunction concretizeTrunc (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, truncFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant : DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemPk : DY.Bytes.SubFunction (concretizeKemPk S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemEncap : DY.Bytes.SubFunction (concretizeKemEncap i) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKemSS : DY.Bytes.SubFunction (concretizeKemSS i S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
instance subKemRej : DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVk : DY.Bytes.SubFunction (concretizeVk S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSign : DY.Bytes.SubFunction (concretizeSign S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, sigFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrInit : DY.Bytes.SubFunction (concretizeSpqrInit S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendState : DY.Bytes.SubFunction (concretizeSpqrSendState S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendKey : DY.Bytes.SubFunction (concretizeSpqrSendKey S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrSendMsg : DY.Bytes.SubFunction (concretizeSpqrSendMsg S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrRecvState : DY.Bytes.SubFunction (concretizeSpqrRecvState S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrRecvKey : DY.Bytes.SubFunction (concretizeSpqrRecvKey S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subSpqrChainKey : DY.Bytes.SubFunction (concretizeSpqrChainKey S) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, spqrFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subTrWire : DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll i S g) := @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma'_pack_kemEncap (x : DY.PQKem.Encap.SubF DY.Bytes) :
    gamma' i S g x.pack = concretizeKemEncap i x (fun y _ => gamma' i S g y) := by
  unfold gamma'; exact DY.Bytes.rec_eq (concretizeKemEncap i) (concretizeAll i S g) x

theorem gamma'_pack_kemSS (x : DY.PQKem.SharedSecret.SubF DY.Bytes) :
    gamma' i S g x.pack = concretizeKemSS i S x (fun y _ => gamma' i S g y) := by
  unfold gamma'; exact DY.Bytes.rec_eq (concretizeKemSS i S) (concretizeAll i S g) x

theorem gamma'_pack_kemPk (x : DY.PQKem.Pk.SubF DY.Bytes) :
    gamma' i S g x.pack = concretizeKemPk S x (fun y _ => gamma' i S g y) := by
  unfold gamma'; exact DY.Bytes.rec_eq (concretizeKemPk S) (concretizeAll i S g) x

theorem gamma'_pack_kemRej (x : DY.PQKem.RejKey.SubF DY.Bytes) :
    gamma' i S g x.pack = concretizeKemRej S x (fun y _ => gamma' i S g y) := by
  unfold gamma'; exact DY.Bytes.rec_eq (concretizeKemRej S) (concretizeAll i S g) x

theorem gamma'_pack_random (x : DY.Random.Random DY.Bytes) :
    gamma' i S g x.pack = concretizeRandom g x (fun y _ => gamma' i S g y) := by
  unfold gamma'; exact DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll i S g) x

/-- `gamma'` on `Encap` in the 32-byte entropy branch: emits a non-opaque `node`. -/
theorem gamma'_kemEncap_of_len32 {pk e : DY.Bytes} (h32 : (gamma i S g e).length = 32) :
    gamma' i S g (DY.PQKem.kemEncap pk e).1 =
      node (((i kyberEncapsSymbol [gamma i S g pk, gamma i S g e]).getD []).take 1568)
        (DY.PQKem.kemEncap pk e).1
        ({ pk := (gamma' i S g pk).shape,
           entropy := (gamma' i S g e).shape } : DY.PQKem.Encap.SubF DY.Bytes).pack
        [gamma' i S g pk, gamma' i S g e] := by
  rw [kemEncap_fst_eq_pack, gamma'_pack_kemEncap]
  dsimp only [concretizeKemEncap]
  change (if (gamma i S g e).length = 32 then _ else _) = _
  simp only [h32, ↓reduceIte]; rfl

/-- `gamma'` on `Encap` in the non-32-byte entropy branch: emits `opaqueNode []`. -/
theorem gamma'_kemEncap_of_len_ne32 {pk e : DY.Bytes} (hne : (gamma i S g e).length ≠ 32) :
    gamma' i S g (DY.PQKem.kemEncap pk e).1 =
      opaqueNode [] [gamma' i S g pk, gamma' i S g e] := by
  rw [kemEncap_fst_eq_pack, gamma'_pack_kemEncap]
  dsimp only [concretizeKemEncap]
  change (if (gamma i S g e).length = 32 then _ else _) = _
  simp only [hne, ↓reduceIte]

/-- `gamma'` on `SharedSecret` in the 32-byte entropy branch: emits a non-opaque `node`. -/
theorem gamma'_kemSS_of_len32 {pk e : DY.Bytes} (h32 : (gamma i S g e).length = 32) :
    gamma' i S g (DY.PQKem.kemEncap pk e).2 =
      node (((i kyberEncapsSymbol [gamma i S g pk, gamma i S g e]).getD []).drop 1568)
        (DY.PQKem.kemEncap pk e).2
        ({ pk := (gamma' i S g pk).shape,
           entropy := (gamma' i S g e).shape } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack
        [gamma' i S g pk, gamma' i S g e] := by
  rw [kemEncap_snd_eq_pack, gamma'_pack_kemSS]
  dsimp only [concretizeKemSS]
  change (if (gamma i S g e).length = 32 then _ else _) = _
  simp only [h32, ↓reduceIte]; rfl

/-- `gamma'` on `SharedSecret` in the non-32-byte entropy branch: emits `opaqueNode` with
`S.kemDecap`. -/
theorem gamma'_kemSS_of_len_ne32 {pk e : DY.Bytes} (hne : (gamma i S g e).length ≠ 32) :
    gamma' i S g (DY.PQKem.kemEncap pk e).2 =
      opaqueNode (S.kemDecap (gamma i S g pk) (gamma i S g e))
        [gamma' i S g pk, gamma' i S g e] := by
  rw [kemEncap_snd_eq_pack, gamma'_pack_kemSS]
  dsimp only [concretizeKemSS]
  change (if (gamma i S g e).length = 32 then _ else _) = _
  simp only [hne, ↓reduceIte]; rfl

/-- Byte-level concretization `γ` on `(kemEncap pk e).1`. -/
theorem gamma_kemEncap_fst (pk e : DY.Bytes) :
    gamma i S g (DY.PQKem.kemEncap pk e).1 =
      if (gamma i S g e).length = 32 then
        ((i kyberEncapsSymbol [gamma i S g pk, gamma i S g e]).getD []).take 1568
      else [] := by
  by_cases h32 : (gamma i S g e).length = 32
  · simp only [h32, ↓reduceIte]
    exact congrArg ConcretizedTerm.bytes (gamma'_kemEncap_of_len32 i S g (pk := pk) h32)
  · simp only [h32, ↓reduceIte]
    exact congrArg ConcretizedTerm.bytes (gamma'_kemEncap_of_len_ne32 i S g (pk := pk) h32)

/-- Byte-level concretization `γ` on `(kemEncap pk e).2`. -/
theorem gamma_kemEncap_snd (pk e : DY.Bytes) :
    gamma i S g (DY.PQKem.kemEncap pk e).2 =
      if (gamma i S g e).length = 32 then
        ((i kyberEncapsSymbol [gamma i S g pk, gamma i S g e]).getD []).drop 1568
      else S.kemDecap (gamma i S g pk) (gamma i S g e) := by
  by_cases h32 : (gamma i S g e).length = 32
  · simp only [h32, ↓reduceIte]
    exact congrArg ConcretizedTerm.bytes (gamma'_kemSS_of_len32 i S g (pk := pk) h32)
  · simp only [h32, ↓reduceIte]
    exact congrArg ConcretizedTerm.bytes (gamma'_kemSS_of_len_ne32 i S g (pk := pk) h32)

/-! ## Memo Membership and Self-Memo Entries -/

theorem mem_memo_kemEncap_self_of_len32 {pk e : DY.Bytes} (h32 : (gamma i S g e).length = 32) :
    ((DY.PQKem.kemEncap pk e).1,
     (gamma' i S g (DY.PQKem.kemEncap pk e).1).shape,
     gamma i S g (DY.PQKem.kemEncap pk e).1) ∈
      (gamma' i S g (DY.PQKem.kemEncap pk e).1).memo := by
  unfold gamma; rw [gamma'_kemEncap_of_len32 i S g h32]; exact List.Mem.head _

theorem mem_memo_kemSS_self_of_len32 {pk e : DY.Bytes} (h32 : (gamma i S g e).length = 32) :
    ((DY.PQKem.kemEncap pk e).2,
     (gamma' i S g (DY.PQKem.kemEncap pk e).2).shape,
     gamma i S g (DY.PQKem.kemEncap pk e).2) ∈
      (gamma' i S g (DY.PQKem.kemEncap pk e).2).memo := by
  unfold gamma; rw [gamma'_kemSS_of_len32 i S g h32]; exact List.Mem.head _

/-- If `x.pack` (`Encap`) equals its own shape, `(x.pack, x.pack, gamma i S g x.pack)` lies in its memo. -/
theorem self_mem_memo_kemEncap_of_shape_eq_self {x : DY.PQKem.Encap.SubF DY.Bytes}
    (hsh : (gamma' i S g x.pack).shape = x.pack) :
    (x.pack, x.pack, gamma i S g x.pack) ∈ (gamma' i S g x.pack).memo := by
  rcases x with ⟨pk, e⟩
  by_cases h32 : (gamma i S g e).length = 32
  · have hm := mem_memo_kemEncap_self_of_len32 i S g (pk := pk) h32
    dsimp only [kemEncap_fst_eq_pack] at hm; rwa [hsh] at hm
  · have hopq := gamma'_kemEncap_of_len_ne32 i S g (pk := pk) h32
    dsimp only [kemEncap_fst_eq_pack] at hopq; rw [hopq] at hsh
    exact False.elim (litOf_ne_kemEncap_pack [] ⟨pk, e⟩ hsh)

/-- If `x.pack` (`SharedSecret`) equals its own shape, `(x.pack, x.pack, gamma i S g x.pack)` lies in its memo. -/
theorem self_mem_memo_kemSS_of_shape_eq_self {x : DY.PQKem.SharedSecret.SubF DY.Bytes}
    (hsh : (gamma' i S g x.pack).shape = x.pack) :
    (x.pack, x.pack, gamma i S g x.pack) ∈ (gamma' i S g x.pack).memo := by
  rcases x with ⟨pk, e⟩
  by_cases h32 : (gamma i S g e).length = 32
  · have hm := mem_memo_kemSS_self_of_len32 i S g (pk := pk) h32
    dsimp only [kemEncap_snd_eq_pack] at hm; rwa [hsh] at hm
  · have hopq := gamma'_kemSS_of_len_ne32 i S g (pk := pk) h32
    dsimp only [kemEncap_snd_eq_pack] at hopq; rw [hopq] at hsh
    exact False.elim (litOf_ne_kemSS_pack _ ⟨pk, e⟩ hsh)

theorem gamma_kemPk_eq (sk : DY.Bytes) :
    gamma i S g (DY.PQKem.kemPk sk) = S.kemPk (gamma i S g sk) := by
  unfold gamma
  rw [kemPk_eq_pack, gamma'_pack_kemPk]
  rfl

/-- `gamma'` on `kemRejKey`: unconditionally emits a transparent `node` with shape
`kemRejKey s.shape c.shape`. -/
theorem gamma'_kemRejKey_eq (sk ct : DY.Bytes) :
    gamma' i S g (DY.PQKem.kemRejKey sk ct) =
      let s := gamma' i S g sk; let c := gamma' i S g ct
      node (S.kemDecap (S.kemPk s.bytes) c.bytes) (DY.PQKem.kemRejKey sk ct)
        (DY.PQKem.kemRejKey s.shape c.shape) [s, c] := by
  rw [kemRejKey_eq_pack, gamma'_pack_kemRej]
  rfl

/-- Byte-level concretization `γ` on `kemRejKey sk ct`. -/
theorem gamma_kemRejKey_eq (sk ct : DY.Bytes) :
    gamma i S g (DY.PQKem.kemRejKey sk ct) =
      S.kemDecap (S.kemPk (gamma i S g sk)) (gamma i S g ct) := by
  exact congrArg ConcretizedTerm.bytes (gamma'_kemRejKey_eq i S g sk ct)

theorem mem_memo_kemRejKey_self (sk ct : DY.Bytes) :
    (DY.PQKem.kemRejKey sk ct,
     (gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape,
     gamma i S g (DY.PQKem.kemRejKey sk ct)) ∈
      (gamma' i S g (DY.PQKem.kemRejKey sk ct)).memo := by
  unfold gamma; rw [gamma'_kemRejKey_eq i S g sk ct]; exact List.Mem.head _

end SubFunctions

/-! ## `assumedInjective` Characterization -/

unseal DY.Bytes in
@[simp]
theorem assumedInjective_kemPk_eq_false (sk : DY.Bytes) :
    assumedInjective (DY.PQKem.kemPk sk) = false := by
  change assumedInjective (({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes).pack) = false
  unfold assumedInjective
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF]
  rfl

unseal DY.Bytes in
@[simp]
theorem assumedInjective_litOf_eq_false (v : HwBytes) :
    assumedInjective (litOf v) = false := by
  unfold litOf assumedInjective
  rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.Encap.SubF,
      Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.PQKem.SharedSecret.SubF]
  rfl

/-- Eight-way inversion of `assumedInjective t = true`. -/
theorem assumedInjective_eq_true_iff (t : DY.Bytes) :
    assumedInjective t = true ↔
      (∃ r : DY.Random.Random DY.Bytes, t.view? DY.Random.Random = some r ∧ r.size ≠ 0) ∨
      (t.view? DY.DiffieHellman.DhPk.SubF).isSome = true ∨
      (t.view? DY.DiffieHellman.Dh.SubF).isSome = true ∨
      (t.view? DY.KdfExtract.KdfExtract.SubF).isSome = true ∨
      (t.view? DY.SymEnc.Enc.SubF).isSome = true ∨
      (t.view? DY.Trunc.Trunc8.SubF).isSome = true ∨
      (t.view? DY.PQKem.Encap.SubF).isSome = true ∨
      (t.view? DY.PQKem.SharedSecret.SubF).isSome = true := by
  unfold assumedInjective
  simp only [Bool.or_eq_true, or_assoc]
  apply or_congr_left
  cases hv : t.view? DY.Random.Random with
  | none => simp
  | some r => simp [bne_iff_ne]

/-! ## Shape Head Disjointness and `gamma'.shape` Classification -/

section ShapeInversion

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

unseal DY.Bytes in
/-- Unconditional across both `= 32` and `≠ 32` branches: `(gamma' (kemEncap pk e).1).shape` never
has head `Concat`, `DhPk`, `Dh`, `KdfExtract`, `SymEnc.Enc`, `Trunc8`, or `Random`. -/
theorem shape_kemEncap_heads_none (pk e : DY.Bytes) :
    ((gamma' i S g (DY.PQKem.kemEncap pk e).1).shape).view? DY.Concat.Concat.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).1).shape).view? DY.DiffieHellman.DhPk.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).1).shape).view? DY.DiffieHellman.Dh.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).1).shape).view? DY.KdfExtract.KdfExtract.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).1).shape).view? DY.SymEnc.Enc.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).1).shape).view? DY.Trunc.Trunc8.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).1).shape).view? DY.Random.Random = none := by
  by_cases h32 : (gamma i S g e).length = 32
  · rw [gamma'_kemEncap_of_len32 i S g h32]
    dsimp only [node]
    exact ⟨Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Concat.Concat.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _⟩
  · rw [gamma'_kemEncap_of_len_ne32 i S g h32]
    dsimp only [opaqueNode, litOf]
    exact ⟨Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Concat.Concat.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _⟩

unseal DY.Bytes in
/-- Unconditional across both `= 32` and `≠ 32` branches: `(gamma' (kemEncap pk e).2).shape` never
has head `Concat`, `DhPk`, `Dh`, `KdfExtract`, `SymEnc.Enc`, `Trunc8`, or `Random`. -/
theorem shape_kemSS_heads_none (pk e : DY.Bytes) :
    ((gamma' i S g (DY.PQKem.kemEncap pk e).2).shape).view? DY.Concat.Concat.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).2).shape).view? DY.DiffieHellman.DhPk.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).2).shape).view? DY.DiffieHellman.Dh.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).2).shape).view? DY.KdfExtract.KdfExtract.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).2).shape).view? DY.SymEnc.Enc.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).2).shape).view? DY.Trunc.Trunc8.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemEncap pk e).2).shape).view? DY.Random.Random = none := by
  by_cases h32 : (gamma i S g e).length = 32
  · rw [gamma'_kemSS_of_len32 i S g h32]
    dsimp only [node]
    exact ⟨Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Concat.Concat.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _⟩
  · rw [gamma'_kemSS_of_len_ne32 i S g h32]
    dsimp only [opaqueNode, litOf]
    exact ⟨Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Concat.Concat.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF _,
           Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _⟩

private theorem shape_concat (a b : DY.Bytes) :
    (gamma' i S g (DY.Concat.concat a b)).shape =
      ({ lhs := (gamma' i S g a).shape, rhs := (gamma' i S g b).shape } :
        DY.Concat.Concat.SubF DY.Bytes).pack := by
  have hc : DY.Concat.concat a b = ({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack := rfl
  rw [hc]; unfold gamma'; rw [DY.Bytes.rec_eq concretizeConcat (concretizeAll i S g)]; rfl

/-- `(gamma' i S g (kemEncap pk e).2).shape` is never a `Concat` shape. -/
theorem shape_kemSS_ne_concat (pk e a b : DY.Bytes) :
    (gamma' i S g (DY.PQKem.kemEncap pk e).2).shape ≠
      (gamma' i S g (DY.Concat.concat a b)).shape := by
  intro h
  have hv := congrArg (fun t : DY.Bytes => t.view? DY.Concat.Concat.SubF) h
  rw [(shape_kemSS_heads_none i S g pk e).1, shape_concat, DY.BytesView.view_pack] at hv
  cases hv

unseal DY.Bytes in
/-- `(gamma' (kemRejKey sk ct)).shape` never has head `Concat`, `DhPk`, `Dh`, `KdfExtract`,
`SymEnc.Enc`, `Trunc8`, or `Random`. -/
theorem shape_kemRejKey_heads_none (sk ct : DY.Bytes) :
    ((gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape).view? DY.Concat.Concat.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape).view? DY.DiffieHellman.DhPk.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape).view? DY.DiffieHellman.Dh.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape).view? DY.KdfExtract.KdfExtract.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape).view? DY.SymEnc.Enc.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape).view? DY.Trunc.Trunc8.SubF = none ∧
    ((gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape).view? DY.Random.Random = none := by
  rw [gamma'_kemRejKey_eq i S g sk ct]
  dsimp only [node, kemRejKey_eq_pack]
  exact ⟨Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Concat.Concat.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.DhPk.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.DiffieHellman.Dh.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.SymEnc.Enc.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Trunc.Trunc8.SubF _,
         Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random _⟩

/-- `(gamma' i S g (kemRejKey sk ct)).shape` is never a `Concat` shape. -/
theorem shape_kemRejKey_ne_concat (sk ct a b : DY.Bytes) :
    (gamma' i S g (DY.PQKem.kemRejKey sk ct)).shape ≠
      (gamma' i S g (DY.Concat.concat a b)).shape := by
  intro h
  have hv := congrArg (fun t : DY.Bytes => t.view? DY.Concat.Concat.SubF) h
  rw [(shape_kemRejKey_heads_none i S g sk ct).1, shape_concat, DY.BytesView.view_pack] at hv
  cases hv

unseal DY.Bytes in
private theorem partialFunDep_shape_cases_step
    {F : Type → Type} [DY.SubBytesFunctor F] [DY.BytesFunctor.Has F] {M : DY.Bytes → Prop}
    (pf : DY.Bytes.PartialFunction F ConcretizedTerm) [DY.Bytes.SubFunction pf (concretizeAll i S g)]
    (hstep : ∀ x : F DY.Bytes,
      (gamma' i S g (DY.BytesView.pack x)).shape =
        (pf x (fun y _ => gamma' i S g y)).shape →
      M (DY.BytesView.pack x)) :
    DY.ALaCarte.Container.PartialFunDep F (g := DY.BytesF) M := by
  intro x _
  refine (Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x) ▸ ?_
  apply hstep x
  change ((DY.BytesView.pack x).rec (concretizeAll i S g)).shape = _
  rw [DY.Bytes.rec_eq pf (concretizeAll i S g) x]; rfl

/-- Canonical top-level forms of `(gamma' i S g u).shape`. -/
def Gamma'ShapeClass (u : DY.Bytes) : Prop :=
  (∃ v : HwBytes, (gamma' i S g u).shape = litOf v) ∨
  (∃ x : DY.Literal.Literal.SubF DY.Bytes,
      u = DY.BytesView.pack x ∧ (gamma' i S g u).shape = DY.BytesView.pack x) ∨
  (∃ r : DY.Random.Random DY.Bytes,
      r.size ≠ 0 ∧ u = DY.BytesView.pack r ∧ (gamma' i S g u).shape = DY.BytesView.pack r) ∨
  (∃ y : DY.Concat.Concat.SubF DY.Bytes, (gamma' i S g u).shape = DY.BytesView.pack y) ∨
  (∃ y : DY.DiffieHellman.DhPk.SubF DY.Bytes, (gamma' i S g u).shape = DY.BytesView.pack y) ∨
  (∃ y : DY.DiffieHellman.Dh.SubF DY.Bytes, (gamma' i S g u).shape = DY.BytesView.pack y) ∨
  (∃ y : DY.KdfExtract.KdfExtract.SubF DY.Bytes, (gamma' i S g u).shape = DY.BytesView.pack y) ∨
  (∃ y : DY.SymEnc.Enc.SubF DY.Bytes, (gamma' i S g u).shape = DY.BytesView.pack y) ∨
  (∃ y : DY.Trunc.Trunc8.SubF DY.Bytes, (gamma' i S g u).shape = DY.BytesView.pack y) ∨
  (∃ y : DY.X25519.Variant.SubF DY.Bytes, (gamma' i S g u).shape = DY.BytesView.pack y) ∨
  (∃ x : DY.PQKem.Encap.SubF DY.Bytes,
    u = x.pack ∧ (gamma i S g x.entropy).length = 32 ∧
    (gamma' i S g u).shape =
      ({ pk := (gamma' i S g x.pk).shape, entropy := (gamma' i S g x.entropy).shape } :
        DY.PQKem.Encap.SubF DY.Bytes).pack) ∨
  (∃ x : DY.PQKem.SharedSecret.SubF DY.Bytes,
    u = x.pack ∧ (gamma i S g x.entropy).length = 32 ∧
    (gamma' i S g u).shape =
      ({ pk := (gamma' i S g x.pk).shape, entropy := (gamma' i S g x.entropy).shape } :
        DY.PQKem.SharedSecret.SubF DY.Bytes).pack) ∨
  (∃ x : DY.PQKem.RejKey.SubF DY.Bytes,
    u = x.pack ∧
    (gamma' i S g u).shape =
      ({ sk := (gamma' i S g x.sk).shape, cipher := (gamma' i S g x.cipher).shape } :
        DY.PQKem.RejKey.SubF DY.Bytes).pack) ∨
  (∃ y : DY.TrWire.TrWireMsg.SubF DY.Bytes, (gamma' i S g u).shape = DY.BytesView.pack y)

unseal DY.Bytes in
/-- Top-level shape classification for `(gamma' i S g u).shape` across all functors of `DY.BytesF`. -/
theorem gamma'_shape_cases (u : DY.Bytes) : Gamma'ShapeClass i S g u := by
  have hpack : ∀ {SubF : Type → Type} [DY.ALaCarte.FunctorSizeOf SubF]
      [DY.ALaCarte.SubFunctorTC SubF DY.BytesF] {M : DY.Bytes → Prop}
      (v : SubF (DY.ALaCarte.ContainerFor DY.BytesF)),
      M (DY.ALaCarte.Container.pack SubF v) →
      M (DY.ALaCarte.Container.pack DY.BytesF (DY.ALaCarte.SubFunctorTC.inj (g := DY.BytesF) v)) := by
    intro SubF _ _ M v hm
    have hv : DY.ALaCarte.Container.view DY.BytesF (DY.ALaCarte.Container.pack SubF v) =
        some (DY.ALaCarte.SubFunctorTC.inj (g := DY.BytesF) v) := by
      rw [Symbolic.DYBridge.DY.ALaCarte.Container.view_pack_cross]
      rfl
    have hp := DY.ALaCarte.Container.pack_view (f := DY.BytesF) (DY.ALaCarte.Container.pack SubF v)
    rw [hv] at hp
    exact hp ▸ hm
  refine DY.ALaCarte.Container.rec (f := DY.BytesF) (motive := Gamma'ShapeClass i S g) ?_ u
  rintro ⟨⟨id, hid⟩, val⟩ rec
  match id with
  | 0 =>
    refine hpack _ (partialFunDep_shape_cases_step i S g (concretizeRandom g) ?_ val rec)
    intro x hsh; dsimp only [concretizeRandom] at hsh
    by_cases h0 : x.size = 0
    · simp only [h0, ↓reduceIte] at hsh; exact .inl ⟨[], hsh⟩
    · simp only [h0, ↓reduceIte] at hsh; exact .inr (.inr (.inl ⟨x, h0, rfl, hsh⟩))
  | 1 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g concretizeLit
        (fun x hsh => .inr (.inl ⟨x, rfl, hsh⟩)) v rec)
    | n + 1 => omega
  | 2 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g concretizeConcat
        (fun _ hsh => .inr (.inr (.inr (.inl ⟨_, hsh⟩)))) v rec)
    | n + 1 => omega
  | 3 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeDhPk i)
        (fun _ hsh => .inr (.inr (.inr (.inr (.inl ⟨_, hsh⟩))))) v rec)
    | 1 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeDh i)
        (fun _ hsh => .inr (.inr (.inr (.inr (.inr (.inl ⟨_, hsh⟩)))))) v rec)
    | n + 2 => omega
  | 4 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeKdf i)
        (fun _ hsh => .inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, hsh⟩))))))) v rec)
    | n + 1 => omega
  | 5 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeSym i)
        (fun _ hsh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, hsh⟩)))))))) v rec)
    | n + 1 => omega
  | 6 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g concretizeTrunc
        (fun _ hsh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, hsh⟩))))))))) v rec)
    | n + 1 => omega
  | 7 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeVariant i)
        (fun _ hsh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨_, hsh⟩)))))))))) v rec)
    | n + 1 => omega
  | 8 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeKemPk S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | 1 =>
      refine hpack _ (partialFunDep_shape_cases_step i S g (concretizeKemEncap i) (fun x _ => ?_) v rec)
      by_cases h32 : (gamma i S g x.entropy).length = 32
      · have heq := congrArg ConcretizedTerm.shape (gamma'_kemEncap_of_len32 i S g (pk := x.pk) h32)
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨x, rfl, h32, heq⟩))))))))))
      · have heq := congrArg ConcretizedTerm.shape (gamma'_kemEncap_of_len_ne32 i S g (pk := x.pk) h32)
        exact .inl ⟨[], heq⟩
    | 2 =>
      refine hpack _ (partialFunDep_shape_cases_step i S g (concretizeKemSS i S) (fun x _ => ?_) v rec)
      by_cases h32 : (gamma i S g x.entropy).length = 32
      · have heq := congrArg ConcretizedTerm.shape (gamma'_kemSS_of_len32 i S g (pk := x.pk) h32)
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨x, rfl, h32, heq⟩)))))))))))
      · have heq := congrArg ConcretizedTerm.shape (gamma'_kemSS_of_len_ne32 i S g (pk := x.pk) h32)
        exact .inl ⟨_, heq⟩
    | 3 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeKemRej S)
        (fun x hsh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨x, rfl, hsh⟩))))))))))))) v rec)
    | n + 4 => omega
  | 9 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeVk S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | 1 => exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeSign S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | n + 2 => omega
  | 10 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 => exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeSpqrInit S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | 1 => exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeSpqrSendState S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | 2 => exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeSpqrSendKey S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | 3 => exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeSpqrSendMsg S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | 4 => exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeSpqrRecvState S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | 5 => exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeSpqrRecvKey S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | 6 => exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeSpqrChainKey S) (fun _ hsh => .inl ⟨_, hsh⟩) v rec)
    | n + 7 => omega
  | 11 =>
    rcases val with ⟨⟨sid, hsid⟩, v⟩; match sid with
    | 0 =>
      exact hpack _ (partialFunDep_shape_cases_step i S g (concretizeTrWire g)
        (fun _ hsh => .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨_, hsh⟩))))))))))))) v rec)
    | n + 1 => omega
  | n + 12 => omega

unseal DY.Bytes in
/-- `(gamma' i S g u).shape` equals a packed `Encap` shape `{ pk := sh_p, entropy := sh_e }` iff
`u` is an `Encap` term in the 32-byte entropy branch with matching child shapes. -/
theorem shape_eq_kemEncap_pack_iff (u : DY.Bytes) (sh_p sh_e : DY.Bytes) :
    (gamma' i S g u).shape =
      ({ pk := sh_p, entropy := sh_e } : DY.PQKem.Encap.SubF DY.Bytes).pack ↔
      ∃ pk' e' : DY.Bytes,
        u = ({ pk := pk', entropy := e' } : DY.PQKem.Encap.SubF DY.Bytes).pack ∧
        (gamma i S g e').length = 32 ∧
        (gamma' i S g pk').shape = sh_p ∧
        (gamma' i S g e').shape = sh_e := by
  constructor
  · intro hsh
    rcases gamma'_shape_cases i S g u with
      ⟨w, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
      ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨⟨pk', e'⟩, rfl, h32, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩
    · rw [h] at hsh; exact False.elim (litOf_ne_kemEncap_pack w _ hsh)
    all_goals try (
      rw [h] at hsh
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hsh))
    rw [h] at hsh
    have hinj := kemEncap_pack_inj hsh
    injection hinj with hp_eq he_eq
    exact ⟨pk', e', rfl, h32, hp_eq, he_eq⟩
  · rintro ⟨pk', e', rfl, h32, rfl, rfl⟩
    have heq := gamma'_kemEncap_of_len32 i S g (pk := pk') h32
    dsimp only [kemEncap_fst_eq_pack] at heq; rw [heq]; rfl

unseal DY.Bytes in
/-- `(gamma' i S g u).shape` equals a packed `SharedSecret` shape `{ pk := sh_p, entropy := sh_e }`
iff `u` is a `SharedSecret` term in the 32-byte entropy branch with matching child shapes. -/
theorem shape_eq_kemSS_pack_iff (u : DY.Bytes) (sh_p sh_e : DY.Bytes) :
    (gamma' i S g u).shape =
      ({ pk := sh_p, entropy := sh_e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack ↔
      ∃ pk' e' : DY.Bytes,
        u = ({ pk := pk', entropy := e' } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack ∧
        (gamma i S g e').length = 32 ∧
        (gamma' i S g pk').shape = sh_p ∧
        (gamma' i S g e').shape = sh_e := by
  constructor
  · intro hsh
    rcases gamma'_shape_cases i S g u with
      ⟨w, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
      ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨⟨pk', e'⟩, rfl, h32, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩
    · rw [h] at hsh; exact False.elim (litOf_ne_kemSS_pack w _ hsh)
    all_goals try (
      rw [h] at hsh
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hsh))
    rw [h] at hsh
    have hinj := kemSS_pack_inj hsh
    injection hinj with hp_eq he_eq
    exact ⟨pk', e', rfl, h32, hp_eq, he_eq⟩
  · rintro ⟨pk', e', rfl, h32, rfl, rfl⟩
    have heq := gamma'_kemSS_of_len32 i S g (pk := pk') h32
    dsimp only [kemEncap_snd_eq_pack] at heq; rw [heq]; rfl

unseal DY.Bytes in
/-- For `sz ≠ 0`, `(gamma' i S g u).shape = randTerm ts sz` iff `u = randTerm ts sz`. -/
theorem shape_eq_randTerm_iff (u : DY.Bytes) {ts sz : Nat} (hsz : sz ≠ 0) :
    (gamma' i S g u).shape = randTerm ts sz ↔ u = randTerm ts sz := by
  constructor
  · intro hsh
    have hr : ∃ r0 : DY.Random.Random DY.Bytes, randTerm ts sz = DY.BytesView.pack r0 := ⟨_, rfl⟩
    rcases hr with ⟨r0, hr0⟩
    rcases gamma'_shape_cases i S g u with
      ⟨_, h⟩ | ⟨_, _, h⟩ | ⟨r, _, rfl, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
      ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩
    · rw [h, hr0] at hsh
      have hv2 := congrArg (fun b : DY.Bytes => b.view? DY.Random.Random) hsh
      simp [DY.BytesView.view_pack] at hv2
    all_goals try (
      rw [h, hr0] at hsh
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hsh))
    rw [h] at hsh
    exact hsh
  · rintro rfl
    unfold randTerm
    rw [gamma'_pack_random]
    dsimp only [concretizeRandom]
    simp only [hsz, ↓reduceIte]; rfl

end ShapeInversion

unseal DY.Bytes in
/-- `(gamma' interp S g t).shape = PQKem.kemRejKey skSh ctSh` iff `t = PQKem.kemRejKey sk ct`
with matching child shapes. -/
theorem shape_eq_kemRejKey_pack_iff {interp : ExternInterpretation} {S : OpaqueSymbolSemantics}
    {g : Ghost} {t skSh ctSh : DY.Bytes} :
    (gamma' interp S g t).shape = DY.PQKem.kemRejKey skSh ctSh ↔
      ∃ sk ct : DY.Bytes,
        t = DY.PQKem.kemRejKey sk ct ∧
        (gamma' interp S g sk).shape = skSh ∧
        (gamma' interp S g ct).shape = ctSh := by
  constructor
  · intro hsh
    rw [kemRejKey_eq_pack] at hsh
    rcases gamma'_shape_cases interp S g t with
      ⟨w, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ |
      ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ | ⟨⟨sk', ct'⟩, rfl, h⟩ | ⟨_, h⟩
    · rw [h] at hsh; exact False.elim (litOf_ne_kemRejKey_pack w _ hsh)
    all_goals try (
      rw [h] at hsh
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hsh))
    rw [h] at hsh
    have hinj := kemRejKey_pack_inj hsh
    injection hinj with hs_eq hc_eq
    exact ⟨sk', ct', rfl, hs_eq, hc_eq⟩
  · rintro ⟨sk', ct', rfl, rfl, rfl⟩
    rw [gamma'_kemRejKey_eq interp S g sk' ct']
    rfl

/-! ## KEM Twin Canonicalization and Bob's KEM Share -/

section TwinAndCollision

variable (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)

/-- Shape equality against a 32-byte `SharedSecret` forces the other term to be a 32-byte
`SharedSecret` with matching `pk` and `entropy` shapes. -/
theorem eq_kemSS_of_shape_eq_kemSS_len32 {u pk₁ e₁ : DY.Bytes}
    (h32 : (gamma i S g e₁).length = 32)
    (hsh : (gamma' i S g u).shape = (gamma' i S g (DY.PQKem.kemEncap pk₁ e₁).2).shape) :
    ∃ pk₂ e₂ : DY.Bytes,
      u = (DY.PQKem.kemEncap pk₂ e₂).2 ∧
      (gamma i S g e₂).length = 32 ∧
      (gamma' i S g pk₂).shape = (gamma' i S g pk₁).shape ∧
      (gamma' i S g e₂).shape = (gamma' i S g e₁).shape := by
  rw [gamma'_kemSS_of_len32 i S g h32] at hsh
  dsimp only [node] at hsh
  exact (shape_eq_kemSS_pack_iff i S g u (gamma' i S g pk₁).shape (gamma' i S g e₁).shape).mp hsh

/-- Timestamp equality for two `SharedSecret` terms with 32-byte random entropies and equal shapes. -/
theorem kemSS_rand32_twin_ts_eq {pk₁ pk₂ : DY.Bytes} {ts₁ ts₂ : Nat}
    (h32₁ : (gamma i S g (randTerm ts₁ 32)).length = 32)
    (hsh : (gamma' i S g (DY.PQKem.kemEncap pk₁ (randTerm ts₁ 32)).2).shape =
           (gamma' i S g (DY.PQKem.kemEncap pk₂ (randTerm ts₂ 32)).2).shape) :
    ts₁ = ts₂ := by
  obtain ⟨pk', e₂', hu_eq, _, _, he_sh⟩ :=
    eq_kemSS_of_shape_eq_kemSS_len32 i S g h32₁ hsh.symm
  obtain ⟨_, rfl⟩ := kemEncap_snd_inj hu_eq
  have hsz : (32 : Nat) ≠ 0 := by decide
  rw [(shape_eq_randTerm_iff i S g (randTerm ts₁ 32) hsz).mpr rfl] at he_sh
  have he_eq : randTerm ts₂ 32 = randTerm ts₁ 32 :=
    (shape_eq_randTerm_iff i S g (randTerm ts₂ 32) hsz).mp he_sh
  exact (randTerm_inj he_eq).1.symm

end TwinAndCollision

private theorem setupPublic_6_eq_kemPk (r : ProtocolSetup) (halice : r.alice ≠ r.bob) :
    setupPublic r 6 = DY.PQKem.kemPk (setupSecret r 4) := by
  have hs4 : setupSecret r 4 = randTerm 16 64 := by
    rw [setupSecret, Symbolic.Swarm.CREF.TR.setupRandoms_eq r halice]
    cases r.withOpk <;> rfl
  rw [hs4]
  have hlen4 : (Symbolic.Swarm.CREF.TR.setupTr4 r.alice r.bob).length = 22 := by
    simp only [Symbolic.Swarm.CREF.TR.setupTr4, Symbolic.Swarm.CREF.TR.setupTr3,
      Symbolic.Swarm.CREF.TR.setupTr2, Symbolic.Swarm.CREF.TR.setupTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hlen5 : (Symbolic.Swarm.CREF.TR.setupTr5 r.alice r.bob).length = 26 := by
    simp only [Symbolic.Swarm.CREF.TR.setupTr5, Symbolic.Swarm.CREF.TR.setupTr4,
      Symbolic.Swarm.CREF.TR.setupTr3, Symbolic.Swarm.CREF.TR.setupTr2,
      Symbolic.Swarm.CREF.TR.setupTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
  have hr22 : List.range' 0 (22 - 0) =
      [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21] := rfl
  have hr26 : List.range' 0 (26 - 0) =
      [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25] := rfl
  rw [setupPublic, setupSent, Symbolic.Swarm.CREF.TR.setupTrace_eq r halice]
  cases r.withOpk
  · simp only [Bool.false_eq_true, ↓reduceIte, newIndices,
      Symbolic.DYBridge.DY.Trace.length_eq_1, hlen4, hr22,
      List.filterMap_cons, List.filterMap_nil]
    simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
      Symbolic.Swarm.CREF.TR.setupTr4, Symbolic.Swarm.CREF.TR.setupTr3,
      Symbolic.Swarm.CREF.TR.setupTr2, Symbolic.Swarm.CREF.TR.setupTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1,
      DY.Trace.at?, Symbolic.DYBridge.DY.Trace.at_eq_2,
      Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
    rfl
  · simp only [↓reduceIte, newIndices,
      Symbolic.DYBridge.DY.Trace.length_eq_1, hlen5, hr26,
      List.filterMap_cons, List.filterMap_nil]
    simp [Symbolic.DYBridge.DY.Trace.getMessageSentAt_eq_1,
      Symbolic.Swarm.CREF.TR.setupTr5, Symbolic.Swarm.CREF.TR.setupTr4,
      Symbolic.Swarm.CREF.TR.setupTr3, Symbolic.Swarm.CREF.TR.setupTr2,
      Symbolic.Swarm.CREF.TR.setupTr1,
      Symbolic.DYBridge.DY.Trace.append_eq_1,
      DY.Trace.at?, Symbolic.DYBridge.DY.Trace.at_eq_2,
      Symbolic.DYBridge.DY.Trace.length_eq_1,
      Symbolic.DYBridge.DY.Trace.length_eq_2]
    rfl

/-- Unconditional concretization of Bob's KEM share (`SharedSecret` on valid `Encap` or `kemRejKey`
on implicit rejection): both branches evaluate to `(kyberDecapsBytes interp r (gamma interp S g ct)).getD []`
whenever `GhostAndSemMatchSetup`, `¬ KyberMismatch`, and `(gamma interp S g ct).length = 1568` hold. -/
theorem gamma_bobKemShare {interp : ExternInterpretation} {r : ProtocolSetup}
    {S : OpaqueSymbolSemantics} {g : Ghost} {p : PreKeyFields} {ct : DY.Bytes}
    (halice : r.alice ≠ r.bob) (hsetup : GhostAndSemMatchSetup interp r S g)
    (hnkm : ¬ KyberMismatch interp r p)
    (hct_p : p.kyberCiphertext = some (kyberKey (gamma interp S g ct)))
    (hct_len : (gamma interp S g ct).length = 1568) :
    gamma interp S g ((DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap (setupSecret r 4) ct)).getD
        (DY.PQKem.kemRejKey (setupSecret r 4) ct)) =
      (kyberDecapsBytes interp r (gamma interp S g ct)).getD [] := by
  have hp6 : setupPublic r 6 = DY.PQKem.kemPk (setupSecret r 4) :=
    setupPublic_6_eq_kemPk r halice
  have hpk_gamma : gamma interp S g (DY.PQKem.kemPk (setupSecret r 4)) =
      r.opaqueBytes (setupPublic r 6) := by
    rw [← hp6]
    exact hsetup.2.1 r.pqpkPubTerm (by simp)
  cases hdec : DY.Libsignal.PQXDH.errToOption (DY.PQKem.kemDecap (setupSecret r 4) ct) with
  | none =>
    dsimp only [Option.getD]
    rw [gamma_kemRejKey_eq, ← gamma_kemPk_eq, hpk_gamma]
    exact hsetup.2.2 _
  | some ss =>
    dsimp only [Option.getD]
    obtain ⟨eTerm, hct_eq, hss_eq⟩ := errToOption_kemDecap_eq_some_iff.mp hdec
    have hct_gamma :
        (if (gamma interp S g eTerm).length = 32 then
          ((interp kyberEncapsSymbol
            [r.opaqueBytes (setupPublic r 6), gamma interp S g eTerm]).getD []).take 1568
         else []) = gamma interp S g ct := by
      conv_rhs => rw [hct_eq, gamma_kemEncap_fst, hpk_gamma]
    have hss_gamma : gamma interp S g ss =
        if (gamma interp S g eTerm).length = 32 then
          ((interp kyberEncapsSymbol
            [r.opaqueBytes (setupPublic r 6), gamma interp S g eTerm]).getD []).drop 1568
        else S.kemDecap (r.opaqueBytes (setupPublic r 6)) (gamma interp S g eTerm) := by
      rw [hss_eq, gamma_kemEncap_snd, hpk_gamma]
    have he_len : (gamma interp S g eTerm).length = 32 := by
      by_cases h32 : (gamma interp S g eTerm).length = 32
      · exact h32
      · simp only [h32, ↓reduceIte] at hct_gamma
        rw [← hct_gamma] at hct_len
        simp at hct_len
    simp only [he_len, ↓reduceIte] at hct_gamma hss_gamma
    have henc : kyberEncapsBytes interp r (gamma interp S g eTerm) =
        some (gamma interp S g ct, gamma interp S g ss) := by
      unfold kyberEncapsBytes
      rw [show r.pqpkPubTerm = setupPublic r 6 from rfl]
      cases hout : interp kyberEncapsSymbol
          [r.opaqueBytes (setupPublic r 6), gamma interp S g eTerm] with
      | none =>
        rw [hout] at hct_gamma
        simp at hct_gamma
        rw [hct_gamma] at hct_len
        simp at hct_len
      | some out =>
        rw [hout] at hct_gamma hss_gamma
        dsimp only [Option.getD] at hct_gamma hss_gamma
        rw [← hct_gamma, hss_gamma]
        rfl
    have hdec_eq : kyberDecapsBytes interp r (gamma interp S g ct) =
        some (gamma interp S g ss) := by
      refine Classical.byContradiction fun hne => hnkm ?_
      exact ⟨gamma interp S g eTerm, gamma interp S g ct, gamma interp S g ss,
        he_len, hct_p, henc, hne⟩
    rw [hdec_eq]

end Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
