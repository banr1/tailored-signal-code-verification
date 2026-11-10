/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.CaseSplit
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Actions.Random
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Init.Data.String.Defs
public import Symbolic.Proofs.Swarm.CREF.TR.G1.MacKdfSafeTR
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

/-!
# Attacker-Known HMAC Branch (`g1c_own_key_branch'`)

Proves `kdfExtract_shape_eq_inv_c` and the three-stage KDF inversion `hmac_wire_attackerKnows_inv`:
if a received MAC is `trunc8 inp₀` with `inp₀` attacker-known and matching the shape of the
receiver's HMAC input, then under `G1cAttackerBuiltSeedExcl'` the receiver's Double Ratchet seed is
attacker-known (`g1c_own_key_branch'`).
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR.G1

cref_open
open DY.Libsignal.TripleRatchet (TRState TRSignalMsg parseTrSignalMsg)

open DY DY.Comparse DY.DiffieHellman
open DY.Libsignal (HwBytes)
open DY.Libsignal.TripleRatchet (RecvChain consumeMessageKey lit litByte)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR.RecvDecStep

/-! ## `KdfExtract`-headed shape inversion -/

def KdfViewMotive (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (sh_s sh_i : DY.Bytes) (u : DY.Bytes) : Prop :=
  DY.Bytes.view? (gamma' interpretation S g u).shape DY.KdfExtract.KdfExtract.SubF =
      some { salt := sh_s, ikm := sh_i } →
    ∃ s i : DY.Bytes,
      u = KdfExtract.kdfExtract s i ∧
      (gamma' interpretation S g s).shape = sh_s ∧
      (gamma' interpretation S g i).shape = sh_i

private theorem container_pack_inj_sub
    (f g : Type → Type)
    [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g]
    (x : f (DY.ALaCarte.ContainerFor g)) :
    DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x) =
      DY.ALaCarte.Container.pack f x := by
  have hv := DY.ALaCarte.Container.pack_view g (DY.ALaCarte.Container.pack f x)
  rw [Symbolic.DYBridge.DY.ALaCarte.Container.view_pack_cross f g x] at hv
  exact hv

private theorem lift_partialFunDep
    {f g : Type → Type} [DY.ALaCarte.FunctorSizeOf f] [DY.ALaCarte.FunctorSizeOf g]
    [DY.ALaCarte.SubFunctorTC f g] [DY.ALaCarte.Representable g]
    {motive : DY.ALaCarte.ContainerFor g → Prop}
    (h : DY.ALaCarte.Container.PartialFunDep f (g := g) motive)
    (x : f (DY.ALaCarte.ContainerFor g))
    (rec : ∀ y : DY.ALaCarte.ContainerFor g,
      sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf (DY.ALaCarte.SubFunctorTC.inj (g := g) x) → motive y) :
    motive (DY.ALaCarte.Container.pack g (DY.ALaCarte.SubFunctorTC.inj (g := g) x)) := by
  rw [container_pack_inj_sub f g x]
  exact h x fun y hy => rec y (DY.ALaCarte.SubFunctorTC.sizeOf_inj (g := g) x ▸ hy)

unseal DY.Bytes in
theorem partialFunDep_not_kdf
    {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_s sh_i : DY.Bytes)
    (gF : DY.Bytes.PartialFunction SubF ConcretizedTerm) [DY.Bytes.SubFunction gF (concretizeAll interpretation S g)]
    (hg : ∀ (x : SubF DY.Bytes) (rec : ∀ y : DY.Bytes, sizeOf y ≤ DY.ALaCarte.FunctorSizeOf.sizeOf x → ConcretizedTerm),
      DY.Bytes.view? (gF x rec).shape DY.KdfExtract.KdfExtract.SubF = none) :
    DY.ALaCarte.Container.PartialFunDep SubF (g := DY.BytesF)
      (KdfViewMotive interpretation S g sh_s sh_i) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll interpretation S g)).shape
    DY.KdfExtract.KdfExtract.SubF = _ at hview
  rw [DY.Bytes.rec_eq gF (concretizeAll interpretation S g) x, hg x _] at hview
  contradiction

unseal DY.Bytes in
theorem partialFunDep_kdf
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (sh_s sh_i : DY.Bytes) :
    DY.ALaCarte.Container.PartialFunDep DY.KdfExtract.KdfExtract.SubF (g := DY.BytesF)
      (KdfViewMotive interpretation S g sh_s sh_i) := by
  intro x _ hview
  rw [← Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x] at hview
  change DY.Bytes.view? ((BytesView.pack x).rec (concretizeAll interpretation S g)).shape
    DY.KdfExtract.KdfExtract.SubF = _ at hview
  rw [DY.Bytes.rec_eq (concretizeKdf interpretation) (concretizeAll interpretation S g) x] at hview
  dsimp only [concretizeKdf, node] at hview
  rw [DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF)] at hview
  injection hview with h1
  cases h1
  exact ⟨x.salt, x.ikm, (Symbolic.DYBridge.DY.BytesView.pack_eq_container_pack x).symm, rfl, rfl⟩

private theorem litOf_view?_kdf_none (bs : HwBytes) :
    DY.Bytes.view? (litOf bs) DY.KdfExtract.KdfExtract.SubF = none :=
  Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _

unseal DY.Bytes in
private instance subKemRejOKB (i : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKemRej S) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kemFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
theorem view?_kdfExtract_shape_eq_some
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (u sh_s sh_i : DY.Bytes) :
    KdfViewMotive interpretation S g sh_s sh_i u := by
  · refine DY.ALaCarte.Container.rec (f := DY.BytesF)
      (motive := KdfViewMotive interpretation S g sh_s sh_i) ?_ u
    rintro ⟨⟨id, hid⟩, val⟩ rec
    match id with
    | 0 =>
      exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeRandom g)
        (fun _ _ => by dsimp only [concretizeRandom]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) val rec
    | 1 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i concretizeLit (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | n + 1 => omega
    | 2 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i concretizeConcat (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | n + 1 => omega
    | 3 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeDhPk interpretation) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | 1 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeDh interpretation) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | n + 2 => omega
    | 4 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_kdf interpretation S g sh_s sh_i) v rec
      | n + 1 => omega
    | 5 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeSym interpretation) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | n + 1 => omega
    | 6 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i concretizeTrunc (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | n + 1 => omega
    | 7 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeVariant interpretation) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | n + 1 => omega
    | 8 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeKemPk S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | 1 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeKemEncap interpretation) (fun _ _ => by dsimp only [concretizeKemEncap]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | 2 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeKemSS interpretation S) (fun _ _ => by dsimp only [concretizeKemSS]; split <;> exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | 3 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeKemRej S) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | n + 4 => omega
    | 9 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeVk S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | 1 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeSign S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | n + 2 => omega
    | 10 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeSpqrInit S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | 1 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeSpqrSendState S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | 2 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeSpqrSendKey S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | 3 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeSpqrSendMsg S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | 4 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeSpqrRecvState S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | 5 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeSpqrRecvKey S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | 6 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeSpqrChainKey S) (fun _ _ => litOf_view?_kdf_none _)) v rec
      | n + 7 => omega
    | 11 =>
      rcases val with ⟨⟨sid, hsid⟩, v⟩
      match sid with
      | 0 => exact lift_partialFunDep (partialFunDep_not_kdf interpretation S g sh_s sh_i (concretizeTrWire g) (fun _ _ => Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.KdfExtract.KdfExtract.SubF _)) v rec
      | n + 1 => omega

/-- If `(gamma' u).shape` equals `(gamma' (kdfExtract s₁ i₁)).shape`, then `u = kdfExtract s₀ i₀`
with matching child shapes. -/
theorem kdfExtract_shape_eq_inv_c
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {u s₁ i₁ : DY.Bytes}
    (hsh : (gamma' interpretation S g u).shape =
      (gamma' interpretation S g (KdfExtract.kdfExtract s₁ i₁)).shape) :
    ∃ s₀ i₀ : DY.Bytes,
      (gamma' interpretation S g s₀).shape = (gamma' interpretation S g s₁).shape ∧
      (gamma' interpretation S g i₀).shape = (gamma' interpretation S g i₁).shape ∧
      u = KdfExtract.kdfExtract s₀ i₀ := by
  have hview : DY.Bytes.view? (gamma' interpretation S g u).shape DY.KdfExtract.KdfExtract.SubF =
      some { salt := (gamma' interpretation S g s₁).shape,
             ikm := (gamma' interpretation S g i₁).shape } := by
    rw [hsh, shape_kdfExtract_tr]
    exact DY.BytesView.view_pack (SubF := DY.KdfExtract.KdfExtract.SubF) _
  obtain ⟨s₀, i₀, hu, hs, hi⟩ := view?_kdfExtract_shape_eq_some interpretation S g u _ _ hview
  exact ⟨s₀, i₀, hs, hi, hu⟩

/-! ## `recvSeed` structure and shape disjointness -/

theorem consumeMessageKey_eq_some_kdfExtract
    {c c' : RecvChain} {counter : UInt32} {seed : DY.Bytes}
    (h : consumeMessageKey c counter = some (seed, c')) :
    ∃ ck : DY.Bytes, seed = KdfExtract.kdfExtract ck (litByte 0x01) := by
  unfold consumeMessageKey at h
  split at h <;> [cases h; (split at h <;> [cases h; (split at h <;> [cases h; skip])])]
  injection h with h
  injection h with hseed _
  exact ⟨_, hseed.symm⟩

/-- Every seed returned by `recvSeed` has the form `KdfExtract.kdfExtract ck (litByte 0x01)`. -/
theorem recvSeed_eq_some_kdfExtract
    {st : TRState} {msg : TRSignalMsg} {seed : DY.Bytes}
    (hseed : recvSeed st msg = some seed) :
    ∃ ck : DY.Bytes, seed = KdfExtract.kdfExtract ck (litByte 0x01) := by
  unfold recvSeed at hseed
  split at hseed
  · split at hseed
    · cases hseed
    · simp only [Option.map_eq_some_iff] at hseed
      obtain ⟨⟨s, c'⟩, hcmk, rfl⟩ := hseed
      exact consumeMessageKey_eq_some_kdfExtract hcmk
  · cases hseed

unseal DY.Bytes in
theorem literal_ne_concat (b : ByteArray) (l r : DY.Bytes) :
    Literal.literalToBytes b ≠ Concat.concat l r := by
  intro h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

unseal DY.Bytes in
theorem literal_ne_trWireMsg (b : ByteArray) (v : UInt8) (rk : DY.Bytes) (c pc : UInt32)
    (ct pq : DY.Bytes) (ev : DY.TrWire.EncodingVariation) :
    Literal.literalToBytes b ≠ DY.TrWire.trWireMsg v rk c pc ct pq ev := by
  intro h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

unseal DY.Bytes in
theorem literal_ne_kdfExtract (b : ByteArray) (s i : DY.Bytes) :
    Literal.literalToBytes b ≠ KdfExtract.kdfExtract s i := by
  intro h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

unseal DY.Bytes in
theorem concat_ne_kdfExtract (l r s i : DY.Bytes) :
    Concat.concat l r ≠ KdfExtract.kdfExtract s i := by
  intro h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

theorem lit_whisperRatchet_ne_whisperMessageKeys :
    lit "WhisperRatchet" ≠ lit "WhisperMessageKeys" := by
  intro h
  have h1 : (lit "WhisperRatchet").length = 14 := by
    unfold lit
    rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
        ← String.ofList_toList (s := "WhisperRatchet"), String.toByteArray_ofList]
    decide
  have h2 : (lit "WhisperMessageKeys").length = 18 := by
    unfold lit
    rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
        ← String.ofList_toList (s := "WhisperMessageKeys"), String.toByteArray_ofList]
    decide
  rw [h, h2] at h1
  cases h1

theorem pqxdhLabel_ne_whisperMessageKeys :
    DY.Libsignal.PQXDH.pqxdhLabel ≠ lit "WhisperMessageKeys" := by
  intro h
  have h1 : DY.Libsignal.PQXDH.pqxdhLabel.length = 46 := by
    unfold DY.Libsignal.PQXDH.pqxdhLabel lit
    rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
        ← String.ofList_toList (s := "WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024"),
        String.toByteArray_ofList]
    decide
  have h2 : (lit "WhisperMessageKeys").length = 18 := by
    unfold lit
    rw [Literal.length_literalToBytes, String.toUTF8_eq_toByteArray,
        ← String.ofList_toList (s := "WhisperMessageKeys"), String.toByteArray_ofList]
    decide
  rw [h, h2] at h1
  cases h1

/-! ## Three-stage KDF inversion -/

theorem parseTrSignalMsg_unpack_c {t : DY.Bytes} {msg : TRSignalMsg}
    (h : parseTrSignalMsg t = some msg) :
    ∃ x : TrWire.TrWireMsg.SubF DY.Bytes,
      Concat.split t (t.length - Trunc.trunc8Length) = some (msg.wire, msg.mac) ∧
      TrWire.trWireMsgFields? msg.wire = some x ∧ msg.wire = x.pack ∧
      msg.ratchetKey = x.senderRatchetKey ∧ msg.ciphertext = x.ciphertext ∧
      msg.pqRatchet = x.pqRatchet := by
  unfold parseTrSignalMsg at h
  simp only [Bind.bind, Option.bind_eq_some_iff, Pure.pure, Option.some.injEq] at h
  rcases h with ⟨⟨wire, mac⟩, hsplit, x, hx, rfl⟩; dsimp only at hx ⊢
  exact ⟨x, hsplit, hx, TrWire.trWireMsg_of_fields? hx, rfl, rfl, rfl⟩

/-- Valid input shapes for an attacker-known `kdfExtract s i` on a reachable composed trace: either
both inputs are attacker-known, or `i` is a Double Ratchet or PQXDH key-derivation label. -/
def KdfInputValidC (T : ExecTrace) (s i : DY.Bytes) : Prop :=
  (s.AttackerKnows T ∧ i.AttackerKnows T) ∨
  i = litByte 0x01 ∨
  i = litByte 0x02 ∨
  i = Concat.concat (lit "WhisperRatchet") (litByte 1) ∨
  ∃ b1, IsRatchetOrPqxdhBlock23 b1 i

theorem macKdfSafe_c_kdfExtract_inv (r₀ : ProtocolSetup) (ms : List Move) (s i : DY.Bytes)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (hknows : (KdfExtract.kdfExtract s i).AttackerKnows (runTraceMoves r₀ ms)) :
    KdfInputValidC (runTraceMoves r₀ ms) s i := by
  rcases macKdfSafe_tr_kdfExtract_inv r₀ ms s i hreach hknows with
    h1 | ⟨h2, _⟩ | h3 | h4 | h5
  · exact .inl h1
  · exact .inr (.inl h2)
  · exact .inr (.inr (.inl h3))
  · exact .inr (.inr (.inr (.inl h4)))
  · exact .inr (.inr (.inr (.inr h5)))

/-! ## Attacker-built seed exclusion and `g1c_own_key_branch'` -/

/-- Hypothesis excluding a collision-free received representation `t₀` from reaching `G1cOwnKeyCaseB3`
(`msg₀.mac = trunc8 inp₀` with `inp₀` attacker-known and matching the shape of the receiver's HMAC
input) when the receiver's seed `mkSeed` is not attacker-known. -/
def G1cAttackerBuiltSeedExcl' (interpretation : ExternInterpretation) (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics)
    (g : Ghost) (ms : List Move) : Prop :=
  ∀ (b : HwBytes) (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (st₀ : TRState)
    (mkSeed k_own : DY.Bytes),
    (runTraceMoves r₀ ms).Reachable reachability →
    t₀ ∈ recvRepresentations interpretation r₀ S g ms b →
    parseTrSignalMsg t₀ = some msg₀ →
    ¬RecvCollision interpretation r₀ S g ms t₀ →
    st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms) →
    recvSeed st₀ msg₀ = some mkSeed →
    ¬mkSeed.AttackerKnows (runTraceMoves r₀ ms) →
    G1cOwnKeyCaseB3 interpretation r₀ S g ms msg₀ st₀ mkSeed k_own →
    False

/-- Discharges the attacker-known HMAC branch (`G1cOwnKeyCaseB3`) from `G1cAttackerBuiltSeedExcl'`. -/
theorem g1c_own_key_branch'
    (interpretation : ExternInterpretation)
    (r₀ : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (b ptext : HwBytes)
    (hABS' : G1cAttackerBuiltSeedExcl' interpretation r₀ S g ms)
    (hreach : (runTraceMoves r₀ ms).Reachable reachability)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g ms b)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t₀)
    (st₀ : TRState) (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms))
    (mkSeed : DY.Bytes) (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (k_own : DY.Bytes)
    (hCaseC : G1cOwnKeyCaseB3 interpretation r₀ S g ms msg₀ st₀ mkSeed k_own) :
    mkSeed.AttackerKnows (runTraceMoves r₀ ms) ∨
    AuthenticDecryptRepB3_g1 interpretation r₀ S g ms b ptext msg₀ st₀ mkSeed k_own := by
  by_cases hSeedKnows : mkSeed.AttackerKnows (runTraceMoves r₀ ms)
  · exact Or.inl hSeedKnows
  · exact (hABS' b t₀ msg₀ st₀ mkSeed k_own hreach ht₀ hparse₀ hNotCol hst₀ hseed hSeedKnows
      hCaseC).elim

end Symbolic.Swarm.CREF.TR.G1
