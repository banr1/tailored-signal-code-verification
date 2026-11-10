/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Security.Model
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Trace.Basic
import DY.Trace.Monad
import DY.Trace.Manipulation
import DY.Trace.BaseAttackerKnowledge
import DY.Actions.Network
import DY.Actions.PersistentLocalState
import DY.Actions.PersistentGlobalState
import DY.Actions.ProtocolEvent
import DY.Actions.Random
import DY.Bytes.AttackerKnowledge
import DY.EquationalTheory.Literal
import DY.EquationalTheory.Concat
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.SymEnc
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Kem
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
public import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.X25519
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.COMPOSED.CompTermAlgebra
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.Sign

/-!
# Composed Attacker-Knowledge Over-Approximation and Schedule Inversion

Defines the KDF salt-spine depth `saltDepth`, chain-root injectivity (`IsChainRoot`,
`chainKeyAt_root_inj`), and the parameterized inductive over-approximation `CompTrClosed E` of
composed Dolev-Yao attacker knowledge (`CompTrClosed.attackerKnowledge_implies`). Proves KDF,
chain-key, and hybrid cipher-key inversion lemmas (`CompTrClosed.inv_chainKeyAt`,
`CompTrClosed.inv_trKeyKnown`).
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.COMPOSED.CompRatchet

open DY DY.Comparse DY.DiffieHellman DY.KdfExtract DY.Concat DY.Literal DY.SymEnc DY.Trunc
open DY.X25519 DY.Spqr DY.TrWire DY.PQKem DY.Signature
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet
open DY.Libsignal.TripleRatchet.Cheval
open DY.Libsignal.PQXDH hiding x25519LowOrder
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Security
open Symbolic.Swarm.COMPOSED.CompTermAlgebra

/-! ## KDF salt-spine depth and chain-root injectivity -/

section SizeOfPos
unseal Bytes
attribute [local instance_reducible] Bytes
private theorem bytes_sizeOf_pos (b : Bytes) : 1 ≤ sizeOf b := by
  cases b with
  | mk val prop =>
    change 1 ≤ sizeOf (Subtype.mk val prop)
    rw [Subtype.mk.sizeOf_spec val prop]
    omega
end SizeOfPos

set_option linter.unusedVariables false in
/-- Number of `kdfExtract` (`hmac`) applications along the left (`salt`) spine of a symbolic term. -/
def saltDepth (b : Bytes) : Nat :=
  match h : b.view? KdfExtract.KdfExtract.SubF with
  | some v => saltDepth v.salt + 1
  | none => 0
termination_by sizeOf b
decreasing_by
  have hsz := Bytes.sizeOf_view KdfExtract.KdfExtract.SubF b; rw [h] at hsz
  have hpos : 1 ≤ sizeOf v.ikm := bytes_sizeOf_pos v.ikm
  change sizeOf v.salt + sizeOf v.ikm ≤ sizeOf b at hsz; omega

@[simp] theorem saltDepth_kdfExtract (salt ikm : Bytes) :
    saltDepth (kdfExtract salt ikm) = saltDepth salt + 1 := by
  conv => lhs; unfold saltDepth
  split
  · rename_i v hv
    dsimp [kdfExtract] at hv
    rw [BytesView.view_pack] at hv
    injection hv with hv
    cases hv
    rfl
  · rename_i hv
    dsimp [kdfExtract] at hv
    rw [BytesView.view_pack] at hv
    cases hv

@[simp] theorem saltDepth_hmac (k m : Bytes) : saltDepth (hmac k m) = saltDepth k + 1 :=
  saltDepth_kdfExtract k m
@[simp] theorem saltDepth_hkdfBlock1 (prk info : Bytes) :
    saltDepth (hkdfBlock1 prk info) = saltDepth prk + 1 := saltDepth_kdfExtract prk _
@[simp] theorem saltDepth_hkdfBlock2 (prk info : Bytes) :
    saltDepth (hkdfBlock2 prk info) = saltDepth prk + 1 := saltDepth_kdfExtract prk _
@[simp] theorem saltDepth_kdfRk_fst (rk dhOut : Bytes) :
    saltDepth (kdfRk rk dhOut).1 = saltDepth rk + 2 := by simp [kdfRk]
@[simp] theorem saltDepth_kdfRk_snd (rk dhOut : Bytes) :
    saltDepth (kdfRk rk dhOut).2 = saltDepth rk + 2 := by simp [kdfRk]
@[simp] theorem saltDepth_createChain_fst (rk pk sk : Bytes) :
    saltDepth (createChain rk pk sk).1 = saltDepth rk + 2 := by simp [createChain, DY.X25519.agree]
@[simp] theorem saltDepth_createChain_snd (rk pk sk : Bytes) :
    saltDepth (createChain rk pk sk).2 = saltDepth rk + 2 := by simp [createChain, DY.X25519.agree]
@[simp] theorem saltDepth_kdfCk_fst (ck : Bytes) :
    saltDepth (kdfCk ck).1 = saltDepth ck + 1 := by simp [kdfCk]
@[simp] theorem saltDepth_kdfCk_snd (ck : Bytes) :
    saltDepth (kdfCk ck).2 = saltDepth ck + 1 := by simp [kdfCk]

@[simp] theorem saltDepth_chainKeyAt (ck : Bytes) : ∀ n : Nat,
    saltDepth (chainKeyAt ck n) = saltDepth ck + n
  | 0 => by simp [chainKeyAt]
  | n + 1 => by simp only [chainKeyAt, saltDepth_chainKeyAt _ n, saltDepth_kdfCk_fst]; omega

@[simp] theorem saltDepth_zeroSalt : saltDepth zeroSalt = 0 := by
  unfold saltDepth
  split
  · rename_i v hv
    dsimp [zeroSalt, literalToBytes] at hv
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none KdfExtract.KdfExtract.SubF] at hv
    cases hv
  · rfl

@[simp] theorem saltDepth_pqxdhKdf_rk (ikm : Bytes) :
    saltDepth (pqxdhKdf ikm).rk = 2 := by simp [pqxdhKdf]
@[simp] theorem saltDepth_pqxdhKdf_ck (ikm : Bytes) :
    saltDepth (pqxdhKdf ikm).ck = 2 := by simp [pqxdhKdf]

/-- Symbolic random term at timestamp `ts` with size `sz`. -/
abbrev mkRand (ts sz : Nat) : Bytes :=
  BytesView.pack (SubF := Random.Random) { timestamp := ts, size := sz }

@[simp] theorem saltDepth_mkRand (ts sz : Nat) : saltDepth (mkRand ts sz) = 0 := by
  unfold saltDepth
  split
  · rename_i v hv
    rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none KdfExtract.KdfExtract.SubF] at hv
    cases hv
  · rfl

theorem mkRand_inj {t₁ s₁ t₂ s₂ : Nat} (h : mkRand t₁ s₁ = mkRand t₂ s₂) :
    t₁ = t₂ ∧ s₁ = s₂ := by
  have hv := congrArg (fun b : Bytes => b.view? Random.Random) h
  simp only [mkRand, BytesView.view_pack, Option.some.injEq, Random.Random.mk.injEq] at hv
  exact hv

theorem kdfCk_fst_ne_snd (ck₁ ck₂ : Bytes) : (kdfCk ck₁).1 ≠ (kdfCk ck₂).2 := by
  intro h; have hm := litByte_inj (hmac_inj h).2; revert hm; decide

/-- A chain root `ck₀` is not the `.1` step of any `kdfCk`. -/
def IsChainRoot (ck₀ : Bytes) : Prop := ∀ x, ck₀ ≠ (kdfCk x).1

theorem isChainRoot_mkRand (ts sz : Nat) : IsChainRoot (mkRand ts sz) :=
  fun _ h => by
    dsimp [mkRand, kdfCk, hmac, kdfExtract] at h
    exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

theorem isChainRoot_createChain_snd (rk pk sk : Bytes) :
    IsChainRoot (createChain rk pk sk).2 := by
  intro x h; obtain ⟨_, hikm⟩ := hmac_inj h
  dsimp [litByte, literalToBytes, concat] at hikm
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hikm

theorem isChainRoot_hkdfBlock2 (prk info : Bytes) :
    IsChainRoot (hkdfBlock2 prk info) := by
  intro x h; obtain ⟨_, hikm⟩ := hmac_inj h
  dsimp [litByte, literalToBytes, concat] at hikm
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hikm

theorem isChainRoot_pqxdhKdf_ck (ikm : Bytes) : IsChainRoot (pqxdhKdf ikm).ck :=
  isChainRoot_hkdfBlock2 (hmac zeroSalt ikm) pqxdhLabel

theorem chainKeyAt_root_inj {ck₁ ck₂ : Bytes} (h₁ : IsChainRoot ck₁) (h₂ : IsChainRoot ck₂) :
    ∀ {n₁ n₂ : Nat}, chainKeyAt ck₁ n₁ = chainKeyAt ck₂ n₂ → ck₁ = ck₂ ∧ n₁ = n₂
  | 0, 0, h => ⟨h, rfl⟩
  | 0, n₂ + 1, h => by rw [chainKeyAt_succ_eq_kdfCk_fst] at h; exact False.elim (h₁ _ h)
  | n₁ + 1, 0, h => by rw [chainKeyAt_succ_eq_kdfCk_fst] at h; exact False.elim (h₂ _ h.symm)
  | n₁ + 1, n₂ + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst, chainKeyAt_succ_eq_kdfCk_fst] at h
    obtain ⟨rfl, rfl⟩ := chainKeyAt_root_inj h₁ h₂ (kdfCk_fst_inj h); exact ⟨rfl, rfl⟩

/-! ## `IsAtomicExposure` and `CompTrClosed` -/

/-- `IsAtomicExposure E` means every term in `E` is atomic (`Random` or `KdfExtract`) and never
packs as `Concat`, `SymEnc.Enc`, `X25519.Variant`, `TrWireMsg`, or `Spqr` states. -/
def IsAtomicExposure (E : Bytes → Prop) : Prop :=
  ∀ b, E b →
    b.view? Concat.Concat.SubF = none ∧
    b.view? SymEnc.Enc.SubF = none ∧
    b.view? X25519.Variant.SubF = none ∧
    b.view? TrWire.TrWireMsg.SubF = none ∧
    b.view? Spqr.InitState.SubF = none ∧
    b.view? Spqr.SendState.SubF = none ∧
    b.view? Spqr.RecvState.SubF = none

theorem isAtomic_mkRand (ts sz : Nat) :
    (mkRand ts sz).view? Concat.Concat.SubF = none ∧
    (mkRand ts sz).view? SymEnc.Enc.SubF = none ∧
    (mkRand ts sz).view? X25519.Variant.SubF = none ∧
    (mkRand ts sz).view? TrWire.TrWireMsg.SubF = none ∧
    (mkRand ts sz).view? Spqr.InitState.SubF = none ∧
    (mkRand ts sz).view? Spqr.SendState.SubF = none ∧
    (mkRand ts sz).view? Spqr.RecvState.SubF = none := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

theorem isAtomic_kdfExtract (salt ikm : Bytes) :
    (kdfExtract salt ikm).view? Concat.Concat.SubF = none ∧
    (kdfExtract salt ikm).view? SymEnc.Enc.SubF = none ∧
    (kdfExtract salt ikm).view? X25519.Variant.SubF = none ∧
    (kdfExtract salt ikm).view? TrWire.TrWireMsg.SubF = none ∧
    (kdfExtract salt ikm).view? Spqr.InitState.SubF = none ∧
    (kdfExtract salt ikm).view? Spqr.SendState.SubF = none ∧
    (kdfExtract salt ikm).view? Spqr.RecvState.SubF = none := by
  dsimp [kdfExtract]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _

/-- Inductive over-approximation `CompTrClosed E` of attacker knowledge over the 12 sub-theories
of `DY.Libsignal.Composed` parameterized by an atomic exposure predicate `E`. -/
inductive CompTrClosed (E : Bytes → Prop) : Bytes → Prop where
  | exposed {b : Bytes} (h : E b) : CompTrClosed E b
  | literal (bs : ByteArray) : CompTrClosed E (literalToBytes bs)
  | dhPk (sk : Bytes) : CompTrClosed E (DiffieHellman.dhPk sk)
  | dhSk (sk pk : Bytes) (h : CompTrClosed E sk) :
      CompTrClosed E (({ sk := sk, pk := pk } : DiffieHellman.Dh.SubF Bytes).pack)
  | dhPeer (sk s : Bytes) (h : CompTrClosed E s) :
      CompTrClosed E (({ sk := sk, pk := DiffieHellman.dhPk s } : DiffieHellman.Dh.SubF Bytes).pack)
  | kemPk (sk : Bytes) : CompTrClosed E (PQKem.kemPk sk)
  | kemEncap (pk e : Bytes) : CompTrClosed E (PQKem.kemEncap pk e).1
  | kemSs (pk e : Bytes) (hpk : CompTrClosed E pk) (he : CompTrClosed E e) :
      CompTrClosed E (PQKem.kemEncap pk e).2
  | kemSsKey (sk e : Bytes) (hsk : CompTrClosed E sk) :
      CompTrClosed E (PQKem.kemEncap (PQKem.kemPk sk) e).2
  | kemRejKey {sk ct : Bytes} (hsk : CompTrClosed E sk) (hct : CompTrClosed E ct) :
      CompTrClosed E (({ sk := sk, cipher := ct } : PQKem.RejKey.SubF Bytes).pack)
  | vk (sk : Bytes) : CompTrClosed E (Signature.vk sk)
  | sign (sk nonce msg : Bytes) : CompTrClosed E (Signature.sign sk nonce msg)
  | trunc8 (m : Bytes) : CompTrClosed E (Trunc.trunc8 m)
  | kdf {salt ikm : Bytes} (hsalt : CompTrClosed E salt) (hikm : CompTrClosed E ikm) :
      CompTrClosed E (kdfExtract salt ikm)
  | concat {lhs rhs : Bytes} (hlhs : CompTrClosed E lhs) (hrhs : CompTrClosed E rhs) :
      CompTrClosed E (Concat.concat lhs rhs)
  | symEnc {k iv msg : Bytes} (hmsg : CompTrClosed E msg) :
      CompTrClosed E (SymEnc.symEnc k iv msg)
  | variant {key : Bytes} (v : Fin 4) {t : Fin 8} (hkey : CompTrClosed E key) :
      CompTrClosed E (({ key := key, variation := v, torsion := t } : X25519.Variant.SubF Bytes).pack)
  | trWireMsg {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes}
      {ev : TrWire.EncodingVariation}
      (hrk : CompTrClosed E rk) (hct : CompTrClosed E ct) (hpq : CompTrClosed E pq) :
      CompTrClosed E (TrWire.trWireMsg v rk c pc ct pq ev)
  | spqrInit {authKey params : Bytes}
      (hauth : CompTrClosed E authKey) (hparams : CompTrClosed E params) :
      CompTrClosed E (Spqr.spqrInit authKey params)
  | spqrChainKey (authKey params idx : Bytes) :
      CompTrClosed E (Spqr.spqrChainKey authKey params idx)
  | spqrSendState {st coins : Bytes}
      (hst : CompTrClosed E st) (hcoins : CompTrClosed E coins) :
      CompTrClosed E (({ st := st, coins := coins } : Spqr.SendState.SubF Bytes).pack)
  | spqrSendKey (st coins : Bytes) :
      CompTrClosed E (({ st := st, coins := coins } : Spqr.SendKey.SubF Bytes).pack)
  | spqrSendMsg (st coins : Bytes) :
      CompTrClosed E (({ st := st, coins := coins } : Spqr.SendMsg.SubF Bytes).pack)
  | spqrRecvState {st msg : Bytes}
      (hst : CompTrClosed E st) (hmsg : CompTrClosed E msg) :
      CompTrClosed E (({ st := st, msg := msg } : Spqr.RecvState.SubF Bytes).pack)
  | spqrRecvKey (st msg : Bytes) :
      CompTrClosed E (({ st := st, msg := msg } : Spqr.RecvKey.SubF Bytes).pack)

theorem CompTrClosed.mono {E E' : Bytes → Prop} (hEE' : ∀ b, E b → E' b)
    {b : Bytes} (h : CompTrClosed E b) : CompTrClosed E' b := by
  induction h with
  | exposed h => exact .exposed (hEE' _ h)
  | literal bs => exact .literal bs
  | dhPk sk => exact .dhPk sk
  | dhSk sk pk _ ih => exact .dhSk sk pk ih
  | dhPeer sk s _ ih => exact .dhPeer sk s ih
  | kemPk sk => exact .kemPk sk
  | kemEncap pk e => exact .kemEncap pk e
  | kemSs pk e _ _ ih1 ih2 => exact .kemSs pk e ih1 ih2
  | kemSsKey sk e _ ih => exact .kemSsKey sk e ih
  | kemRejKey _ _ ih1 ih2 => exact .kemRejKey ih1 ih2
  | vk sk => exact .vk sk
  | sign sk nonce msg => exact .sign sk nonce msg
  | trunc8 m => exact .trunc8 m
  | kdf _ _ ih1 ih2 => exact .kdf ih1 ih2
  | concat _ _ ih1 ih2 => exact .concat ih1 ih2
  | symEnc _ ih => exact .symEnc ih
  | variant v _ ih => exact .variant v ih
  | trWireMsg _ _ _ ih1 ih2 ih3 =>
    exact .trWireMsg ih1 ih2 ih3
  | spqrInit _ _ ih1 ih2 => exact .spqrInit ih1 ih2
  | spqrChainKey authKey params idx => exact .spqrChainKey authKey params idx
  | spqrSendState _ _ ih1 ih2 => exact .spqrSendState ih1 ih2
  | spqrSendKey st coins => exact .spqrSendKey st coins
  | spqrSendMsg st coins => exact .spqrSendMsg st coins
  | spqrRecvState _ _ ih1 ih2 => exact .spqrRecvState ih1 ih2
  | spqrRecvKey st msg => exact .spqrRecvKey st msg

theorem CompTrClosed.dh {E : Bytes → Prop} {pk sk : Bytes} (hsk : CompTrClosed E sk) :
    CompTrClosed E (DiffieHellman.dh pk sk) := by
  dsimp only [DiffieHellman.dh, DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 _
    split
    · exact .dhSk sk (DiffieHellman.dhPk sk2) hsk
    · exact .dhPeer sk2 sk hsk
  · exact .dhSk sk pk hsk

theorem CompTrClosed.inv_kdfExtract {E : Bytes → Prop} {salt ikm : Bytes}
    (h : CompTrClosed E (kdfExtract salt ikm)) :
    E (kdfExtract salt ikm) ∨ (CompTrClosed E salt ∧ CompTrClosed E ikm) := by
  generalize hq : kdfExtract salt ikm = q at h
  cases h with
  | exposed hexp => exact .inl hexp
  | kdf hsalt hikm =>
    obtain ⟨rfl, rfl⟩ := kdfExtract_inj hq
    exact .inr ⟨hsalt, hikm⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_kdfExtract_salt {E : Bytes → Prop} {salt ikm : Bytes}
    (h : CompTrClosed E (kdfExtract salt ikm)) :
    E (kdfExtract salt ikm) ∨ CompTrClosed E salt :=
  (CompTrClosed.inv_kdfExtract h).imp id And.left

theorem CompTrClosed.inv_kdfExtract_ikm {E : Bytes → Prop} {salt ikm : Bytes}
    (h : CompTrClosed E (kdfExtract salt ikm)) :
    E (kdfExtract salt ikm) ∨ CompTrClosed E ikm :=
  (CompTrClosed.inv_kdfExtract h).imp id And.right

theorem CompTrClosed.inv_rnd {E : Bytes → Prop} {t n : Nat}
    (h : CompTrClosed E (BytesView.pack (SubF := Random.Random) { timestamp := t, size := n })) :
    E (BytesView.pack (SubF := Random.Random) { timestamp := t, size := n }) := by
  generalize hq :
    BytesView.pack (SubF := Random.Random) { timestamp := t, size := n } = q at h
  cases h with
  | exposed hexp => exact hexp
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_concat {E : Bytes → Prop} (hE : IsAtomicExposure E) {lhs rhs : Bytes}
    (h : CompTrClosed E (Concat.concat lhs rhs)) :
    CompTrClosed E lhs ∧ CompTrClosed E rhs := by
  generalize hq : Concat.concat lhs rhs = q at h
  cases h with
  | exposed hexp =>
    have hnone := (hE _ hexp).1
    rw [← hq] at hnone
    dsimp [Concat.concat] at hnone
    rw [BytesView.view_pack] at hnone
    cases hnone
  | concat hlhs hrhs =>
    have hv := congrArg (fun b : Bytes => b.view? Concat.Concat.SubF) hq
    simp only [Concat.concat, Concat.CanConcat.concat, BytesView.view_pack,
      Option.some.injEq, Concat.Concat.SubF.mk.injEq] at hv
    obtain ⟨rfl, rfl⟩ := hv
    exact ⟨hlhs, hrhs⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_symEnc {E : Bytes → Prop} (hE : IsAtomicExposure E) {k iv msg : Bytes}
    (h : CompTrClosed E (SymEnc.symEnc k iv msg)) : CompTrClosed E msg := by
  generalize hq : SymEnc.symEnc k iv msg = q at h
  cases h with
  | exposed hexp =>
    have hnone := (hE _ hexp).2.1
    rw [← hq] at hnone
    dsimp [SymEnc.symEnc] at hnone
    rw [BytesView.view_pack] at hnone
    cases hnone
  | symEnc hmsg =>
    have hv := congrArg (fun b : Bytes => b.view? SymEnc.Enc.SubF) hq
    simp only [SymEnc.symEnc, SymEnc.CanSymEnc.symEnc, BytesView.view_pack,
      Option.some.injEq, SymEnc.Enc.SubF.mk.injEq] at hv
    obtain ⟨_, _, rfl⟩ := hv
    exact hmsg
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_variant {E : Bytes → Prop} (hE : IsAtomicExposure E)
    {x : X25519.Variant.SubF Bytes} (h : CompTrClosed E x.pack) : CompTrClosed E x.key := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (hE _ hexp).2.2.1
    rw [← hq, BytesView.view_pack] at hnone
    cases hnone
  | variant v hkey =>
    have hv := congrArg (fun b : Bytes => b.view? X25519.Variant.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact hkey
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.normalizeX25519Key {E : Bytes → Prop} (hE : IsAtomicExposure E) {pk : Bytes}
    (h : CompTrClosed E pk) : CompTrClosed E (X25519.normalizeX25519Key pk) := by
  unfold X25519.normalizeX25519Key
  have hp := Bytes.pack_view? X25519.Variant.SubF pk
  cases hv : pk.view? X25519.Variant.SubF with
  | none => exact h
  | some x => rw [hv] at hp; rw [← hp] at h; exact CompTrClosed.inv_variant hE h

theorem CompTrClosed.x25519TorsionVariant {E : Bytes → Prop} (hE : IsAtomicExposure E)
    {key : Bytes} (v : Fin 4) (t : Fin 8) (hkey : CompTrClosed E key) :
    CompTrClosed E (X25519.x25519TorsionVariant key v t) := by
  dsimp [X25519.x25519TorsionVariant]
  split
  · exact CompTrClosed.normalizeX25519Key hE hkey
  · exact .variant v (CompTrClosed.normalizeX25519Key hE hkey)

theorem CompTrClosed.inv_trWireMsg {E : Bytes → Prop} (hE : IsAtomicExposure E)
    {v : UInt8} {rk : Bytes} {c pc : UInt32} {ct pq : Bytes} {ev : TrWire.EncodingVariation}
    (h : CompTrClosed E (TrWire.trWireMsg v rk c pc ct pq ev)) :
    CompTrClosed E rk ∧ CompTrClosed E ct ∧ CompTrClosed E pq := by
  generalize hq : TrWire.trWireMsg v rk c pc ct pq ev = q at h
  cases h with
  | exposed hexp =>
    have hnone := (hE _ hexp).2.2.2.1
    rw [← hq] at hnone
    dsimp [TrWire.trWireMsg] at hnone
    rw [BytesView.view_pack] at hnone
    cases hnone
  | trWireMsg hrk hct hpq =>
    have hv := congrArg (fun b : Bytes => b.view? TrWire.TrWireMsg.SubF) hq
    simp only [TrWire.trWireMsg, TrWire.CanTrWireMsg.trWireMsg, BytesView.view_pack,
      Option.some.injEq, TrWire.TrWireMsg.SubF.mk.injEq] at hv
    obtain ⟨_, rfl, _, _, rfl, rfl, _⟩ := hv
    exact ⟨hrk, hct, hpq⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_spqrInit {E : Bytes → Prop} (hE : IsAtomicExposure E)
    {x : Spqr.InitState.SubF Bytes} (h : CompTrClosed E x.pack) :
    CompTrClosed E x.authKey ∧ CompTrClosed E x.params := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (hE _ hexp).2.2.2.2.1
    rw [← hq, BytesView.view_pack] at hnone
    cases hnone
  | spqrInit hauth hparams =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.InitState.SubF) hq
    simp only [Spqr.spqrInit, BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact ⟨hauth, hparams⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_spqrSendState {E : Bytes → Prop} (hE : IsAtomicExposure E)
    {x : Spqr.SendState.SubF Bytes} (h : CompTrClosed E x.pack) :
    CompTrClosed E x.st ∧ CompTrClosed E x.coins := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (hE _ hexp).2.2.2.2.2.1
    rw [← hq, BytesView.view_pack] at hnone
    cases hnone
  | spqrSendState hst hcoins =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.SendState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact ⟨hst, hcoins⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.inv_spqrRecvState {E : Bytes → Prop} (hE : IsAtomicExposure E)
    {x : Spqr.RecvState.SubF Bytes} (h : CompTrClosed E x.pack) :
    CompTrClosed E x.st ∧ CompTrClosed E x.msg := by
  generalize hq : x.pack = q at h
  cases h with
  | exposed hexp =>
    have hnone := (hE _ hexp).2.2.2.2.2.2
    rw [← hq, BytesView.view_pack] at hnone
    cases hnone
  | spqrRecvState hst hmsg =>
    have hv := congrArg (fun b : Bytes => b.view? Spqr.RecvState.SubF) hq
    simp only [BytesView.view_pack, Option.some.injEq] at hv
    cases x; cases hv; exact ⟨hst, hmsg⟩
  | _ =>
    try dsimp [literalToBytes, DiffieHellman.dhPk, PQKem.kemPk, PQKem.kemEncap,
      Signature.vk, Signature.sign, Trunc.trunc8, kdfExtract, Concat.concat,
      SymEnc.symEnc, TrWire.trWireMsg, Spqr.spqrInit, Spqr.spqrChainKey] at hq
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hq)

theorem CompTrClosed.spqrSendKey_of {E : Bytes → Prop} (st coins : Bytes) :
    CompTrClosed E (Spqr.spqrSend st coins).2.1 := by
  unfold Spqr.spqrSend
  dsimp only
  cases st.view? Spqr.InitState.SubF with
  | none => exact .spqrSendKey st coins
  | some x => exact .spqrChainKey x.authKey x.params (Spqr.encodeSpqrIndexTerm 1)

theorem CompTrClosed.spqrRecvState_of {E : Bytes → Prop} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r)
    (hst : CompTrClosed E st) (hm : CompTrClosed E msg) : CompTrClosed E r.1 := by
  rw [Spqr.spqrRecv_state st msg idx r hrecv]
  exact .spqrRecvState hst hm

theorem CompTrClosed.spqrRecvKey_of {E : Bytes → Prop} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) : CompTrClosed E r.2 := by
  unfold Spqr.spqrRecv at hrecv
  split at hrecv
  · cases hrecv
  · cases hv : st.view? Spqr.InitState.SubF with
    | none =>
      rw [hv] at hrecv
      injection hrecv with hrecv'
      subst hrecv'
      exact .spqrRecvKey st msg
    | some x =>
      rw [hv] at hrecv
      rcases x with ⟨authKey, params⟩
      dsimp only at hrecv
      cases hd : Spqr.spqrParamsDir? params with
      | none => rw [hd] at hrecv; cases hrecv
      | some dir =>
        rw [hd] at hrecv
        injection hrecv with hrecv'
        subst hrecv'
        dsimp only
        split
        · exact .literal _
        · exact .spqrChainKey authKey _ (Spqr.encodeSpqrIndexTerm idx)

set_option maxHeartbeats 400000 in
theorem CompTrClosed.attackerKnowledge_implies {E : Bytes → Prop} (hE : IsAtomicExposure E) :
    SubAttackerKnowledge.Implies AttackerKnowledge.attackerKnowledge (CompTrClosed E) := by
  change SubAttackerKnowledge.Implies
    DY.Libsignal.Composed.attackerKnowledge (CompTrClosed E)
  dsimp [DY.Libsignal.Composed.attackerKnowledge]
  apply SubAttackerKnowledge.combine.implies
  rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, hlt⟩
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
    intro b hb
    rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hb
    exact hb.elim
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Literal.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · intro b hb
      dsimp [Literal.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hb
      rcases hb with ⟨bs, rfl⟩; exact .literal bs
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Concat.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | n, hlt'⟩
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hb
      rcases hb with ⟨lhs, rhs, rfl, hlhs, hrhs⟩; exact .concat hlhs hrhs
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, rhs, i, hsplit, hinp⟩
      exact (CompTrClosed.inv_concat hE (Concat.concat_split inp i b rhs hsplit.symm ▸ hinp)).1
    · intro b hb
      dsimp [Concat.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hb
      rcases hb with ⟨inp, lhs, i, hsplit, hinp⟩
      exact (CompTrClosed.inv_concat hE (Concat.concat_split inp i lhs b hsplit.symm ▸ hinp)).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      DiffieHellman.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩; exact .dhPk sk
    · intro b hb
      dsimp [DiffieHellman.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hb
      rcases hb with ⟨pk, sk, rfl, _, hsk⟩; exact CompTrClosed.dh hsk
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      KdfExtract.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · intro b hb
      dsimp [KdfExtract.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hb
      rcases hb with ⟨salt, ikm, rfl, hsalt, hikm⟩; exact .kdf hsalt hikm
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      SymEnc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨k', iv, msg, rfl, _, _, hmsg⟩; exact .symEnc hmsg
    · rintro b ⟨key, iv, ct, hdec, _, _, hct⟩
      dsimp [SymEnc.symDec, SymEnc.CanSymEnc.symDec] at hdec
      have hp := Bytes.pack_view? SymEnc.Enc.SubF ct
      cases hv : ct.view? SymEnc.Enc.SubF with
      | none => rw [hv] at hdec; cases hdec
      | some x =>
        rw [hv] at hdec hp
        rcases x with ⟨k', iv', msg'⟩
        dsimp only at hdec hp
        split at hdec
        · injection hdec with hdec'
          subst hdec'
          rw [← hp] at hct
          exact CompTrClosed.inv_symEnc hE hct
        · cases hdec
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Trunc.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | n, hlt'⟩
    · rintro b ⟨m, rfl, _⟩; exact .trunc8 m
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      X25519.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨key, v, t, rfl, hkey⟩; exact CompTrClosed.x25519TorsionVariant hE v t hkey
    · rintro b ⟨x, hpack, rfl⟩; exact CompTrClosed.inv_variant hE hpack
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      PQKem.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨sk, rfl, _⟩; exact .kemPk sk
    · rintro b ⟨pk, e, rhs, heq, _, _⟩
      have h1 : b = (PQKem.kemEncap pk e).1 := congrArg Prod.fst heq
      rw [h1]; exact .kemEncap pk e
    · rintro b ⟨pk, e, lhs, heq, hpk, he⟩
      have h2 : b = (PQKem.kemEncap pk e).2 := congrArg Prod.snd heq
      rw [h2]; exact .kemSs pk e hpk he
    · rintro b ⟨sk, ct, hdec, hsk, _⟩
      obtain ⟨e, _, rfl⟩ := kemDecap_eq_some_iff.mp hdec.symm
      exact .kemSsKey sk e hsk
    · rintro b ⟨sk, ct, rfl, hsk, hct⟩
      exact .kemRejKey hsk hct
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Signature.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · intro b hb
      dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, rfl, _⟩; exact .vk sk
    · intro b hb
      dsimp [Signature.attackerKnowledge.internal] at hb
      rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hb
      rcases hb with ⟨sk, nonce, msg, rfl, _, _, _⟩; exact .sign sk nonce msg
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      Spqr.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, hlt'⟩
    · rintro b ⟨authKey, params, rfl, hauth, hparams⟩; exact .spqrInit hauth hparams
    · rintro b ⟨authKey, params, idx, rfl, _, _, _⟩; exact .spqrChainKey authKey params idx
    · rintro b ⟨st, coins, rfl, hst, hcoins⟩; exact .spqrSendState hst hcoins
    · rintro b ⟨st, coins, rfl, _, _⟩; exact CompTrClosed.spqrSendKey_of st coins
    · rintro b ⟨st, coins, rfl, _, _⟩; exact .spqrSendMsg st coins
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, hst, hmsg⟩
      exact CompTrClosed.spqrRecvState_of hrecv hst hmsg
    · rintro b ⟨st, msg, idx, r, hrecv, rfl, _, _⟩
      exact CompTrClosed.spqrRecvKey_of hrecv
    · rintro b (⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩ | ⟨x, hpack, rfl | rfl⟩)
      · exact (CompTrClosed.inv_spqrInit hE hpack).1
      · exact (CompTrClosed.inv_spqrInit hE hpack).2
      · exact (CompTrClosed.inv_spqrSendState hE hpack).1
      · exact (CompTrClosed.inv_spqrSendState hE hpack).2
      · exact (CompTrClosed.inv_spqrRecvState hE hpack).1
      · exact (CompTrClosed.inv_spqrRecvState hE hpack).2
    · omega
  · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal,
      TrWire.attackerKnowledge]
    apply SubAttackerKnowledge.combine'.implies
    rintro ⟨_ | _ | n, hlt'⟩
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, rfl, hrk, hct, hpq⟩
      exact .trWireMsg hrk hct hpq
    · rintro b ⟨⟨v, rk, c, pc, ct, pq, ev⟩, hw, hmem⟩
      obtain ⟨hrk, hct, hpq⟩ := CompTrClosed.inv_trWireMsg hE hw
      rcases hmem with rfl | rfl | rfl <;> assumption
    · omega
  · omega

/-! ## Schedule and hybrid cipher-key inversion -/

theorem CompTrClosed.inv_chainKeyAt {E : Bytes → Prop} {ck₀ : Bytes} :
    ∀ {n : Nat}, CompTrClosed E (chainKeyAt ck₀ n) →
      (∃ j ≤ n, E (chainKeyAt ck₀ j)) ∨ CompTrClosed E ck₀
  | 0, h => .inr h
  | n + 1, h => by
    rw [chainKeyAt_succ_eq_kdfCk_fst] at h
    rcases CompTrClosed.inv_kdfExtract_salt h with hexp | hprev
    · exact .inl ⟨n + 1, Nat.le_refl _, by rw [chainKeyAt_succ_eq_kdfCk_fst]; exact hexp⟩
    · rcases CompTrClosed.inv_chainKeyAt hprev with ⟨j, hj, hexp⟩ | h0
      · exact .inl ⟨j, Nat.le_succ_of_le hj, hexp⟩
      · exact .inr h0

theorem CompTrClosed.inv_kdfCk_snd_chainKeyAt {E : Bytes → Prop} {ck₀ : Bytes} {n : Nat}
    (h : CompTrClosed E (kdfCk (chainKeyAt ck₀ n)).2) :
    E (kdfCk (chainKeyAt ck₀ n)).2 ∨ (∃ j ≤ n, E (chainKeyAt ck₀ j)) ∨ CompTrClosed E ck₀ := by
  rcases CompTrClosed.inv_kdfExtract_salt h with hexp | hck
  · exact .inl hexp
  · exact .inr (CompTrClosed.inv_chainKeyAt hck)

theorem CompTrClosed.inv_createChain_fst {E : Bytes → Prop}
    (hprk : ∀ r p s, ¬ E (kdfExtract r (DiffieHellman.dh p s)))
    {rk pk sk : Bytes} (h : CompTrClosed E (createChain rk pk sk).1) :
    E (createChain rk pk sk).1 ∨ CompTrClosed E rk := by
  rcases CompTrClosed.inv_kdfExtract_salt h with hexp | h1
  · exact .inl hexp
  · rcases CompTrClosed.inv_kdfExtract_salt h1 with hprk_exp | hrk
    · exact False.elim (hprk _ _ _ hprk_exp)
    · exact .inr hrk

theorem CompTrClosed.inv_createChain_snd {E : Bytes → Prop}
    (hprk : ∀ r p s, ¬ E (kdfExtract r (DiffieHellman.dh p s)))
    {rk pk sk : Bytes} (h : CompTrClosed E (createChain rk pk sk).2) :
    E (createChain rk pk sk).2 ∨ CompTrClosed E rk := by
  rcases CompTrClosed.inv_kdfExtract_salt h with hexp | h1
  · exact .inl hexp
  · rcases CompTrClosed.inv_kdfExtract_salt h1 with hprk_exp | hrk
    · exact False.elim (hprk _ _ _ hprk_exp)
    · exact .inr hrk

theorem CompTrClosed.inv_trMsgKeys_cipherKey {E : Bytes → Prop}
    (hcipher : ∀ p c, ¬ E (trMsgKeys p (kdfCk c).2).cipherKey)
    (hprk_hyb : ∀ p c, ¬ E (hmac p (kdfCk c).2))
    {pqSalt ck : Bytes}
    (h : CompTrClosed E (trMsgKeys pqSalt (kdfCk ck).2).cipherKey) :
    CompTrClosed E (kdfCk ck).2 := by
  rcases CompTrClosed.inv_kdfExtract_salt h with hexp | hprk
  · exact False.elim (hcipher pqSalt ck hexp)
  · rcases CompTrClosed.inv_kdfExtract_ikm hprk with hexp' | hseed
    · exact False.elim (hprk_hyb pqSalt ck hexp')
    · exact hseed

theorem CompTrClosed.inv_trKeyKnown {E : Bytes → Prop}
    (hcipher : ∀ p c, ¬ E (trMsgKeys p (kdfCk c).2).cipherKey)
    (hprk_hyb : ∀ p c, ¬ E (hmac p (kdfCk c).2))
    {pqSalt ck : Bytes}
    (h : TRKeyKnown (CompTrClosed E) (kdfCk ck).2 pqSalt) :
    CompTrClosed E (kdfCk ck).2 := by
  rcases h with hseed | hck
  · exact hseed
  · exact CompTrClosed.inv_trMsgKeys_cipherKey hcipher hprk_hyb hck

theorem dh_ne_kdfExtract (pk sk s m : Bytes) : DiffieHellman.dh pk sk ≠ kdfExtract s m := by
  intro h
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh, KdfExtract.kdfExtract,
    KdfExtract.CanKdfExtract.kdfExtract] at h
  split at h
  · split at h <;> exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
  · exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h

theorem concat_ne_kdfExtract (a b s m : Bytes) : Concat.concat a b ≠ kdfExtract s m := by
  intro h; dsimp [Concat.concat, kdfExtract] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
theorem litByte_ne_kdfExtract (x : UInt8) (s m : Bytes) : litByte x ≠ kdfExtract s m := by
  intro h; dsimp [litByte, literalToBytes, kdfExtract] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
theorem litByte_ne_concat (x : UInt8) (a b : Bytes) : litByte x ≠ Concat.concat a b := by
  intro h; dsimp [litByte, literalToBytes, Concat.concat] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
theorem trMsgKeys_cipherKey_ne_mkRand (pqSalt seed : Bytes) (t sz : Nat) :
    (trMsgKeys pqSalt seed).cipherKey ≠ mkRand t sz := by
  intro h; dsimp [trMsgKeys, hkdfBlock1, hmac, kdfExtract, mkRand] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
theorem trMsgKeys_cipherKey_ne_kdfCk_fst (pqSalt seed ck : Bytes) :
    (trMsgKeys pqSalt seed).cipherKey ≠ (kdfCk ck).1 := by
  intro h; exact litByte_ne_concat _ _ _ (hmac_inj h).2.symm
theorem trMsgKeys_cipherKey_ne_kdfCk_snd (pqSalt seed ck : Bytes) :
    (trMsgKeys pqSalt seed).cipherKey ≠ (kdfCk ck).2 := by
  intro h; exact litByte_ne_concat _ _ _ (hmac_inj h).2.symm
theorem trMsgKeys_cipherKey_ne_createChain_fst (pqSalt ck r p sk : Bytes) :
    (trMsgKeys pqSalt (kdfCk ck).2).cipherKey ≠ (createChain r p sk).1 := by
  intro h; exact dh_ne_kdfExtract _ sk ck (litByte 1) (hmac_inj (hmac_inj h).1).2.symm
theorem trMsgKeys_cipherKey_ne_createChain_snd (pqSalt ck r p sk : Bytes) :
    (trMsgKeys pqSalt (kdfCk ck).2).cipherKey ≠ (createChain r p sk).2 := by
  intro h; exact dh_ne_kdfExtract _ sk ck (litByte 1) (hmac_inj (hmac_inj h).1).2.symm
theorem hmac_kdfCk_snd_ne_mkRand (pqSalt ck : Bytes) (t sz : Nat) :
    hmac pqSalt (kdfCk ck).2 ≠ mkRand t sz := by
  intro h; dsimp [hmac, kdfExtract, mkRand] at h
  exact Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none h
theorem hmac_kdfCk_snd_ne_kdfCk_fst (pqSalt ck ck' : Bytes) :
    hmac pqSalt (kdfCk ck).2 ≠ (kdfCk ck').1 := by
  intro h; exact litByte_ne_kdfExtract _ _ _ (hmac_inj h).2.symm
theorem hmac_kdfCk_snd_ne_kdfCk_snd (pqSalt ck ck' : Bytes) :
    hmac pqSalt (kdfCk ck).2 ≠ (kdfCk ck').2 := by
  intro h; exact litByte_ne_kdfExtract _ _ _ (hmac_inj h).2.symm
theorem hmac_kdfCk_snd_ne_createChain_fst (pqSalt ck r p sk : Bytes) :
    hmac pqSalt (kdfCk ck).2 ≠ (createChain r p sk).1 := by
  intro h; exact concat_ne_kdfExtract _ _ _ _ (hmac_inj h).2.symm
theorem hmac_kdfCk_snd_ne_createChain_snd (pqSalt ck r p sk : Bytes) :
    hmac pqSalt (kdfCk ck).2 ≠ (createChain r p sk).2 := by
  intro h; exact concat_ne_kdfExtract _ _ _ _ (hmac_inj h).2.symm

theorem CompTrClosed.not_false_rnd (t n : Nat) :
    ¬ CompTrClosed (fun _ => False) (mkRand t n) :=
  fun h => CompTrClosed.inv_rnd h

example : ¬ CompTrClosed (fun _ => False) (mkRand 0 32) :=
  CompTrClosed.not_false_rnd 0 32

namespace Closed

end Closed

end Symbolic.Swarm.COMPOSED.CompRatchet
