/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Specifications.Model.Instance
import Symbolic.Proofs.Swarm.COMPOSED.CompTrace
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.Bytes.AttackerKnowledge
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Trace.Basic
import Symbolic.DYBridge.DY.Trace.BaseAttackerKnowledge
import Symbolic.DYBridge.DY.Trace.Monad
import Symbolic.DYBridge.DY.Trace.Manipulation
import Symbolic.DYBridge.DY.Actions.Network
import Symbolic.DYBridge.DY.Actions.PersistentLocalState
import Symbolic.DYBridge.DY.Actions.PersistentGlobalState
import Symbolic.DYBridge.DY.Actions.ProtocolEvent
import Symbolic.DYBridge.DY.Actions.Random
import Symbolic.DYBridge.DY.EquationalTheory.Literal
import Symbolic.DYBridge.DY.EquationalTheory.Concat
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract
import Symbolic.DYBridge.DY.EquationalTheory.DiffieHellman
import Symbolic.DYBridge.DY.EquationalTheory.Sign
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Spqr
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.SymEnc
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.Trunc

/-!
# Non-Derivability of Kyber Implicit-Rejection Keys

Proves that on an arbitrary trace, attacker knowledge of `PQKem.kemRejKey sk ct` implies either
attacker knowledge of both `sk` and `ct` or base exposure in a projecting subterm position
(`rejKey_attackerKnows_or_baseExposed_proof`). On reachable composed traces, no base-exposed term
contains `kemRejKey sk ct` in such a position, yielding `rejKey_attackerKnows_iff_of_reachable_proof`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Proofs.Tests.Model.RejKeyNonDerivability

open DY
open DY.Libsignal.Composed
open Symbolic.Swarm.COMPOSED.CompTrace (NetE RndE TREvE PQEvE CEvE TRStE PQStE TREntry mkRand
  Preserves PQXDHStoredAt TRStateStoredAt composed_reachable_induction)

/-- Terms from which the projecting Dolev-Yao destructor rules (`Concat`, `SymEnc`, `X25519`,
`Spqr`, `TrWire`) can extract `target` without reconstructing it. -/
inductive ExposesSubterm (target : Bytes) : Bytes → Prop
  | refl : ExposesSubterm target target
  | concatL {l r} : ExposesSubterm target l → ExposesSubterm target (Concat.concat l r)
  | concatR {l r} : ExposesSubterm target r → ExposesSubterm target (Concat.concat l r)
  | symEnc {k iv m} : ExposesSubterm target m → ExposesSubterm target (SymEnc.symEnc k iv m)
  | variant (x : X25519.Variant.SubF Bytes) :
      ExposesSubterm target x.key → ExposesSubterm target x.pack
  | spqrInit (x : Spqr.InitState.SubF Bytes) {u : Bytes} :
      (u = x.authKey ∨ u = x.params) → ExposesSubterm target u → ExposesSubterm target x.pack
  | spqrSend (x : Spqr.SendState.SubF Bytes) {u : Bytes} :
      (u = x.st ∨ u = x.coins) → ExposesSubterm target u → ExposesSubterm target x.pack
  | spqrRecv (x : Spqr.RecvState.SubF Bytes) {u : Bytes} :
      (u = x.st ∨ u = x.msg) → ExposesSubterm target u → ExposesSubterm target x.pack
  | trWire (x : TrWire.TrWireMsg.SubF Bytes) {u : Bytes} :
      (u = x.senderRatchetKey ∨ u = x.ciphertext ∨ u = x.pqRatchet) →
      ExposesSubterm target u → ExposesSubterm target x.pack

/-- Parameterized subterm exposure: `allowPk = false` is equivalent to `ExposesSubterm`;
`allowPk = true` additionally peels `dhPk` and `kemPk` to close `invertDH` and `invertKEM`. -/
private inductive ExposesGen (allowPk : Bool) (target : Bytes) : Bytes → Prop
  | refl : ExposesGen allowPk target target
  | dhPk {s} : allowPk = true → ExposesGen allowPk target s → ExposesGen allowPk target (DiffieHellman.dhPk s)
  | kemPk {s} : allowPk = true → ExposesGen allowPk target s → ExposesGen allowPk target (PQKem.kemPk s)
  | concatL {l r} : ExposesGen allowPk target l → ExposesGen allowPk target (Concat.concat l r)
  | concatR {l r} : ExposesGen allowPk target r → ExposesGen allowPk target (Concat.concat l r)
  | symEnc {k iv m} : ExposesGen allowPk target m → ExposesGen allowPk target (SymEnc.symEnc k iv m)
  | variant (x : X25519.Variant.SubF Bytes) :
      ExposesGen allowPk target x.key → ExposesGen allowPk target x.pack
  | spqrInit (x : Spqr.InitState.SubF Bytes) {u : Bytes} :
      (u = x.authKey ∨ u = x.params) → ExposesGen allowPk target u → ExposesGen allowPk target x.pack
  | spqrSend (x : Spqr.SendState.SubF Bytes) {u : Bytes} :
      (u = x.st ∨ u = x.coins) → ExposesGen allowPk target u → ExposesGen allowPk target x.pack
  | spqrRecv (x : Spqr.RecvState.SubF Bytes) {u : Bytes} :
      (u = x.st ∨ u = x.msg) → ExposesGen allowPk target u → ExposesGen allowPk target x.pack
  | trWire (x : TrWire.TrWireMsg.SubF Bytes) {u : Bytes} :
      (u = x.senderRatchetKey ∨ u = x.ciphertext ∨ u = x.pqRatchet) →
      ExposesGen allowPk target u → ExposesGen allowPk target x.pack

private theorem ExposesGen.toSubterm {target b : Bytes} (h : ExposesGen false target b) :
    ExposesSubterm target b := by
  induction h with
  | refl => exact .refl
  | dhPk hp _ _ => cases hp
  | kemPk hp _ _ => cases hp
  | concatL _ ih => exact .concatL ih
  | concatR _ ih => exact .concatR ih
  | symEnc _ ih => exact .symEnc ih
  | variant x _ ih => exact .variant x ih
  | spqrInit x hmem _ ih => exact .spqrInit x hmem ih
  | spqrSend x hmem _ ih => exact .spqrSend x hmem ih
  | spqrRecv x hmem _ ih => exact .spqrRecv x hmem ih
  | trWire x hmem _ ih => exact .trWire x hmem ih

section Unsealed
unseal DY.Bytes

private theorem pack_inj_sub {SubF : Type → Type} [SubBytesFunctor SubF] [BytesFunctor.Has SubF]
    {x₁ x₂ : SubF Bytes} (h : BytesView.pack x₁ = BytesView.pack x₂) : x₁ = x₂ := by
  have h1 : Bytes.view? (BytesView.pack x₁) SubF = some x₁ := BytesView.view_pack (SubF := SubF) x₁
  have h2 : Bytes.view? (BytesView.pack x₂) SubF = some x₂ := BytesView.view_pack (SubF := SubF) x₂
  rw [h, h2] at h1; injection h1 with h1; exact h1.symm

/-! ## Subterm exposure inversion and fixpoint induction -/

private theorem not_exposesGen_rejKey_of_views_none {allowPk : Bool} {sk ct b : Bytes}
    (h0a : b.view? DiffieHellman.DhPk.SubF = none) (h0b : b.view? PQKem.Pk.SubF = none)
    (h1 : b.view? PQKem.RejKey.SubF = none) (h2 : b.view? Concat.Concat.SubF = none)
    (h3 : b.view? SymEnc.Enc.SubF = none)
    (h5 : b.view? X25519.Variant.SubF = none) (h6 : b.view? Spqr.InitState.SubF = none)
    (h7 : b.view? Spqr.SendState.SubF = none) (h8 : b.view? Spqr.RecvState.SubF = none)
    (h9 : b.view? TrWire.TrWireMsg.SubF = none) :
    ¬ ExposesGen allowPk (PQKem.kemRejKey sk ct) b := by
  intro hexp; cases hexp with
  | refl => dsimp [PQKem.kemRejKey, PQKem.CanPQKem.kemRejKey] at h1; rw [BytesView.view_pack] at h1; cases h1
  | dhPk _ _ => dsimp [DiffieHellman.dhPk, DiffieHellman.CanDH.dhPk] at h0a; rw [BytesView.view_pack] at h0a; cases h0a
  | kemPk _ _ => dsimp [PQKem.kemPk, PQKem.CanPQKem.kemPk] at h0b; rw [BytesView.view_pack] at h0b; cases h0b
  | concatL _ | concatR _ => dsimp [Concat.concat, Concat.CanConcat.concat] at h2; rw [BytesView.view_pack] at h2; cases h2
  | symEnc _ => dsimp [SymEnc.symEnc, SymEnc.CanSymEnc.symEnc] at h3; rw [BytesView.view_pack] at h3; cases h3
  | variant _ _ => rw [BytesView.view_pack] at h5; cases h5
  | spqrInit _ _ _ => rw [BytesView.view_pack] at h6; cases h6
  | spqrSend _ _ _ => rw [BytesView.view_pack] at h7; cases h7
  | spqrRecv _ _ _ => rw [BytesView.view_pack] at h8; cases h8
  | trWire _ _ _ => rw [BytesView.view_pack] at h9; cases h9

local macro "not_exposesGen_term%" : term =>
  `(not_exposesGen_rejKey_of_views_none
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)
      (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _))

private theorem exposesGen_rejKey_inv {allowPk : Bool} {sk ct sk' ct' : Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) (PQKem.kemRejKey sk' ct')) : sk' = sk ∧ ct' = ct := by
  generalize hy : PQKem.kemRejKey sk' ct' = y at h
  have hv : y.view? PQKem.RejKey.SubF = some { sk := sk', cipher := ct' } :=
    hy ▸ BytesView.view_pack (SubF := PQKem.RejKey.SubF) { sk := sk', cipher := ct' }
  cases h with
  | refl => have hinj := pack_inj_sub (SubF := PQKem.RejKey.SubF) hy; injection hinj with h1 h2; exact ⟨h1, h2⟩
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem exposesGen_rejKey_dhPk {allowPk : Bool} {sk ct s : Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) (DiffieHellman.dhPk s)) :
    allowPk = true ∧ ExposesGen allowPk (PQKem.kemRejKey sk ct) s := by
  generalize hy : DiffieHellman.dhPk s = y at h
  have hv : y.view? DiffieHellman.DhPk.SubF = some { sk := s } := hy ▸ BytesView.view_pack (SubF := DiffieHellman.DhPk.SubF) { sk := s }
  cases h with
  | dhPk hp hs => have hinj := pack_inj_sub (SubF := DiffieHellman.DhPk.SubF) hy; injection hinj with h1; subst h1; exact ⟨hp, hs⟩
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem exposesGen_rejKey_kemPk {allowPk : Bool} {sk ct s : Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) (PQKem.kemPk s)) :
    allowPk = true ∧ ExposesGen allowPk (PQKem.kemRejKey sk ct) s := by
  generalize hy : PQKem.kemPk s = y at h
  have hv : y.view? PQKem.Pk.SubF = some { sk := s } := hy ▸ BytesView.view_pack (SubF := PQKem.Pk.SubF) { sk := s }
  cases h with
  | kemPk hp hs => have hinj := pack_inj_sub (SubF := PQKem.Pk.SubF) hy; injection hinj with h1; subst h1; exact ⟨hp, hs⟩
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem exposesGen_rejKey_concat {allowPk : Bool} {sk ct l r : Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) (Concat.concat l r)) :
    ExposesGen allowPk (PQKem.kemRejKey sk ct) l ∨ ExposesGen allowPk (PQKem.kemRejKey sk ct) r := by
  generalize hy : Concat.concat l r = y at h
  have hv : y.view? Concat.Concat.SubF = some { lhs := l, rhs := r } := hy ▸ BytesView.view_pack (SubF := Concat.Concat.SubF) { lhs := l, rhs := r }
  cases h with
  | concatL hl => have hinj := pack_inj_sub (SubF := Concat.Concat.SubF) hy; injection hinj with h1 _; subst h1; exact .inl hl
  | concatR hr => have hinj := pack_inj_sub (SubF := Concat.Concat.SubF) hy; injection hinj with _ h2; subst h2; exact .inr hr
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem exposesGen_rejKey_symEnc {allowPk : Bool} {sk ct k iv m : Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) (SymEnc.symEnc k iv m)) :
    ExposesGen allowPk (PQKem.kemRejKey sk ct) m := by
  generalize hy : SymEnc.symEnc k iv m = y at h
  have hv : y.view? SymEnc.Enc.SubF = some { key := k, iv := iv, msg := m } := hy ▸ BytesView.view_pack (SubF := SymEnc.Enc.SubF) { key := k, iv := iv, msg := m }
  cases h with
  | symEnc hm => have hinj := pack_inj_sub (SubF := SymEnc.Enc.SubF) hy; injection hinj with _ _ h3; subst h3; exact hm
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem exposesGen_rejKey_variant {allowPk : Bool} {sk ct : Bytes} {v : X25519.Variant.SubF Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) v.pack) : ExposesGen allowPk (PQKem.kemRejKey sk ct) v.key := by
  generalize hy : v.pack = y at h
  have hv : y.view? X25519.Variant.SubF = some v := hy ▸ BytesView.view_pack (SubF := X25519.Variant.SubF) v
  cases h with
  | variant v' hk => have hinj := pack_inj_sub (SubF := X25519.Variant.SubF) hy; subst hinj; exact hk
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem exposesGen_rejKey_spqrInit {allowPk : Bool} {sk ct : Bytes} {s : Spqr.InitState.SubF Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) s.pack) :
    ExposesGen allowPk (PQKem.kemRejKey sk ct) s.authKey ∨ ExposesGen allowPk (PQKem.kemRejKey sk ct) s.params := by
  generalize hy : s.pack = y at h
  have hv : y.view? Spqr.InitState.SubF = some s := hy ▸ BytesView.view_pack (SubF := Spqr.InitState.SubF) s
  cases h with
  | spqrInit s' hmem hu =>
    have hinj := pack_inj_sub (SubF := Spqr.InitState.SubF) hy; subst hinj
    exact hmem.elim (· ▸ .inl hu) (· ▸ .inr hu)
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem exposesGen_rejKey_spqrSend {allowPk : Bool} {sk ct : Bytes} {s : Spqr.SendState.SubF Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) s.pack) :
    ExposesGen allowPk (PQKem.kemRejKey sk ct) s.st ∨ ExposesGen allowPk (PQKem.kemRejKey sk ct) s.coins := by
  generalize hy : s.pack = y at h
  have hv : y.view? Spqr.SendState.SubF = some s := hy ▸ BytesView.view_pack (SubF := Spqr.SendState.SubF) s
  cases h with
  | spqrSend s' hmem hu =>
    have hinj := pack_inj_sub (SubF := Spqr.SendState.SubF) hy; subst hinj
    exact hmem.elim (· ▸ .inl hu) (· ▸ .inr hu)
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem exposesGen_rejKey_spqrRecv {allowPk : Bool} {sk ct : Bytes} {s : Spqr.RecvState.SubF Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) s.pack) :
    ExposesGen allowPk (PQKem.kemRejKey sk ct) s.st ∨ ExposesGen allowPk (PQKem.kemRejKey sk ct) s.msg := by
  generalize hy : s.pack = y at h
  have hv : y.view? Spqr.RecvState.SubF = some s := hy ▸ BytesView.view_pack (SubF := Spqr.RecvState.SubF) s
  cases h with
  | spqrRecv s' hmem hu =>
    have hinj := pack_inj_sub (SubF := Spqr.RecvState.SubF) hy; subst hinj
    exact hmem.elim (· ▸ .inl hu) (· ▸ .inr hu)
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem exposesGen_rejKey_trWire {allowPk : Bool} {sk ct : Bytes} {w : TrWire.TrWireMsg.SubF Bytes}
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) w.pack) :
    ExposesGen allowPk (PQKem.kemRejKey sk ct) w.senderRatchetKey ∨ ExposesGen allowPk (PQKem.kemRejKey sk ct) w.ciphertext ∨
    ExposesGen allowPk (PQKem.kemRejKey sk ct) w.pqRatchet := by
  generalize hy : w.pack = y at h
  have hv : y.view? TrWire.TrWireMsg.SubF = some w := hy ▸ BytesView.view_pack (SubF := TrWire.TrWireMsg.SubF) w
  cases h with
  | trWire w' hmem hu =>
    have hinj := pack_inj_sub (SubF := TrWire.TrWireMsg.SubF) hy; subst hinj
    exact hmem.elim (· ▸ .inl hu) fun h2 => h2.elim (· ▸ .inr (.inl hu)) (· ▸ .inr (.inr hu))
  | _ => erw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _] at hv; cases hv

private theorem dh_eq_pack (p s : Bytes) :
    ∃ pk' sk', DiffieHellman.dh p s = ({ pk := pk', sk := sk' } : DiffieHellman.Dh.SubF Bytes).pack := by
  dsimp [DiffieHellman.dh, DiffieHellman.CanDH.dh]
  split
  · split <;> exact ⟨_, _, rfl⟩
  · exact ⟨_, _, rfl⟩

private theorem spqrSend_snd_fst_eq (st coins : Bytes) :
    (∃ k p i, (Spqr.spqrSend st coins).2.1 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.SendKey.SubF Bytes, (Spqr.spqrSend st coins).2.1 = x.pack) := by
  dsimp only [Spqr.spqrSend]
  split
  · exact .inl ⟨_, _, _, rfl⟩
  · exact .inr ⟨_, rfl⟩

private theorem spqrRecv_snd_eq {st msg : Bytes} {idx : UInt32} {r : Bytes × Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) :
    r.2 = Spqr.zeroKey ∨ (∃ k p i, r.2 = Spqr.spqrChainKey k p i) ∨
    (∃ x : Spqr.RecvKey.SubF Bytes, r.2 = x.pack) := by
  unfold Spqr.spqrRecv at hrecv
  split at hrecv
  · cases hrecv
  · split at hrecv
    · split at hrecv
      · injection hrecv with hr; rw [← hr]; dsimp only
        split
        · exact .inl rfl
        · exact .inr (.inl ⟨_, _, _, rfl⟩)
      · cases hrecv
    · injection hrecv with hr; rw [← hr]; exact .inr (.inr ⟨_, rfl⟩)

private theorem exposesGen_normalizeX25519Key {allowPk : Bool} {target pk : Bytes}
    (h : ExposesGen allowPk target (X25519.normalizeX25519Key pk)) :
    ExposesGen allowPk target pk := by
  unfold X25519.normalizeX25519Key at h
  have hpack := Bytes.pack_view? X25519.Variant.SubF pk
  rcases hv : pk.view? X25519.Variant.SubF with _ | v
  · rw [hv] at h; exact h
  · rw [hv] at h hpack; dsimp only at hpack; rw [← hpack]; exact .variant v h

private theorem exposesGen_rejKey_x25519TorsionVariant {allowPk : Bool} {sk ct key : Bytes}
    (v : Fin 4) (t : Fin 8)
    (h : ExposesGen allowPk (PQKem.kemRejKey sk ct) (X25519.x25519TorsionVariant key v t)) :
    ExposesGen allowPk (PQKem.kemRejKey sk ct) key := by
  dsimp only [X25519.x25519TorsionVariant] at h; split at h
  · exact exposesGen_normalizeX25519Key h
  · exact exposesGen_normalizeX25519Key (exposesGen_rejKey_variant h)

private theorem kemDecap_eq_some_pack {sk ct out : Bytes}
    (h : PQKem.kemDecap sk ct = some out) :
    ∃ x : PQKem.SharedSecret.SubF Bytes, out = x.pack := by
  dsimp [PQKem.kemDecap, PQKem.CanPQKem.kemDecap] at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h
  · injection h with h; exact ⟨_, h.symm⟩
  · cases h

private theorem exposesGen_of_attackerKnows (allowPk : Bool) {tr : ExecTrace} {b sk ct : Bytes}
    (hak : b.AttackerKnows tr) (hexp₀ : ExposesGen allowPk (PQKem.kemRejKey sk ct) b) :
    (sk.AttackerKnows tr ∧ ct.AttackerKnows tr) ∨
      ∃ m, tr.BaseAttackerKnows m ∧ ExposesGen allowPk (PQKem.kemRejKey sk ct) m := by
  let Goal : Prop :=
    (sk.AttackerKnows tr ∧ ct.AttackerKnows tr) ∨
      ∃ m, tr.BaseAttackerKnows m ∧ ExposesGen allowPk (PQKem.kemRejKey sk ct) m
  let P : Bytes → Prop := fun u =>
    u.AttackerKnows tr ∧ (ExposesGen allowPk (PQKem.kemRejKey sk ct) u → Goal)
  suffices hP : P b from hP.2 hexp₀
  refine Bytes.AttackerKnows.is_least_fixpoint P b tr ?_ ?_ hak
  · change SubAttackerKnowledge.Implies DY.Libsignal.Composed.attackerKnowledge P
    dsimp [DY.Libsignal.Composed.attackerKnowledge]; apply SubAttackerKnowledge.combine.implies
    rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | n, _⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Random.attackerKnowledge]
      intro x hx; rw [Symbolic.DYBridge.DY.Random.attKnowsRand_pred] at hx; exact hx.elim
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Literal.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩
      · intro x hx; dsimp [Literal.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Literal.literalToBytes.attackerKnowledge_pred] at hx
        rcases hx with ⟨bs, rfl⟩
        exact ⟨Literal.attacker_knows_literalToBytes bs tr, fun hexp => (not_exposesGen_term% hexp).elim⟩
      · omega
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Concat.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.concat.attackerKnowledge_pred] at hx
        rcases hx with ⟨lhs, rhs, rfl, ⟨hl_ak, hl_e⟩, ⟨hr_ak, hr_e⟩⟩
        exact ⟨Concat.attacker_knows_concat lhs rhs tr hl_ak hr_ak,
          fun hexp => (exposesGen_rejKey_concat hexp).elim hl_e hr_e⟩
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred] at hx
        rcases hx with ⟨inp, rhs, i, hsplit, ⟨hinp_ak, hinp_e⟩⟩
        refine ⟨Bytes.AttackerKnows.prove Concat.splitLeft.attackerKnowledge x tr
          (by rw [Symbolic.DYBridge.DY.Concat.splitLeft.attackerKnowledge_pred]; exact ⟨inp, rhs, i, hsplit, hinp_ak⟩),
          fun hexp => hinp_e ?_⟩
        rw [← Concat.concat_split inp i x rhs hsplit.symm]; exact .concatL hexp
      · intro x hx; dsimp [Concat.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred] at hx
        rcases hx with ⟨inp, lhs, i, hsplit, ⟨hinp_ak, hinp_e⟩⟩
        refine ⟨Bytes.AttackerKnows.prove Concat.splitRight.attackerKnowledge x tr
          (by rw [Symbolic.DYBridge.DY.Concat.splitRight.attackerKnowledge_pred]; exact ⟨inp, lhs, i, hsplit, hinp_ak⟩),
          fun hexp => hinp_e ?_⟩
        rw [← Concat.concat_split inp i lhs x hsplit.symm]; exact .concatR hexp
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, DiffieHellman.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [DiffieHellman.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.DiffieHellman.dhPk.attackerKnowledge_pred] at hx
        rcases hx with ⟨s, rfl, ⟨hs_ak, hs_e⟩⟩
        exact ⟨DiffieHellman.attacker_knows_dhPk s tr hs_ak,
          fun hexp => hs_e (exposesGen_rejKey_dhPk hexp).2⟩
      · intro x hx; dsimp [DiffieHellman.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.DiffieHellman.dh.attackerKnowledge_pred] at hx
        rcases hx with ⟨p, s, rfl, ⟨hp_ak, _⟩, ⟨hs_ak, _⟩⟩
        refine ⟨DiffieHellman.attacker_knows_dh p s tr hp_ak hs_ak, fun hexp => ?_⟩
        obtain ⟨p', s', heq⟩ := dh_eq_pack p s; rw [heq] at hexp
        exact (not_exposesGen_term% hexp).elim
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, KdfExtract.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩
      · intro x hx; dsimp [KdfExtract.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.KdfExtract.kdfExtract.attackerKnowledge_pred] at hx
        rcases hx with ⟨salt, ikm, rfl, ⟨hs_ak, _⟩, ⟨hi_ak, _⟩⟩
        exact ⟨KdfExtract.attacker_knows_kdfExtract salt ikm tr hs_ak hi_ak,
          fun hexp => (not_exposesGen_term% hexp).elim⟩
      · omega
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, SymEnc.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨k, iv, msg, rfl, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hm_ak, hm_e⟩⟩
        exact ⟨SymEnc.attacker_knows_symEnc k iv msg tr hk_ak hiv_ak hm_ak,
          fun hexp => hm_e (exposesGen_rejKey_symEnc hexp)⟩
      · rintro x ⟨key, iv, ciph, hdec, ⟨hk_ak, _⟩, ⟨hiv_ak, _⟩, ⟨hc_ak, hc_e⟩⟩
        have heq := SymEnc.symDec_eq_some key iv ciph x hdec.symm
        exact ⟨SymEnc.attacker_knows_symDec key iv ciph x tr hk_ak hiv_ak hc_ak hdec.symm,
          fun hexp => hc_e (heq ▸ .symEnc hexp)⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Trunc.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | n, _⟩
      · rintro x ⟨m, rfl, ⟨hm_ak, _⟩⟩
        exact ⟨Trunc.attacker_knows_trunc8 m tr hm_ak, fun hexp => (not_exposesGen_term% hexp).elim⟩
      · omega
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, X25519.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨key, v, t, rfl, ⟨hk_ak, hk_e⟩⟩
        exact ⟨Bytes.AttackerKnows.prove X25519.x25519Variant.attackerKnowledge _ tr ⟨key, v, t, rfl, hk_ak⟩,
          fun hexp => hk_e (exposesGen_rejKey_x25519TorsionVariant v t hexp)⟩
      · rintro x ⟨v, ⟨hv_ak, hv_e⟩, rfl⟩
        exact ⟨Bytes.AttackerKnows.prove X25519.normalizeX25519Key.attackerKnowledge _ tr ⟨v, hv_ak, rfl⟩,
          fun hexp => hv_e (.variant v hexp)⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, PQKem.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | _ | _ | _ | n, _⟩ <;> try omega
      · rintro x ⟨s, rfl, ⟨hs_ak, hs_e⟩⟩
        exact ⟨Bytes.AttackerKnows.prove PQKem.kemPk.attackerKnowledge _ tr ⟨s, rfl, hs_ak⟩,
          fun hexp => hs_e (exposesGen_rejKey_kemPk hexp).2⟩
      · rintro x ⟨pk, e, rhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
        refine ⟨Bytes.AttackerKnows.prove PQKem.kemEncapCipher.attackerKnowledge x tr ⟨pk, e, rhs, heq, hpk_ak, he_ak⟩, fun hexp => ?_⟩
        have hx : x = ({ pk := pk, entropy := e } : PQKem.Encap.SubF Bytes).pack := congrArg Prod.fst heq
        rw [hx] at hexp; exact (not_exposesGen_term% hexp).elim
      · rintro x ⟨pk, e, lhs, heq, ⟨hpk_ak, _⟩, ⟨he_ak, _⟩⟩
        refine ⟨Bytes.AttackerKnows.prove PQKem.kemEncapSS.attackerKnowledge x tr ⟨pk, e, lhs, heq, hpk_ak, he_ak⟩, fun hexp => ?_⟩
        have hx : x = ({ pk := pk, entropy := e } : PQKem.SharedSecret.SubF Bytes).pack := congrArg Prod.snd heq
        rw [hx] at hexp; exact (not_exposesGen_term% hexp).elim
      · rintro x ⟨s, ciph, hdec, ⟨hs_ak, _⟩, ⟨hc_ak, _⟩⟩
        refine ⟨Bytes.AttackerKnows.prove PQKem.kemDecap.attackerKnowledge x tr ⟨s, ciph, hdec, hs_ak, hc_ak⟩, fun hexp => ?_⟩
        obtain ⟨ss, rfl⟩ := kemDecap_eq_some_pack hdec.symm
        exact (not_exposesGen_term% hexp).elim
      · rintro x ⟨s, ciph, rfl, ⟨hs_ak, _⟩, ⟨hc_ak, _⟩⟩
        refine ⟨Bytes.AttackerKnows.prove PQKem.kemRejKey.attackerKnowledge _ tr ⟨s, ciph, rfl, hs_ak, hc_ak⟩, fun hexp => ?_⟩
        obtain ⟨rfl, rfl⟩ := exposesGen_rejKey_inv hexp
        exact .inl ⟨hs_ak, hc_ak⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Signature.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · intro x hx; dsimp [Signature.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Signature.vk.attackerKnowledge_pred] at hx
        rcases hx with ⟨s, rfl, ⟨hs_ak, _⟩⟩
        exact ⟨Signature.attacker_knows_vk s tr hs_ak, fun hexp => (not_exposesGen_term% hexp).elim⟩
      · intro x hx; dsimp [Signature.attackerKnowledge.internal] at hx
        rw [Symbolic.DYBridge.DY.Signature.sign.attackerKnowledge_pred] at hx
        rcases hx with ⟨s, m, r, rfl, ⟨hs_ak, _⟩, ⟨hm_ak, _⟩, ⟨hr_ak, _⟩⟩
        exact ⟨Signature.attacker_knows_sign s m r tr hs_ak hm_ak hr_ak,
          fun hexp => (not_exposesGen_term% hexp).elim⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, Spqr.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | _ | _ | _ | _ | _ | _ | n, _⟩ <;> try omega
      · rintro x ⟨authKey, params, rfl, ⟨hk_ak, hk_e⟩, ⟨hp_ak, hp_e⟩⟩
        exact ⟨Bytes.AttackerKnows.prove Spqr.spqrInit.attackerKnowledge _ tr ⟨authKey, params, rfl, hk_ak, hp_ak⟩,
          fun hexp => (exposesGen_rejKey_spqrInit hexp).elim hk_e hp_e⟩
      · rintro x ⟨authKey, params, idx, rfl, ⟨hk_ak, _⟩, ⟨hp_ak, _⟩, ⟨hi_ak, _⟩⟩
        exact ⟨Bytes.AttackerKnows.prove Spqr.spqrChainKey.attackerKnowledge _ tr ⟨authKey, params, idx, rfl, hk_ak, hp_ak, hi_ak⟩,
          fun hexp => (not_exposesGen_term% hexp).elim⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, hst_e⟩, ⟨hc_ak, hc_e⟩⟩
        exact ⟨Bytes.AttackerKnows.prove Spqr.spqrSendState.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩,
          fun hexp => (exposesGen_rejKey_spqrSend hexp).elim hst_e hc_e⟩
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
        refine ⟨Bytes.AttackerKnows.prove Spqr.spqrSendKey.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩, fun hexp => ?_⟩
        rcases spqrSend_snd_fst_eq st coins with ⟨k, p, i, heq⟩ | ⟨sk_f, heq⟩ <;> rw [heq] at hexp
        · exact (not_exposesGen_term% hexp).elim
        · exact (not_exposesGen_term% hexp).elim
      · rintro x ⟨st, coins, rfl, ⟨hst_ak, _⟩, ⟨hc_ak, _⟩⟩
        exact ⟨Bytes.AttackerKnows.prove Spqr.spqrSendMsg.attackerKnowledge _ tr ⟨st, coins, rfl, hst_ak, hc_ak⟩,
          fun hexp => (not_exposesGen_term% hexp).elim⟩
      · rintro x ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, hst_e⟩, ⟨hm_ak, hm_e⟩⟩
        refine ⟨Bytes.AttackerKnows.prove Spqr.spqrRecvState.attackerKnowledge _ tr ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩, fun hexp => ?_⟩
        rw [Spqr.spqrRecv_state st msg idx r hrecv] at hexp
        exact (exposesGen_rejKey_spqrRecv hexp).elim hst_e hm_e
      · rintro x ⟨st, msg, idx, r, hrecv, rfl, ⟨hst_ak, _⟩, ⟨hm_ak, _⟩⟩
        refine ⟨Bytes.AttackerKnows.prove Spqr.spqrRecvKey.attackerKnowledge _ tr ⟨st, msg, idx, r, hrecv, rfl, hst_ak, hm_ak⟩, fun hexp => ?_⟩
        rcases spqrRecv_snd_eq hrecv with heq | ⟨k, p, i, heq⟩ | ⟨rk_f, heq⟩ <;> rw [heq] at hexp
        · exact (not_exposesGen_term% hexp).elim
        · exact (not_exposesGen_term% hexp).elim
        · exact (not_exposesGen_term% hexp).elim
      · rintro x (⟨s, ⟨hs_ak, hs_e⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_e⟩, harg⟩ | ⟨s, ⟨hs_ak, hs_e⟩, harg⟩)
        · exact ⟨Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inl ⟨s, hs_ak, harg⟩),
            fun hexp => hs_e (.spqrInit s harg hexp)⟩
        · exact ⟨Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inr (.inl ⟨s, hs_ak, harg⟩)),
            fun hexp => hs_e (.spqrSend s harg hexp)⟩
        · exact ⟨Bytes.AttackerKnows.prove Spqr.spqrStateArg.attackerKnowledge x tr (.inr (.inr ⟨s, hs_ak, harg⟩)),
            fun hexp => hs_e (.spqrRecv s harg hexp)⟩
    · dsimp [DY.Libsignal.Composed.attackerKnowledge.internal, TrWire.attackerKnowledge]; apply SubAttackerKnowledge.combine'.implies
      rintro ⟨_ | _ | n, _⟩ <;> try omega
      · rintro x ⟨w, rfl, ⟨h1_ak, h1_e⟩, ⟨h2_ak, h2_e⟩, ⟨h3_ak, h3_e⟩⟩
        refine ⟨Bytes.AttackerKnows.prove TrWire.trWireMsg.attackerKnowledge _ tr ⟨w, rfl, h1_ak, h2_ak, h3_ak⟩, fun hexp => ?_⟩
        rcases exposesGen_rejKey_trWire hexp with h | h | h
        · exact h1_e h
        · exact h2_e h
        · exact h3_e h
      · rintro x ⟨w, ⟨hw_ak, hw_e⟩, hmem⟩
        exact ⟨Bytes.AttackerKnows.prove TrWire.trWireMsgArg.attackerKnowledge x tr ⟨w, hw_ak, hmem⟩,
          fun hexp => hw_e (.trWire w hmem hexp)⟩
    · omega
  · intro x hx
    simp only [Symbolic.DYBridge.DY.Bytes.AttackerKnows.baseKnowledge_eq_1, SubAttackerKnowledge.fromPred] at hx
    exact ⟨Bytes.AttackerKnows.prove_from_base x tr hx, fun hexp => .inr ⟨x, hx, hexp⟩⟩

/-- On any trace, attacker knowledge of `kemRejKey sk ct` comes either from knowing both `sk` and
`ct` or from a base-known term that exposes `kemRejKey sk ct` as a projecting subterm. -/
theorem rejKey_attackerKnows_or_baseExposed_proof (tr : ExecTrace) (sk ct : Bytes)
    (hak : (PQKem.kemRejKey sk ct).AttackerKnows tr) :
    (sk.AttackerKnows tr ∧ ct.AttackerKnows tr) ∨
      ∃ m, tr.BaseAttackerKnows m ∧ ExposesSubterm (PQKem.kemRejKey sk ct) m :=
  (exposesGen_of_attackerKnows false hak .refl).elim .inl fun ⟨m, hm, hexp⟩ => .inr ⟨m, hm, hexp.toSubterm⟩

/-! ## Term safety predicates -/

private def RejSafeAt (tr : ExecTrace) (b : Bytes) : Prop :=
  ∀ sk ct, ExposesGen true (PQKem.kemRejKey sk ct) b → sk.AttackerKnows tr ∧ ct.AttackerKnows tr

private theorem RejSafeAt.mono {tr tr' : ExecTrace} (hle : tr ≤ tr') {b : Bytes} (h : RejSafeAt tr b) : RejSafeAt tr' b :=
  fun sk ct hexp => let ⟨hsk, hct⟩ := h sk ct hexp; ⟨Bytes.AttackerKnows_le sk tr tr' hle hsk, Bytes.AttackerKnows_le ct tr tr' hle hct⟩
private theorem rejSafeAt_mkRand {tr : ExecTrace} (t n : Nat) : RejSafeAt tr (mkRand t n) := fun _ _ hexp => (not_exposesGen_term% hexp).elim
private theorem rejSafeAt_literal {tr : ExecTrace} (bs : ByteArray) : RejSafeAt tr (Literal.literalToBytes bs) := fun _ _ hexp => (not_exposesGen_term% hexp).elim
private theorem rejSafeAt_kdfExtract {tr : ExecTrace} (salt ikm : Bytes) : RejSafeAt tr (KdfExtract.kdfExtract salt ikm) := fun _ _ hexp => (not_exposesGen_term% hexp).elim
private theorem rejSafeAt_trunc8 {tr : ExecTrace} (m : Bytes) : RejSafeAt tr (Trunc.trunc8 m) := fun _ _ hexp => (not_exposesGen_term% hexp).elim
private theorem rejSafeAt_vk {tr : ExecTrace} (s : Bytes) : RejSafeAt tr (Signature.vk s) := fun _ _ hexp => (not_exposesGen_term% hexp).elim
private theorem rejSafeAt_sign {tr : ExecTrace} (s m r : Bytes) : RejSafeAt tr (Signature.sign s m r) := fun _ _ hexp => (not_exposesGen_term% hexp).elim
private theorem rejSafeAt_encap_fst {tr : ExecTrace} (pk e : Bytes) : RejSafeAt tr (PQKem.kemEncap pk e).1 := fun _ _ hexp => (not_exposesGen_term% hexp).elim
private theorem rejSafeAt_spqrSend_msg {tr : ExecTrace} (st coins : Bytes) : RejSafeAt tr (Spqr.spqrSend st coins).2.2 := fun _ _ hexp => (not_exposesGen_term% hexp).elim

private theorem rejSafeAt_spqrSend_key {tr : ExecTrace} (st coins : Bytes) : RejSafeAt tr (Spqr.spqrSend st coins).2.1 :=
  fun _ _ hexp => (spqrSend_snd_fst_eq st coins).elim (fun ⟨_, _, _, heq⟩ => (not_exposesGen_term% (heq ▸ hexp)).elim)
    (fun ⟨_, heq⟩ => (not_exposesGen_term% (heq ▸ hexp)).elim)

private theorem rejSafeAt_spqrRecv_key {tr : ExecTrace} {st msg : Bytes} {idx : UInt32}
    {r : Bytes × Bytes} (hrecv : Spqr.spqrRecv st msg idx = some r) : RejSafeAt tr r.2 :=
  fun _ _ hexp => (spqrRecv_snd_eq hrecv).elim (fun heq => (not_exposesGen_term% (heq ▸ hexp)).elim) fun h2 =>
    h2.elim (fun ⟨_, _, _, heq⟩ => (not_exposesGen_term% (heq ▸ hexp)).elim) (fun ⟨_, heq⟩ => (not_exposesGen_term% (heq ▸ hexp)).elim)

private theorem RejSafeAt.dhPk {tr : ExecTrace} {s : Bytes} (hs : RejSafeAt tr s) : RejSafeAt tr (DiffieHellman.dhPk s) :=
  fun sk ct hexp => hs sk ct (exposesGen_rejKey_dhPk hexp).2
private theorem RejSafeAt.kemPk {tr : ExecTrace} {s : Bytes} (hs : RejSafeAt tr s) : RejSafeAt tr (PQKem.kemPk s) :=
  fun sk ct hexp => hs sk ct (exposesGen_rejKey_kemPk hexp).2
private theorem RejSafeAt.concat {tr : ExecTrace} {l r : Bytes} (hl : RejSafeAt tr l) (hr : RejSafeAt tr r) : RejSafeAt tr (Concat.concat l r) :=
  fun sk ct hexp => (exposesGen_rejKey_concat hexp).elim (hl sk ct) (hr sk ct)
private theorem RejSafeAt.symEnc {tr : ExecTrace} (k iv : Bytes) {m : Bytes} (hm : RejSafeAt tr m) : RejSafeAt tr (SymEnc.symEnc k iv m) :=
  fun sk ct hexp => hm sk ct (exposesGen_rejKey_symEnc hexp)
private theorem RejSafeAt.trHonestWireMsg {tr : ExecTrace} {pk ct pq : Bytes} (ns pn : UInt32)
    (h1 : RejSafeAt tr pk) (h2 : RejSafeAt tr ct) (h3 : RejSafeAt tr pq) :
    RejSafeAt tr (DY.Libsignal.TripleRatchet.trHonestWireMsg pk ns pn ct pq) :=
  fun sk ciph hexp => (exposesGen_rejKey_trWire hexp).elim (h1 sk ciph) fun h => h.elim (h2 sk ciph) (h3 sk ciph)
private theorem RejSafeAt.spqrInit {tr : ExecTrace} {k p : Bytes} (hk : RejSafeAt tr k) (hp : RejSafeAt tr p) : RejSafeAt tr (Spqr.spqrInit k p) :=
  fun sk ct hexp => (exposesGen_rejKey_spqrInit hexp).elim (hk sk ct) (hp sk ct)
private theorem RejSafeAt.spqrSend_state {tr : ExecTrace} {st coins : Bytes} (hst : RejSafeAt tr st) (hc : RejSafeAt tr coins) : RejSafeAt tr (Spqr.spqrSend st coins).1 :=
  fun sk ct hexp => (exposesGen_rejKey_spqrSend hexp).elim (hst sk ct) (hc sk ct)
private theorem RejSafeAt.spqrRecv_state {tr : ExecTrace} {st msg : Bytes} {idx : UInt32} {r : Bytes × Bytes}
    (hrecv : Spqr.spqrRecv st msg idx = some r) (hst : RejSafeAt tr st) (hm : RejSafeAt tr msg) : RejSafeAt tr r.1 :=
  Spqr.spqrRecv_state st msg idx r hrecv ▸ fun sk ct hexp => (exposesGen_rejKey_spqrRecv hexp).elim (hst sk ct) (hm sk ct)

private theorem dhSkOf_eq_some {pk sk : Bytes}
    (h : DY.Libsignal.PQXDH.extractDhSecretKey pk = some sk) :
    pk = DiffieHellman.dhPk sk := by
  unfold DY.Libsignal.PQXDH.extractDhSecretKey at h
  have hpack := Bytes.pack_view? DiffieHellman.DhPk.SubF pk
  rcases hv : pk.view? DiffieHellman.DhPk.SubF with _ | s
  · rw [hv] at h; cases h
  · rw [hv] at h hpack; injection h with hsk; subst hsk; exact hpack.symm

private theorem kemPkInvert_eq_some {pk sk : Bytes}
    (h : PQKem.invertKemPublicKey pk = some sk) :
    pk = PQKem.kemPk sk := by
  unfold PQKem.invertKemPublicKey at h
  have hpack := Bytes.pack_view? PQKem.Pk.SubF pk
  rcases hv : pk.view? PQKem.Pk.SubF with _ | s
  · rw [hv] at h; cases h
  · rw [hv] at h hpack; injection h with hsk; subst hsk; exact hpack.symm

private theorem parseTrSignalMsg_pqRatchet_safe {tr : ExecTrace} {raw : Bytes}
    {msg : DY.Libsignal.TripleRatchet.TRSignalMsg}
    (hraw : RejSafeAt tr raw) (hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw = some msg) :
    RejSafeAt tr msg.pqRatchet := by
  unfold DY.Libsignal.TripleRatchet.parseTrSignalMsg at hparse
  dsimp only [bind, Option.bind] at hparse
  rcases hsplit : Concat.split raw (raw.length - Trunc.trunc8Length) with _ | ⟨wire, mac⟩
  · rw [hsplit] at hparse; cases hparse
  · rw [hsplit] at hparse; dsimp only at hparse
    have hraw_eq : raw = Concat.concat wire mac :=
      (Concat.concat_split raw (raw.length - Trunc.trunc8Length) wire mac hsplit).symm
    rcases hfields : TrWire.trWireMsgFields? wire with _ | x
    · rw [hfields] at hparse; cases hparse
    · rw [hfields] at hparse; dsimp only [pure] at hparse
      injection hparse with hmsg_eq; subst hmsg_eq; dsimp only
      have hpack := Bytes.pack_view? TrWire.TrWireMsg.SubF wire
      change wire.view? TrWire.TrWireMsg.SubF = some x at hfields
      rw [hfields] at hpack; dsimp only at hpack
      intro sk ct hexp
      exact hraw sk ct (hraw_eq ▸ .concatL (hpack ▸ .trWire x (.inr (.inr rfl)) hexp))

end Unsealed

/-! ## Reachable-trace invariant -/

private structure RejTraceInv (tr : ExecTrace) : Prop where
  baseSafe : ∀ m, tr.BaseAttackerKnows m → RejSafeAt tr m
  pqSafe : ∀ p st idx, PQXDHStoredAt tr p st idx → RejSafeAt tr st.sk
  trSafe : ∀ me st idx, TRStateStoredAt me st idx tr →
    RejSafeAt tr st.rk ∧ RejSafeAt tr st.dhs ∧ RejSafeAt tr st.cks ∧
    RejSafeAt tr st.spqr ∧ ∀ c ∈ st.recv, RejSafeAt tr c.chainKey
  skipSafe : ∀ s pk n seed rIdx src idx,
    tr.EventLoggedAt (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src) idx →
    RejSafeAt tr seed

private theorem RejTraceInv.of_attackerKnows {tr : ExecTrace} (hc : RejTraceInv tr)
    {b : Bytes} (hak : b.AttackerKnows tr) : RejSafeAt tr b :=
  fun sk ct hexp =>
    (exposesGen_of_attackerKnows true hak hexp).elim id fun ⟨m, hm, hexpm⟩ => hc.baseSafe m hm sk ct hexpm

private theorem rejTraceInv_nil : RejTraceInv Trace.nil where
  baseSafe m hm := by rw [Symbolic.DYBridge.DY.Trace.BaseAttackerKnows_eq_1] at hm; exact hm.elim
  pqSafe _ _ _ hst := by
    simp only [PQXDHStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte] at hst
    cases hst
  trSafe _ _ _ hst := by
    simp only [TRStateStoredAt, Trace.at?, Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte] at hst
    cases hst
  skipSafe _ _ _ _ _ _ _ hev := by
    simp only [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1, Trace.at?,
      Symbolic.DYBridge.DY.Trace.nil_length_not_lt, ↓reduceDIte] at hev
    cases hev

private theorem RejTraceInv.append_net {tr : ExecTrace} (hc : RejTraceInv tr) {msg : Bytes}
    (hmsg : RejSafeAt tr msg) : RejTraceInv (tr.append (NetE msg)) := by
  have hle : tr ≤ tr.append (NetE msg) := Trace.append_le tr (NetE msg)
  exact ⟨fun m hm => ((Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_net tr msg m).mp hm).elim
      (fun h => h ▸ hmsg.mono hle) (fun hm' => (hc.baseSafe m hm').mono hle),
    fun p st idx hst => (hc.pqSafe p st idx (Symbolic.Swarm.COMPOSED.CompTrace.pqxdhStoredAt_append_other rfl hst)).mono hle,
    fun me st idx hst => let ⟨h1, h2, h3, h4, h5⟩ := hc.trSafe me st idx (Symbolic.Swarm.COMPOSED.CompTrace.trStateStoredAt_append_other rfl hst)
      ⟨h1.mono hle, h2.mono hle, h3.mono hle, h4.mono hle, fun c hmem => (h5 c hmem).mono hle⟩,
    fun s pk n seed rIdx src idx hev => (hc.skipSafe s pk n seed rIdx src idx (Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_other rfl hev)).mono hle⟩

private theorem RejTraceInv.append_rnd {tr : ExecTrace} (hc : RejTraceInv tr) (n : Nat) :
    RejTraceInv (tr.append (RndE n)) := by
  have hle : tr ≤ tr.append (RndE n) := Trace.append_le tr (RndE n)
  exact ⟨fun m hm => (hc.baseSafe m ((Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_rnd tr n m).mp hm)).mono hle,
    fun p st idx hst => (hc.pqSafe p st idx (Symbolic.Swarm.COMPOSED.CompTrace.pqxdhStoredAt_append_other rfl hst)).mono hle,
    fun me st idx hst => let ⟨h1, h2, h3, h4, h5⟩ := hc.trSafe me st idx (Symbolic.Swarm.COMPOSED.CompTrace.trStateStoredAt_append_other rfl hst)
      ⟨h1.mono hle, h2.mono hle, h3.mono hle, h4.mono hle, fun c hmem => (h5 c hmem).mono hle⟩,
    fun s pk n' seed rIdx src idx hev => (hc.skipSafe s pk n' seed rIdx src idx (Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_other rfl hev)).mono hle⟩

private theorem RejTraceInv.append_pqEv {tr : ExecTrace} (hc : RejTraceInv tr)
    (ev : DY.Libsignal.PQXDH.PQXDHEvent) : RejTraceInv (tr.append (PQEvE ev)) := by
  have hle : tr ≤ tr.append (PQEvE ev) := Trace.append_le tr (PQEvE ev)
  exact ⟨fun m hm => (hc.baseSafe m ((Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_pqEv tr ev m).mp hm)).mono hle,
    fun p st idx hst => (hc.pqSafe p st idx (Symbolic.Swarm.COMPOSED.CompTrace.pqxdhStoredAt_append_other rfl hst)).mono hle,
    fun me st idx hst => let ⟨h1, h2, h3, h4, h5⟩ := hc.trSafe me st idx (Symbolic.Swarm.COMPOSED.CompTrace.trStateStoredAt_append_other rfl hst)
      ⟨h1.mono hle, h2.mono hle, h3.mono hle, h4.mono hle, fun c hmem => (h5 c hmem).mono hle⟩,
    fun s pk n seed rIdx src idx hev => (hc.skipSafe s pk n seed rIdx src idx (Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_other rfl hev)).mono hle⟩

private theorem RejTraceInv.append_cEv {tr : ExecTrace} (hc : RejTraceInv tr)
    (ev : ComposedEvent) : RejTraceInv (tr.append (CEvE ev)) := by
  have hle : tr ≤ tr.append (CEvE ev) := Trace.append_le tr (CEvE ev)
  exact ⟨fun m hm => (hc.baseSafe m ((Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_cEv tr ev m).mp hm)).mono hle,
    fun p st idx hst => (hc.pqSafe p st idx (Symbolic.Swarm.COMPOSED.CompTrace.pqxdhStoredAt_append_other rfl hst)).mono hle,
    fun me st idx hst => let ⟨h1, h2, h3, h4, h5⟩ := hc.trSafe me st idx (Symbolic.Swarm.COMPOSED.CompTrace.trStateStoredAt_append_other rfl hst)
      ⟨h1.mono hle, h2.mono hle, h3.mono hle, h4.mono hle, fun c hmem => (h5 c hmem).mono hle⟩,
    fun s pk n seed rIdx src idx hev => (hc.skipSafe s pk n seed rIdx src idx (Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_other rfl hev)).mono hle⟩

private theorem RejTraceInv.append_trEv {tr : ExecTrace} (hc : RejTraceInv tr) {ev : DY.Libsignal.TripleRatchet.TREvent}
    (hskip : ∀ s pk n seed rIdx src, ev = DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src → RejSafeAt tr seed) :
    RejTraceInv (tr.append (TREvE ev)) := by
  have hle : tr ≤ tr.append (TREvE ev) := Trace.append_le tr (TREvE ev)
  refine ⟨fun m hm => (hc.baseSafe m ((Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_trEv tr ev m).mp hm)).mono hle,
    fun p st idx hst => (hc.pqSafe p st idx (Symbolic.Swarm.COMPOSED.CompTrace.pqxdhStoredAt_append_other rfl hst)).mono hle,
    fun me st idx hst => let ⟨h1, h2, h3, h4, h5⟩ := hc.trSafe me st idx (Symbolic.Swarm.COMPOSED.CompTrace.trStateStoredAt_append_other rfl hst)
      ⟨h1.mono hle, h2.mono hle, h3.mono hle, h4.mono hle, fun c hmem => (h5 c hmem).mono hle⟩, ?_⟩
  intro s pk n seed rIdx src idx hev
  rcases Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_same hev with ⟨_, hev'⟩ | ⟨_, heq⟩
  · exact (hc.skipSafe s pk n seed rIdx src idx hev').mono hle
  · exact (hskip s pk n seed rIdx src heq).mono hle

private theorem RejTraceInv.append_pqSt {tr : ExecTrace} (hc : RejTraceInv tr)
    {p : Participant} {st : DY.Libsignal.PQXDH.PQXDHState} (hsk : RejSafeAt tr st.sk) :
    RejTraceInv (tr.append (PQStE p st)) := by
  have hle : tr ≤ tr.append (PQStE p st) := Trace.append_le tr (PQStE p st)
  refine ⟨fun m hm => (hc.baseSafe m ((Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_pqSt tr p st m).mp hm)).mono hle, ?_,
    fun me st' idx hst => let ⟨h1, h2, h3, h4, h5⟩ := hc.trSafe me st' idx (Symbolic.Swarm.COMPOSED.CompTrace.trStateStoredAt_append_other rfl hst)
      ⟨h1.mono hle, h2.mono hle, h3.mono hle, h4.mono hle, fun c hmem => (h5 c hmem).mono hle⟩,
    fun s pk n seed rIdx src idx hev => (hc.skipSafe s pk n seed rIdx src idx (Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_other rfl hev)).mono hle⟩
  intro p' st' idx hst
  rcases Symbolic.Swarm.COMPOSED.CompTrace.pqxdhStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, rfl, rfl⟩
  · exact (hc.pqSafe p' st' idx hst').mono hle
  · exact hsk.mono hle

private theorem RejTraceInv.append_trSt {tr : ExecTrace} (hc : RejTraceInv tr) {me : Participant}
    {st : DY.Libsignal.TripleRatchet.TRState} (hrk : RejSafeAt tr st.rk) (hdhs : RejSafeAt tr st.dhs)
    (hcks : RejSafeAt tr st.cks) (hspqr : RejSafeAt tr st.spqr) (hrecv : ∀ c ∈ st.recv, RejSafeAt tr c.chainKey) :
    RejTraceInv (tr.append (TRStE me st)) := by
  have hle : tr ≤ tr.append (TRStE me st) := Trace.append_le tr (TRStE me st)
  refine ⟨fun m hm => (hc.baseSafe m ((Symbolic.Swarm.COMPOSED.CompTrace.baseAttackerKnows_append_trSt tr me st m).mp hm)).mono hle,
    fun p st' idx hst => (hc.pqSafe p st' idx (Symbolic.Swarm.COMPOSED.CompTrace.pqxdhStoredAt_append_other rfl hst)).mono hle, ?_,
    fun s pk n seed rIdx src idx hev => (hc.skipSafe s pk n seed rIdx src idx (Symbolic.Swarm.COMPOSED.CompTrace.eventLoggedAt_append_other rfl hev)).mono hle⟩
  intro me' st' idx hst
  rcases Symbolic.Swarm.COMPOSED.CompTrace.trStateStoredAt_append_same hst with ⟨_, hst'⟩ | ⟨_, rfl, rfl⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hc.trSafe me' st' idx hst'
    exact ⟨h1.mono hle, h2.mono hle, h3.mono hle, h4.mono hle, fun c hmem => (h5 c hmem).mono hle⟩
  · exact ⟨hrk.mono hle, hdhs.mono hle, hcks.mono hle, hspqr.mono hle, fun c hmem => (hrecv c hmem).mono hle⟩

private def PreservesFrom (tr₀ : ExecTrace) {α : Type} (x : Traceful α) : Prop :=
  ∀ tr, tr₀ ≤ tr → RejTraceInv tr → RejTraceInv (x.run tr).2.val
private theorem PreservesFrom.of_preserves {tr₀ : ExecTrace} {α : Type} {x : Traceful α} (hx : Preserves RejTraceInv x) : PreservesFrom tr₀ x :=
  fun tr _ hInv => hx tr hInv
private theorem PreservesFrom.bind {tr₀ : ExecTrace} {α β : Type} {x : Traceful α} {f : α → Traceful β}
    (hx : PreservesFrom tr₀ x) (hf : ∀ a, PreservesFrom tr₀ (f a)) : PreservesFrom tr₀ (x >>= f) := by
  intro tr hle hInv; rw [Traceful.run_bind]; rcases hr : x.run tr with ⟨o, trMid, hstep⟩
  have hMid : RejTraceInv trMid := by have := hx tr hle hInv; rw [hr] at this; exact this
  cases o with | none => exact hMid | some a => exact hf a trMid (Trace.le_trans tr₀ tr trMid hle hstep) hMid
private theorem PreservesFrom.genRand (tr₀ : ExecTrace) (n : Nat) : PreservesFrom tr₀ (Random.genRand n) := by
  intro tr _ hInv; simp only [Symbolic.DYBridge.DY.Random.genRand_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]; exact hInv.append_rnd n
private theorem PreservesFrom.sendMessage {tr₀ : ExecTrace} {msg : Bytes} (hmsg : RejSafeAt tr₀ msg) : PreservesFrom tr₀ (Network.sendMessage msg) := by
  intro tr hle hInv; simp only [Symbolic.DYBridge.DY.Network.sendMessage_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hInv.append_net (hmsg.mono hle)
private theorem PreservesFrom.logPqEv (tr₀ : ExecTrace) (ev : DY.Libsignal.PQXDH.PQXDHEvent) : PreservesFrom tr₀ (ProtocolEvent.logEvent ev) := by
  intro tr _ hInv; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]; exact hInv.append_pqEv ev
private theorem PreservesFrom.logCEv (tr₀ : ExecTrace) (ev : ComposedEvent) : PreservesFrom tr₀ (ProtocolEvent.logEvent ev) := by
  intro tr _ hInv; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]; exact hInv.append_cEv ev
private theorem PreservesFrom.logTrEv {tr₀ : ExecTrace} (ev : DY.Libsignal.TripleRatchet.TREvent)
    (hskip : ∀ s pk n seed rIdx src, ev = DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src → RejSafeAt tr₀ seed) :
    PreservesFrom tr₀ (ProtocolEvent.logEvent ev) := by
  intro tr hle hInv; simp only [Symbolic.DYBridge.DY.ProtocolEvent.logEvent_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1]
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; rw [Traceful.run_pure]
  exact hInv.append_trEv fun s pk n seed rIdx src heq => (hskip s pk n seed rIdx src heq).mono hle
private theorem PreservesFrom.logTrEv_nonSkip (tr₀ : ExecTrace) (ev : DY.Libsignal.TripleRatchet.TREvent)
    (hno : ∀ s pk n seed rIdx src, ev ≠ DY.Libsignal.TripleRatchet.TREvent.SkippedKeyStored s pk n seed rIdx src) :
    PreservesFrom tr₀ (ProtocolEvent.logEvent ev) :=
  PreservesFrom.logTrEv ev fun s pk n seed rIdx src heq => (hno s pk n seed rIdx src heq).elim
private theorem PreservesFrom.storePq {tr₀ : ExecTrace} (p : Participant) (st : DY.Libsignal.PQXDH.PQXDHState) (hsk : RejSafeAt tr₀ st.sk) :
    PreservesFrom tr₀ (PersistentLocalState.storeLocalState p st) := by
  intro tr hle hInv
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hInv.append_pqSt (hsk.mono hle)
private theorem PreservesFrom.storeTr {tr₀ : ExecTrace} (me : Participant) (st : DY.Libsignal.TripleRatchet.TRState)
    (hrk : RejSafeAt tr₀ st.rk) (hdhs : RejSafeAt tr₀ st.dhs) (hcks : RejSafeAt tr₀ st.cks)
    (hspqr : RejSafeAt tr₀ st.spqr) (hrecv : ∀ c ∈ st.recv, RejSafeAt tr₀ c.chainKey) :
    PreservesFrom tr₀ (PersistentLocalState.storeLocalState me st) := by
  intro tr hle hInv
  simp only [Symbolic.DYBridge.DY.PersistentLocalState.storeLocalState_eq_1, Symbolic.DYBridge.DY.PersistentGlobalState.storeGlobalState_eq_1, Symbolic.DYBridge.DY.appendEntry_eq_1, Traceful.run_mk]
  exact hInv.append_trSt (hrk.mono hle) (hdhs.mono hle) (hcks.mono hle) (hspqr.mono hle) fun c hmem => (hrecv c hmem).mono hle
private theorem PreservesFrom.logMessageKeyAndStore {tr₀ : ExecTrace} (me : Participant) (s : DY.Libsignal.TripleRatchet.SessionInfo)
    (dir : DY.Libsignal.TripleRatchet.KeyDir) (seed pqSalt : Bytes) (n : UInt32) (rIdx parent : Nat) (st : DY.Libsignal.TripleRatchet.TRState)
    (hrk : RejSafeAt tr₀ st.rk) (hdhs : RejSafeAt tr₀ st.dhs) (hcks : RejSafeAt tr₀ st.cks)
    (hspqr : RejSafeAt tr₀ st.spqr) (hrecv : ∀ c ∈ st.recv, RejSafeAt tr₀ c.chainKey) :
    PreservesFrom tr₀ (DY.Libsignal.TripleRatchet.logMessageKeyAndStore me s dir seed pqSalt n rIdx parent st) := by
  unfold DY.Libsignal.TripleRatchet.logMessageKeyAndStore
  exact PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip tr₀ _ (by intros; rintro ⟨⟩)) fun _ => PreservesFrom.storeTr me st hrk hdhs hcks hspqr hrecv
private theorem PreservesFrom.logSkippedKeys (tr₀ : ExecTrace) (s : DY.Libsignal.TripleRatchet.SessionInfo) (pk : Bytes) (rIdx src : Nat) (ck : Bytes) (n : UInt32) (count : Nat) :
    PreservesFrom tr₀ (DY.Libsignal.TripleRatchet.logSkippedKeys s pk rIdx src ck n count) := by
  induction count generalizing ck n with
  | zero => unfold DY.Libsignal.TripleRatchet.logSkippedKeys; exact PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.pure ())
  | succ _ ih =>
    unfold DY.Libsignal.TripleRatchet.logSkippedKeys; refine PreservesFrom.bind (PreservesFrom.logTrEv _ ?_) fun _ => ih _ _
    intro _ _ _ seed _ _ heq; injection heq with _ _ _ hseed _ _; subst hseed; exact rejSafeAt_kdfExtract _ _
private theorem bind_genRand_at {α : Type} {f : Bytes → Traceful α} (n : Nat) (tr : ExecTrace) (_hInv : RejTraceInv tr)
    (hf : ∀ r, (∀ t', RejSafeAt t' r) → RejTraceInv ((f r).run (tr.append (RndE n))).2.val) :
    RejTraceInv (((Random.genRand n >>= f).run tr).2.val) := by
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_genRand_bind_snd]; exact hf (mkRand tr.length n) (fun _ => rejSafeAt_mkRand tr.length n)
private theorem rejSafeAt_createChain_fst {tr : ExecTrace} (rk pk sk : Bytes) : RejSafeAt tr (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 := rejSafeAt_kdfExtract _ _
private theorem rejSafeAt_createChain_snd {tr : ExecTrace} (rk pk sk : Bytes) : RejSafeAt tr (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := rejSafeAt_kdfExtract _ _
private theorem rejSafeAt_kdfCk_fst {tr : ExecTrace} (ck : Bytes) : RejSafeAt tr (DY.Libsignal.TripleRatchet.kdfCk ck).1 := rejSafeAt_kdfExtract _ _
private theorem rejSafeAt_pqxdhKdf_rk {tr : ExecTrace} (ikm : Bytes) : RejSafeAt tr (DY.Libsignal.PQXDH.pqxdhKdf ikm).rk := rejSafeAt_kdfExtract _ _
private theorem rejSafeAt_pqxdhKdf_ck {tr : ExecTrace} (ikm : Bytes) : RejSafeAt tr (DY.Libsignal.PQXDH.pqxdhKdf ikm).ck := rejSafeAt_kdfExtract _ _
private theorem rejSafeAt_pqxdhKdf_pqr {tr : ExecTrace} (ikm : Bytes) : RejSafeAt tr (DY.Libsignal.PQXDH.pqxdhKdf ikm).pqr := rejSafeAt_kdfExtract _ _

private theorem consumeMessageKey_chainKey_safe {tr : ExecTrace}
    {c c' : DY.Libsignal.TripleRatchet.RecvChain} {ctr : UInt32} {seed : Bytes}
    (h : DY.Libsignal.TripleRatchet.consumeMessageKey c ctr = some (seed, c')) :
    RejSafeAt tr c'.chainKey := by
  unfold DY.Libsignal.TripleRatchet.consumeMessageKey at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  injection h with hp; injection hp with _ hc'; subst hc'; exact rejSafeAt_kdfCk_fst _

private theorem setRecvChain_safe {tr : ExecTrace} {recv : List DY.Libsignal.TripleRatchet.RecvChain}
    {c' : DY.Libsignal.TripleRatchet.RecvChain}
    (hrecv : ∀ c ∈ recv, RejSafeAt tr c.chainKey) (hc' : RejSafeAt tr c'.chainKey) :
    ∀ c ∈ DY.Libsignal.TripleRatchet.setRecvChain recv c', RejSafeAt tr c.chainKey := by
  intro c hmem
  unfold DY.Libsignal.TripleRatchet.setRecvChain at hmem
  rw [List.mem_map] at hmem
  rcases hmem with ⟨c₀, hc₀, rfl⟩
  split
  · exact hc'
  · exact hrecv c₀ hc₀

private theorem findRecvChain_mem {recv : List DY.Libsignal.TripleRatchet.RecvChain} {pk : Bytes}
    {c : DY.Libsignal.TripleRatchet.RecvChain}
    (h : DY.Libsignal.TripleRatchet.findRecvChain recv pk = some c) : c ∈ recv :=
  List.mem_of_find?_eq_some h

private theorem bind_receiveSignalMsg_safe {tr : ExecTrace} (hc : RejTraceInv tr) {α : Type}
    (msgIdx : Nat) {f : DY.Libsignal.TripleRatchet.TRSignalMsg → Traceful α}
    (hf : ∀ msg, RejSafeAt tr msg.pqRatchet → RejTraceInv ((f msg).run tr).2.val) :
    RejTraceInv (((DY.Libsignal.TripleRatchet.receiveSignalMsg msgIdx >>= f).run tr).2.val) := by
  unfold DY.Libsignal.TripleRatchet.receiveSignalMsg
  rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd]
  refine Symbolic.Swarm.COMPOSED.CompTrace.bind_receiveMessage_at msgIdx tr hc fun raw _ hraw => ?_
  rcases hparse : DY.Libsignal.TripleRatchet.parseTrSignalMsg raw with _ | msg
  · dsimp only; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_failure]; exact hc
  · dsimp only; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd]
    exact Symbolic.Swarm.COMPOSED.CompTrace.bind_guardP_at _ tr hc fun _ =>
      hf msg (parseTrSignalMsg_pqRatchet_safe (hc.of_attackerKnows hraw) hparse)

private theorem bind_ensureReceiverChain_safe {tr₀ : ExecTrace} {α : Type}
    (st : DY.Libsignal.TripleRatchet.TRState) (theirPk : Bytes)
    (hrk : RejSafeAt tr₀ st.rk) (hdhs : RejSafeAt tr₀ st.dhs) (hcks : RejSafeAt tr₀ st.cks)
    (hspqr : RejSafeAt tr₀ st.spqr) (hrecv : ∀ c ∈ st.recv, RejSafeAt tr₀ c.chainKey)
    {f : DY.Libsignal.TripleRatchet.TRState × DY.Libsignal.TripleRatchet.RecvChain × Bool → Traceful α}
    (hf : ∀ st1 c rat tr₁, tr₀ ≤ tr₁ → RejTraceInv tr₁ →
      RejSafeAt tr₁ st1.rk → RejSafeAt tr₁ st1.dhs → RejSafeAt tr₁ st1.cks →
      RejSafeAt tr₁ st1.spqr → (∀ c₀ ∈ st1.recv, RejSafeAt tr₁ c₀.chainKey) →
      RejSafeAt tr₁ c.chainKey → RejTraceInv ((f (st1, c, rat)).run tr₁).2.val) :
    PreservesFrom tr₀ (DY.Libsignal.TripleRatchet.ensureReceiverChain st theirPk >>= f) := by
  intro tr hle hInv
  simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.ensureReceiverChain_eq_recvChainFor]; unfold DY.Libsignal.TripleRatchet.recvChainFor
  rcases hfind : DY.Libsignal.TripleRatchet.findRecvChain st.recv theirPk with _ | c
  · dsimp only
    rcases DY.Libsignal.TripleRatchet.x25519LowOrder theirPk with _ | _
    · simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.dhRatchetStep_eq_guard]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd, Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd]
      refine Symbolic.Swarm.COMPOSED.CompTrace.bind_guardP_at _ tr hInv fun _ => ?_
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_assoc_snd]
      refine bind_genRand_at 32 tr hInv fun dhs' hdhs' => ?_
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_pure_bind_snd, Symbolic.Swarm.COMPOSED.CompTrace.run_pure_bind_snd]
      have hle1 : tr₀ ≤ tr.append (RndE 32) := Trace.le_trans tr₀ tr _ hle (Trace.append_le tr _)
      refine hf _ _ true (tr.append (RndE 32)) hle1 (hInv.append_rnd 32)
        (rejSafeAt_createChain_fst _ _ _) (hdhs' _) (rejSafeAt_createChain_snd _ _ _) (hspqr.mono hle1) ?_
        (rejSafeAt_createChain_snd _ _ _)
      intro c₀ hmem
      have hmem' : c₀ ∈ st.recv ++ [{ ratchetKey := theirPk, chainKey := (DY.Libsignal.TripleRatchet.createChain st.rk theirPk st.dhs).2, index := 0, rIdx := st.rIdx + 2 }] :=
        List.mem_of_mem_drop hmem
      rcases List.mem_append.mp hmem' with hmem0 | hmem1
      · exact (hrecv c₀ hmem0).mono hle1
      · rw [List.mem_singleton] at hmem1; subst hmem1; exact rejSafeAt_createChain_snd _ _ _
    · simp only [↓reduceIte]; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_failure]; exact hInv
  · dsimp only; rw [Symbolic.Swarm.COMPOSED.CompTrace.run_pure_bind_snd]
    exact hf st c false tr hle hInv (hrk.mono hle) (hdhs.mono hle) (hcks.mono hle) (hspqr.mono hle)
      (fun c₀ hmem => (hrecv c₀ hmem).mono hle) ((hrecv c (findRecvChain_mem hfind)).mono hle)

private theorem rejTraceInv_of_reachable {tr : ExecTrace}
    (hreach : tr.Reachable reachability) : RejTraceInv tr := by
  refine composed_reachable_induction rejTraceInv_nil
    (fun msg tr hmsg hInv => hInv.append_net (hInv.of_attackerKnows hmsg)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hreach
  · intro p tr₀ hInv; unfold DY.Libsignal.PQXDH.registerIdentity
    refine (PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.requireTracePredicate _)) fun _ t _ hI => ?_) tr₀ (Trace.le_refl tr₀) hInv
    refine bind_genRand_at 32 t hI fun sk hsk => ?_
    exact (PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.bind (PreservesFrom.sendMessage (hsk _).dhPk) fun _ =>
      PreservesFrom.bind (PreservesFrom.sendMessage (rejSafeAt_vk _)) fun _ =>
      PreservesFrom.storePq p _ (hsk _)) _ (Trace.le_refl _) (hI.append_rnd 32)
  · intro p skIdx tr₀ hInv; unfold DY.Libsignal.PQXDH.registerCorruptIdentity
    exact (PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.requireTracePredicate _)) fun _ =>
      PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.receiveMessage _)) fun _ =>
      PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.logPqEv _ _) tr₀ (Trace.le_refl tr₀) hInv
  · intro b idStateIdx tr₀ hInv; unfold DY.Libsignal.PQXDH.genSignedPrekey
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getKey_at b idStateIdx .identity tr₀ hInv fun ikSk _ => ?_
    refine bind_genRand_at 32 tr₀ hInv fun spkSk hspk => ?_
    refine bind_genRand_at 64 _ (hInv.append_rnd 32) fun nonce _ => ?_
    exact (PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.bind (PreservesFrom.storePq b _ (hspk _)) fun _ =>
      PreservesFrom.bind (PreservesFrom.sendMessage (hspk _).dhPk) fun _ =>
      PreservesFrom.bind (PreservesFrom.sendMessage (rejSafeAt_sign _ _ _)) fun _ =>
      PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.pure _))
      _ (Trace.le_refl _) ((hInv.append_rnd 32).append_rnd 64)
  · intro b idStateIdx tr₀ hInv; unfold DY.Libsignal.PQXDH.genPQPrekey
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getKey_at b idStateIdx .identity tr₀ hInv fun ikSk _ => ?_
    refine bind_genRand_at 64 tr₀ hInv fun pqSk hpq => ?_
    refine bind_genRand_at 64 _ (hInv.append_rnd 64) fun nonce _ => ?_
    exact (PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.bind (PreservesFrom.storePq b _ (hpq _)) fun _ =>
      PreservesFrom.bind (PreservesFrom.sendMessage (hpq _).kemPk) fun _ =>
      PreservesFrom.bind (PreservesFrom.sendMessage (rejSafeAt_sign _ _ _)) fun _ =>
      PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.pure _))
      _ (Trace.le_refl _) ((hInv.append_rnd 64).append_rnd 64)
  · intro b tr₀ hInv; unfold DY.Libsignal.PQXDH.genOneTimePrekey
    refine bind_genRand_at 32 tr₀ hInv fun opkSk hopk => ?_
    exact (PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.bind (PreservesFrom.storePq b _ (hopk _)) fun _ =>
      PreservesFrom.bind (PreservesFrom.sendMessage (hopk _).dhPk) fun _ =>
      PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.pure _))
      _ (Trace.le_refl _) (hInv.append_rnd 32)
  · intro a b idStateIdx regIdxB bh tr₀ hInv; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.aliceStart_eq_inline]
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_aliceHandshake_at a b idStateIdx regIdxB bh tr₀ hInv (hInv.append_rnd 32)
      fun ikA ikBPk _ spkPk _ pqPk _ opk _ _ _ _ _ _ _ _ _ _ _ _ => ?_
    let tr₂ := (tr₀.append (RndE 32)).append (RndE 32)
    have hInv₂ : RejTraceInv tr₂ := (hInv.append_rnd 32).append_rnd 32
    refine bind_genRand_at 32 tr₂ hInv₂ fun dhsA hdhsA => ?_
    let tr₃ := tr₂.append (RndE 32)
    exact (PreservesFrom.bind (PreservesFrom.sendMessage (rejSafeAt_mkRand _ _).dhPk) fun _ =>
      PreservesFrom.bind (PreservesFrom.sendMessage (rejSafeAt_encap_fst _ _)) fun _ =>
      PreservesFrom.bind (PreservesFrom.of_preserves Symbolic.Swarm.COMPOSED.CompTrace.Preserves.traceLength) fun _ =>
      PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
      PreservesFrom.bind (PreservesFrom.logCEv _ _) fun _ =>
      PreservesFrom.storeTr a _ (rejSafeAt_createChain_fst _ _ _) (hdhsA _) (rejSafeAt_createChain_snd _ _ _)
        ((rejSafeAt_pqxdhKdf_pqr _).spqrInit (rejSafeAt_literal _))
        (fun c hmem => by rw [List.mem_singleton] at hmem; subst hmem; exact rejSafeAt_pqxdhKdf_ck _))
      tr₃ (Trace.le_refl tr₃) (hInv₂.append_rnd 32)
  · intro b a kh regIdxA mh pqIdx spqrMsgIdx tr₀ hInv; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.Composed.bobStart_eq_inline]
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_bobHandshake_at b a kh regIdxA mh.ek mh.ct tr₀ hInv
      fun ikB spkSk pqsk opk ikA _ ek ct _ keys _ hspk _ _ _ _ _ _ hagree => ?_
    have hspkSafe : RejSafeAt tr₀ spkSk := hInv.pqSafe b _ _ hspk
    have hpqrSafe : ∀ t', RejSafeAt t' keys.pqr := by
      dsimp only [DY.Libsignal.PQXDH.bobAgreement] at hagree; injection hagree with hk
      rw [← hk]; exact fun _ => rejSafeAt_pqxdhKdf_pqr _
    have hrkSafe : ∀ t', RejSafeAt t' keys.rk := by
      dsimp only [DY.Libsignal.PQXDH.bobAgreement] at hagree; injection hagree with hk
      rw [← hk]; exact fun _ => rejSafeAt_pqxdhKdf_rk _
    have hckSafe : ∀ t', RejSafeAt t' keys.ck := by
      dsimp only [DY.Libsignal.PQXDH.bobAgreement] at hagree; injection hagree with hk
      rw [← hk]; exact fun _ => rejSafeAt_pqxdhKdf_ck _
    refine bind_receiveSignalMsg_safe hInv mh.msg fun msg hpq => ?_
    refine bind_ensureReceiverChain_safe _ msg.ratchetKey (hrkSafe _) hspkSafe (hckSafe _)
      ((hpqrSafe _).spqrInit (rejSafeAt_literal _)) (fun _ hmem => by cases hmem)
      (fun st c rat tr₁ hle₁ hInv₁ hrk₁ hdhs₁ hcks₁ hspqr₁ hrecv₁ _ => ?_) tr₀ (Trace.le_refl tr₀) hInv
    dsimp only
    split
    · rename_i seed c' hcons
      split
      · rename_i spqr' key hspqr_recv
        have hfin (m pqSalt : Bytes) (lenIdx : Nat) : PreservesFrom tr₁ (do
            DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx
              (lenIdx + (msg.counter.toNat - c.index.toNat) + 2) c.chainKey c.index (msg.counter.toNat - c.index.toNat)
            ProtocolEvent.logEvent (DY.Libsignal.TripleRatchet.TREvent.Received b st.peer msg.ratchetKey msg.counter m)
            DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
              msg.counter c.rIdx (lenIdx + (msg.counter.toNat - c.index.toNat) + 2)
              { st with recv := DY.Libsignal.TripleRatchet.setRecvChain st.recv c', spqr := spqr' }) :=
          PreservesFrom.bind (PreservesFrom.logSkippedKeys _ _ _ _ _ _ _ _) fun _ =>
          PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _
            (DY.Libsignal.TripleRatchet.TREvent.Received b st.peer msg.ratchetKey msg.counter m)
            (by intros; rintro ⟨⟩)) fun _ =>
          PreservesFrom.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
            msg.counter c.rIdx (lenIdx + (msg.counter.toNat - c.index.toNat) + 2)
            { st with recv := DY.Libsignal.TripleRatchet.setRecvChain st.recv c', spqr := spqr' }
            hrk₁ hdhs₁ hcks₁ (hspqr₁.spqrRecv_state hspqr_recv (hpq.mono hle₁))
            (setRecvChain_safe hrecv₁ (consumeMessageKey_chainKey_safe hcons))
        have hmid (m pqSalt : Bytes) : PreservesFrom tr₁ (do
            let doneIdx ← DY.Libsignal.TripleRatchet.traceLength
            ProtocolEvent.logEvent (DY.Libsignal.PQXDH.PQXDHEvent.BobDone b a (DiffieHellman.dhPk ikB) ikA
              (DiffieHellman.dhPk spkSk) (PQKem.kemPk pqsk) (opk.map DiffieHellman.dhPk) ek ct keys)
            if rat then
              ProtocolEvent.logEvent (DY.Libsignal.TripleRatchet.TREvent.DHRatchet b st.peer msg.ratchetKey (DiffieHellman.dhPk st.dhs))
              ProtocolEvent.logEvent (DY.Libsignal.TripleRatchet.TREvent.HonestDH (st.sessionInfo b) st.dhs (st.rIdx - 2))
            ProtocolEvent.logEvent (ComposedEvent.HandshakeSession (st.sessionInfo b) doneIdx)
            let lenIdx ← DY.Libsignal.TripleRatchet.traceLength
            DY.Libsignal.TripleRatchet.logSkippedKeys (st.sessionInfo b) msg.ratchetKey c.rIdx
              (lenIdx + (msg.counter.toNat - c.index.toNat) + 2) c.chainKey c.index (msg.counter.toNat - c.index.toNat)
            ProtocolEvent.logEvent (DY.Libsignal.TripleRatchet.TREvent.Received b st.peer msg.ratchetKey msg.counter m)
            DY.Libsignal.TripleRatchet.logMessageKeyAndStore b (st.sessionInfo b) .receiver seed pqSalt
              msg.counter c.rIdx (lenIdx + (msg.counter.toNat - c.index.toNat) + 2)
              { st with recv := DY.Libsignal.TripleRatchet.setRecvChain st.recv c', spqr := spqr' }) := by
          refine PreservesFrom.bind (PreservesFrom.of_preserves Symbolic.Swarm.COMPOSED.CompTrace.Preserves.traceLength) fun doneIdx =>
            PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ => ?_
          cases rat <;> simp only [Bool.false_eq_true, ↓reduceIte]
          · exact PreservesFrom.bind (PreservesFrom.logCEv _ _) fun _ =>
              PreservesFrom.bind (PreservesFrom.of_preserves Symbolic.Swarm.COMPOSED.CompTrace.Preserves.traceLength) fun lenIdx =>
              hfin m pqSalt lenIdx
          · exact PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
              PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
              PreservesFrom.bind (PreservesFrom.logCEv _ _) fun _ =>
              PreservesFrom.bind (PreservesFrom.of_preserves Symbolic.Swarm.COMPOSED.CompTrace.Preserves.traceLength) fun lenIdx =>
              hfin m pqSalt lenIdx
        refine (PreservesFrom.bind (PreservesFrom.sendMessage (rejSafeAt_spqrRecv_key hspqr_recv)) fun _ =>
          PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.receiveMessage _)) fun pqSalt =>
          PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _)) fun m =>
          ?_) tr₁ (Trace.le_refl tr₁) hInv₁
        cases opk <;> dsimp only [Option.map]
        · exact hmid m pqSalt
        · exact PreservesFrom.bind
            (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.requireTracePredicate _)) fun _ =>
            PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ => hmid m pqSalt
      · exact Symbolic.Swarm.COMPOSED.CompTrace.Preserves.failure tr₁ hInv₁
    · exact Symbolic.Swarm.COMPOSED.CompTrace.Preserves.failure tr₁ hInv₁
  · intro me stH coinsLen pqIdx tr₀ hInv; unfold DY.Libsignal.TripleRatchet.messageEncrypt
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getLocalState_tr_at me stH tr₀ hInv fun st hst => ?_
    obtain ⟨hrk, hdhs, _, hspqr, hrecv⟩ := hInv.trSafe me st stH hst
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_guardP_at _ tr₀ hInv fun _ => ?_
    refine bind_genRand_at 32 tr₀ hInv fun m hm => ?_
    refine bind_genRand_at coinsLen _ (hInv.append_rnd 32) fun coins hcoins => ?_
    let tr₂ := (tr₀.append (RndE 32)).append (RndE coinsLen)
    have hle₀₂ : tr₀ ≤ tr₂ := Trace.le_trans tr₀ _ tr₂ (Trace.append_le tr₀ _) (Trace.append_le _ _)
    exact (PreservesFrom.bind (PreservesFrom.sendMessage (rejSafeAt_spqrSend_key _ _)) fun _ =>
      PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.receiveMessage _)) fun pqSalt =>
      PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _
        (DY.Libsignal.TripleRatchet.TREvent.Sent me st.peer (DiffieHellman.dhPk st.dhs) st.ns m)
        (by intros; rintro ⟨⟩)) fun _ =>
      PreservesFrom.bind (PreservesFrom.logMessageKeyAndStore me (st.sessionInfo me) .sender
        (DY.Libsignal.TripleRatchet.kdfCk st.cks).2 pqSalt st.ns st.rIdx stH
        { st with cks := (DY.Libsignal.TripleRatchet.kdfCk st.cks).1, ns := st.ns + 1, spqr := (Spqr.spqrSend st.spqr coins).1 }
        (hrk.mono hle₀₂) (hdhs.mono hle₀₂) (rejSafeAt_kdfCk_fst _)
        ((hspqr.mono hle₀₂).spqrSend_state (hcoins _))
        (fun c hmem => (hrecv c hmem).mono hle₀₂)) fun _ =>
      PreservesFrom.sendMessage (((hdhs.mono hle₀₂).dhPk.trHonestWireMsg st.ns st.pn
        ((hm _).symEnc _ _) (rejSafeAt_spqrSend_msg _ _)).concat (rejSafeAt_trunc8 _)))
      tr₂ (Trace.le_refl tr₂) ((hInv.append_rnd 32).append_rnd coinsLen)
  · intro me stH tr₀ hInv; unfold DY.Libsignal.TripleRatchet.messageEncryptAbort
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getLocalState_tr_at me stH tr₀ hInv fun _ _ => ?_
    exact (PreservesFrom.bind (PreservesFrom.genRand tr₀ 32) fun _ =>
      PreservesFrom.of_preserves Symbolic.Swarm.COMPOSED.CompTrace.Preserves.failure) tr₀ (Trace.le_refl tr₀) hInv
  · intro me stH msgH pqIdx spqrMsgIdx tr₀ hInv; simp (config := { zeta := false, beta := false, eta := false, proj := false, iota := false, failIfUnchanged := false }) only [DY.Libsignal.TripleRatchet.messageDecrypt_eq_inline]
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getLocalState_tr_at me stH tr₀ hInv fun st hst => ?_
    obtain ⟨hrk, hdhs, hcks, hspqr, hrecv⟩ := hInv.trSafe me st stH hst
    refine bind_receiveSignalMsg_safe hInv msgH fun msg hpq => ?_
    refine bind_ensureReceiverChain_safe st msg.ratchetKey hrk hdhs hcks hspqr hrecv
      (fun st1 c rat tr₁ hle₁ hInv₁ hrk₁ hdhs₁ hcks₁ hspqr₁ hrecv₁ _ => ?_) tr₀ (Trace.le_refl tr₀) hInv
    dsimp only
    split
    · rename_i seed c' hcons
      split
      · rename_i spqr' key hspqr_recv
        have hfin (m pqSalt : Bytes) : PreservesFrom tr₁ (do
            DY.Libsignal.TripleRatchet.logSkippedKeys (st1.sessionInfo me) msg.ratchetKey c.rIdx stH c.chainKey
              c.index (msg.counter.toNat - c.index.toNat)
            ProtocolEvent.logEvent (DY.Libsignal.TripleRatchet.TREvent.Received me st1.peer msg.ratchetKey msg.counter m)
            DY.Libsignal.TripleRatchet.logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt
              msg.counter c.rIdx stH
              { st1 with recv := DY.Libsignal.TripleRatchet.setRecvChain st1.recv c', spqr := spqr' }) :=
          PreservesFrom.bind (PreservesFrom.logSkippedKeys _ _ _ _ _ _ _ _) fun _ =>
          PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _
            (DY.Libsignal.TripleRatchet.TREvent.Received me st1.peer msg.ratchetKey msg.counter m)
            (by intros; rintro ⟨⟩)) fun _ =>
          PreservesFrom.logMessageKeyAndStore me (st1.sessionInfo me) .receiver seed pqSalt
            msg.counter c.rIdx stH
            { st1 with recv := DY.Libsignal.TripleRatchet.setRecvChain st1.recv c', spqr := spqr' }
            hrk₁ hdhs₁ hcks₁ (hspqr₁.spqrRecv_state hspqr_recv (hpq.mono hle₁))
            (setRecvChain_safe hrecv₁ (consumeMessageKey_chainKey_safe hcons))
        refine (PreservesFrom.bind (PreservesFrom.sendMessage (rejSafeAt_spqrRecv_key hspqr_recv)) fun _ =>
          PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.receiveMessage _)) fun pqSalt =>
          PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _)) fun m =>
          ?_) tr₁ (Trace.le_refl tr₁) hInv₁
        cases rat <;> simp only [Bool.false_eq_true, ↓reduceIte]
        · exact hfin m pqSalt
        · exact PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
            PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
            hfin m pqSalt
      · exact Symbolic.Swarm.COMPOSED.CompTrace.Preserves.failure tr₁ hInv₁
    · exact Symbolic.Swarm.COMPOSED.CompTrace.Preserves.failure tr₁ hInv₁
  · intro me stH msgH evH pqIdx spqrMsgIdx tr₀ hInv; unfold DY.Libsignal.TripleRatchet.messageDecryptSkipped
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getLocalState_tr_at me stH tr₀ hInv fun st hst => ?_
    obtain ⟨hrk, hdhs, hcks, hspqr, hrecv⟩ := hInv.trSafe me st stH hst
    refine bind_receiveSignalMsg_safe hInv msgH fun msg hpq => ?_
    have hge : ((DY.getEntry evH : Traceful TREntry).run tr₀).2.val = tr₀ := by
      simp only [Symbolic.DYBridge.DY.getEntry_eq_1]; rw [Traceful.run_mk]
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, hge]
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
    rcases (tr₀.at? evH : Option TREntry) with _ | ⟨⟨ev⟩⟩
    · exact hInv
    · dsimp only
      cases ev with
      | SkippedKeyStored s pk n seed rIdx _src =>
        dsimp only
        refine (PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.guardP _)) fun _ =>
          PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.guardTrace _)) fun _ => ?_)
          tr₀ (Trace.le_refl tr₀) hInv
        rcases hspqr_recv : Spqr.spqrRecv st.spqr msg.pqRatchet spqrMsgIdx with _ | ⟨spqr', key⟩
        · dsimp only; exact PreservesFrom.of_preserves Symbolic.Swarm.COMPOSED.CompTrace.Preserves.failure
        · dsimp only
          exact PreservesFrom.bind (PreservesFrom.sendMessage (rejSafeAt_spqrRecv_key hspqr_recv)) fun _ =>
            PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.receiveMessage _)) fun pqSalt =>
            PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.verifyMacAndDecrypt _ _ _ _)) fun m =>
            PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _
              (DY.Libsignal.TripleRatchet.TREvent.SkippedKeyUsed s evH) (by intros; rintro ⟨⟩)) fun _ =>
            PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _
              (DY.Libsignal.TripleRatchet.TREvent.Received me st.peer pk n m) (by intros; rintro ⟨⟩)) fun _ =>
            PreservesFrom.logMessageKeyAndStore me s .receiver seed pqSalt n rIdx stH
              { st with spqr := spqr' }
              hrk hdhs hcks (hspqr.spqrRecv_state hspqr_recv hpq) hrecv
      | _ => dsimp only; rw [Traceful.run_failure]; exact hInv
  · intro me stH k tr₀ hInv; unfold DY.Libsignal.TripleRatchet.exposeKey
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getLocalState_tr_at me stH tr₀ hInv fun st hst => ?_
    obtain ⟨hrk, hdhs, hcks, _, hrecv⟩ := hInv.trSafe me st stH hst
    cases k with
    | rk =>
      exact (PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
        PreservesFrom.sendMessage hrk) tr₀ (Trace.le_refl tr₀) hInv
    | dhs =>
      exact (PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
        PreservesFrom.sendMessage hdhs) tr₀ (Trace.le_refl tr₀) hInv
    | cks =>
      exact (PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
        PreservesFrom.sendMessage hcks) tr₀ (Trace.le_refl tr₀) hInv
    | ckr pk =>
      dsimp only
      rcases hfind : DY.Libsignal.TripleRatchet.findRecvChain st.recv pk with _ | c
      · dsimp only; rw [Traceful.run_failure]; exact hInv
      · dsimp only
        exact (PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
          PreservesFrom.sendMessage (hrecv c (findRecvChain_mem hfind))) tr₀ (Trace.le_refl tr₀) hInv
  · intro me stH tr₀ hInv; unfold DY.Libsignal.TripleRatchet.exposeSpqr
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getLocalState_tr_at me stH tr₀ hInv fun st hst => ?_
    obtain ⟨_, _, _, hspqr, _⟩ := hInv.trSafe me st stH hst
    exact (PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
      PreservesFrom.sendMessage hspqr) tr₀ (Trace.le_refl tr₀) hInv
  · intro evH tr₀ hInv; unfold DY.Libsignal.TripleRatchet.exposeSkipped
    have hge : ((DY.getEntry evH : Traceful TREntry).run tr₀).2.val = tr₀ := by
      simp only [Symbolic.DYBridge.DY.getEntry_eq_1]; rw [Traceful.run_mk]
    rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, hge]
    simp only [Symbolic.DYBridge.DY.getEntry_eq_1, Traceful.run_mk]
    rcases he : (tr₀.at? evH : Option TREntry) with _ | ⟨⟨ev⟩⟩
    · exact hInv
    · dsimp only
      cases ev with
      | SkippedKeyStored s pk n seed rIdx src =>
        dsimp only
        have hseed : RejSafeAt tr₀ seed :=
          hInv.skipSafe s pk n seed rIdx src evH (by rwa [Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1])
        exact (PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.guardTrace _)) fun _ =>
          PreservesFrom.bind (PreservesFrom.logTrEv_nonSkip _ _ (by intros; rintro ⟨⟩)) fun _ =>
          PreservesFrom.sendMessage hseed) tr₀ (Trace.le_refl tr₀) hInv
      | _ => dsimp only; rw [Traceful.run_failure]; exact hInv
  · intro p stateIdx tr₀ hInv; unfold DY.Libsignal.PQXDH.compromiseIK
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getKey_at p stateIdx .identity tr₀ hInv fun sk hst => ?_
    exact (PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.sendMessage (hInv.pqSafe p _ stateIdx hst)) tr₀ (Trace.le_refl tr₀) hInv
  · intro b stateIdx tr₀ hInv; unfold DY.Libsignal.PQXDH.compromiseSPK
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getKey_at b stateIdx .signedPrekey tr₀ hInv fun sk hst => ?_
    exact (PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.sendMessage (hInv.pqSafe b _ stateIdx hst)) tr₀ (Trace.le_refl tr₀) hInv
  · intro b stateIdx tr₀ hInv; unfold DY.Libsignal.PQXDH.compromisePQSPK
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getKey_at b stateIdx .pqPrekey tr₀ hInv fun sk hst => ?_
    exact (PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.sendMessage (hInv.pqSafe b _ stateIdx hst)) tr₀ (Trace.le_refl tr₀) hInv
  · intro b stateIdx tr₀ hInv; unfold DY.Libsignal.PQXDH.compromiseOPK
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_getKey_at b stateIdx .oneTimePrekey tr₀ hInv fun sk hst => ?_
    exact (PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.requireTracePredicate _)) fun _ =>
      PreservesFrom.bind (PreservesFrom.logPqEv _ _) fun _ =>
      PreservesFrom.sendMessage (hInv.pqSafe b _ stateIdx hst)) tr₀ (Trace.le_refl tr₀) hInv
  · intro tr₀ hInv; unfold DY.Libsignal.PQXDH.breakDH
    exact PreservesFrom.logPqEv tr₀ _ tr₀ (Trace.le_refl tr₀) hInv
  · intro tr₀ hInv; unfold DY.Libsignal.PQXDH.breakKEM
    exact PreservesFrom.logPqEv tr₀ _ tr₀ (Trace.le_refl tr₀) hInv
  · intro msgIdx tr₀ hInv; unfold DY.Libsignal.PQXDH.invertDH
    refine (PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.requireTracePredicate _)) fun _ t _ hI => ?_)
      tr₀ (Trace.le_refl tr₀) hInv
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_receiveMessage_at msgIdx t hI fun pk _ hpk => ?_
    have hpkSafe : RejSafeAt t (X25519.normalizeX25519Key pk) :=
      fun sk ct hexp => (hI.of_attackerKnows hpk) sk ct (exposesGen_normalizeX25519Key hexp)
    rcases hdh : DY.Libsignal.PQXDH.extractDhSecretKey (X25519.normalizeX25519Key pk) with _ | sk
    · dsimp only; rw [Traceful.run_failure]; exact hI
    · dsimp only
      rw [dhSkOf_eq_some hdh] at hpkSafe
      exact PreservesFrom.sendMessage (fun s c hexp => hpkSafe s c (.dhPk rfl hexp)) t (Trace.le_refl t) hI
  · intro msgIdx tr₀ hInv; unfold DY.Libsignal.PQXDH.invertKEM
    refine (PreservesFrom.bind (PreservesFrom.of_preserves (Symbolic.Swarm.COMPOSED.CompTrace.Preserves.requireTracePredicate _)) fun _ t _ hI => ?_)
      tr₀ (Trace.le_refl tr₀) hInv
    refine Symbolic.Swarm.COMPOSED.CompTrace.bind_receiveMessage_at msgIdx t hI fun pk _ hpk => ?_
    have hpkSafe : RejSafeAt t pk := hI.of_attackerKnows hpk
    rcases hkem : PQKem.invertKemPublicKey pk with _ | sk
    · dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only; exact hI
    · dsimp only [liftM, monadLift, MonadLift.monadLift]
      rw [Symbolic.Swarm.COMPOSED.CompTrace.run_bind_snd, Traceful.run_mk]; dsimp only
      rw [kemPkInvert_eq_some hkem] at hpkSafe
      exact PreservesFrom.sendMessage (fun s c hexp => hpkSafe s c (.kemPk rfl hexp)) t (Trace.le_refl t) hI

/-- On any reachable trace of the composed protocol, the attacker knows `kemRejKey sk ct` if and
only if the attacker knows both `sk` and `ct`. -/
theorem rejKey_attackerKnows_iff_of_reachable_proof (tr : ExecTrace)
    (hreach : tr.Reachable reachability) (sk ct : Bytes) :
    (PQKem.kemRejKey sk ct).AttackerKnows tr ↔
      sk.AttackerKnows tr ∧ ct.AttackerKnows tr :=
  ⟨fun hak => (rejTraceInv_of_reachable hreach).of_attackerKnows hak sk ct .refl,
   fun ⟨hsk, hct⟩ => Bytes.AttackerKnows.prove PQKem.kemRejKey.attackerKnowledge _ tr
     ⟨sk, ct, rfl, hsk, hct⟩⟩

end Symbolic.Proofs.Tests.Model.RejKeyNonDerivability
