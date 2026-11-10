/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Model
import ProofLib.SepLogic.WP.StateNorm

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

/-!
# Pure Model Bridges for `spqr::recv`

Unfolding and no-panic bridging lemmas connecting `LibsignalSpqrV1.recv` with
`(spqrV1Recv F K).recv` and `(spqrV1Recv F K).recvPanics`.
-/
namespace CryptoVerification.SpqrV1.Top.Recv

open Arm64
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1

/-- Unfold `(spqrV1Recv F K).recv` to `toSpqrRecvModel (spqrDeps F K) (spqrHkdfWith F)`. -/
theorem spqrV1Recv_recv_eq
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) (stateBytes msgBytes : Bytes) :
    (spqrV1Recv F K).recv stateBytes msgBytes =
      (toSpqrRecvModel (spqrDeps F K) (spqrHkdfWith F)).recv stateBytes msgBytes := rfl

/-- Unfold `(spqrV1Recv F K).recvPanics` to `toSpqrRecvModel (spqrDeps F K) (spqrHkdfWith F)`. -/
theorem spqrV1Recv_recvPanics_eq
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) (stateBytes msgBytes : Bytes) :
    (spqrV1Recv F K).recvPanics stateBytes msgBytes =
      (toSpqrRecvModel (spqrDeps F K) (spqrHkdfWith F)).recvPanics stateBytes msgBytes := rfl

/-- Bridge `.ok r` of `LibsignalSpqrV1.recv` to `(spqrV1Recv F K).recv`. -/
theorem spqrV1Recv_recv_of_ok
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {r : Recv}
    (h : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) stateBytes msgBytes = .ok r) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .ok (r.state, r.key) := by
  rw [spqrV1Recv_recv_eq]
  simp only [toSpqrRecvModel, h]

theorem spqrV1Recv_recv_of_err
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {e : LibsignalSpqrV1.Error}
    (h : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) stateBytes msgBytes = .error (.err e)) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error e.isStateDecode := by
  rw [spqrV1Recv_recv_eq]
  simp only [toSpqrRecvModel, h]

theorem spqrV1Recv_recvPanics_of_panic
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {p : SpqrApiPanic}
    (h : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) stateBytes msgBytes = .error (.panic p)) :
    (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  rw [spqrV1Recv_recvPanics_eq]
  simp only [toSpqrRecvModel, recvPanicsB, h, decide_true]

/-!
## No-Panic Lemmas for Normal Return

`spqrRecvSpecExactKey.post` requires `¬ R.recvPanics st msg`. Because a model panic projects to
`.error false` (`spqrV1Recv_recv_of_panic_err_false`), the projected result `.error false` alone
cannot rule out a panic; these lemmas derive `¬ recvPanics` from the unprojected Rust-level result
or from a projected `.ok _` / `.error true`.
-/

/-- A Rust-level `.ok r` of `LibsignalSpqrV1.recv` rules out a model panic. -/
theorem spqrV1Recv_noPanic_of_ok
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {r : Recv}
    (h : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) stateBytes msgBytes = .ok r) :
    ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  rw [spqrV1Recv_recvPanics_eq]
  simp only [toSpqrRecvModel, recvPanicsB, h]
  decide

/-- A Rust-level `.error (.err e)` of `LibsignalSpqrV1.recv` rules out a model panic. -/
theorem spqrV1Recv_noPanic_of_err
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {e : LibsignalSpqrV1.Error}
    (h : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) stateBytes msgBytes = .error (.err e)) :
    ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := by
  rw [spqrV1Recv_recvPanics_eq]
  simp only [toSpqrRecvModel, recvPanicsB, h]
  decide

/-- `spqrV1Recv_recv_of_err` together with the no-panic fact. -/
theorem spqrV1Recv_recv_noPanic_of_err
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem}
    {stateBytes msgBytes : Bytes} {e : LibsignalSpqrV1.Error}
    (h : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) stateBytes msgBytes = .error (.err e)) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error e.isStateDecode ∧
      ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes :=
  ⟨spqrV1Recv_recv_of_err h, spqrV1Recv_noPanic_of_err h⟩

/-- A model panic projects to `.error false`: the projection alone cannot exclude it. -/
theorem spqrV1Recv_recv_of_panic_err_false
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem} {stateBytes msgBytes : Bytes}
    (h : (spqrV1Recv F K).recvPanics stateBytes msgBytes) :
    (spqrV1Recv F K).recv stateBytes msgBytes = .error false := by
  rw [spqrV1Recv_recvPanics_eq] at h
  rw [spqrV1Recv_recv_eq]
  simp only [toSpqrRecvModel, recvPanicsB] at h ⊢
  split <;> simp_all

/-- A projected `.ok v` rules out a model panic. -/
theorem spqrV1Recv_noPanic_of_recv_ok
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem} {stateBytes msgBytes : Bytes}
    {v : Bytes × Option Bytes}
    (h : (spqrV1Recv F K).recv stateBytes msgBytes = .ok v) :
    ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := fun hp => by
  rw [spqrV1Recv_recv_of_panic_err_false hp] at h
  cases h

/-- A projected `.error true` (`Error::StateDecode`) rules out a model panic. -/
theorem spqrV1Recv_noPanic_of_recv_err_true
    {F : CryptoGames.LibsignalSession.ShaCompress} {K : MlKem} {stateBytes msgBytes : Bytes}
    (h : (spqrV1Recv F K).recv stateBytes msgBytes = .error true) :
    ¬ (spqrV1Recv F K).recvPanics stateBytes msgBytes := fun hp => by
  rw [spqrV1Recv_recv_of_panic_err_false hp] at h
  cases h

theorem recv_of_msgPreamble_error
    (D : SpqrApiDeps) (hkdf : HkdfFn) {stateBytes msgBytes : Bytes} {e : LibsignalSpqrV1.Error}
    (hm : msgPreamble msgBytes = .error e) :
    LibsignalSpqrV1.recv D hkdf stateBytes msgBytes = .error (.err e) := by
  unfold LibsignalSpqrV1.recv
  simp only [hm, SpqrApiResult.ofError, Bind.bind, Except.bind]

theorem recv_of_decodeState_error
    (D : SpqrApiDeps) (hkdf : HkdfFn) {stateBytes msgBytes : Bytes}
    {m : MsgPreamble} {e : LibsignalSpqrV1.Error}
    (hm : msgPreamble msgBytes = .ok m)
    (hd : decodeState D stateBytes = .error e) :
    LibsignalSpqrV1.recv D hkdf stateBytes msgBytes = .error (.err e) := by
  unfold LibsignalSpqrV1.recv
  simp only [hm, hd, SpqrApiResult.ofError, Bind.bind, Except.bind]

theorem recv_vn_none_lt
    (D : SpqrApiDeps) (hkdf : HkdfFn) {stateBytes msgBytes : Bytes}
    {m : MsgPreamble} {prePb : PqRatchetStatePB D.V1StatePB}
    (hm : msgPreamble msgBytes = .ok m)
    (hd : decodeState D stateBytes = .ok prePb)
    (hvn : prePb.versionNegotiation = none)
    (hlt : m.version < (stateVersion prePb).toU8) :
    LibsignalSpqrV1.recv D hkdf stateBytes msgBytes = .error (.err .minimumVersion) := by
  unfold LibsignalSpqrV1.recv
  simp only [hm, hd, hvn, hlt, ↓reduceIte, SpqrApiResult.ofError, Bind.bind, Except.bind]

theorem recv_vn_none_inner_none
    (D : SpqrApiDeps) (hkdf : HkdfFn) {stateBytes msgBytes : Bytes}
    {m : MsgPreamble} {prePb : PqRatchetStatePB D.V1StatePB}
    (hm : msgPreamble msgBytes = .ok m)
    (hd : decodeState D stateBytes = .ok prePb)
    (hvn : prePb.versionNegotiation = none)
    (hinner : prePb.inner = none) :
    LibsignalSpqrV1.recv D hkdf stateBytes msgBytes = .ok { state := [], key := none } := by
  unfold LibsignalSpqrV1.recv
  have hlt : ¬ (m.version < 0#8) := by bv_omega
  simp only [hm, hd, hvn, stateVersion, hinner, Version.toU8, hlt, Option.isSome,
    Bool.not_true, Bool.not_false, Bool.and_false, Bool.and_true, Bool.false_eq_true,
    beq_self_eq_true, ↓reduceIte,
    SpqrApiResult.ofError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem recv_vn_none_inner_some_gt
    (D : SpqrApiDeps) (hkdf : HkdfFn) {stateBytes msgBytes : Bytes}
    {m : MsgPreamble} {prePb : PqRatchetStatePB D.V1StatePB} {pb : D.V1StatePB}
    (hm : msgPreamble msgBytes = .ok m)
    (hd : decodeState D stateBytes = .ok prePb)
    (hvn : prePb.versionNegotiation = none)
    (hinner : prePb.inner = some pb)
    (hgt : m.version > 1#8) :
    LibsignalSpqrV1.recv D hkdf stateBytes msgBytes = .error (.err .versionMismatch) := by
  unfold LibsignalSpqrV1.recv
  have hlt : ¬ (m.version < 1#8) := by bv_omega
  have h10 : (1#8 == 0#8) = false := by decide
  have hne : (m.version != 1#8) = true := by
    rw [bne_iff_ne]
    intro heq
    rw [heq] at hgt
    exact BitVec.lt_irrefl _ hgt
  simp only [hm, hd, hvn, stateVersion, hinner, Version.toU8, hlt, hne, h10, Option.isSome,
    Bool.not_false, Bool.and_true, ↓reduceIte,
    SpqrApiResult.ofError, Bind.bind, Except.bind]

theorem recv_vn_some_lt
    (D : SpqrApiDeps) (hkdf : HkdfFn) {stateBytes msgBytes : Bytes}
    {m : MsgPreamble} {prePb : PqRatchetStatePB D.V1StatePB} {vn : VersionNegotiationPB}
    (hm : msgPreamble msgBytes = .ok m)
    (hd : decodeState D stateBytes = .ok prePb)
    (hvn : prePb.versionNegotiation = some vn)
    (hlt : m.version < vn.minVersion.truncate 8) :
    LibsignalSpqrV1.recv D hkdf stateBytes msgBytes = .error (.err .minimumVersion) := by
  unfold LibsignalSpqrV1.recv
  simp only [hm, hd, hvn, hlt, ↓reduceIte, SpqrApiResult.ofError, Bind.bind, Except.bind]

theorem recv_vn_some_inner_none
    (D : SpqrApiDeps) (hkdf : HkdfFn) {stateBytes msgBytes : Bytes}
    {m : MsgPreamble} {prePb : PqRatchetStatePB D.V1StatePB} {vn : VersionNegotiationPB}
    (hm : msgPreamble msgBytes = .ok m)
    (hd : decodeState D stateBytes = .ok prePb)
    (hvn : prePb.versionNegotiation = some vn)
    (hinner : prePb.inner = none)
    (hge : ¬ (m.version < vn.minVersion.truncate 8)) :
    LibsignalSpqrV1.recv D hkdf stateBytes msgBytes = .ok { state := [], key := none } := by
  unfold LibsignalSpqrV1.recv
  simp only [hm, hd, hvn, stateVersion, hinner, Version.toU8, hge, Option.isSome,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, beq_self_eq_true, ↓reduceIte,
    SpqrApiResult.ofError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem recv_vn_some_inner_some_gt
    (D : SpqrApiDeps) (hkdf : HkdfFn) {stateBytes msgBytes : Bytes}
    {m : MsgPreamble} {prePb : PqRatchetStatePB D.V1StatePB}
    {vn : VersionNegotiationPB} {pb : D.V1StatePB}
    (hm : msgPreamble msgBytes = .ok m)
    (hd : decodeState D stateBytes = .ok prePb)
    (hvn : prePb.versionNegotiation = some vn)
    (hinner : prePb.inner = some pb)
    (hge : ¬ (m.version < vn.minVersion.truncate 8))
    (hgt : m.version > 1#8) :
    LibsignalSpqrV1.recv D hkdf stateBytes msgBytes = (do
      let chain0 ← SpqrApiResult.ofError (chainFrom hkdf prePb.chain (some vn))
      let (chain1, rawKey) ← SpqrApiResult.ofChainResult (chain0.recvKey hkdf 0#64 m.index)
      let newStateBytes := D.encodeState {
        chain := some chain1.intoPb
        versionNegotiation := some vn
        inner := some pb
      }
      .ok { key := some rawKey, state := newStateBytes }) := by
  have h10 : (1#8 == 0#8) = false := by decide
  unfold LibsignalSpqrV1.recv
  simp only [hm, hd, hvn, stateVersion, hinner, Version.toU8, hge, hgt, h10, Option.isSome,
    Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
    SpqrApiResult.ofError, Bind.bind, Except.bind]

theorem recv_vn_some_inner_some_lt
    (F : CryptoGames.LibsignalSession.ShaCompress) (K : MlKem) (hkdf : HkdfFn)
    {stateBytes msgBytes : Bytes}
    {m : MsgPreamble} {prePb : PqRatchetStatePB V1State}
    {vn : VersionNegotiationPB} {pb : V1State}
    (hm : msgPreamble msgBytes = .ok m)
    (hd : decodeState (spqrDeps F K) stateBytes = .ok prePb)
    (hvn : prePb.versionNegotiation = some vn)
    (hinner : prePb.inner = some pb)
    (hge : ¬ (m.version < vn.minVersion.truncate 8))
    (hlt : m.version < 1#8) :
    LibsignalSpqrV1.recv (spqrDeps F K) hkdf stateBytes msgBytes =
      match Direction.fromI32? vn.direction with
      | none => .error (.err .stateDecode)
      | some _ =>
        match chainFrom hkdf prePb.chain (some vn) with
        | .error e => .error (.err e)
        | .ok _ => .ok { state := [], key := none } := by
  have hm0 : m.version = 0#8 := by bv_omega
  have hge0 : ¬ (0#8 < vn.minVersion.truncate 8) := hm0 ▸ hge
  have hgt0 : ¬ (0#8 > 1#8) := by decide
  have h10 : (1#8 == 0#8) = false := by decide
  have h01 : (0#8 == 1#8) = false := by decide
  have h1gt0 : decide (1#8 > 0#8) = true := by decide
  unfold LibsignalSpqrV1.recv
  simp only [hm, hd, hvn, stateVersion, hinner, Version.toU8, hm0, hge0, hgt0,
    h10, h01, h1gt0, Option.isSome, Bool.not_true, Bool.and_false, Bool.and_true,
    Bool.false_eq_true, ↓reduceIte,
    Version.fromU8?, SpqrApiResult.ofError, SpqrApiResult.ofPanic, Bind.bind, Except.bind,
    Pure.pure, Except.pure, initInner]
  cases Direction.fromI32? vn.direction with
  | none => rfl
  | some dir =>
    cases chainFrom hkdf prePb.chain (some vn) <;> rfl

theorem recv_v1_ratchet_eq
    (D : SpqrApiDeps) (hkdf : HkdfFn) {stateBytes msgBytes : Bytes}
    {m : MsgPreamble} {prePb : PqRatchetStatePB D.V1StatePB} {pb : D.V1StatePB}
    (hm : msgPreamble msgBytes = .ok m)
    (hd : decodeState D stateBytes = .ok prePb)
    (hinner : prePb.inner = some pb)
    (hmv : m.version = 1#8)
    (hmin : ∀ vn, prePb.versionNegotiation = some vn → ¬ (1#8 < vn.minVersion.truncate 8)) :
    LibsignalSpqrV1.recv D hkdf stateBytes msgBytes = (do
      let sckaMsg ← D.msgDeserialize m.epoch m.remaining
      let st0 ← D.statesFromPb pb
      let (key, st1) ← D.statesRecv st0 sckaMsg
      if m.epoch == 0#64 then
        .error (.panic .recvEpochUnderflow)
      else do
        let msgKeyEpoch : Epoch := m.epoch - 1#64
        let chain0 ← SpqrApiResult.ofError (chainFrom hkdf prePb.chain prePb.versionNegotiation)
        let chain1 ←
          match key with
          | some epochSecret => SpqrApiResult.ofChainPanic (chain0.addEpoch hkdf epochSecret)
          | none => pure chain0
        let (chain2, msgKey) ← SpqrApiResult.ofChainResult (chain1.recvKey hkdf msgKeyEpoch m.index)
        let newStateBytes := D.encodeState {
          inner := some (D.statesIntoPb st1)
          versionNegotiation := none
          chain := some chain2.intoPb
        }
        let outKey : MessageKey := if msgKey.isEmpty then none else some msgKey
        .ok { state := newStateBytes, key := outKey }) := by
  have hlt1 : ¬ (1#8 < 1#8) := by decide
  have hgt1 : ¬ (1#8 > 1#8) := by decide
  have hne1 : (1#8 != 1#8) = false := by decide
  have h10 : (1#8 == 0#8) = false := by decide
  unfold LibsignalSpqrV1.recv
  cases hvn : prePb.versionNegotiation with
  | none =>
    simp only [hm, hd, hvn, stateVersion, hinner, Version.toU8, hmv, hlt1, hgt1, hne1, h10,
      Option.isSome, Bool.not_false, Bool.and_true, Bool.false_eq_true, beq_self_eq_true,
      ↓reduceIte, SpqrApiResult.ofError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl
  | some vn =>
    have hge := hmin vn hvn
    simp only [hm, hd, hvn, stateVersion, hinner, Version.toU8, hmv, hge, hgt1, h10,
      Option.isSome, Bool.not_true, Bool.and_false, Bool.false_eq_true, beq_self_eq_true,
      ↓reduceIte, SpqrApiResult.ofError, Bind.bind, Except.bind, Pure.pure, Except.pure]
    rfl

end CryptoVerification.SpqrV1.Top.Recv
