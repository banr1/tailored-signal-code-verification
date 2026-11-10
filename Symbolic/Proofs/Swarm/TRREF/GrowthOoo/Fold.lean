/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Grow.Defs
public import Symbolic.Proofs.Swarm.TRREF.SpqrSemOf
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.State

/-!
# SPQR V1 `SpqrOooBounded` Preservation Across State Encoding and Send

Proves that `SpqrOooBounded` holds on `(spqrDepsWithMac F K mac).encodeState statePb` whenever the
encoded byte length is `< 2^64` and `statePb` satisfies `PbOoo_fold`, and shows that the trusted
`Chain` operations and `sendAfterStates` preserve those parameter bounds.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthOoo

open Symbolic.Swarm.CREF (SpqrOooBounded)
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open Symbolic.Swarm.TRREF.SpqrSemOf

/-- Parameter bounds on `statePb.chain` and `statePb.versionNegotiation` matching
`SpqrOooBounded`. -/
abbrev PbOoo_fold {V1StatePB : Type} (statePb : PqRatchetStatePB V1StatePB) : Prop :=
  (∀ c ∈ statePb.chain, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000) ∧
  (∀ v ∈ statePb.versionNegotiation, ∀ p ∈ v.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000)

theorem spqrOooBounded_encodeState
    (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (hlen : ((spqrDepsWithMac F K mac).encodeState statePb).length < 2 ^ 64)
    (hch : ∀ c ∈ statePb.chain, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000)
    (hvn : ∀ v ∈ statePb.versionNegotiation, ∀ p ∈ v.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000) :
    SpqrOooBounded ((spqrDepsWithMac F K mac).encodeState statePb) :=
  ooo_of_decodeState (m := pbToPqRatchetState statePb) hlen hch hvn

private theorem except_bind_ok_fold {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem ofError_ok_fold {α : Type} {r : Except Error α} {a : α}
    (h : SpqrApiResult.ofError r = .ok a) : r = .ok a := by
  cases r with
  | error e => cases h
  | ok v => cases h; rfl

private theorem ofChainPanic_ok_fold {α : Type} {r : Except ChainPanic α} {a : α}
    (h : SpqrApiResult.ofChainPanic r = .ok a) : r = .ok a := by
  cases r with
  | error e => cases h
  | ok v => cases h; rfl

private theorem ofChainResult_ok_fold {α : Type} {r : ChainResult α} {a : α}
    (h : SpqrApiResult.ofChainResult r = .ok a) : r = .ok a := by
  cases r with
  | error e => cases h
  | ok v => cases h; rfl

theorem intoPb_params_mem_fold {c : Chain} {p : ChainParamsPB} (hp : p ∈ c.intoPb.params) :
    p = c.params :=
  (Option.some.inj hp).symm

theorem pbOoo_of_decodeState_fold
    (F : ShaCompress) (K : MlKem) (mac : HmacFn)
    (st : Bytes) (statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (hb : SpqrOooBounded st)
    (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok statePb) :
    PbOoo_fold statePb := by
  unfold decodeState at hdec; split at hdec
  · injection hdec with hst; subst hst
    exact ⟨fun c hc => (by cases hc), fun v hv => (by cases hv)⟩
  · dsimp only [spqrDepsWithMac] at hdec
    cases hp : Proto.decodeState st with
    | error _ => simp [hp] at hdec
    | ok rawSt =>
      rw [hp] at hdec; dsimp only at hdec; injection hdec with hst; subst hst
      exact hb rawSt hp

theorem chain_fromPb_params_fold {pb : ChainPB} {c : Chain} (h : Chain.fromPb pb = .ok c) :
    pb.params = some c.params := by
  unfold Chain.fromPb at h
  cases hd : Direction.fromI32? pb.direction with
  | none => simp [hd, Bind.bind, Except.bind] at h
  | some dir =>
    cases hl : Chain.linksFromPb pb.links with
    | error _ => simp [hd, hl, Bind.bind, Except.bind] at h
    | ok links =>
      cases hp : pb.params with
      | none => simp [hd, hl, hp, Bind.bind, Except.bind] at h
      | some params =>
        simp only [hd, hl, hp, Bind.bind, Except.bind] at h
        injection h with hc; subst hc; rfl

theorem chainFromVersionNegotiation_params_fold {hkdf : HkdfFn} {vn : VersionNegotiationPB} {c : Chain}
    (h : chainFromVersionNegotiation hkdf vn = .ok c) : vn.chainParams = some c.params := by
  unfold chainFromVersionNegotiation at h
  cases hd : Direction.fromI32? vn.direction with
  | none => simp [hd, Bind.bind, Except.bind] at h
  | some dir =>
    cases hp : vn.chainParams with
    | none => simp [hd, hp, Bind.bind, Except.bind] at h
    | some params =>
      simp only [hd, hp, Bind.bind, Except.bind] at h
      unfold Chain.new at h; injection h with hc; subst hc; rfl

theorem chain_addEpoch_params_fold {hkdf : HkdfFn} {c c' : Chain} {es : EpochSecret}
    (h : c.addEpoch hkdf es = .ok c') : c'.params = c.params := by
  unfold Chain.addEpoch at h; split at h
  · contradiction
  · split at h
    · contradiction
    · injection h with hc; subst hc; rfl

theorem chain_sendKey_params_fold {hkdf : HkdfFn} {c c' : Chain} {ep : Epoch} {out : BitVec 32 × Bytes}
    (h : c.sendKey hkdf ep = .ok (c', out)) : c'.params = c.params := by
  unfold Chain.sendKey at h; split at h
  · contradiction
  rcases except_bind_ok_fold h with ⟨epochIndex0, _, h⟩; dsimp only at h
  generalize hself1 :
    (if (c.sendEpoch != ep) = true then
      let dropCount := epochIndex0 - EPOCHS_TO_KEEP_PRIOR_TO_SEND_EPOCH
      let epochIndex' := epochIndex0 - dropCount
      let links1 := c.links.drop dropCount
      let links2 := Chain.clearSendNextPrefix epochIndex' links1
      ({ c with sendEpoch := ep, links := links2 }, epochIndex')
    else (c, epochIndex0)) = pair1 at h
  rcases pair1 with ⟨self1, epochIndex⟩
  have hp1 : self1.params = c.params := by
    split at hself1
    · rcases Prod.mk.inj hself1 with ⟨rfl, _⟩; rfl
    · rcases Prod.mk.inj hself1 with ⟨rfl, _⟩; rfl
  dsimp only at h
  cases hget : self1.links[epochIndex]? with
  | none => simp [hget] at h
  | some link =>
    rw [hget] at h; dsimp only [Bind.bind, Except.bind] at h
    rcases except_bind_ok_fold h with ⟨⟨send', out'⟩, _, h⟩
    rcases Prod.mk.inj (Except.ok.inj h) with ⟨rfl, _⟩
    exact hp1

/-- `sendAfterStates` keeps `versionNegotiation` unchanged and produces a `chainPb` whose
parameters come from `statePb.chain` or `statePb.versionNegotiation`. -/
theorem sendAfterStates_ooo_fold {D : SpqrApiDeps} {hkdf : HkdfFn} {statePb : PqRatchetStatePB D.V1StatePB}
    {msg : D.MessageV1} {key : Option EpochSecret} {state : D.States} {out : Send}
    (hooo : PbOoo_fold statePb)
    (h : sendAfterStates D hkdf statePb msg key state = .ok out) :
    ∃ chainPb : Option ChainPB,
      (∀ c ∈ chainPb, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000) ∧
      out.state = D.encodeState {
        inner := some (D.statesIntoPb state)
        versionNegotiation := statePb.versionNegotiation
        chain := chainPb } := by
  unfold sendAfterStates at h
  extract_lets jpT ep jpC1 jpC at h
  have hT : ∀ x, jpT x = .ok out → out.state = D.encodeState {
      inner := some (D.statesIntoPb state)
      versionNegotiation := statePb.versionNegotiation
      chain := x.2.2 } := by
    rintro ⟨index, msgKey, chainPb⟩ hj
    simp only [jpT] at hj
    split at hj
    · cases hj
    · split at hj
      · cases hj
      · cases hj; rfl
  have hC1 : ∀ c1 : Chain, c1.params.maxOooKeysOrDefault.toNat ≤ 2000 → jpC1 c1 = .ok out →
      ∃ chainPb : Option ChainPB,
        (∀ c ∈ chainPb, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000) ∧
        out.state = D.encodeState {
          inner := some (D.statesIntoPb state)
          versionNegotiation := statePb.versionNegotiation
          chain := chainPb } := by
    intro c1 hc1 hj
    simp only [jpC1] at hj
    split at hj
    · simp [bind, Except.bind] at hj
    · rcases except_bind_ok_fold hj with ⟨⟨chain2, idx, mk⟩, h2, hj⟩
      simp only [bind, Except.bind, pure, Except.pure] at hj
      refine ⟨some chain2.intoPb, fun c hc p hp => ?_, hT (idx, mk, some chain2.intoPb) hj⟩
      cases hc
      rw [intoPb_params_mem_fold hp, chain_sendKey_params_fold (ofChainResult_ok_fold h2)]
      exact hc1
  have hC : ∀ ch : Option Chain, (∀ c0 ∈ ch, c0.params.maxOooKeysOrDefault.toNat ≤ 2000) →
      jpC ch = .ok out →
      ∃ chainPb : Option ChainPB,
        (∀ c ∈ chainPb, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000) ∧
        out.state = D.encodeState {
          inner := some (D.statesIntoPb state)
          versionNegotiation := statePb.versionNegotiation
          chain := chainPb } := by
    intro ch hch hj
    cases ch with
    | none =>
      simp only [jpC] at hj
      split at hj
      · simp only [bind, Except.bind, pure, Except.pure] at hj
        exact ⟨none, fun c hc => (by cases hc), hT (0#32, [], none) hj⟩
      · simp [bind, Except.bind] at hj
    | some c0 =>
      simp only [jpC] at hj
      split at hj
      · rcases except_bind_ok_fold hj with ⟨c1, h1, hj⟩
        exact hC1 c1 (by rw [chain_addEpoch_params_fold (ofChainPanic_ok_fold h1)]; exact hch c0 rfl) hj
      · simp only [bind, Except.bind, pure, Except.pure] at hj
        exact hC1 c0 (hch c0 rfl) hj
  cases hpb : statePb.chain with
  | some pb =>
    simp only [hpb] at h
    rcases except_bind_ok_fold h with ⟨c, hc, h⟩
    simp only [bind, Except.bind, pure, Except.pure] at h
    exact hC (some c) (fun c0 hc0 => by
      cases hc0; exact hooo.1 pb hpb _ (chain_fromPb_params_fold (ofError_ok_fold hc))) h
  | none =>
    simp only [hpb] at h
    split at h
    · rename_i vn hvn
      split at h
      · rcases except_bind_ok_fold h with ⟨c, hc, h⟩
        simp only [bind, Except.bind, pure, Except.pure] at h
        exact hC (some c) (fun c0 hc0 => by
          cases hc0
          exact hooo.2 vn hvn _ (chainFromVersionNegotiation_params_fold (ofError_ok_fold hc))) h
      · simp only [bind, Except.bind, pure, Except.pure] at h
        exact hC none (fun c0 hc0 => (by cases hc0)) h
    · simp [bind, Except.bind] at h

/-- `sendAfterStates` preserves `SpqrOooBounded` when the output state has byte length `< 2^64`. -/
theorem spqr_sendAfterStates_oooBounded_fold (F : ShaCompress) (K : MlKem) (mac : HmacFn) (st : Bytes)
    (statePb : PqRatchetStatePB (spqrDepsWithMac F K mac).V1StatePB)
    (msg : (spqrDepsWithMac F K mac).MessageV1) (key : Option EpochSecret)
    (st1 : (spqrDepsWithMac F K mac).States) (out : Send)
    (hb : SpqrOooBounded st) (hdec : decodeState (spqrDepsWithMac F K mac) st = .ok statePb)
    (hsend : sendAfterStates (spqrDepsWithMac F K mac) (spqrHkdfWith F) statePb msg key st1 = .ok out)
    (hout_len : out.state.length < 2 ^ 64) :
    SpqrOooBounded out.state := by
  have hooo := pbOoo_of_decodeState_fold F K mac st statePb hb hdec
  rcases sendAfterStates_ooo_fold hooo hsend with ⟨chainPb, hcp, hout⟩
  rw [hout] at hout_len ⊢
  exact spqrOooBounded_encodeState F K mac _ hout_len hcp hooo.2

end Symbolic.Swarm.TRREF.GrowthOoo
