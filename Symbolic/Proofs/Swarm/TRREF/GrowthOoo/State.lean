/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
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
public import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.Chain
import Symbolic.Proofs.Swarm.TRREF.GrowthOoo.Prims
import VCVio.Prelude.Core

/-!
# SPQR V1 `PqRatchetState` Parameter-Preservation Roundtrip

Proves that `VersionNegotiationPB` roundtrips under `Proto.mergeFieldsLoop` and that decoding
`PqRatchetState.encodeRaw m` (when under `2^64` bytes) preserves `versionNegotiation` and all
`chain` parameters, yielding the unfolded `SpqrOooBounded` consequence `ooo_of_decodeState`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.GrowthOoo

open CryptoVerification
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Prost.MessageMerge CryptoVerification.SpqrV1.Prost.MessageMerge.SymP3

private theorem encodeBytesField_val_len_le (tag : BitVec 32) (v : Bytes) :
    v.length ≤ (Proto.encodeBytesField tag v).length := by
  unfold Proto.encodeBytesField Proto.encodeBytesUncond
  cases hv : v.isEmpty
  · simp [List.length_append]; omega
  · have hv0 : v = [] := List.isEmpty_iff.mp hv
    subst hv0; simp

private theorem encodeOptMessage_sub_len_le {S : Type} (encodeRaw : S → Bytes)
    (tag : BitVec 32) (opt : Option S) (sub : S) (h : opt = some sub) :
    (encodeRaw sub).length ≤ (Proto.encodeOptMessage encodeRaw tag opt).length := by
  subst h
  unfold Proto.encodeOptMessage Proto.encodeMessage
  simp [List.length_append]; omega

/-- `Proto.mergeFieldsLoop` on `VersionNegotiationPB.encodeRaw vn` (with byte length `< 2^64` and
`1 ≤ depth'`) from `default` returns `.ok vn`. -/
theorem versionNegotiationPB_mergeFieldsLoop_encodeRaw
    (vn : VersionNegotiationPB) {depth' : Nat}
    (hlen : (VersionNegotiationPB.encodeRaw vn).length < 2 ^ 64)
    (hdepth : 1 ≤ depth') :
    Proto.mergeFieldsLoop VersionNegotiationPB.mergeField
      (VersionNegotiationPB.encodeRaw vn).length default (VersionNegotiationPB.encodeRaw vn) depth' = .ok vn := by
  obtain ⟨d, rfl⟩ : ∃ d, depth' = d + 1 := ⟨depth' - 1, by omega⟩
  have hauth_len : vn.authKey.length < 2 ^ 64 := by
    have hle := encodeBytesField_val_len_le 1#32 vn.authKey
    unfold VersionNegotiationPB.encodeRaw at hlen
    simp only [List.length_append] at hlen
    omega
  have hcp_len : ∀ sub, vn.chainParams = some sub → (ChainParamsPB.encodeRaw sub).length < 2 ^ 64 := by
    intro sub hsub
    have hle := encodeOptMessage_sub_len_le ChainParamsPB.encodeRaw 4#32 vn.chainParams sub hsub
    unfold VersionNegotiationPB.encodeRaw at hlen
    simp only [List.length_append] at hlen
    omega
  unfold VersionNegotiationPB.encodeRaw
  rw [← List.append_nil (Proto.encodeOptMessage ChainParamsPB.encodeRaw 4#32 vn.chainParams)]
  simp only [List.append_assoc]
  rw [mergeFieldsLoop_encodeBytesField protoPrefixStep_versionNegotiationPB_mergeField
        (fun m v => { m with authKey := v }) default 1#32 vn.authKey _ (d + 1)
        (by decide) (by decide) hauth_len (by intro _; rfl) (by intro _; rfl)]
  rw [mergeFieldsLoop_encodeInt32Field protoPrefixStep_versionNegotiationPB_mergeField
        (fun m v => { m with direction := v }) _ 2#32 vn.direction _ (d + 1)
        (by decide) (by decide) (by intro _; rfl) (by intro _; rfl)]
  rw [mergeFieldsLoop_encodeInt32Field protoPrefixStep_versionNegotiationPB_mergeField
        (fun m v => { m with minVersion := v }) _ 3#32 vn.minVersion _ (d + 1)
        (by decide) (by decide) (by intro _; rfl) (by intro _; rfl)]
  cases hcp : vn.chainParams with
  | none =>
    dsimp only [Proto.encodeOptMessage, List.nil_append]
    rw [mergeFieldsLoop_nil]
    cases vn
    simp at hcp
    subst hcp
    rfl
  | some sub =>
    have hsub_len : (ChainParamsPB.encodeRaw sub).length < 2 ^ 64 := hcp_len sub hcp
    dsimp only [Proto.encodeOptMessage]
    rw [mergeFieldsLoop_encodeMessage protoPrefixStep_versionNegotiationPB_mergeField
          ChainParamsPB.mergeField ChainParamsPB.encodeRaw
          (fun m v => { m with chainParams := some v })
          _ ((default : VersionNegotiationPB).chainParams.getD default) sub 4#32 [] d
          (by decide) (by decide) hsub_len
          (by intro bs
              simp only [VersionNegotiationPB.mergeField, Proto.mergeOptMessage]
              cases Proto.mergeMessage ChainParamsPB.mergeField .lengthDelimited
                ((default : VersionNegotiationPB).chainParams.getD default) bs (d + 1) <;> rfl)]
    have hdef : ((default : VersionNegotiationPB).chainParams.getD default) = (default : ChainParamsPB) := rfl
    rw [hdef, chainParamsPB_mergeFieldsLoop_encodeRaw sub d]
    dsimp only [Bind.bind, Except.bind]
    rw [mergeFieldsLoop_nil]
    cases vn
    simp at hcp
    subst hcp
    rfl

theorem pqRatchetState_step_tag1
    (m0 : PqRatchetState) (opt : Option VersionNegotiationPB) (rest : Bytes) (d : Nat)
    (hm0 : m0.versionNegotiation = none)
    (hlen : (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 opt ++ rest).length < 2 ^ 64)
    (hd : 1 ≤ d) :
    Proto.mergeFieldsLoop PqRatchetState.mergeField
      (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 opt ++ rest).length
      m0 (Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 opt ++ rest) (d + 1) =
    Proto.mergeFieldsLoop PqRatchetState.mergeField
      rest.length { m0 with versionNegotiation := opt } rest (d + 1) := by
  cases opt with
  | none =>
    have hmeq : { m0 with versionNegotiation := none } = m0 := by
      cases m0; simp at hm0; subst hm0; rfl
    dsimp only [Proto.encodeOptMessage, List.nil_append]
    rw [hmeq]
  | some vn =>
    have hsub : (VersionNegotiationPB.encodeRaw vn).length < 2 ^ 64 := by
      have hle := encodeOptMessage_sub_len_le VersionNegotiationPB.encodeRaw 1#32 (some vn) vn rfl
      simp only [List.length_append] at hlen
      omega
    dsimp only [Proto.encodeOptMessage]
    rw [mergeFieldsLoop_encodeMessage protoPrefixStep_pqRatchetState_mergeField
          VersionNegotiationPB.mergeField VersionNegotiationPB.encodeRaw
          (fun m v => { m with versionNegotiation := some v })
          m0 (m0.versionNegotiation.getD default) vn 1#32 rest d
          (by decide) (by decide) hsub
          (by intro bs
              simp only [PqRatchetState.mergeField, Proto.mergeOptMessage]
              cases Proto.mergeMessage VersionNegotiationPB.mergeField .lengthDelimited
                (m0.versionNegotiation.getD default) bs (d + 1) <;> rfl)]
    rw [hm0]
    dsimp only [Option.getD]
    rw [versionNegotiationPB_mergeFieldsLoop_encodeRaw vn hsub hd]
    rfl

theorem pqRatchetState_step_tag2
    (m0 st : PqRatchetState) (opt : Option ChainPB) (rest : Bytes) (d : Nat)
    (hm0 : m0.chain = none)
    (hlen : (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 opt ++ rest).length < 2 ^ 64)
    (hd : 1 ≤ d)
    (hloop : Proto.mergeFieldsLoop PqRatchetState.mergeField
      (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 opt ++ rest).length
      m0 (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 opt ++ rest) (d + 1) = .ok st) :
    ∃ m1 : PqRatchetState,
      m1.versionNegotiation = m0.versionNegotiation ∧
      (∀ c ∈ m1.chain, ∃ c₀ ∈ opt, c.params = c₀.params) ∧
      Proto.mergeFieldsLoop PqRatchetState.mergeField rest.length m1 rest (d + 1) = .ok st := by
  cases opt with
  | none =>
    dsimp only [Proto.encodeOptMessage, List.nil_append] at hloop
    refine ⟨m0, rfl, ?_, hloop⟩
    intro c hc
    rw [hm0] at hc
    cases hc
  | some ch =>
    have hsub : (ChainPB.encodeRaw ch).length < 2 ^ 64 := by
      have hle := encodeOptMessage_sub_len_le ChainPB.encodeRaw 2#32 (some ch) ch rfl
      simp only [List.length_append] at hlen
      omega
    dsimp only [Proto.encodeOptMessage] at hloop
    rw [mergeFieldsLoop_encodeMessage protoPrefixStep_pqRatchetState_mergeField
          ChainPB.mergeField ChainPB.encodeRaw
          (fun m v => { m with chain := some v })
          m0 (m0.chain.getD default) ch 2#32 rest d
          (by decide) (by decide) hsub
          (by intro bs
              simp only [PqRatchetState.mergeField, Proto.mergeOptMessage]
              cases Proto.mergeMessage ChainPB.mergeField .lengthDelimited
                (m0.chain.getD default) bs (d + 1) <;> rfl)] at hloop
    rw [hm0] at hloop
    dsimp only [Option.getD] at hloop
    rcases hch_loop : Proto.mergeFieldsLoop ChainPB.mergeField
        (ChainPB.encodeRaw ch).length default (ChainPB.encodeRaw ch) d with e | ch'
    · rw [hch_loop] at hloop
      nomatch hloop
    · rw [hch_loop] at hloop
      dsimp only [Bind.bind, Except.bind] at hloop
      have hparams := chainPB_mergeFieldsLoop_encodeRaw_params hsub hd hch_loop
      refine ⟨{ m0 with chain := some ch' }, rfl, ?_, hloop⟩
      intro c hc
      simp only [Option.mem_def, Option.some.injEq] at hc
      subst hc
      exact ⟨ch, by simp, hparams⟩

def encodeOptInner : Option PqRatchetState.Inner → Bytes
  | none => []
  | some i => PqRatchetState.Inner.encode i

theorem pqRatchetState_step_tag3
    (m1 st : PqRatchetState) (optInner : Option PqRatchetState.Inner) (d : Nat)
    (hlen : (encodeOptInner optInner).length < 2 ^ 64)
    (hloop : Proto.mergeFieldsLoop PqRatchetState.mergeField
      (encodeOptInner optInner).length m1 (encodeOptInner optInner) (d + 1) = .ok st) :
    st.versionNegotiation = m1.versionNegotiation ∧ st.chain = m1.chain := by
  cases optInner with
  | none =>
    dsimp only [encodeOptInner] at hloop
    rw [mergeFieldsLoop_nil] at hloop
    injection hloop with hst
    subst hst
    exact ⟨rfl, rfl⟩
  | some inner =>
    cases inner with
    | v1 v =>
      dsimp only [encodeOptInner, PqRatchetState.Inner.encode] at hlen hloop
      have hv_len : (V1State.encodeRaw v).length < 2 ^ 64 := by
        unfold Proto.encodeMessage at hlen
        simp only [List.length_append] at hlen
        omega
      rw [← List.append_nil (Proto.encodeMessage V1State.encodeRaw 3#32 v)] at hloop
      have hstep := mergeFieldsLoop_encodeMessage protoPrefixStep_pqRatchetState_mergeField
        V1State.mergeField V1State.encodeRaw
        (fun m v' => { m with inner := some (.v1 v') })
        m1 (match m1.inner with | some (.v1 v0) => v0 | none => default) v 3#32 [] d
        (by decide) (by decide) hv_len
        (by intro bs
            simp only [PqRatchetState.mergeField, PqRatchetState.Inner.merge]
            rcases m1.inner with _ | ⟨v0⟩ <;>
              cases Proto.mergeMessage V1State.mergeField .lengthDelimited _ bs (d + 1) <;> rfl)
      rw [hstep] at hloop
      rcases hv_loop : Proto.mergeFieldsLoop V1State.mergeField
          (V1State.encodeRaw v).length (match m1.inner with | some (.v1 v0) => v0 | none => default)
          (V1State.encodeRaw v) d with e | v'
      · rw [hv_loop] at hloop
        nomatch hloop
      · rw [hv_loop] at hloop
        dsimp only [Bind.bind, Except.bind] at hloop
        rw [mergeFieldsLoop_nil] at hloop
        injection hloop with hst
        subst hst
        exact ⟨rfl, rfl⟩

private theorem pqRatchetState_encodeRaw_eq (m : PqRatchetState) :
    PqRatchetState.encodeRaw m =
      Proto.encodeOptMessage VersionNegotiationPB.encodeRaw 1#32 m.versionNegotiation ++
      (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 m.chain ++ encodeOptInner m.inner) := by
  unfold PqRatchetState.encodeRaw encodeOptInner
  cases m.inner <;> simp [List.append_assoc]

/-- Decoding `PqRatchetState.encodeRaw m` (when `< 2^64` bytes) preserves `versionNegotiation` and
all `chain` parameters. -/
theorem pqRatchetState_decode_encodeRaw_params
    {m st : PqRatchetState}
    (hlen : (PqRatchetState.encodeRaw m).length < 2 ^ 64)
    (hdec : PqRatchetState.decode (PqRatchetState.encodeRaw m) = .ok st) :
    (∀ c ∈ st.chain, ∃ c₀ ∈ m.chain, c.params = c₀.params) ∧
    st.versionNegotiation = m.versionNegotiation := by
  change Proto.mergeFieldsLoop PqRatchetState.mergeField
    (PqRatchetState.encodeRaw m).length default (PqRatchetState.encodeRaw m) (99 + 1) = .ok st at hdec
  rw [pqRatchetState_encodeRaw_eq m] at hlen hdec
  rw [pqRatchetState_step_tag1 default m.versionNegotiation _ 99 rfl hlen (by decide)] at hdec
  have hlen2 : (Proto.encodeOptMessage ChainPB.encodeRaw 2#32 m.chain ++
      encodeOptInner m.inner).length < 2 ^ 64 := by
    simp only [List.length_append] at hlen ⊢
    omega
  obtain ⟨m1, hvn1, hch1, hdec2⟩ := pqRatchetState_step_tag2
    { (default : PqRatchetState) with versionNegotiation := m.versionNegotiation }
    st m.chain _ 99 rfl hlen2 (by decide) hdec
  have hlen3 : (encodeOptInner m.inner).length < 2 ^ 64 := by
    simp only [List.length_append] at hlen2
    omega
  obtain ⟨hvn2, hch2⟩ := pqRatchetState_step_tag3 m1 st m.inner 99 hlen3 hdec2
  refine ⟨?_, hvn2.trans hvn1⟩
  intro c hc
  rw [hch2] at hc
  exact hch1 c hc

/-- Unfolded `SpqrOooBounded` consequence for `PqRatchetState.encodeRaw m`. -/
theorem ooo_of_decodeState
    {m : PqRatchetState}
    (hlen : (PqRatchetState.encodeRaw m).length < 2 ^ 64)
    (hch : ∀ c ∈ m.chain, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000)
    (hvn : ∀ v ∈ m.versionNegotiation, ∀ p ∈ v.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000) :
    ∀ st, PqRatchetState.decode (PqRatchetState.encodeRaw m) = .ok st →
      (∀ c ∈ st.chain, ∀ p ∈ c.params, p.maxOooKeysOrDefault.toNat ≤ 2000) ∧
      (∀ v ∈ st.versionNegotiation, ∀ p ∈ v.chainParams, p.maxOooKeysOrDefault.toNat ≤ 2000) := by
  intro st hdec
  obtain ⟨hc_eq, hvn_eq⟩ := pqRatchetState_decode_encodeRaw_params hlen hdec
  refine ⟨fun c hc p hp => ?_, fun v hv p hp => ?_⟩
  · obtain ⟨c₀, hc₀, hparams⟩ := hc_eq c hc
    rw [hparams] at hp
    exact hch c₀ hc₀ p hp
  · rw [hvn_eq] at hv
    exact hvn v hv p hp

end Symbolic.Swarm.TRREF.GrowthOoo
