/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.StoredRk
public import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonRep
public import Symbolic.Proofs.Swarm.CREF.TR.G1.CaseSplit
import Batteries.Data.UInt
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
import DY.EquationalTheory.DiffieHellman
import DY.EquationalTheory.KdfExtract
import DY.EquationalTheory.Sign
import Symbolic.Specifications.Model.EquationalTheory.Trunc
import Symbolic.Specifications.Model.EquationalTheory.TrWireMsg
import Symbolic.Specifications.Model.EquationalTheory.X25519
import Symbolic.Specifications.Model.EquationalTheory.Spqr
import Symbolic.Proofs.Refinement.TripleRatchet.WireCovered
import Symbolic.Proofs.SpecLemmas.Model.EquationalTheory.TrWireMsg
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.RecvDecStepMac
import Symbolic.Proofs.Swarm.CREF.TR.RecvRep
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
import Symbolic.DYBridge.DY.EquationalTheory.KdfExtract

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.RecvPrekeyProm.HxplG2W

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (RecvChain computeMac messageVersion)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.TrWire (EncodingVariation canonicalVariation)
open DY.Libsignal.TripleRatchet
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR
open Symbolic.Swarm.CREF.TR.RecvRep

local notation "SpqrSem" => OpaqueSymbolSemantics

unseal DY.Bytes in
private instance subKdf0PKD (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance subTrWire0PKD (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeTrWire g) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, trWireFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

unseal DY.Bytes in
private instance subDhPkPKD (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant0PKD (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _
    ⟨fun _ _ => by simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

private theorem termShapeId_iff_termShapeId_x25519Key_pkd (pk : DY.Bytes) :
    G1.TermShapeId pk ↔ G1.TermShapeId (DY.X25519.normalizeX25519Key pk) := by
  unfold DY.X25519.normalizeX25519Key
  have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
  cases hview : pk.view? DY.X25519.Variant.SubF with
  | none => exact Iff.rfl
  | some x =>
    rw [hview] at hv; dsimp only at hv ⊢; rw [← hv]
    constructor
    · intro h i S g
      have h1 := h i S g
      rw [G1.shape_variant_pack_sid] at h1
      have h2 := congrArg (fun u : DY.Bytes => u.view? DY.X25519.Variant.SubF) h1
      rw [DY.BytesView.view_pack (SubF := DY.X25519.Variant.SubF),
          DY.BytesView.view_pack (SubF := DY.X25519.Variant.SubF)] at h2
      injection h2 with hmk
      exact congrArg DY.X25519.Variant.SubF.key hmk
    · intro h i S g
      rw [G1.shape_variant_pack_sid, h i S g]

private theorem gamma_dhPk_ne_nil_pkd (i : ExternInterpretation)
    (hEq : ExternCryptoLawsHold i) (S : SpqrSem) (g : Ghost) (a : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dhPk a) ≠ [] := by
  have hlen : (gamma i S g (DY.DiffieHellman.dhPk a)).length = 32 := by
    unfold gamma gamma'
    rw [show DY.DiffieHellman.dhPk a = ({ sk := a } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
        DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g)]
    exact hEq.x25519_public_key_length _
  intro hnil; rw [hnil] at hlen; cases hlen

private theorem not_mem_ptAtoms_of_view_random_none_pkd
    (r₀ : ProtocolSetup) (ms : List Move) (u : DY.Bytes)
    (h : u.view? DY.Random.Random = none) :
    u ∉ plaintextTerms (runVis r₀ ms) ++ [] := by
  intro hp
  rw [List.append_nil] at hp
  exact G1.not_mem_ptAtoms_of_view_random_isNone r₀ ms [] (fun _ hv => nomatch hv) u
    (Option.isNone_iff_eq_none.mpr h) (by rwa [List.append_nil])

unseal DY.Bytes in
private theorem notSpqrHeaded_dhPk_pkd (a : DY.Bytes) :
    G1.notSpqrHeaded (DY.DiffieHellman.dhPk a) := by
  dsimp only [G1.notSpqrHeaded, DY.DiffieHellman.dhPk]
  simp only [Symbolic.DYBridge.DY.Bytes.view?_pack_cross]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

unseal DY.Bytes in
private theorem notOpaqueHeaded_dhPk_pkd (a : DY.Bytes) :
    G1.notOpaqueHeaded (DY.DiffieHellman.dhPk a) := by
  dsimp only [G1.notOpaqueHeaded, DY.DiffieHellman.dhPk]
  simp only [Symbolic.DYBridge.DY.Bytes.view?_pack_cross]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

unseal DY.Bytes in
private theorem dhPk_not_mem_ptAtoms_pkd (r₀ : ProtocolSetup) (ms : List Move) (a : DY.Bytes) :
    DY.DiffieHellman.dhPk a ∉ plaintextTerms (runVis r₀ ms) ++ [] :=
  not_mem_ptAtoms_of_view_random_none_pkd r₀ ms _
    (by dsimp only [DY.DiffieHellman.dhPk]; exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)

unseal DY.Bytes in
private theorem variant_pack_not_mem_ptAtoms_pkd (r₀ : ProtocolSetup) (ms : List Move)
    (x : DY.X25519.Variant.SubF DY.Bytes) :
    x.pack ∉ plaintextTerms (runVis r₀ ms) ++ [] :=
  not_mem_ptAtoms_of_view_random_none_pkd r₀ ms _
    (Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _)

theorem false_of_noRatchet_sameBase_dhPk_pkd
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g' : Ghost) (ms₁ : List Move)
    (body : HwBytes) (m : SignalMessage) (st₀ : TRState) (c : RecvChain)
    (t₀ : DY.Bytes) (msg₀ : TRSignalMsg) (x : DY.X25519.Variant.SubF DY.Bytes)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g' ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hNotCol : ¬RecvCollision interpretation r₀ S g' ms₁ t₀)
    (hst₀ : st₀ ∈ availableStates r₀ (runTraceMoves r₀ ms₁))
    (hc_mem : c ∈ st₀.recv)
    (hCaseA' : G1.CaseA' c.ratchetKey)
    (hVar : c.ratchetKey.view? DY.X25519.Variant.SubF = some x)
    (hrk_ne : msg₀.ratchetKey ≠ c.ratchetKey)
    (hγ_pk : gamma interpretation S g' c.ratchetKey = m.senderRatchetKey.bytes.toList)
    (hbase : DY.X25519.normalizeX25519Key msg₀.ratchetKey = DY.X25519.normalizeX25519Key c.ratchetKey)
    (hPlain₀ : msg₀.ratchetKey.view? DY.X25519.Variant.SubF = none) :
    False := by
  have hxk₀ : DY.X25519.normalizeX25519Key msg₀.ratchetKey = msg₀.ratchetKey := by
    unfold DY.X25519.normalizeX25519Key; rw [hPlain₀]
  obtain ⟨a, ha⟩ := hCaseA'.2
  have hmsg_dhPk : msg₀.ratchetKey = DY.DiffieHellman.dhPk a :=
    hxk₀.symm.trans (hbase.trans ha)
  have hsid_c : G1.TermShapeId c.ratchetKey :=
    (termShapeId_iff_termShapeId_x25519Key_pkd c.ratchetKey).mpr hCaseA'.1.1
  have hsid_msg₀ : G1.TermShapeId msg₀.ratchetKey :=
    (termShapeId_iff_termShapeId_x25519Key_pkd msg₀.ratchetKey).mpr (hbase.symm ▸ hCaseA'.1.1)
  have hns_msg₀ : G1.notSpqrHeaded msg₀.ratchetKey :=
    hmsg_dhPk ▸ notSpqrHeaded_dhPk_pkd a
  have hno_msg₀ : G1.notOpaqueHeaded msg₀.ratchetKey :=
    hmsg_dhPk ▸ notOpaqueHeaded_dhPk_pkd a
  have hne_nil : gamma interpretation S g' msg₀.ratchetKey ≠ [] := by
    rw [hmsg_dhPk]
    exact gamma_dhPk_ne_nil_pkd interpretation hEq S g' a
  have hx₁ : (msg₀.ratchetKey, (gamma' interpretation S g' msg₀.ratchetKey).shape,
      gamma interpretation S g' msg₀.ratchetKey) ∈
      (G1.recvNewTerms interpretation r₀ S g' ms₁ t₀ msg₀).flatMap
        (fun u => (gamma' interpretation S g' u).memo) := by
    rw [List.mem_flatMap]
    exact ⟨t₀, List.mem_cons_self ..,
      G1.parse_rk_mem_memo_tr interpretation S g' hparse₀ hne_nil hns_msg₀ hno_msg₀⟩
  have hx₂ : (c.ratchetKey, c.ratchetKey, gamma interpretation S g' c.ratchetKey) ∈
      (prefixTerms r₀ (runTraceMoves r₀ ms₁) (runVis r₀ ms₁)).flatMap
        (fun u => (gamma' interpretation S g' u).memo) :=
    G1.rk_mem_prefixTerms_memo_tr interpretation S g' hst₀ hc_mem hsid_c
  have hsh_ne : (gamma' interpretation S g' msg₀.ratchetKey).shape ≠ c.ratchetKey := by
    rw [hsid_msg₀ interpretation S g']
    exact hrk_ne
  have hinj : assumedInjective msg₀.ratchetKey = true :=
    hmsg_dhPk ▸ G1.assumedInjective_dhPk_tr a
  have hmsg_not_pt : msg₀.ratchetKey ∉ plaintextTerms (runVis r₀ ms₁) ++ [] :=
    hmsg_dhPk ▸ dhPk_not_mem_ptAtoms_pkd r₀ ms₁ a
  have hc_not_pt : c.ratchetKey ∉ plaintextTerms (runVis r₀ ms₁) ++ [] := by
    have hp := DY.Bytes.pack_view? DY.X25519.Variant.SubF c.ratchetKey
    rw [hVar] at hp
    dsimp only at hp
    rw [← hp]
    exact variant_pack_not_mem_ptAtoms_pkd r₀ ms₁ x
  obtain ⟨_, _, _, htry₀⟩ := ht₀.2.2.2 msg₀ hparse₀
  have hγ_msg₀ : gamma interpretation S g' msg₀.ratchetKey = m.senderRatchetKey.bytes.toList :=
    (htry₀ m htry).2.1
  have hγ_eq : gamma interpretation S g' msg₀.ratchetKey = gamma interpretation S g' c.ratchetKey := by
    rw [hγ_msg₀, hγ_pk]
  apply hNotCol
  unfold RecvCollision; simp only [hparse₀]
  left
  exact ⟨_, hx₁, _, List.mem_append_left _ hx₂, hsh_ne, Or.inl hinj,
    fun h1 => False.elim (hmsg_not_pt h1),
    fun h2 => False.elim (hc_not_pt h2),
    hγ_eq⟩

end Symbolic.Swarm.CREF.RecvPrekeyProm.HxplG2W
