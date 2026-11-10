/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.CompI0Laws
public import Symbolic.BugInjection.Proofs.Common443.CompExcuse
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse

@[expose] public section
set_option autoImplicit false
namespace Symbolic.BugInjection.Proofs.Common443.CompPlant
open CryptoProofLib.Refinement (ExternInterpretation)
open DY
open DY.Libsignal (HwBytes)
open DY.Libsignal.HwEvents (MachineEvent)
open DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC Symbolic.BugInjection.Proofs.Common443 Symbolic.BugInjection.Proofs.Common443.CompExcuse
open Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse
def SemEqOnNonSpqr (S₁ S₂ : Sem) : Prop := S₁.kemPk = S₂.kemPk ∧ S₁.kemDecap = S₂.kemDecap ∧ S₁.vk = S₂.vk ∧ S₁.sign = S₂.sign
def SpqrIndep (i : ExternInterpretation) (g : Ghost) (t : DY.Bytes) : Prop := ∀ S₁ S₂ : Sem, SemEqOnNonSpqr S₁ S₂ → gamma' i S₁ g t = gamma' i S₂ g t
def SpqrIndepMemo (i : ExternInterpretation) (g : Ghost) (t : DY.Bytes) : Prop := ∀ S₁ S₂ : Sem, SemEqOnNonSpqr S₁ S₂ → (gamma' i S₁ g t).memo = (gamma' i S₂ g t).memo
theorem SpqrIndep.memo {i : ExternInterpretation} {g : Ghost} {t : DY.Bytes} (h : SpqrIndep i g t) : SpqrIndepMemo i g t := fun S₁ S₂ hS => congrArg ConcretizedTerm.memo (h S₁ S₂ hS)
theorem bytes_rec_gAll (i : ExternInterpretation) (S : Sem) (g : Ghost) (u : DY.Bytes) : u.rec (gAll i S g) = gamma' i S g u := rfl
inductive LitConcatTree : DY.Bytes → Prop where
  | lit (b : ByteArray) : LitConcatTree (DY.Literal.literalToBytes b)
  | concat {lhs rhs : DY.Bytes} :
      LitConcatTree lhs → LitConcatTree rhs → LitConcatTree (DY.Concat.concat lhs rhs)
theorem litConcatTree_of_concat {lhs rhs : DY.Bytes} (h : LitConcatTree (DY.Concat.concat lhs rhs)) : LitConcatTree lhs ∧ LitConcatTree rhs := by
  generalize heq : DY.Concat.concat lhs rhs = t at h; cases h with
  | lit b =>
    have hv := congrArg (fun u : DY.Bytes => u.view? DY.Concat.Concat.SubF) heq; dsimp only [DY.Concat.concat, DY.Concat.CanConcat.concat, DY.Literal.literalToBytes] at hv; rw [DY.BytesView.view_pack, view_concat_lit] at hv; cases hv
  | concat hl hr => obtain ⟨rfl, rfl⟩ := concat_inj heq; exact ⟨hl, hr⟩
instance : Comparse.BytesCompatiblePred (LitConcatTree : DY.Bytes → Prop) where
  pred_empty := .lit .empty
  pred_concat _ _ hl hr := .concat hl hr
  pred_split buf n hbuf := by
    cases hsp : Comparse.BytesLike.split buf n with
    | none => trivial
    | some p => rw [← DY.Concat.concat_split buf n p.1 p.2 hsp] at hbuf; exact litConcatTree_of_concat hbuf
  pred_fromByteArray b := .lit b
theorem gamma_literalToBytes_length (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : ByteArray) : (gamma i S g (DY.Literal.literalToBytes b)).length = b.size := by
  unfold gamma gamma' DY.Literal.literalToBytes
  show (((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (gAll i S g))).val.length = b.size
  rw [DY.Bytes.rec_eq gLit0 (gAll i S g)]; simp only [gLit0, concretizeLit, node, ConcretizedTerm.val, ofByteArray, List.length_map, Array.length_toList, ByteArray.size]
theorem gamma_bool_serialize_length (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : Bool) : ((Comparse.NonExtensibleMessageFormat.bool.serialize b).flatMap (gamma i S g)).length = 1 := by
  obtain ⟨ba, hba, hser⟩ := bool_serialize_singleton b
  rw [hser, List.flatMap_cons, List.flatMap_nil, List.append_nil, gamma_literalToBytes_length, hba]
theorem gamma_slowNat_serialize_length (i : ExternInterpretation) (S : Sem) (g : Ghost) : ∀ (n : Nat), ((Comparse.NonExtensibleMessageFormat.slowNat.serialize n).flatMap (gamma i S g)).length = n + 1
  | 0 => by rw [slowNat_serialize_zero]; exact gamma_bool_serialize_length i S g false
  | n + 1 => by
    have hstep := slowNat_serialize_succ n; rw [hstep, List.flatMap_append, List.length_append, gamma_bool_serialize_length i S g true, gamma_slowNat_serialize_length i S g n]; omega
theorem gamma_uint32_serialize_length (i : ExternInterpretation) (S : Sem) (g : Ghost) (x : UInt32) : ((Comparse.NonExtensibleMessageFormat.uint32.serialize x).flatMap (gamma i S g)).length = 4 := by
  obtain ⟨ba, hba, hser⟩ := uint32_serialize_singleton x
  rw [hser, List.flatMap_cons, List.flatMap_nil, List.append_nil, gamma_literalToBytes_length, hba]
structure TRStateSpqrIndep (i : ExternInterpretation) (g : Ghost)
    (st : DY.Libsignal.TripleRatchet.TRState) : Prop where
  myIk : SpqrIndep i g st.myIk
  peerIk : SpqrIndep i g st.peerIk
  rk : SpqrIndep i g st.rk
  dhs : SpqrIndep i g st.dhs
  cks : SpqrIndep i g st.cks
  sid : SpqrIndep i g st.sid
  spqr : SpqrIndepMemo i g st.spqr
  recv : ∀ d ∈ st.recv, SpqrIndep i g d.ratchetKey ∧ SpqrIndep i g d.chainKey
def IsKey32 (u : DY.Bytes) : Prop := ∀ (i : ExternInterpretation) (S : Sem) (g : Ghost), (gamma i S g u).length = 32
theorem gamma_randTerm_length (i : ExternInterpretation) (S : Sem) (g : Ghost) (idx sz : Nat) (hsz : sz ≠ 0) : (gamma i S g (randTerm idx sz)).length = (g.σ idx sz).length := by
  unfold gamma gamma' randTerm
  show (((({ timestamp := idx, size := sz } : DY.Random.Random DY.Bytes).pack).rec (gAll i S g))).val.length = _
  rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)]; simp [gRandom, concretizeRandom, hsz, node]
structure RecvChainPlantReady (i : ExternInterpretation) (g : Ghost)
    (d : DY.Libsignal.TripleRatchet.RecvChain) : Prop where
  ck_key : IsKey32 d.chainKey
  ck_bl : Comparse.BytesLike.length d.chainKey = 32
  rk_len : ∀ S : Sem, 4 ≤ (gamma i S g d.ratchetKey).length + Comparse.BytesLike.length d.ratchetKey
structure TRStatePlantReady (i : ExternInterpretation) (g : Ghost)
    (st : DY.Libsignal.TripleRatchet.TRState) : Prop where
  spqrIndep : TRStateSpqrIndep i g st
  recv_ne_nil : st.recv ≠ []
  recv_ready : ∀ d ∈ st.recv, RecvChainPlantReady i g d
theorem x25519Key_dhPk (sk : DY.Bytes) : DY.X25519.x25519Key (DY.DiffieHellman.dhPk sk) = DY.DiffieHellman.dhPk sk := x25519Key_dhPk_eq sk
theorem compAesPerm_length_lt {key iv text : HwBytes} {k : Nat} (hk : 16 < k) (htext : text.length < 16) : (Interp0.compAesPerm key iv text).length < k := by
  rw [CompI0Laws.compAesPerm_length_of_lt_16 key iv text htext]; exact hk
end Symbolic.BugInjection.Proofs.Common443.CompPlant
