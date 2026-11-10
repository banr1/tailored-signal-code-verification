/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest
import Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber
import Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs
open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape (IsKdf IsX IsTrunc8)
open Symbolic.BugInjection.Proofs.Common443.CompC2RestFn (RestFnEntry)
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown (MemoOK)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
abbrev o40 (r : Records) (tr₁ : ExecTrace) : DY.Libsignal.PQXDH.AliceHandshakeOut := iniAliceOut tr₁ (setupSecret r 0) (setupPublic r 2) (setupPublic r 4) (setupPublic r 6) none
abbrev stA1_40 (r : Records) (tr₁ : ExecTrace) : DY.Libsignal.TripleRatchet.TRState := iniAliceStartState tr₁ r.bob (o40 r tr₁)
abbrev keys40 (tr : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl : Nat) : DY.Libsignal.TripleRatchet.MessageKeys := DY.Libsignal.TripleRatchet.trMsgKeys (encSalt tr stA cl (tr.length + 2)) (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2
def coinTerms (tr : ExecTrace) (cl : Nat) : List DY.Bytes :=
  if cl = 0 then [] else [randTerm (tr.length + 1) cl]
def rTerms40Base (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : List DY.Bytes := [ randTerm 0 32, randTerm 5 32, randTerm 10 32, randTerm 16 64, randTerm tr₁.length 32, randTerm (tr₁.length + 1) 32, randTerm (tr₁.length + 2) 32, randTerm tr₂.length 32, randTerm tr₃.length 32, DY.SymEnc.symEnc (keys40 tr₂ (stA1_40 r tr₁) cl₁).cipherKey (keys40 tr₂ (stA1_40 r tr₁) cl₁).iv (randTerm tr₂.length 32), DY.SymEnc.symEnc (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).cipherKey (keys40 tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂).iv (randTerm tr₃.length 32), (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).1, (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₁.length + 1) 32)).2 ]
def rTerms40 (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : List DY.Bytes := (rTerms40Base r tr₁ tr₂ tr₃ cl₁ cl₂ ++ coinTerms tr₂ cl₁) ++ coinTerms tr₃ cl₂
def xTerms40 (tr₁ : ExecTrace) : List DY.Bytes := [ DY.DiffieHellman.dhPk (randTerm 0 32), DY.DiffieHellman.dhPk (randTerm 5 32), DY.DiffieHellman.dhPk (randTerm 10 32), DY.DiffieHellman.dhPk (randTerm tr₁.length 32), DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm 0 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr₁.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr₁.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm (tr₁.length + 2) 32) ]
abbrev zMac40 (salt : DY.Bytes) (tr₃ : ExecTrace) (stA : DY.Libsignal.TripleRatchet.TRState) (cl₂ : Nat) : DY.Bytes := DY.Libsignal.TripleRatchet.computeMac (DY.Libsignal.TripleRatchet.trMsgKeys salt (DY.Libsignal.TripleRatchet.kdfCk stA.cks).2).macKey stA.myIk stA.peerIk (encWire tr₃ stA cl₂ (tr₃.length + 2))
def t8Terms40 (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : List DY.Bytes := [ encMac tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2), encMac tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2), zMac40 DY.Spqr.zeroKey tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂, zMac40 (ck1Salt40 r tr₁) tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ ]
def allTerms40 (r : Records) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : List DY.Bytes := rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ ++ xTerms40 tr₁ ++ t8Terms40 r tr₁ tr₂ tr₃ cl₁ cl₂
theorem mem_allTerms40_of_r {r : Records} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {u : DY.Bytes} (h : u ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) : u ∈ allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_left _ h)
theorem mem_allTerms40_of_x {r : Records} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {u : DY.Bytes} (h : u ∈ xTerms40 tr₁) : u ∈ allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_left _ (List.mem_append_right _ h)
theorem mem_allTerms40_of_t8 {r : Records} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {u : DY.Bytes} (h : u ∈ t8Terms40 r tr₁ tr₂ tr₃ cl₁ cl₂) : u ∈ allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ := List.mem_append_right _ h
def lookupShape40 (S : Sem) (g : Ghost) (ts : List DY.Bytes) (v : HwBytes) : DY.Bytes :=
  match ts.find? (fun t => gamma compI0 S g t == v) with
  | some t => (gamma' compI0 S g t).shape
  | none => DY.Literal.literalToBytes .empty
theorem lookupShape40_eq {S : Sem} {g : Ghost} {ts : List DY.Bytes} (hnd : (ts.map (gamma compI0 S g)).Nodup) {u : DY.Bytes} (hu : u ∈ ts) : (gamma' compI0 S g u).shape = lookupShape40 S g ts (gamma compI0 S g u) := by
  unfold lookupShape40
  rcases hfind : ts.find? (fun t => gamma compI0 S g t == gamma compI0 S g u) with _ | t
  · exact absurd (beq_self_eq_true _) (List.find?_eq_none.mp hfind u hu)
  · have hbeq := List.find?_some hfind
    rw [List.inj_on_of_nodup_map hnd (List.mem_of_find?_eq_some hfind) hu (beq_iff_eq.mp hbeq)]
def fn40 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) : HwBytes → DY.Bytes := lookupShape40 S g (allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂)
def Rv40 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (v : HwBytes) : Prop := v ∈ (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g)
def FnOK40 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := (assumedInjective x.1 = false → ¬ Rv40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x.2.2) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → x.1 ∈ allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → ¬ IsX x.1 → ¬ IsTrunc8 x.1 → x.1 ∈ rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂)
abbrev FnCensus40 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat) (t : DY.Bytes) : Prop := MemoOK compI0 S g (FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂) t
theorem isX_ai_not_kdf40 {b : DY.Bytes} (h : IsX b) : assumedInjective b = true ∧ ¬ IsKdf b := by
  rcases h with ⟨x, rfl⟩ | ⟨a, c, rfl⟩
  · exact ⟨(Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.DiffieHellman.dhPk x = ({ sk := x } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]), fun ⟨_, _, he⟩ => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.dhPk_ne_kdfExtract _ _ _ he⟩
  · exact ⟨(Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [DY.BytesView.view_pack]), fun ⟨_, _, he⟩ => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.dh_pack_ne_kdfExtract _ _ _ _ he⟩
theorem isTrunc8_ai_not_kdf40 {b : DY.Bytes} (h : IsTrunc8 b) : assumedInjective b = true ∧ ¬ IsKdf b := by
  rcases h with ⟨a, rfl⟩
  exact ⟨(Symbolic.Proofs.Swarm.Leaves.IC13_Stage1Kyber.assumedInjective_eq_true_iff _).mpr (by simp [show DY.Trunc.trunc8 a = ({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack from rfl, DY.BytesView.view_pack]), fun ⟨_, _, he⟩ => Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsTrue.trunc8_ne_kdfExtract _ _ _ he⟩
theorem restFnEntry40_of_fnOK {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} (hnd : ((allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g)).Nodup) {x : DY.Bytes × DY.Bytes × HwBytes} (hv : x.2.2 = gamma compI0 S g x.1) (hok : FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x) : RestFnEntry (fn40 r S g tr₁ tr₂ tr₃ cl₁ cl₂) (Rv40 r S g tr₁ tr₂ tr₃ cl₁ cl₂) S g x := by
  refine ⟨fun h => ?_, fun hai hK hX hT => ?_, hok.1⟩
  · have ⟨hai, hK⟩ := h.elim isX_ai_not_kdf40 (fun h' => h'.elim isTrunc8_ai_not_kdf40 id)
    rw [hv]; exact lookupShape40_eq hnd (hok.2.1 hai hK)
  · change x.2.2 ∈ (rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g)
    rw [hv]; exact List.mem_map_of_mem (hok.2.2 hai hK hX hT)
theorem fnOK40_of_nonInj {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace}
    {cl₁ cl₂ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hni : assumedInjective x.1 = false)
    (hnr : ¬ Rv40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x.2.2) : FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x :=
  ⟨fun _ => hnr, fun hai => (by rw [hni] at hai; cases hai), fun hai => (by rw [hni] at hai; cases hai)⟩
theorem fnOK40_of_kdf {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} {k m : DY.Bytes} (hx : x.1 = DY.KdfExtract.kdfExtract k m) : FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x := by
  have hai : assumedInjective x.1 = true := by rw [hx]; exact CompRSplit38QKdf.assumedInjective_kdfExtract k m
  exact ⟨fun h => (by rw [hai] at h; cases h), fun _ hK => absurd ⟨k, m, hx⟩ hK, fun _ hK _ _ => absurd ⟨k, m, hx⟩ hK⟩
theorem fnOK40_of_t8 {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} {a : DY.Bytes} (hx : x.1 = DY.Trunc.trunc8 a) (hm : x.1 ∈ allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂) : FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x := by
  have hai : assumedInjective x.1 = true := by rw [hx]; exact CompC2RestEntry38.ai_trunc8 a
  exact ⟨fun h => (by rw [hai] at h; cases h), fun _ _ => hm, fun _ _ _ hT => absurd ⟨a, hx⟩ hT⟩
theorem fnOK40_of_z40 {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace} {cl₁ cl₂ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hz : x.1 ∈ z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) : FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x := by
  unfold z40Terms saltedNodes40 at hz; simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with (h | h | h | h | h | h) | (h | h | h | h | h | h)
  · exact fnOK40_of_kdf h
  · exact fnOK40_of_kdf h
  · exact fnOK40_of_kdf h
  · exact fnOK40_of_kdf h
  · exact fnOK40_of_kdf h
  · refine fnOK40_of_t8 h ?_; rw [h]
    exact mem_allTerms40_of_t8 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  · exact fnOK40_of_kdf h
  · exact fnOK40_of_kdf h
  · exact fnOK40_of_kdf h
  · exact fnOK40_of_kdf h
  · exact fnOK40_of_kdf h
  · refine fnOK40_of_t8 h ?_; rw [h]
    exact mem_allTerms40_of_t8 (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
def Split40RestFnPreOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x ∈ preMemo40 r S g ms', FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x
def Split40RestFnNewOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ∀ x ∈ newMemo40 r S g ms' p tr₁ tr₂ tr₃ cl₁ cl₂, x ∉ preMemo40 r S g ms' → Cls40 (preMemo40 r S g ms') (z40Terms r tr₁ tr₂ tr₃ cl₁ cl₂) x → FnOK40 r S g tr₁ tr₂ tr₃ cl₁ cl₂ x
def Split40TblNodup : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ : ExecTrace) (cl₁ cl₂ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire3Idx1Bytes = some p → WS40Idx1RunInv r S g ms' tr₁ tr₂ tr₃ cl₁ cl₂ → Links40Own r ms' tr₁ tr₂ tr₃ cl₁ cl₂ → ((allTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂).map (gamma compI0 S g)).Nodup
theorem split40RestFnOwn_of_halves (hA : Split40RestFnPreOwn) (hB : Split40RestFnNewOwn) (hN : Split40TblNodup) : Split40RestFnOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; have hA' := hA r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; have hB' := hB r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown; have hnd := hN r S g p ms' tr₁ tr₂ tr₃ cl₁ cl₂ hfits hp hinv hown
  refine ⟨fn40 r S g tr₁ tr₂ tr₃ cl₁ cl₂, Rv40 r S g tr₁ tr₂ tr₃ cl₁ cl₂, fun x hx hc => ?_⟩
  have hv : x.2.2 = gamma compI0 S g x.1 := exists_memo_of_mem40 hx
  by_cases hpre : x ∈ preMemo40 r S g ms'
  · exact restFnEntry40_of_fnOK hnd hv (hA' x hpre)
  · rcases List.mem_append.mp hx with hx' | hx'
    · exact absurd hx' hpre
    · exact restFnEntry40_of_fnOK hnd hv (hB' x hx' hpre hc)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs
