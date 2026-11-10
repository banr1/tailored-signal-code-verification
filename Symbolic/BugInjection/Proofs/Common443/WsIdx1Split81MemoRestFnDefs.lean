/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement ByteSpecs Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoPreRest Symbolic.BugInjection.Proofs.Common443.WsIdx1Split40MemoRestFnDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81Census Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSubDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoNewSub Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoVals Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoQRestDefs Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
open Symbolic.BugInjection.Proofs.Common443.CompRSplit38UntaggedShape (IsKdf IsX IsTrunc8)
open Symbolic.BugInjection.Proofs.Common443.CompC2RestFn (RestFnEntry)
open Symbolic.BugInjection.Proofs.Common443.CompRMemoKnown (MemoOK)
abbrev o1_81 (r : Records) (tr₁ : ExecTrace) : DY.Libsignal.PQXDH.AliceHandshakeOut := o40 r tr₁
abbrev stA1_81 (r : Records) (tr₁ : ExecTrace) : DY.Libsignal.TripleRatchet.TRState := stA1_40 r tr₁
abbrev o2_81 (r : Records) (tr₄ : ExecTrace) : DY.Libsignal.PQXDH.AliceHandshakeOut := o40 r tr₄
abbrev stA2_81 (r : Records) (tr₄ : ExecTrace) : DY.Libsignal.TripleRatchet.TRState := stA1_40 r tr₄
def rTerms81ExtBase (r : Records) (tr_bob tr₄ tr₅ : ExecTrace) (cl₅ : Nat) : List DY.Bytes := [ randTerm tr_bob.length 32, randTerm tr₄.length 32, randTerm (tr₄.length + 1) 32, randTerm (tr₄.length + 2) 32, randTerm tr₅.length 32, DY.SymEnc.symEnc (keys40 tr₅ (stA2_81 r tr₄) cl₅).cipherKey (keys40 tr₅ (stA2_81 r tr₄) cl₅).iv (randTerm tr₅.length 32), (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₄.length + 1) 32)).1, (DY.PQKem.kemEncap (DY.PQKem.kemPk (randTerm 16 64)) (randTerm (tr₄.length + 1) 32)).2 ]
def rTerms81Ext (r : Records) (tr_bob tr₄ tr₅ : ExecTrace) (cl₅ : Nat) : List DY.Bytes := rTerms81ExtBase r tr_bob tr₄ tr₅ cl₅ ++ coinTerms tr₅ cl₅
def rTerms81 (r : Records) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : List DY.Bytes := rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ ++ rTerms81Ext r tr_bob tr₄ tr₅ cl₅
theorem rTerms81_eq_append (r : Records) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ = rTerms40 r tr₁ tr₂ tr₃ cl₁ cl₂ ++ rTerms81Ext r tr_bob tr₄ tr₅ cl₅ := rfl
def xTerms81Ext (tr₁ tr_bob tr₄ : ExecTrace) : List DY.Bytes := [ DY.DiffieHellman.dhPk (randTerm tr_bob.length 32), DY.DiffieHellman.dhPk (randTerm tr₄.length 32), DY.DiffieHellman.dhPk (randTerm (tr₄.length + 2) 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (randTerm tr_bob.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr₄.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr₄.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm (tr₄.length + 2) 32) ]
def xTerms81 (tr₁ tr_bob tr₄ : ExecTrace) : List DY.Bytes := [ DY.DiffieHellman.dhPk (randTerm 0 32), DY.DiffieHellman.dhPk (randTerm 5 32), DY.DiffieHellman.dhPk (randTerm 10 32), DY.DiffieHellman.dhPk (randTerm tr₁.length 32), DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm 0 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr₁.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr₁.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm (tr₁.length + 2) 32), DY.DiffieHellman.dhPk (randTerm tr_bob.length 32), DY.DiffieHellman.dhPk (randTerm tr₄.length 32), DY.DiffieHellman.dhPk (randTerm (tr₄.length + 2) 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm (tr₁.length + 2) 32)) (randTerm tr_bob.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 5 32)) (randTerm tr₄.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm tr₄.length 32), DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk (randTerm 10 32)) (randTerm (tr₄.length + 2) 32) ]
theorem xTerms81_eq_append (tr₁ tr_bob tr₄ : ExecTrace) : xTerms81 tr₁ tr_bob tr₄ = xTerms40 tr₁ ++ xTerms81Ext tr₁ tr_bob tr₄ := rfl
theorem agree_dhPk_comm (a b : DY.Bytes) : DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk a) b = DY.Libsignal.PQXDH.agree (DY.DiffieHellman.dhPk b) a := Symbolic.Swarm.COMPOSED.CompTermAlgebra.agree_comm a b
abbrev zMac81 (r : Records) (salt : DY.Bytes) (tr₁ tr₂ tr₄ : ExecTrace) (cl₁ : Nat) : DY.Bytes :=
  let seed := bobSeed81 r tr₁ tr₂ tr₄ cl₁
  let stA₁ := stA81 r tr₁
  let w := encWire tr₂ stA₁ cl₁ (tr₂.length + 2)
  let peerIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r 0)
  let myIk := DY.Libsignal.PQXDH.serializedIk (setupPublic r 2)
  let keys := DY.Libsignal.TripleRatchet.trMsgKeys salt seed
  DY.Libsignal.TripleRatchet.computeMac keys.macKey peerIk myIk w
def t8Terms81 (r : Records) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : List DY.Bytes := [ encMac tr₂ (stA1_40 r tr₁) cl₁ (tr₂.length + 2), encMac tr₃ (stA40 r tr₁ tr₂ cl₁) cl₂ (tr₃.length + 2), encMac tr₅ (stA2_81 r tr₄) cl₅ (tr₅.length + 2), zMac81 r DY.Spqr.zeroKey tr₁ tr₂ tr₄ cl₁, zMac81 r (ck1Salt40 r tr₁) tr₁ tr₂ tr₄ cl₁, zMac81 r (send2Salt81 r tr₁ tr₂ tr₃ cl₁ cl₂) tr₁ tr₂ tr₄ cl₁, zMac81 r (ck5Salt81 r tr₄) tr₁ tr₂ tr₄ cl₁ ]
def allTerms81 (r : Records) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : List DY.Bytes := rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ ++ xTerms81 tr₁ tr_bob tr₄ ++ t8Terms81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅
theorem mem_allTerms81_of_r {r : Records} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {u : DY.Bytes} (h : u ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) : u ∈ allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ (List.mem_append_left _ h)
theorem mem_allTerms81_of_x {r : Records} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {u : DY.Bytes} (h : u ∈ xTerms81 tr₁ tr_bob tr₄) : u ∈ allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_left _ (List.mem_append_right _ h)
theorem mem_allTerms81_of_t8 {r : Records} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {u : DY.Bytes} (h : u ∈ t8Terms81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : u ∈ allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ := List.mem_append_right _ h
def fn81 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) : HwBytes → DY.Bytes := lookupShape40 S g (allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅)
def Rv81 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (v : HwBytes) : Prop := v ∈ (rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅).map (gamma compI0 S g)
def FnOK81 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (x : DY.Bytes × DY.Bytes × HwBytes) : Prop := (assumedInjective x.1 = false → ¬ Rv81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x.2.2) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → x.1 ∈ allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) ∧ (assumedInjective x.1 = true → ¬ IsKdf x.1 → ¬ IsX x.1 → ¬ IsTrunc8 x.1 → x.1 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅)
abbrev FnCensus81 (r : Records) (S : Sem) (g : Ghost) (tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat) (t : DY.Bytes) : Prop := MemoOK compI0 S g (FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) t
theorem restFnEntry81_of_fnOK {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} (hnd : ((allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅).map (gamma compI0 S g)).Nodup) {x : DY.Bytes × DY.Bytes × HwBytes} (hv : x.2.2 = gamma compI0 S g x.1) (hok : FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x) : RestFnEntry (fn81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) (Rv81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) S g x := by
  refine ⟨fun h => ?_, fun hai hK hX hT => ?_, hok.1⟩
  · have ⟨hai, hK⟩ := h.elim isX_ai_not_kdf40 (fun h' => h'.elim isTrunc8_ai_not_kdf40 id)
    rw [hv]; exact lookupShape40_eq hnd (hok.2.1 hai hK)
  · change x.2.2 ∈ (rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅).map (gamma compI0 S g)
    rw [hv]; exact List.mem_map_of_mem (hok.2.2 hai hK hX hT)
theorem fnOK81_of_nonInj {r : Records} {S : Sem} {g : Ghost}
    {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
    {x : DY.Bytes × DY.Bytes × HwBytes} (hni : assumedInjective x.1 = false)
    (hnr : ¬ Rv81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x.2.2) :
    FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x :=
  ⟨fun _ => hnr, fun hai => (by rw [hni] at hai; cases hai), fun hai => (by rw [hni] at hai; cases hai)⟩
theorem fnOK81_of_kdf {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} {k m : DY.Bytes} (hx : x.1 = DY.KdfExtract.kdfExtract k m) : FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x := by
  have hai : assumedInjective x.1 = true := by rw [hx]; exact CompRSplit38QKdf.assumedInjective_kdfExtract k m
  have hk : IsKdf x.1 := ⟨k, m, hx⟩
  exact ⟨fun h => (by rw [hai] at h; cases h), fun _ hK => absurd hk hK, fun _ hK _ _ => absurd hk hK⟩
theorem fnOK81_of_t8 {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} {a : DY.Bytes} (hx : x.1 = DY.Trunc.trunc8 a) (hm : x.1 ∈ allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) : FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x := by
  have hai : assumedInjective x.1 = true := by rw [hx]; exact CompC2RestEntry38.ai_trunc8 a
  exact ⟨fun h => (by rw [hai] at h; cases h), fun _ _ => hm, fun _ _ _ hT => absurd ⟨a, hx⟩ hT⟩
theorem fnOK81_of_dhPk {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} {sk : DY.Bytes} (hx : x.1 = DY.DiffieHellman.dhPk sk) (hm : x.1 ∈ allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) : FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x := by
  have hai : assumedInjective x.1 = true := by rw [hx]; exact (isX_ai_not_kdf40 (Or.inl ⟨sk, rfl⟩)).1
  exact ⟨fun h => (by rw [hai] at h; cases h), fun _ _ => hm, fun _ _ hX' _ => absurd (Or.inl ⟨sk, hx⟩) hX'⟩
theorem fnOK81_of_r {r : Records} {S : Sem} {g : Ghost}
    {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat}
    {x : DY.Bytes × DY.Bytes × HwBytes} (hai : assumedInjective x.1 = true)
    (hmR : x.1 ∈ rTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅) :
    FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x :=
  ⟨fun h => (by rw [hai] at h; cases h), fun _ _ => mem_allTerms81_of_r hmR, fun _ _ _ _ => hmR⟩
theorem fnOK81_of_saltedNodes81 {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {salt : DY.Bytes} {x : DY.Bytes × DY.Bytes × HwBytes} (hs : x.1 ∈ saltedNodes81 r salt tr₁ tr₂ tr₄ cl₁) (ht8 : zMac81 r salt tr₁ tr₂ tr₄ cl₁ ∈ t8Terms81 r tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅) : FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x := by
  unfold saltedNodes81 at hs; simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with h | h | h | h | h | h
  · exact fnOK81_of_kdf h
  · exact fnOK81_of_kdf h
  · exact fnOK81_of_kdf h
  · exact fnOK81_of_kdf h
  · exact fnOK81_of_kdf h
  · exact fnOK81_of_t8 h (h ▸ mem_allTerms81_of_t8 ht8)
theorem fnOK81_of_z81 {r : Records} {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ : ExecTrace} {cl₁ cl₂ cl₅ : Nat} {x : DY.Bytes × DY.Bytes × HwBytes} (hz : x.1 ∈ z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂) : FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x := by
  unfold z81Terms at hz; rcases List.mem_append.mp hz with h123 | h4
  · rcases List.mem_append.mp h123 with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2 <;> exact fnOK81_of_saltedNodes81 ‹_› (by simp [t8Terms81])
    · exact fnOK81_of_saltedNodes81 h3 (by simp [t8Terms81])
  · exact fnOK81_of_saltedNodes81 h4 (by simp [t8Terms81])
def Split81RestFnPreOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → ∃ (tr_bob : ExecTrace), gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes ∧ ∀ x ∈ preMemo81 r S g ms', FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x
def Split81RestFnNewOwn : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → ∀ (tr_bob : ExecTrace), gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes → ∀ x ∈ newMemo81 r S g ms' p tr₁ tr₂ tr₄ cl₁, x ∉ preMemo81 r S g ms' → Cls40 (extBaseRows81 r S g ms' tr₁ tr₂ tr₄ cl₁) (z81Terms r tr₁ tr₂ tr₃ tr₄ cl₁ cl₂) x → FnOK81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅ x
def Split81TblNodup : Prop := ∀ (r : Records) (S : Sem) (g : Ghost) (p : PreKeyFields) (ms' : List Move) (tr₁ tr₂ tr₃ tr₄ tr₅ : ExecTrace) (cl₁ cl₂ cl₅ : Nat), compFitsPinned setup compI0 r → parsePreKeyWire wire6Idx1Bytes = some p → WS81Idx1RunInv r S g ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → Links81Own r ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ → ∀ (tr_bob : ExecTrace), gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes → ((allTerms81 r tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅).map (gamma compI0 S g)).Nodup
theorem split81RestFnOwn_of_halves (hA : Split81RestFnPreOwn) (hB : Split81RestFnNewOwn) (hN : Split81TblNodup) : Split81RestFnOwn := by
  intro r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; obtain ⟨tr_bob, hbob, hA'⟩ := hA r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown; have hB' := hB r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown tr_bob hbob; have hnd := hN r S g p ms' tr₁ tr₂ tr₃ tr₄ tr₅ cl₁ cl₂ cl₅ hfits hp hinv hown tr_bob hbob
  refine ⟨fn81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅,
    Rv81 r S g tr₁ tr₂ tr₃ tr_bob tr₄ tr₅ cl₁ cl₂ cl₅, fun x hx hc => ?_⟩
  have hv : x.2.2 = gamma compI0 S g x.1 := exists_memo_of_mem81 hx
  by_cases hpre : x ∈ preMemo81 r S g ms'
  · exact restFnEntry81_of_fnOK hnd hv (hA' x hpre)
  · rcases List.mem_append.mp hx with hx' | hx'
    · exact absurd hx' hpre
    · exact restFnEntry81_of_fnOK hnd hv (hB' x hx' hpre hc)
end Symbolic.BugInjection.Proofs.Common443.WsIdx1Split81MemoRestFnDefs
