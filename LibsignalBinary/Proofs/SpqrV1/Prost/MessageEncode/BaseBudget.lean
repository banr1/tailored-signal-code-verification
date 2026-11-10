/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.Placed.BudgetVmSteps
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Shared Helpers for 48-Byte `Message::encode` Monomorphizations

Defines the deterministic multi-byte `Vec<u8>` capacity reservation transition `reserveStep`
and `encodeRepeatedStep`, together with VM-preserving `SepWPp` basic-block and call combinators
(`sepWPp_of_sepWP_cs_vm_placed`, `sepWP_done_tpidr_placed`, `sepWPp_call_cs_placed_noPanic`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget

open Arm64 ProofLib SepProp
open CryptoVerification.LibsignalProtoCodec (encodeBytesField encodeVarint)
open CryptoVerification.LibsignalTripleRatchet (DoReserveCall reserveCap)
open CryptoVerification.LibsignalTripleRatchet.Prost (StepInvPlaced)
open CryptoVerification.SpqrV1.Varint
  (encodeBytesField_some_length
   encodeKey_lengthDelimited_eq encodeRepeatedBytes encodeRepeatedBytes_cons)
open LibsignalBinary.Heap
  (AllocEvent VmPreserved rustAllocEvents rustReallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget (doReserveEvents)
open LibsignalBinary.Proofs.TripleRatchet.Prost.EncDefsBudget
  (pushByteStep pushBytesEvents pushBytesEvents_of_spare)

/-! ## 1. Deterministic Multi-Byte `Vec<u8>` Reserve & Repeated-Bytes Steps -/

/-- Deterministic `(newCap, evs)` transition of `Vec<u8>` capacity reservation for `additional` bytes:
    if `len + additional ≤ cap`, capacity is unchanged and `[]` events are emitted; otherwise
    `do_reserve_and_handle` grows to `reserveCap cap len additional`, emitting `rustAllocEvents`
    when `cap = 0` and `rustReallocEvents` when `0 < cap`. -/
def reserveStep (cap len additional : Nat) : Nat × List AllocEvent :=
  if len + additional ≤ cap then
    (cap, [])
  else
    let newCap := reserveCap cap len additional
    let evs := if cap = 0 then rustAllocEvents newCap 1 else rustReallocEvents cap newCap 1
    (newCap, evs)

theorem reserveStep_one_eq_pushByteStep (cap len : Nat) :
    reserveStep cap len 1 = pushByteStep cap len := by
  unfold reserveStep pushByteStep
  by_cases h : len < cap
  · have hle : len + 1 ≤ cap := h
    simp only [h, hle, ↓reduceIte]
  · have hnle : ¬ (len + 1 ≤ cap) := h
    simp only [h, hnle, ↓reduceIte]

theorem reserveStep_of_spare {cap len additional : Nat} (h : len + additional ≤ cap) :
    reserveStep cap len additional = (cap, []) := by
  simp only [reserveStep, h, ↓reduceIte]

theorem reserveStep_of_need {cap len additional : Nat} (h : ¬ (len + additional ≤ cap)) :
    reserveStep cap len additional =
      (reserveCap cap len additional,
       if cap = 0 then rustAllocEvents (reserveCap cap len additional) 1
       else rustReallocEvents cap (reserveCap cap len additional) 1) := by
  simp only [reserveStep, h, ↓reduceIte]

theorem reserveStep_of_need_doReserveEvents (v curCap curPtr : BitVec 64)
    (curBs : List (BitVec 8)) (additional : Nat)
    (h : ¬ (curBs.length + additional ≤ curCap.toNat)) :
    reserveStep curCap.toNat curBs.length additional =
      (reserveCap curCap.toNat curBs.length additional,
       doReserveEvents (DoReserveCall.mk v curCap curPtr curBs additional)) := by
  rw [reserveStep_of_need h]
  unfold doReserveEvents
  congr 1
  by_cases h0 : curCap = 0#64
  · rw [h0]; rfl
  · have h0n : curCap.toNat ≠ 0 := fun h0n => h0 (BitVec.eq_of_toNat_eq h0n)
    simp only [h0, h0n, ↓reduceIte]

theorem reserveStep_fst_ge (cap len additional : Nat) :
    cap ≤ (reserveStep cap len additional).1 := by
  unfold reserveStep
  split_ifs with h h0 <;> simp only [reserveCap] <;> omega

/-- Capacity-and-events transition for pushing `n` bytes one-by-one into `Vec<u8>`. -/
def pushBytesStep : Nat → Nat → Nat → Nat × List AllocEvent
  | 0, cap, _ => (cap, [])
  | n + 1, cap, len =>
    let s1 := pushByteStep cap len
    let s2 := pushBytesStep n s1.1 (len + 1)
    (s2.1, s1.2 ++ s2.2)

theorem pushBytesStep_snd_eq :
    ∀ (n cap len : Nat), (pushBytesStep n cap len).2 = pushBytesEvents n cap len
  | 0, _, _ => rfl
  | n + 1, cap, len => by
    simp only [pushBytesStep, pushBytesEvents, pushBytesStep_snd_eq n]

theorem pushBytesStep_of_spare :
    ∀ (n cap len : Nat), len + n ≤ cap → pushBytesStep n cap len = (cap, [])
  | 0, _, _, _ => rfl
  | n + 1, cap, len, h => by
    have hlt : len < cap := by omega
    simp only [pushBytesStep, pushByteStep, hlt, ↓reduceIte, List.nil_append]
    exact pushBytesStep_of_spare n cap (len + 1) (by omega)

/-- Capacity-and-events transition of one iteration of `encode_repeated` (`key` varint +
    `elem.length` varint + `do_reserve_and_handle` for `elem.length` bytes). -/
def encodeRepeatedElemStep (tag cap len : Nat) (elemBs : List (BitVec 8)) :
    Nat × List AllocEvent :=
  let keyLen := (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length
  let s1 := pushBytesStep keyLen cap len
  let vlen := (encodeVarint (BitVec.ofNat 64 elemBs.length)).length
  let s2 := pushBytesStep vlen s1.1 (len + keyLen)
  let s3 := reserveStep s2.1 (len + keyLen + vlen) elemBs.length
  (s3.1, s1.2 ++ s2.2 ++ s3.2)

/-- Capacity-and-events transition of `prost::encoding::bytes::encode_repeated` over `elems`. -/
def encodeRepeatedStep (tag : Nat) : Nat → Nat → List (List (BitVec 8)) → Nat × List AllocEvent
  | cap, _, [] => (cap, [])
  | cap, len, elemBs :: rest =>
    let s1 := encodeRepeatedElemStep tag cap len elemBs
    let s2 := encodeRepeatedStep tag s1.1 (len + (encodeBytesField tag (some elemBs)).length) rest
    (s2.1, s1.2 ++ s2.2)

theorem encodeRepeatedElemStep_of_spare {tag cap len : Nat} {elemBs : List (BitVec 8)}
    (h : len + (encodeBytesField tag (some elemBs)).length ≤ cap) :
    encodeRepeatedElemStep tag cap len elemBs = (cap, []) := by
  rw [encodeBytesField_some_length, encodeKey_lengthDelimited_eq] at h
  dsimp only [encodeRepeatedElemStep]
  have hs1 : pushBytesStep (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length cap len =
      (cap, []) :=
    pushBytesStep_of_spare _ _ _ (by omega)
  rw [hs1]
  have hs2 : pushBytesStep (encodeVarint (BitVec.ofNat 64 elemBs.length)).length cap
      (len + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length) = (cap, []) :=
    pushBytesStep_of_spare _ _ _ (by omega)
  rw [hs2]
  have hs3 : reserveStep cap
      (len + (encodeVarint (BitVec.ofNat 64 (tag * 8 + 2))).length +
        (encodeVarint (BitVec.ofNat 64 elemBs.length)).length) elemBs.length = (cap, []) :=
    reserveStep_of_spare (by omega)
  rw [hs3]
  rfl

theorem encodeRepeatedStep_of_spare (tag : Nat) :
    ∀ (cap len : Nat) (elems : List (List (BitVec 8))),
      len + (encodeRepeatedBytes tag elems).length ≤ cap →
      encodeRepeatedStep tag cap len elems = (cap, [])
  | cap, _, [], _ => rfl
  | cap, len, elemBs :: rest, h => by
    rw [encodeRepeatedBytes_cons, List.length_append] at h
    have hs1 := encodeRepeatedElemStep_of_spare (tag := tag) (cap := cap) (len := len)
      (elemBs := elemBs) (by omega)
    simp only [encodeRepeatedStep, hs1, List.nil_append]
    exact encodeRepeatedStep_of_spare tag cap
      (len + (encodeBytesField tag (some elemBs)).length) rest (by omega)

/-! ## 2. VM-Preserving `SepWPp` Basic-Block & Call Combinators (`StepInvPlaced` + `VmPreserved`) -/

/-- Lift a `SepWP` basic-block step that establishes `VmPreserved s sm` (e.g. via `by_vm_steps` and
    `sepWP_done_tpidr_placed`) to `SepWPp`, supplying both `VmPreserved s sm` and `StepInvPlaced s sm`
    to the continuation with polymorphic `Q`, `Qp`, and `oom`. -/
theorem sepWPp_of_sepWP_cs_vm_placed {prog : Program} {mid ret : BitVec 64}
    {s : State} {Pre : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (h : SepWP prog mid s Pre (fun sm Pm =>
      VmPreserved s sm ∧
        (VmPreserved s sm → StepInvPlaced s sm → SepWPp prog ret sm Pm Q Qp oom))) :
    SepWPp prog ret s Pre Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvmp, hnext⟩ | ⟨_, hfalse⟩⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ :=
      hnext hvmp (StepInvPlaced.of_steps hsteps) R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim (not_satisfies_false_sepConj hfalse)

/-- Close the `SepWP` goal inside `by_vm_steps` (`sepWP_rebase_vmPreserved`) by discharging `pc`,
    `status = .Running`, and `tpidrEl0` preservation. -/
theorem sepWP_done_tpidr_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (htp : s.tpidrEl0 = s0.tpidrEl0)
    (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => sm.tpidrEl0 = s0.tpidrEl0 ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨htp, hpost⟩

/-- Close a non-`STR`/`STP` `SepWP` basic-block goal directly when `VmPreserved s0 s` reduces by
    `wp_norm`/`arm64_norm`. -/
theorem sepWP_done_vm_placed {prog : Program} {target_pc : BitVec 64} {s0 s : State}
    {P : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = target_pc) (hrun : s.status = .Running)
    (hvm : VmPreserved s0 s)
    (hpost : Q s P) :
    SepWP prog target_pc s P (fun sm Pm => VmPreserved s0 sm ∧ Q sm Pm) :=
  SepWP.done hpc hrun ⟨hvm, hpost⟩

/-- Polymorphic-outcome (`Q`, `Qp`, `oom`) call combinator for `subroutine_ok` contracts that
    neither panic, exit, nor OOM (`onPanic = ⌜False⌝`, `onExit = ⌜False⌝`, `onOom = ⌜False⌝`),
    supplying `CalleeSavedPreserved s sm` and `StepInvPlaced s sm` to the continuation. -/
theorem sepWPp_call_cs_placed_noPanic {α : Type} {prog : Program} {entry ret ret_pc : BitVec 64}
    {spec : Spec α} {x : α} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R, s.mem ⊨ P ∗ R → s.mem ⊨ spec.pre x s ∗ (F ∗ R))
    (hexit : ∀ sf code R, sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R) → False)
    (hpanic : ∀ sf R, sf.status = .Panicked → (sf.mem ⊨ spec.onPanic x s sf ∗ R) → False)
    (hoom : ∀ sf R, sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom x s sf ∗ R) → False)
    (hnext : ∀ sm : State, sm.pc = ret_pc → sm.status = .Running → sm.sp = s.sp →
      CalleeSavedPreserved s sm → StepInvPlaced s sm →
      SepWPp prog ret sm (spec.post x s sm ∗ F) Q Qp oom) :
    SepWPp prog ret s P Q Qp oom := by
  intro R hm hL
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun (hpre R hm) hsp hL
  rcases hout with
      ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpan_mem⟩ | ⟨code, hex, hex_mem⟩ | ⟨hoom_sm, hoom_mem⟩
  · rw [hlr] at hpcm
    rw [← sepConj_assoc] at hpost
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hcsm (StepInvPlaced.of_steps hsteps) R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact (hpanic sm (F ∗ R) hpan hpan_mem).elim
  · exact (hexit sm code (F ∗ R) hex hex_mem).elim
  · exact (hoom sm (F ∗ R) hoom_sm hoom_mem).elim

end LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.BaseBudget
