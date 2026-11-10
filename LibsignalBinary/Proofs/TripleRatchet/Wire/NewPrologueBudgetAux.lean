/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
public import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
public meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
meta import LibsignalBinary.Proofs.Placed.BudgetPoolSync

/-!
# Budget-Threaded `<SignalMessage>::new` Prologue & Address/Key Serialization

Prologue allocator event prefixes and `FitsEvents` splitting lemmas, no-panic `[LibsignalPlacement]`
call/sequencing helpers, and budget-threaded proofs for the prologue (`+0x000 → +0x054`) and
`serialize_addresses` + `PublicKey::serialize` (`+0x054 → +0x07c / +0x0f0`) on Block `63`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux

open Arm64 ProofLib SepProp
open CryptoVerification
  (LibsignalPlacement LibsignalHooks LibsignalCodeLoaded withLsCodeLoaded lsmpl)
open CryptoVerification.RustHeap (allocHookStack)
open CryptoVerification.LibsignalProtoCodec (encode)
open CryptoVerification.LibsignalTripleRatchetRepr
  (AddrGhost UuidParser noneCap protocolAddressAt serializeAddresses serviceIdParse)
open CryptoVerification.LibsignalTripleRatchet
  (blkPC_63 blkPl_63 SignalMessageNewGhost SerializeAddressesGhost TraceVRegsEq
   boxU8Buf computeMacStack computeMacStackX extHookStack memRegion_24_split_8_16
   newSavedRegs optAddrAt optSerializeAddressesAt serializeAddressesStack
   serializeAddressesStackX signalMessageNew_of_sepWP_placed
   sp_add_32_add_8 sp_sub_96_add_112 sp_sub_96_add_120 sp_sub_96_add_128 sp_sub_96_add_96)
open CryptoVerification.LibsignalTripleRatchet.NewPrologueCallees
  (entails_of_sep_focus satisfies_of_sep_focus)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FitsEnv FitsEvents RustCliAllocBudget
   fitsEvents_append rustAllocEvents rustDeallocEvents)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (PublicKeySerializeEnv fitsEnv_publicKeySerialize_iff publicKeySerializeEvents
   publicKeySerializeSpec publicKeySerializeSpecWithStack publicKeySerializeSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Mac.DefsBudget
  (SerializeAddressesEnv computeMacEvents fitsEnv_serializeAddresses_iff serializeAddressesEvents
   serializeAddressesSpec serializeAddressesSpecWithStack serializeAddressesSpecX)
open LibsignalBinary.Proofs.TripleRatchet.Wire.NewDefsBudget
  (SignalMessageNewEnv fitsEnv_signalMessageNew_iff signalMessageNewEvents)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm]
  sp_sub_96_add_96 sp_sub_96_add_112 sp_sub_96_add_120 sp_sub_96_add_128 sp_add_32_add_8

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_neg_beq_zero_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if ¬(v == 0#64) = true then b else a) = (if v = 0#64 then a else b) := by
  by_cases h : v = 0#64 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_not_beq_zero_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if (!(v == 0#64)) = true then b else a) = (if v = 0#64 then a else b) := by
  by_cases h : v = 0#64 <;> simp [h]

@[local simp, local wp_norm, local arm64_norm]
private theorem branch_pos_beq_zero_ite {α : Type} (v : BitVec 64) (a b : α) :
    (if (v == 0#64) = true then a else b) = (if v = 0#64 then a else b) := by
  by_cases h : v = 0#64 <;> simp [h]

/-! ## Prologue event prefixes and `FitsEvents` splitting lemmas -/

/-- Events of Segment 2 (`serialize_addresses` + `PublicKey::serialize`) in `<SignalMessage>::new`. -/
def newAddrAndRkEvents (parse : UuidParser) (x : SignalMessageNewGhost) : List AllocEvent :=
  (if (x.addresses parse).isSome then rustAllocEvents 36 1 else []) ++ publicKeySerializeEvents

/-- Events of Segment 3 (temporary `ciphertext` copy) in `<SignalMessage>::new`. -/
def newCtCopyEvents (x : SignalMessageNewGhost) : List AllocEvent :=
  if x.ciphertext.isEmpty then [] else rustAllocEvents x.ciphertext.length 1

/-- Events of Segment 4 (temporary `pq_ratchet` copy) in `<SignalMessage>::new`. -/
def newPqCopyEvents (x : SignalMessageNewGhost) : List AllocEvent :=
  if x.pqRatchet.isEmpty then [] else rustAllocEvents x.pqRatchet.length 1

/-- Combined event prefix of Segments 1–4 (`+0x000..+0x100`) in `<SignalMessage>::new`. -/
def newPrologueEvents (parse : UuidParser) (x : SignalMessageNewGhost) : List AllocEvent :=
  newAddrAndRkEvents parse x ++ newCtCopyEvents x ++ newPqCopyEvents x

/-- Remaining events of `<SignalMessage>::new` after `+0x100` (Phase 2 + epilogue). -/
def newPostPrologueEvents (parse : UuidParser) (x : SignalMessageNewGhost) : List AllocEvent :=
  rustAllocEvents ((encode (x.protoMsg parse)).length + 9) 1 ++
    computeMacEvents ++
    (if x.ciphertext.isEmpty then [] else rustAllocEvents x.ciphertext.length 1) ++
    (if x.pqRatchet.isEmpty then [] else rustAllocEvents x.pqRatchet.length 1) ++
    rustDeallocEvents 33 1 ++
    (if x.ciphertext.isEmpty then [] else rustDeallocEvents x.ciphertext.length 1) ++
    (if x.pqRatchet.isEmpty then [] else rustDeallocEvents x.pqRatchet.length 1)

theorem signalMessageNewEvents_eq_prologue_append (parse : UuidParser)
    (x : SignalMessageNewGhost) :
    signalMessageNewEvents parse x =
      newPrologueEvents parse x ++ newPostPrologueEvents parse x := by
  simp only [signalMessageNewEvents, newPrologueEvents, newAddrAndRkEvents, newCtCopyEvents,
    newPqCopyEvents, newPostPrologueEvents, List.append_assoc]

theorem fitsEvents_prologue_and_post_of_signalMessageNew {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {parse : UuidParser} {x : SignalMessageNewGhost}
    (h : FitsEnv M lim st (SignalMessageNewEnv parse x)) :
    FitsEvents M lim st (newPrologueEvents parse x) ∧
      FitsEvents M lim (M.stepEvents (newPrologueEvents parse x) st)
        (newPostPrologueEvents parse x) := by
  have hevs := (fitsEnv_signalMessageNew_iff parse x).mp h
  rw [signalMessageNewEvents_eq_prologue_append] at hevs
  exact (fitsEvents_append M lim _ _ st).mp hevs

theorem fitsEvents_segments_of_prologue {M : AllocCostModel} {lim : BudgetLimits}
    {st : M.σ} {parse : UuidParser} {x : SignalMessageNewGhost}
    (h : FitsEvents M lim st (newPrologueEvents parse x)) :
    let st1 := M.stepEvents (newAddrAndRkEvents parse x) st
    let st2 := M.stepEvents (newCtCopyEvents x) st1
    FitsEvents M lim st (newAddrAndRkEvents parse x) ∧
      FitsEvents M lim st1 (newCtCopyEvents x) ∧
      FitsEvents M lim st2 (newPqCopyEvents x) ∧
      M.stepEvents (newPqCopyEvents x) st2 = M.stepEvents (newPrologueEvents parse x) st := by
  dsimp only [newPrologueEvents] at h ⊢
  rw [List.append_assoc] at h
  obtain ⟨h1, h23⟩ := (fitsEvents_append M lim _ _ st).mp h
  obtain ⟨h2, h3⟩ := (fitsEvents_append M lim _ _ _).mp h23
  refine ⟨h1, h2, h3, ?_⟩
  rw [← M.stepEvents_append, ← M.stepEvents_append, List.append_assoc]

private theorem serializeAddressesEvents_eq_if_isSome (parse : UuidParser)
    (ret locA : BitVec 64) (l : AddrGhost) (remA : BitVec 64) (rem : AddrGhost) :
    serializeAddressesEvents parse ⟨ret, locA, l, remA, rem⟩ =
      (if (serializeAddresses (serviceIdParse parse) l rem).isSome then
        rustAllocEvents 36 1
       else []) := by
  unfold serializeAddressesEvents
  dsimp only
  cases (serializeAddresses (serviceIdParse parse) l rem) <;> rfl

/-! ## No-panic `[LibsignalPlacement]` call and sequencing helpers -/

theorem call_noPanic_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    {entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {F : SepProp}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf R', sf.status = .Panicked →
      (sf.mem ⊨ spec.onPanic x s sf ∗ R') → False)
    (hnext : ∀ sf : State, LibsignalCodeLoaded lsmpl sf.mem →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ R') → False := by
        intro _ _ _ ho; exact not_satisfies_false_sepConj ho) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ (F ∗ R) := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_comm (spec.pre x s), sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcl, hpre R hm⟩
  obtain ⟨sm, hsteps, hout, -⟩ :=
    hcall.no_fault_before_outcome x (F ∗ R) s hpc hrun hpre' hsp hL
  have hcl_m : LibsignalCodeLoaded lsmpl sm.mem := hcl.of_keepsFrozen hsteps.keepsFrozen
  rcases hout with
    ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨hoom_s, hpost⟩
  · dsimp only [withLsCodeLoaded] at hpost
    rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hcl_m hpcm hrunm hspm hcsm R hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · dsimp only [withLsCodeLoaded] at hpost
    exact (hpanic sm (F ∗ R) hpan hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    exact (hexit sm code (F ∗ R) hex hpost).elim
  · dsimp only [withLsCodeLoaded] at hpost
    exact (hoom sm (F ∗ R) hoom_s hpost).elim

/-- Sequence a panic-free `SepWPp` segment (`Qp = fun _ _ => False`) into an arbitrary `SepWPp`
continuation while preserving `LibsignalCodeLoaded`. -/
theorem signalMessageNew_seq_noPanic_placed [LibsignalPlacement] {prog : Program}
    {mid ret : BitVec 64} {s : State}
    {P P1 F P2 : SepProp} {φ : State → Prop} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h1 : SepWPp prog mid s P1 (fun sm P_m => φ sm ∧ (P_m ⊢ P2)) (fun _ _ => False))
    (hfocus : P = P1 ∗ F := by sep_focus)
    (h2 : ∀ sm, LibsignalCodeLoaded lsmpl sm.mem →
      sm.pc = mid → sm.status = .Running → φ sm →
      SepWPp prog ret sm (P2 ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hfocus, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hφ, hent⟩ | ⟨_, _, _, hfalse⟩ | ⟨_, hfoom⟩⟩ :=
    h1 (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P2 ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout⟩ :=
      h2 sm (hcl.of_keepsFrozen hsteps.keepsFrozen) hpcm hrunm hφ R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact False.elim hfalse
  · exact (not_satisfies_false_sepConj hfoom).elim

theorem stackAt_split_ge {sub total : Nat} (hle : sub ≤ total) (hbnd : total ≤ 2 ^ 64)
    (sp : BitVec 64) :
    stackAt sp total =
      stackAt sp sub ∗ memRegion (sp - BitVec.ofNat 64 total) (total - sub) := by
  have heq : total = sub + (total - sub) := (Nat.add_sub_of_le hle).symm
  conv => lhs; rw [heq]
  rw [ProofLib.stackAt_split_bottom sp sub (total - sub) (by omega),
    show sub + (total - sub) = total by omega, sepConj_comm]

/-! ## Prologue (`+0x000 → +0x054`) with `A.pool` transport -/

theorem new_prologue_wp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {H : LibsignalHooks}
    (x : SignalMessageNewGhost) (sp0 w368 w360 w352 w344 w328 : BitVec 64) (w332 : BitVec 32)
    (s0 : State)
    (hpc : s0.pc = (blkPl_63).base)
    (hrun : s0.status = .Running)
    (hsp : s0.sp = sp0)
    (hsp_align : s0.spAligned = true)
    (hx1 : s0.readReg64 .x1 = x.macKeyA)
    (hx2 : s0.readReg64 .x2 = 32#64)
    (hx4 : s0.readReg64 .x4 = x.remA)
    (hx5 : s0.readReg64 .x5 = x.senderRatchetKeyA)
    (hx6 : (s0.readReg64 .x6).setWidth 32 = x.counter)
    (hx7 : (s0.readReg64 .x7).setWidth 32 = x.previousCounter)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    SepWP ((blkPC_63).rebase (blkPl_63).base H) ((blkPl_63).base + 84#64) s0
      ((sp0 ↦₆₄ x.ciphertextA) ∗
       ((sp0 + 0x08#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
       ((sp0 + 0x10#64) ↦₆₄ x.senderIkA) ∗
       ((sp0 + 0x18#64) ↦₆₄ x.receiverIkA) ∗
       ((sp0 + 0x20#64) ↦₆₄ x.pqRatchetA) ∗
       ((sp0 + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
       ((sp0 - 368#64) ↦₆₄ w368) ∗
       ((sp0 - 360#64) ↦₆₄ w360) ∗
       ((sp0 - 352#64) ↦₆₄ w352) ∗
       ((sp0 - 344#64) ↦₆₄ w344) ∗
       ((sp0 - 332#64) ↦₃₂ w332) ∗
       ((sp0 - 328#64) ↦₆₄ w328) ∗
       cells (sp0 - 96#64) 12 ∗
       A.pool lim st s0)
      (fun s1 P1 =>
        (s1.sp = sp0 - 416#64 ∧
         s1.spAligned = true ∧
         s1.readReg64 .x3 = s0.readReg64 .x3 ∧
         s1.readReg64 .x4 = x.remA ∧
         s1.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         s1.readReg64 .x20 = x.senderRatchetKeyA ∧
         s1.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         s1.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         s1.readReg64 .x24 = x.ret ∧
         s1.readReg64 .x25 = x.ciphertextA ∧
         s1.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         s1.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq s1 s0) ∧
        (P1 ⊢
          (sp0 ↦₆₄ x.ciphertextA) ∗
          ((sp0 + 0x08#64) ↦₆₄ BitVec.ofNat 64 x.ciphertext.length) ∗
          ((sp0 + 0x10#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 + 0x18#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 + 0x20#64) ↦₆₄ x.pqRatchetA) ∗
          ((sp0 + 0x28#64) ↦₆₄ BitVec.ofNat 64 x.pqRatchet.length) ∗
          ((sp0 - 368#64) ↦₆₄ x.senderIkA) ∗
          ((sp0 - 360#64) ↦₆₄ x.receiverIkA) ∗
          ((sp0 - 352#64) ↦₆₄ x.macKeyA) ∗
          ((sp0 - 344#64) ↦₆₄ 32#64) ∗
          ((sp0 - 332#64) ↦₃₂ (s0.readReg64 .x0).setWidth 32) ∗
          ((sp0 - 328#64) ↦₆₄ x.pqRatchetA) ∗
          newSavedRegs sp0 s0 ∗
          A.pool lim st s1)) := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp] using hsp_align
  subst hsp
  simp only [arm64_norm] at hx1 hx2 hx4 hx5 hx6 hx7 hx8
  unfold newSavedRegs
  cells_unfold
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ =>
    SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => SepWP.exists_elim fun _ => ?_
  wp_steps_sync_pool ((blkPl_63).base + 84#64)
  refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
  · rw [← hx6, ← hx7]
    simp only [State.spAligned, wp_norm, arm64_norm, *]
  · exact entails_of_sep_focus (by sep_focus)

/-! ## `addresses` and `PublicKey::serialize` (`+0x054 → +0x07c / +0x0f0`) -/

theorem new_addr_and_rk_wpp_placed_at [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {pkStack saStack cmStack : Nat} {Qp : State → SepProp → Prop}
    (hpk_le : pkStack + 32 ≤ cmStack := by decide)
    (hsa_le : saStack ≤ cmStack := by decide)
    (hcm_bnd : cmStack ≤ 2 ^ 64 := by decide)
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecWithStack M A lim pkStack)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpecWithStack M A lim parse saStack)))
    (x : SignalMessageNewGhost) (sp0 : BitVec 64) (s : State)
    (hfit : FitsEvents M lim st (newAddrAndRkEvents parse x))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx3 : s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64))
    (hloc_ne : x.loc.isSome → x.locA ≠ 0#64)
    (hx4 : s.readReg64 .x4 = x.remA)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64)
      s
      (optAddrAt A.repAlloc x.locA x.loc ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       memRegion (sp0 - 312#64) 24 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) cmStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          optAddrAt A.repAlloc x.locA x.loc ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          optSerializeAddressesAt A.repAlloc (sp0 - 312#64) (x.addresses parse) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x28) x.senderRatchetKey.serialize ∗
          A.pool lim (M.stepEvents (newAddrAndRkEvents parse x) st) sm ∗
          stackAt (sp0 - 416#64) cmStack))
      Qp := by
  have hsp0_align : (sp0 &&& 15#64 == 0#64) = true := by
    simpa only [State.spAligned, hsp, arm64_norm] using hsp_align
  simp only [arm64_norm] at hx3 hx4 hx19 hx20 hx22 hx23 hx24 hx25 hx27 hx29
  cases hloc : x.loc with
  | none =>
    have hevs_eq : newAddrAndRkEvents parse x = publicKeySerializeEvents := by
      simp [newAddrAndRkEvents, SignalMessageNewGhost.addresses, hloc]
    rw [hevs_eq] at hfit ⊢
    have hfit_pk : FitsEnv M lim st PublicKeySerializeEnv :=
      fitsEnv_publicKeySerialize_iff.mpr hfit
    simp only [hloc, Bool.false_eq_true, ↓reduceIte] at hx3
    simp only [hloc, optAddrAt, SignalMessageNewGhost.addresses, Option.bind_none, emp_sepConj,
      memRegion_24_split_8_16 (sp0 - 312#64), bv_sub_add_lit sp0 312 8,
      sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun w312 => ?_
    apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 205) hcl
    wp_steps_sync_pool (lsmpl.base 205)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl0
    refine call_noPanic_placed
      (x := (⟨x.senderRatchetKeyA, x.senderRatchetKey⟩, st))
      (F := protocolAddressAt A.repAlloc x.rem x.remA ∗
            ((sp0 - 312#64) ↦₆₄ noneCap) ∗
            memRegion (sp0 - 304#64) 16 ∗
            memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - (pkStack + 32)))
      hcl0 hPk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      rw [stackAt_split_ge hpk_le hcm_bnd (sp0 - 416#64)] at hm
      simp only [publicKeySerializeSpecWithStack, noneCap, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 _ hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [publicKeySerializeSpecWithStack, wp_norm, arm64_norm, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1_1, htr1⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, *]
    · rw [stackAt_split_ge hpk_le hcm_bnd (sp0 - 416#64)]
      simp only [optSerializeAddressesAt, noneCap, Alloc.DefsBudget.boxU8Buf,
        bv_sub_add_lit sp0 312 8, wp_norm, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)
  | some l =>
    let g_sa : SerializeAddressesGhost :=
      ⟨sp0 - 312#64, x.locA, l, x.remA, x.rem⟩
    have hevs_eq : newAddrAndRkEvents parse x =
        serializeAddressesEvents parse g_sa ++ publicKeySerializeEvents := by
      simp only [newAddrAndRkEvents, SignalMessageNewGhost.addresses, hloc, Option.bind_some, g_sa,
        serializeAddressesEvents_eq_if_isSome]
    rw [hevs_eq] at hfit ⊢
    obtain ⟨hfit_sa_evs, hfit_pk_evs⟩ := (fitsEvents_append M lim _ _ st).mp hfit
    have hfit_sa : FitsEnv M lim st (SerializeAddressesEnv parse g_sa) :=
      (fitsEnv_serializeAddresses_iff parse g_sa).mpr hfit_sa_evs
    have hfit_pk : FitsEnv M lim (M.stepEvents (serializeAddressesEvents parse g_sa) st)
        PublicKeySerializeEnv :=
      fitsEnv_publicKeySerialize_iff.mpr hfit_pk_evs
    rw [M.stepEvents_append]
    have hloc_ne' : x.locA ≠ 0#64 := hloc_ne (by simp [hloc])
    have hloc_beq : (x.locA == 0#64) = false := beq_eq_false_iff_ne.mpr hloc_ne'
    simp only [hloc, ↓reduceIte] at hx3
    simp only [hloc, optAddrAt, SignalMessageNewGhost.addresses, Option.bind_some]
    apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 61) hcl
    wp_steps_sync_pool (lsmpl.base 61)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl0
    refine call_noPanic_placed
      (x := (g_sa, st))
      (F := (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
            memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - saStack))
      hcl0 hSerAddr (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      rw [stackAt_split_ge hsa_le hcm_bnd (sp0 - 416#64)] at hm
      simp only [serializeAddressesSpecWithStack, g_sa, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf1 hcl1 hpc1 hrun1 hsp1 hcs1
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1, hfp_1⟩
    simp only [wp_norm, arm64_norm, *] at hsp1 h19_1 h20_1 h21_1 h22_1 h23_1 h24_1 h25_1 h26_1 h27_1 h28_1 hfp_1
    simp only [serializeAddressesSpecWithStack, Mac.DefsBudget.optSerializeAddressesAt,
      wp_norm, arm64_norm, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htr1 => ?_
    have hreasm :
        protocolAddressAt A.repAlloc l x.locA ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          optSerializeAddressesAt A.repAlloc (sp0 - 312#64)
            (serializeAddresses (serviceIdParse parse) l x.rem) ∗
          A.pool lim (M.stepEvents (serializeAddressesEvents parse g_sa) st) sf1 ∗
          stackAt (sp0 - 416#64) saStack ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - saStack) =
        protocolAddressAt A.repAlloc l x.locA ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          optSerializeAddressesAt A.repAlloc (sp0 - 312#64)
            (serializeAddresses (serviceIdParse parse) l x.rem) ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          A.pool lim (M.stepEvents (serializeAddressesEvents parse g_sa) st) sf1 ∗
          stackAt (sp0 - 416#64) cmStack := by
      rw [stackAt_split_ge hsa_le hcm_bnd (sp0 - 416#64)]
      sep_ac_rfl
    rw [hreasm]
    apply signalMessageNew_of_sepWP_placed (mid := lsmpl.base 205) hcl1
    wp_steps_sync_pool (lsmpl.base 205)
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hcl1'
    refine call_noPanic_placed
      (x := (⟨x.senderRatchetKeyA, x.senderRatchetKey⟩,
        M.stepEvents (serializeAddressesEvents parse g_sa) st))
      (F := protocolAddressAt A.repAlloc l x.locA ∗
            protocolAddressAt A.repAlloc x.rem x.remA ∗
            optSerializeAddressesAt A.repAlloc (sp0 - 312#64)
              (serializeAddresses (serviceIdParse parse) l x.rem) ∗
            memRegion (sp0 - 416#64 - BitVec.ofNat 64 cmStack) (cmStack - (pkStack + 32)))
      hcl1' hPk (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.spAligned, wp_norm, arm64_norm, hsp1, hsp0_align])
      (by simp only [arm64_norm]; rfl) ?_
      (fun _ _ _ _ he => not_satisfies_false_sepConj he)
      (fun _ _ _ hp => not_satisfies_false_sepConj hp) ?_
    · intro R' hm
      rw [stackAt_split_ge hpk_le hcm_bnd (sp0 - 416#64)] at hm
      simp only [publicKeySerializeSpecWithStack, sepConj_assoc,
        wp_norm, arm64_norm, *] at hm ⊢
      exact satisfies_of_sep_focus hm (by sep_focus)
    intro sf2 _ hpc2 hrun2 hsp2 hcs2
    rcases hcs2 with ⟨h19_2, h20_2, h21_2, h22_2, h23_2, h24_2, h25_2, h26_2, h27_2, h28_2, hfp_2⟩
    simp only [wp_norm, arm64_norm, *] at hsp2 h19_2 h20_2 h21_2 h22_2 h23_2 h24_2 h25_2 h26_2 h27_2 h28_2 hfp_2
    simp only [publicKeySerializeSpecWithStack, wp_norm, arm64_norm, hsp1, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx1_2, htr2⟩ => ?_
    simp only [wp_norm, arm64_norm, htr1] at hx1_2 htr2
    apply SepWPp.of_sepWP_ret
    wp_steps_sync_pool
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64)
    refine SepWP.done (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) ⟨?_, ?_⟩
    · simp only [wp_norm, arm64_norm, *]
    · rw [stackAt_split_ge hpk_le hcm_bnd (sp0 - 416#64)]
      simp only [Alloc.DefsBudget.boxU8Buf, wp_norm, arm64_norm]
      exact entails_of_sep_focus (by sep_focus)

theorem new_addr_and_rk_wpp_placed [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec M A lim)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpec M A lim parse)))
    (x : SignalMessageNewGhost) (sp0 : BitVec 64) (s : State)
    (hfit : FitsEvents M lim st (newAddrAndRkEvents parse x))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx3 : s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64))
    (hloc_ne : x.loc.isSome → x.locA ≠ 0#64)
    (hx4 : s.readReg64 .x4 = x.remA)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64)
      s
      (optAddrAt A.repAlloc x.locA x.loc ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       memRegion (sp0 - 312#64) 24 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStack)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          optAddrAt A.repAlloc x.locA x.loc ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          optSerializeAddressesAt A.repAlloc (sp0 - 312#64) (x.addresses parse) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x28) x.senderRatchetKey.serialize ∗
          A.pool lim (M.stepEvents (newAddrAndRkEvents parse x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStack))
      Qp :=
  new_addr_and_rk_wpp_placed_at (pkStack := allocHookStack) (saStack := serializeAddressesStack)
    (cmStack := computeMacStack) (by decide) (by decide) (by decide)
    hPk hSerAddr x sp0 s hfit hcl hpc hrun hsp hsp_align
    hx3 hloc_ne hx4 hx19 hx20 hx22 hx23 hx24 hx25 hx27 hx29

theorem new_addr_and_rk_wpp_placed_x [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits} {st : M.σ} {parse : UuidParser}
    {H : LibsignalHooks} {Qp : State → SepProp → Prop}
    (hPk : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpecX M A lim)))
    (hSerAddr : subroutine_ok ((blkPC_63).rebase (blkPl_63).base H) (lsmpl.base 61)
      (withLsCodeLoaded lsmpl (serializeAddressesSpecX M A lim parse)))
    (x : SignalMessageNewGhost) (sp0 : BitVec 64) (s : State)
    (hfit : FitsEvents M lim st (newAddrAndRkEvents parse x))
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_63).base + 84#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 416#64)
    (hsp_align : s.spAligned = true)
    (hx3 : s.readReg64 .x3 = (if x.loc.isSome then x.locA else 0#64))
    (hloc_ne : x.loc.isSome → x.locA ≠ 0#64)
    (hx4 : s.readReg64 .x4 = x.remA)
    (hx19 : s.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length)
    (hx20 : s.readReg64 .x20 = x.senderRatchetKeyA)
    (hx22 : s.readReg64 .x22 = x.previousCounter.zeroExtend 64)
    (hx23 : s.readReg64 .x23 = x.counter.zeroExtend 64)
    (hx24 : s.readReg64 .x24 = x.ret)
    (hx25 : s.readReg64 .x25 = x.ciphertextA)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length)
    (hx29 : s.readReg64 .x29 = sp0 - 96#64) :
    SepWPp ((blkPC_63).rebase (blkPl_63).base H)
      (if BitVec.ofNat 64 x.ciphertext.length = 0#64 then
        (blkPl_63).base + 240#64
       else
        (blkPl_63).base + 124#64)
      s
      (optAddrAt A.repAlloc x.locA x.loc ∗
       protocolAddressAt A.repAlloc x.rem x.remA ∗
       (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
       memRegion (sp0 - 312#64) 24 ∗
       A.pool lim st s ∗ stackAt (sp0 - 416#64) computeMacStackX)
      (fun sm Pm =>
        (sm.sp = sp0 - 416#64 ∧
         sm.spAligned = true ∧
         sm.readReg64 .x19 = BitVec.ofNat 64 x.ciphertext.length ∧
         sm.readReg64 .x20 = x.senderRatchetKeyA ∧
         sm.readReg64 .x21 = 33#64 ∧
         sm.readReg64 .x22 = x.previousCounter.zeroExtend 64 ∧
         sm.readReg64 .x23 = x.counter.zeroExtend 64 ∧
         sm.readReg64 .x24 = x.ret ∧
         sm.readReg64 .x25 = x.ciphertextA ∧
         sm.readReg64 .x27 = BitVec.ofNat 64 x.pqRatchet.length ∧
         sm.readReg64 .x29 = sp0 - 96#64 ∧
         TraceVRegsEq sm s) ∧
        (Pm ⊢
          optAddrAt A.repAlloc x.locA x.loc ∗
          protocolAddressAt A.repAlloc x.rem x.remA ∗
          (x.senderRatchetKeyA ↦ₛ x.senderRatchetKey.bytes.toList) ∗
          optSerializeAddressesAt A.repAlloc (sp0 - 312#64) (x.addresses parse) ∗
          boxU8Buf A.repAlloc (sm.readReg64 .x28) x.senderRatchetKey.serialize ∗
          A.pool lim (M.stepEvents (newAddrAndRkEvents parse x) st) sm ∗
          stackAt (sp0 - 416#64) computeMacStackX))
      Qp :=
  new_addr_and_rk_wpp_placed_at (pkStack := extHookStack) (saStack := serializeAddressesStackX)
    (cmStack := computeMacStackX) (by decide) (by decide) (by decide)
    hPk hSerAddr x sp0 s hfit hcl hpc hrun hsp hsp_align
    hx3 hloc_ne hx4 hx19 hx20 hx22 hx23 hx24 hx25 hx27 hx29

end LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologueBudgetAux
