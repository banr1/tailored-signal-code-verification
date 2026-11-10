/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Decodes
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.MessageEncodeCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.GenLsBlock
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.Defs
import ProofLib.SepLogic.WPp

/-!
# Relocatable `[LibsignalPlacement]` Shared Step Lemmas for `EpochDirection::encode`

Provides relocatable `[LibsignalPlacement]` basic-block and 64-byte-frame call steppers shared
between `EpochDirection::encode [local#1]` (`Block 154`) and `[local#2]` (`Block 317`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.MessageEncode

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Prost.EncodeVarintNorm
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  EncodedLen.zeroExtend64_beq_zero32
  EncodedLen.ofNat_countLeadingZeros_64 EncodedLen.ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 EncodedLen.hwVarintLen_eq_ofNat_varintLen_norm
  EncodedLen.hwVarintLen_bvShift_eq_ofNat_varintLen_norm EncodedLen.zext64_truncate32
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  EncodedLen.ule_zero_64 EncodedLen.ult_zero_64 EncodedLen.ule_self_64 EncodedLen.ult_self_64
  zext64_trunc32_orr_1 zext64_trunc32_orr_100000001 zext64_orr_1_32

def AuthEncodeCalleeSavedPlaced (s0 s : State) : Prop :=
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  calleeSavedVRegs s = calleeSavedVRegs s0 ∧
  StepInvPlaced s0 s

theorem AuthEncodeCalleeSavedPlaced.refl (s0 : State) : AuthEncodeCalleeSavedPlaced s0 s0 :=
  ⟨rfl, rfl, rfl, rfl, rfl, StepInvPlaced.refl s0⟩

theorem AuthEncodeCalleeSavedPlaced.trans {s0 s1 s2 : State}
    (h01 : AuthEncodeCalleeSavedPlaced s0 s1) (h12 : AuthEncodeCalleeSavedPlaced s1 s2) :
    AuthEncodeCalleeSavedPlaced s0 s2 :=
  ⟨h12.1.trans h01.1, h12.2.1.trans h01.2.1, h12.2.2.1.trans h01.2.2.1,
    h12.2.2.2.1.trans h01.2.2.2.1, h12.2.2.2.2.1.trans h01.2.2.2.2.1,
    h01.2.2.2.2.2.trans h12.2.2.2.2.2⟩

theorem AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved {s1 s2 : State}
    (hcs : CalleeSavedPreserved s1 s2) (hinv : StepInvPlaced s1 s2) : AuthEncodeCalleeSavedPlaced s1 s2 :=
  ⟨hcs.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.1, hcs.2.2.2.2.2.2.2.2.2.1,
    hcs.2.2.2.2.2.2.2.2.2.2.2, hinv⟩

theorem AuthEncodeCalleeSavedPlaced.step {s0 s1 s2 : State}
    (h01 : AuthEncodeCalleeSavedPlaced s0 s1)
    (hx25 : s2.readReg64 (Reg.gpr 25#5) = s1.readReg64 (Reg.gpr 25#5))
    (hx26 : s2.readReg64 (Reg.gpr 26#5) = s1.readReg64 (Reg.gpr 26#5))
    (hx27 : s2.readReg64 (Reg.gpr 27#5) = s1.readReg64 (Reg.gpr 27#5))
    (hx28 : s2.readReg64 (Reg.gpr 28#5) = s1.readReg64 (Reg.gpr 28#5))
    (hinv : StepInvPlaced s1 s2)
    (hvregs : calleeSavedVRegs s2 = calleeSavedVRegs s1 := by simp only [arm64_norm]) :
    AuthEncodeCalleeSavedPlaced s0 s2 :=
  h01.trans ⟨hx25, hx26, hx27, hx28, hvregs, hinv⟩

def withAuthEncodeCSPlaced {α : Type} (s0 : State) (spec : Spec α) : Spec α where
  pre := fun x s => ⌜AuthEncodeCalleeSavedPlaced s0 s⌝ ∗ spec.pre x s
  post := spec.post
  onPanic := spec.onPanic
  onExit := spec.onExit
  onOom := spec.onOom

theorem subroutine_ok_withAuthEncodeCSPlaced {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (s0 : State) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (withAuthEncodeCSPlaced s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withAuthEncodeCSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s hpc hrun hpre.2 hsp fun _ hout => hout

theorem subroutine_ok_withAuthEncodeCSPlaced_x {α : Type} {prog : Program} {entry : BitVec 64} {spec : Spec α}
    (img : Obj.Image) (s0 : State) (hinv0 : ImgCallInv img s0)
    (h : subroutine_ok prog entry (spec.inImage img)) :
    subroutine_ok prog entry (withAuthEncodeCSPlaced s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withAuthEncodeCSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (spec.inImage img).pre x s ∗ R := by
    rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpre.1.2.2.2.2.2.1 img hinv0, hpre.2⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout

theorem subroutine_ok_withAuthEncodeCSPlaced_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {entry : BitVec 64} {spec : Spec α} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (h : subroutine_ok prog entry (withLsCodeLoaded lsmpl spec)) :
    subroutine_ok prog entry (withAuthEncodeCSPlaced s0 spec) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hsp => ?_
  rw [withAuthEncodeCSPlaced, sepConj_assoc, satisfies_pure_sepConj] at hpre
  have hpre' : s.mem ⊨ (withLsCodeLoaded lsmpl spec).pre x s ∗ R := by
    dsimp only [withLsCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0.of_keepsFrozen hpre.1.2.2.2.2.2.2, hpre.2⟩
  exact h.mono_outcome x R s hpc hrun hpre' hsp fun _ hout => hout


theorem epochDirection_unpinned_of_pinned_placed_x [LibsignalPlacement] {resStack : Nat}
    {prog : Program} {entry : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A))) :
    subroutine_ok prog entry
      (withLsCodeLoaded lsmpl (encodeEpochDirectionSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  dsimp only [withLsCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  obtain ⟨hinv0, hpre⟩ := hpre
  dsimp only [encodeEpochDirectionSpecOf] at hpre
  rw [epochDirectionPBAt_eq_exists_pinned] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  have hpre' : s0.mem ⊨ (withLsCodeLoaded lsmpl (encodeEpochDirectionPinnedSpecOf resStack A)).pre
      ⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ s0 ∗ R := by
    dsimp only [withLsCodeLoaded]; rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hinv0, hpre⟩
  refine hpinned.mono_outcome ⟨x.tag, x.dirA, g, x.dir, x.v, x.cap, x.ptr, x.bs⟩
    R s0 hpc hrun hpre' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | hrest
  · exact Or.inl ⟨hret, hcc, epochDirection_post_unpinned_of_pinned hq⟩
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact Or.inr (Or.inr hrest)


def IsEpochDirectionEncodeEntryProg (prog : Program) (entry : BitVec 64) : Prop :=
  (∃ b ext, prog = tripleRatchetProgAtExt b ext ∧ IsEpochDirectionEncodeEntry b ext entry) ∨
  (∃ (_ : LibsignalPlacement) (H : String → Option (State → State)),
    prog = lsProg_154 H ∧ entry = (blkPl_154).base) ∨
  (∃ (_ : LibsignalPlacement) (H : String → Option (State → State)),
    prog = lsProg_317 H ∧ entry = (blkPl_317).base)

theorem epochDirectionEncode_fetch_entry_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsEpochDirectionEncodeEntryProg prog entry) {ins : Instr}
    (h1 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name) = some ins)
    (h2 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection2Name) = some ins)
    (h183 : ∀ [LibsignalPlacement] H, ((blkPC_154).rebase (blkPl_154).base H).fetch ((blkPl_154).base + 0#64) = some ins)
    (h367 : ∀ [LibsignalPlacement] H, ((blkPC_317).rebase (blkPl_317).base H).fetch ((blkPl_317).base + 0#64) = some ins) :
    prog.fetch entry = some ins := by
  rcases hfn with ⟨b, ext, rfl, rfl | rfl⟩ | ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩
  · exact h1 b ext
  · exact h2 b ext
  · simpa using @h183 inst H
  · simpa using @h367 inst H

theorem epochDirectionEncode_fetch_add_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsEpochDirectionEncodeEntryProg prog entry) {k : Nat} {ins : Instr}
    (h1 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection1Name + BitVec.ofNat 64 k) = some ins)
    (h2 : ∀ b ext, (tripleRatchetProgAtExt b ext).fetch
      ((tripleRatchetProgAtExt b ext).fnAddr encodeEpochDirection2Name + BitVec.ofNat 64 k) = some ins)
    (h183 : ∀ [LibsignalPlacement] H,
      ((blkPC_154).rebase (blkPl_154).base H).fetch ((blkPl_154).base + BitVec.ofNat 64 k) = some ins)
    (h367 : ∀ [LibsignalPlacement] H,
      ((blkPC_317).rebase (blkPl_317).base H).fetch ((blkPl_317).base + BitVec.ofNat 64 k) = some ins) :
    prog.fetch (entry + BitVec.ofNat 64 k) = some ins := by
  rcases hfn with ⟨b, ext, rfl, rfl | rfl⟩ | ⟨inst, H, rfl, rfl⟩ | ⟨inst, H, rfl, rfl⟩
  · exact h1 b ext
  · exact h2 b ext
  · exact @h183 inst H
  · exact @h367 inst H

open Lean Elab Tactic in
scoped elab "ed_fetches_range_placed " hfn:ident kStart:num kEnd:num : tactic => do
  let off1 := 0x37850
  let off2 := 0x4d3c8
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let fnOff1 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x37850
  let fnOff2 := mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x4d3c8
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    let hexK := String.ofList (Nat.toDigits 16 k)
    let dec1 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off1 + k))}")
    let dec2 := mkIdent (`CryptoVerification.SpqrV1.Prost.MessageEncode |>.str
      s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (off2 + k))}")
    let p183 := mkIdent (`CryptoVerification |>.str s!"blkPC_154_rebase_fetch_0x{hexK}")
    let p367 := mkIdent (`CryptoVerification |>.str s!"blkPC_317_rebase_fetch_0x{hexK}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := epochDirectionEncode_fetch_entry_placed $hfn
          (fun b ext => $fetchEntry (b := b) (H := Rust.withPanics ext) $fnOff1 (by decide) $dec1)
          (fun b ext => $fetchEntry (b := b) (H := Rust.withPanics ext) $fnOff2 (by decide) $dec2)
          (fun [LibsignalPlacement] H => $p183 _ H)
          (fun [LibsignalPlacement] H => $p367 _ H)))
    else
      evalTactic (← `(tactic|
        have := epochDirectionEncode_fetch_add_placed $hfn (k := $kq)
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff1 (by decide) $dec1 (by decide))
          (fun b ext => $fetchAdd (b := b) (H := Rust.withPanics ext) (k := $kq) $fnOff2 (by decide) $dec2 (by decide))
          (fun [LibsignalPlacement] H => $p183 _ H)
          (fun [LibsignalPlacement] H => $p367 _ H)))


theorem step_epochDir_prologue_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {entry : BitVec 64} (hfn : IsEpochDirectionEncodeEntryProg prog entry)
    (tag : BitVec 32) (dirA v sp : BitVec 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hhs0 : s = s0) (hpc : s.pc = entry)
    (hrun : s.status = .Running) (hsp : s.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hw0 : s.readReg32 .x0 = tag)
    (hx1 : s.readReg64 .x1 = dirA) (hx2 : s.readReg64 .x2 = v) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = stackAt sp (authEncodeStackOf resStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 40#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) →
      sm.readReg64 .x1 = v → sm.readReg64 .x19 = v → sm.readReg64 .x21 = dirA →
      AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((stackAt (sp - 64#64) (0x30 + resStack) ∗
          epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
            (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
            (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_range_placed hfn 0 40
  examples_hide_fetches; subst hP hhs0
  have hsp_aligned := sp_sub_64_aligned halign
  rw [stackAt_authEncode hres sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun sv0 => SepWPp.exists_elim fun sv1 =>
    SepWPp.exists_elim fun sv2 => SepWPp.exists_elim fun sv3 =>
    SepWPp.exists_elim fun sv4 => SepWPp.exists_elim fun sv5 =>
    SepWPp.exists_elim fun sv6 => SepWPp.exists_elim fun sv7 => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 40#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  have hx0_eq :
      BitVec.zeroExtend 64 (BitVec.truncate 32
        (2#64 ||| BitVec.zeroExtend 64 (BitVec.truncate 32 (s.readReg64 (Reg.gpr 0#5)) <<< 3))) =
      (((tag <<< 3) ||| (Proto.WireType.lengthDelimited).toU32).zeroExtend 64) := by
    change BitVec.zeroExtend 64 (BitVec.truncate 32
      (2#64 ||| BitVec.zeroExtend 64 (s.readReg32 .x0 <<< 3))) = _
    rw [hw0]; dsimp only [Proto.WireType.toU32]; bv_bits
  refine SepWPp.weaken_pre (by dsimp only [epochDirectionSavedFrame]; exact Entails.of_eq (by ac_rfl))
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))

/-- Shared inline `EpochDirection::encoded_len` computation (`+44..+168` and `+452..+484`):
loads `w23 = d.ctr`, `x22 = d.next.length`, `x20 = d.prev.length`, and computes
`x0 = BitVec.ofNat 64 (epochDirectionPBEncodedLen d)` and `x1 = v` at `entry + 168#64`. -/
theorem step_epochDir_len_placed {prog : Program}
    {entry : BitVec 64} (hfn : IsEpochDirectionEncodeEntryProg prog entry)
    (v dirA nextPtr prevPtr sp : BitVec 64) (d : EpochDirectionPB)
    (hnext_lt : d.next.length < 2 ^ 63) (hprev_lt : d.prev.length < 2 ^ 63)
    (hlen_fit : epochDirectionPBEncodedLen d < 2 ^ 64)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 44#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64) (htr : s.trace = s0.trace)
    (hx19 : s.readReg64 .x19 = v) (hx21 : s.readReg64 .x21 = dirA) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 168#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 (epochDirectionPBEncodedLen d) → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = d.ctr.zeroExtend 64 → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm (epochDirectionElemsAt dirA nextPtr prevPtr d ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_range_placed hfn 44 168
  ed_fetches_range_placed hfn 452 484
  examples_hide_fetches; subst hP
  dsimp only [epochDirectionElemsAt]
  obtain ⟨hnext_beq, hnext_bne⟩ := ofNat_length_beq_zero_of_lt (bs := d.next) (by omega)
  obtain ⟨hprev_beq, hprev_bne⟩ := ofNat_length_beq_zero_of_lt (bs := d.prev) (by omega)
  cases hctr : (d.ctr == 0#32) <;> cases hn : d.next.isEmpty <;> cases hp : d.prev.isEmpty
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hn_val := bv_bytesField_nonempty hn
    have hp_val := bv_bytesField_nonempty hp
    have hadd12 := EncodedLen.bv_add_ofNat_comm (u32VarintFieldEncodedLen d.ctr) (bytesFieldEncodedLen d.next)
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen d.prev)
        (b := u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.next)
        (c := epochDirectionPBEncodedLen d) rfl hlen_fit
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hn_val := bv_bytesField_nonempty hn
    have hadd12 := EncodedLen.bv_add_ofNat_comm (u32VarintFieldEncodedLen d.ctr) (bytesFieldEncodedLen d.next)
    have htot_eq : epochDirectionPBEncodedLen d =
        u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.next := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hp]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have hp_val := bv_bytesField_nonempty hp
    have htot_eq : u32VarintFieldEncodedLen d.ctr + bytesFieldEncodedLen d.prev =
        epochDirectionPBEncodedLen d := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hn]
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen d.prev)
        (b := u32VarintFieldEncodedLen d.ctr) (c := epochDirectionPBEncodedLen d) htot_eq hlen_fit
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · have hctr_val := bv_u32VarintField_nonzero (beq_eq_false_iff_ne.mp hctr)
    have htot_eq : epochDirectionPBEncodedLen d = u32VarintFieldEncodedLen d.ctr := by
      simp [epochDirectionPBEncodedLen, bytesFieldEncodedLen, hn, hp]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · have hn_val := bv_bytesField_nonempty hn
    have hp_val := bv_bytesField_nonempty hp
    have htot_eq : bytesFieldEncodedLen d.next + bytesFieldEncodedLen d.prev =
        epochDirectionPBEncodedLen d := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr]
    obtain ⟨hadd, hult1, hule1, hult2, hule2⟩ :=
      adds_no_overflow_of_eq (a := bytesFieldEncodedLen d.prev)
        (b := bytesFieldEncodedLen d.next) (c := epochDirectionPBEncodedLen d) htot_eq hlen_fit
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · have hn_val := bv_bytesField_nonempty hn
    have htot_eq : epochDirectionPBEncodedLen d = bytesFieldEncodedLen d.next := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr, bytesFieldEncodedLen, hp]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · have hp_val := bv_bytesField_nonempty hp
    have htot_eq : epochDirectionPBEncodedLen d = bytesFieldEncodedLen d.prev := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr, bytesFieldEncodedLen, hn]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)
  · have htot_eq : epochDirectionPBEncodedLen d = 0 := by
      simp [epochDirectionPBEncodedLen, u32VarintFieldEncodedLen, beq_iff_eq.mp hctr, bytesFieldEncodedLen, hn, hp]
    apply SepWPp.of_sepWP_cs_placed (mid := entry + 168#64); wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
    exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [htot_eq]; simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv)

/-- Shared `ctr` tag push (`+192..+220`):
given `curBs.length < curCap.toNat`, pushes `0x08#8` (`tag = 1`, varint) to `buf`
and sets `x0 = d.ctr.zeroExtend 64`, `x1 = v`. -/
theorem step_epochDir_push_ctr_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} (hfn : IsEpochDirectionEncodeEntryProg prog entry)
    (v curCap curPtr dirA sp : BitVec 64) (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 192#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = d.ctr.zeroExtend 64) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 220#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = d.ctr.zeroExtend 64 → sm.readReg64 .x1 = v → sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x21 = dirA →
      sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x08#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_range_placed hfn 192 220
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 220#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x08#8 hlt]; exact Entails.of_eq (by ac_rfl)

/-- Shared `next` tag push (`+248..+276`):
given `curBs.length < curCap.toNat`, pushes `0x12#8` (`tag = 2`, length-delimited) to `buf`
and sets `x0 = x22`, `x1 = v`. -/
theorem step_epochDir_push_next_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} (hfn : IsEpochDirectionEncodeEntryProg prog entry)
    (v curCap curPtr dirA nextPtr sp : BitVec 64) (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 248#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = dirA) (hx22 : s.readReg64 .x22 = BitVec.ofNat 64 d.next.length)
    (hx23 : s.readReg64 .x23 = nextPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 276#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 d.next.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = dirA → sm.readReg64 .x22 = BitVec.ofNat 64 d.next.length →
      sm.readReg64 .x23 = nextPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x12#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_range_placed hfn 248 276
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 276#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x12#8 hlt]; exact Entails.of_eq (by ac_rfl)

/-- Shared `prev` tag push (`+352..+380`):
given `curBs.length < curCap.toNat`, pushes `0x1a#8` (`tag = 3`, length-delimited) to `buf`
and sets `x0 = x20`, `x1 = v`. -/
theorem step_epochDir_push_prev_tag_placed {prog : Program} (A : RustAlloc)
    {entry : BitVec 64} (hfn : IsEpochDirectionEncodeEntryProg prog entry)
    (v curCap curPtr prevPtr sp : BitVec 64) (curBs : List (BitVec 8)) (d : EpochDirectionPB)
    (hlt : curBs.length < curCap.toNat)
    {s0 s : State} {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 352#64) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (htr : s.trace = s0.trace) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 curBs.length)
    (hx19 : s.readReg64 .x19 = v) (hx20 : s.readReg64 .x20 = BitVec.ofNat 64 d.prev.length)
    (hx21 : s.readReg64 .x21 = prevPtr) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = vecU8At A v curCap curPtr curBs ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = entry + 380#64 → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      sm.readReg64 .x0 = BitVec.ofNat 64 d.prev.length → sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v → sm.readReg64 .x20 = BitVec.ofNat 64 d.prev.length →
      sm.readReg64 .x21 = prevPtr → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm (vecU8At A v curCap curPtr (curBs ++ [0x1a#8]) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_range_placed hfn 352 380
  examples_hide_fetches; subst hP
  rw [vecU8At_open_one A v curCap curPtr curBs hlt]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun y => ?_
  apply SepWPp.of_sepWP_cs_placed (mid := entry + 380#64); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv
  refine SepWPp.weaken_pre ?_
    (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hcs.step (by simp only [arm64_norm]) (by simp only [arm64_norm])
        (by simp only [arm64_norm]) (by simp only [arm64_norm]) hinv))
  rw [← vecU8At_close_one A v curCap curPtr curBs 0x1a#8 hlt]; exact Entails.of_eq (by ac_rfl)

/-- Shared epilogue (`+432..+452`):
restores `x20, x19, x22, x21, x24, x23, fp, lr`, deallocates the 64-byte frame, and returns. -/
theorem step_epochDir_epilogue_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} {entry : BitVec 64} (hfn : IsEpochDirectionEncodeEntryProg prog entry)
    (sp : BitVec 64) {s0 s : State} {R : SepProp} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 432#64) (hrun : s.status = .Running)
    (hsp : s.sp = sp - 64#64) (halign : sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (stackAt (sp - 64#64) (0x30 + resStack) ∗
      epochDirectionSavedFrame sp (s0.readReg64 .fp) (s0.readReg64 .lr)
        (s0.readReg64 .x24) (s0.readReg64 .x23) (s0.readReg64 .x22)
        (s0.readReg64 .x21) (s0.readReg64 .x20) (s0.readReg64 .x19)) ∗ F)
    (hnext : ∀ (sf : State),
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp → sf.trace = s0.trace →
      CalleeSavedPreserved s0 sf → StepInv s0 sf →
      Q sf (stackAt sp (authEncodeStackOf resStack) ∗ F)) :
    SepWPp prog (s0.readReg64 .lr) s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  ed_fetches_range_placed hfn 432 452
  examples_hide_fetches; subst hP
  dsimp only [epochDirectionSavedFrame]
  have hsp_aligned := sp_sub_64_aligned halign
  rcases hcs with ⟨h25, h26, h27, h28, hvregs, hinv0⟩
  apply SepWPp.of_sepWP_cs_placed (mid := s0.readReg64 .lr); wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]); intro hinv1
  refine SepWPp.weaken_pre ?_
    (SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by epochEncLen_cc_close) (hinv0.trans hinv1).1))
  rw [stackAt_authEncode hres sp]
  refine sepConj_mono_left (sepConj_mono_right ?_)
  exact Entails.sepExists_right (s0.readReg64 .fp)
    (Entails.sepExists_right (s0.readReg64 .lr)
      (Entails.sepExists_right (s0.readReg64 .x24)
        (Entails.sepExists_right (s0.readReg64 .x23)
          (Entails.sepExists_right (s0.readReg64 .x22)
            (Entails.sepExists_right (s0.readReg64 .x21)
              (Entails.sepExists_right (s0.readReg64 .x20)
                (Entails.sepExists_right (s0.readReg64 .x19) (Entails.refl _))))))))


theorem subroutine_ok_withAuthEncodeCSPlaced_placed_blk [LibsignalPlacement] {α : Type}
    {callerProg calleeProg : Program} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α} (s0 : State) (hcl0 : LibsignalCodeLoaded lsmpl s0.mem)
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hi : i < 619 := by decide) (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok callerProg entry (withAuthEncodeCSPlaced s0 spec) := by
  refine subroutine_ok_mono
    (ls_subroutine_ok_cl_of_block (callerProg := callerProg) hcallee hi hj hj_unmut)
    (fun _ s _ hpre => ?_) (fun _ _ _ _ hpost => ?_)
  · dsimp only [withAuthEncodeCSPlaced, withLsCl] at hpre ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    exact ⟨hcl0.of_keepsFrozen hpre.1.2.2.2.2.2.2, hpre.2⟩
  · dsimp only [withAuthEncodeCSPlaced, withLsCl] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost; exact hpost.2


theorem step_ed_memcpy_call_placed {prog : Program}
    {call_pc : BitVec 64}
    (hmemcpy : subroutine_ok prog call_pc sessionMemcpyRegionSpec)
    (dst src sp ret_pc : BitVec 64) (bs : List (BitVec 8))
    {s0 s : State} {R : SepProp}
    {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = dst) (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = bs.length) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (memRegion dst bs.length ∗ (src ↦ₛ bs)) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs_placed (x := (dst, src, bs)) (F := F)
    hmemcpy hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [sessionMemcpyRegionSpec, memcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by convert hm using 1; ac_rfl⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    simp only [sessionMemcpyRegionSpec, sepConj_assoc, satisfies_pure_sepConj] at hm
    exact hm.1.elim
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; simp only [sessionMemcpyRegionSpec, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htrm⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))

theorem step_ed_encode_varint_call_placed {resStack : Nat} {prog : Program} (A : RustAlloc)
    {call_pc : BitVec 64} {s0 s : State}
    (henc : subroutine_ok prog call_pc (withAuthEncodeCSPlaced s0 (encodeVarintFitSpecOf resStack A)))
    (val v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8))
    (hlen_lt : curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat ∨
      curBs.length + 10 < 2 ^ 62)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = val) (hx1 : s.readReg64 .x1 = v)
    (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (nextCap nextPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSavedPlaced s0 sm → curCap.toNat ≤ nextCap.toNat →
      (curBs.length + (CryptoVerification.LibsignalProtoCodec.encodeVarint val).length ≤ curCap.toNat →
        nextCap = curCap ∧ nextPtr = curPtr) →
      SepWPp prog ret sm
        ((vecU8At A v nextCap nextPtr (curBs ++ CryptoVerification.LibsignalProtoCodec.encodeVarint val) ∗ A.pool ∗
          stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs_placed (x := EncodeVarintGhost.mk val v curCap curPtr curBs) (F := F)
    henc hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm; rw [hP] at hm
    simp only [withAuthEncodeCSPlaced, encodeVarintFitSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcs, ⟨hx0, hx1, hlen_lt⟩, by convert hm using 1; ac_rfl⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withAuthEncodeCSPlaced, encodeVarintFitSpecOf, encodeVarintSpec, encodeVarintSpecOf,
      msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm
    dsimp only [withAuthEncodeCSPlaced, encodeVarintFitSpecOf, encodeVarintSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun nextCap => SepWPp.exists_elim fun nextPtr => ?_
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hge, hpres⟩ => ?_
    refine SepWPp.weaken_pre (Entails.of_eq (by ac_rfl))
      (hnext sm nextCap nextPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)) hge hpres)

theorem step_ed_do_reserve2_call_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withAuthEncodeCSPlaced s0 (doReserve2SpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs_placed (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)] at hm
    simp only [withAuthEncodeCSPlaced, doReserve2SpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcs, ⟨hx0, hx1, hx2, hbound⟩, by convert hm using 1; ac_rfl⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withAuthEncodeCSPlaced, doReserve2SpecOf, doReserveSpec, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; dsimp only [withAuthEncodeCSPlaced, doReserve2SpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)

theorem step_ed_do_reserve7_call_placed {resStack : Nat} (hres : resStack + 48 + 64 < 2 ^ 64)
    {prog : Program} (A : RustAlloc) {call_pc : BitVec 64} {s0 s : State}
    (hdoReserve : subroutine_ok prog call_pc (withAuthEncodeCSPlaced s0 (doReserveSpecOf resStack A)))
    (v curCap curPtr sp ret_pc : BitVec 64) (curBs : List (BitVec 8)) (additional : Nat)
    (hbound : reserveCap curCap.toNat curBs.length additional + 1 ≤ 2 ^ 63)
    {R : SepProp} {ret : BitVec 64} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = call_pc) (hrun : s.status = .Running) (hsp : s.sp = sp - 64#64)
    (halign : sp &&& 15#64 = 0#64) (htr : s.trace = s0.trace) (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = v) (hx1 : (s.readReg64 .x1).toNat = curBs.length)
    (hx2 : (s.readReg64 .x2).toNat = additional) (hx3 : s.readReg64 .x3 = 1#64)
    (hx4 : s.readReg64 .x4 = 1#64) (hcs : AuthEncodeCalleeSavedPlaced s0 s)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
    (hnext : ∀ (sm : State) (newPtr : BitVec 64),
      sm.pc = ret_pc → sm.status = .Running → sm.sp = sp - 64#64 → sm.trace = s0.trace →
      CalleeSavedPreserved s sm → AuthEncodeCalleeSavedPlaced s0 sm →
      SepWPp prog ret sm
        ((vecU8At A v (BitVec.ofNat 64 (reserveCap curCap.toNat curBs.length additional)) newPtr curBs ∗
          A.pool ∗ stackAt (sp - 64#64) (0x30 + resStack)) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R))) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ msgEncOnPanic s0 sf ∗ R)) := by
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]; exact sp_sub_64_aligned halign
  refine SepWPp.call_cs_placed (x := DoReserveCall.mk v curCap curPtr curBs additional)
    (F := memRegion (sp - 64#64 - BitVec.ofNat 64 (0x30 + resStack)) 48 ∗ F)
    hdoReserve hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)] at hm
    simp only [withAuthEncodeCSPlaced, doReserveSpecOf, hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hcs, ⟨hx0, hx1, hx2, hx3, hx4, hbound⟩, by convert hm using 1; ac_rfl⟩
  · intro sf code R' _ hm; exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [withAuthEncodeCSPlaced, doReserveSpecOf, doReserveSpec, msgEncOnPanic, allocFailedIn] at hm ⊢
    rw [htr] at hm; exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcsm hinv_call
    rw [hsp] at hspm; dsimp only [withAuthEncodeCSPlaced, doReserveSpecOf]
    rw [hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepExists_sepConj_left]
    refine SepWPp.exists_elim fun newPtr => ?_
    refine SepWPp.weaken_pre ?_
      (hnext sm newPtr hpcm hrunm hspm (htrm.trans htr) hcsm
        (hcs.trans (AuthEncodeCalleeSavedPlaced.of_calleeSavedPreserved hcsm hinv_call)))
    rw [stackAt_encodeVarint_eq_doReserve64 hres (sp - 64#64)]
    exact Entails.of_eq (by ac_rfl)


end CryptoVerification.SpqrV1.Prost.MessageEncode
