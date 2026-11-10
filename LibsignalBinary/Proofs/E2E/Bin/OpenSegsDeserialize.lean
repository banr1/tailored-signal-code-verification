/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.Common.HookTrace
import LibsignalBinary.Proofs.E2E.Bin.SegCommon
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsKeysAddressesWp -- shake: keep

@[expose] public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.HookTrace

variable {C : Crypto} {A : RustAlloc} {S : SpqrModel} {img : Obj.Image} {ctl : BitVec 64}
  {abs : String → Option (State → State)}

/-! ## `SegExit` and `OpenSeam` Combinators -/

theorem openSpec_panic_of_allocFailed (A : RustAlloc) (img : Obj.Image)
    (g : OpenGhost) (R : SepProp) {s0 s1 sf : State}
    (htr : s1.trace = s0.trace) (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ anyHeap ∗ R) (halloc : allocFailedIn s1 sf ∧ s1.trace <+: sf.trace) :
    SubroutineOutcome (openSpec A img) g R s0 sf := by
  refine Or.inr (Or.inl ⟨hpan, ?_⟩)
  dsimp only [openSpec, Spec.inImage]
  have ⟨ha0, hpref⟩ := allocFailedIn_of_trace_eq htr halloc
  have h1 : (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R =
    ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ (anyHeap ∗ R) := by ac_rfl
  rw [h1, satisfies_pure_sepConj]
  exact ⟨⟨ha0, hpref⟩, hm⟩

theorem openSpec_panic_of_callee_onPanic (A : RustAlloc) (img : Obj.Image)
    (g : OpenGhost) (R R_extra : SepProp) {s0 s1 sf : State}
    (htr : s1.trace = s0.trace) (hpan : sf.status = .Panicked)
    (hm : sf.mem ⊨ (⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ anyHeap) ∗ (R_extra ∗ R)) :
    SubroutineOutcome (openSpec A img) g R s0 sf := by
  have hm' : sf.mem ⊨ ⌜allocFailedIn s1 sf ∧ s1.trace <+: sf.trace⌝ ∗ ((anyHeap ∗ R_extra) ∗ R) :=
    Satisfies.of_eq hm (by ac_rfl)
  rw [satisfies_pure_sepConj] at hm'
  exact openSpec_panic_of_allocFailed A img g R htr hpan
    (Satisfies.mono (sepConj_mono_left (anyHeap_absorb_right R_extra)) hm'.2) hm'.1

theorem sepWP_bind_segExit_open (C : Crypto) (A : RustAlloc)
    (ctl : BitVec 64) (img : Obj.Image)
    (abs : String → Option (State → State))
    (g : OpenGhost) (R : SepProp) {s0 s : State} {next : State → Prop}
    {target_pc : BitVec 64} {P F : SepProp} {post : State → SepProp → Prop}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hpre : s.mem ⊨ P ∗ F)
    (hwp : SepWP (tripleRatchetProgAt img.base C ctl abs) target_pc s P post)
    (hnext : ∀ s1 P_f, Steps (tripleRatchetProgAt img.base C ctl abs) s s1 →
      s1.pc = target_pc → s1.status = .Running →
      s1.mem ⊨ P_f ∗ F → post s1 P_f →
      SegExit (binProg img C ctl abs) (openSpec A img) g R s0 s1 next) :
    SegExit (binProg img C ctl abs) (openSpec A img) g R s0 s next := by
  refine segExit_trans
    (mid := fun s1 => ∃ P_f, Steps (tripleRatchetProgAt img.base C ctl abs) s s1 ∧
      s1.pc = target_pc ∧ s1.status = .Running ∧
      s1.mem ⊨ P_f ∗ F ∧ post s1 P_f)
    ?_ ?_
  · exact sepWP_to_segExit_tripleRatchetProgAt hloads hpre hwp
      (fun s1 P_f hst1 hpc1 hrun1 hm1 hp1 => Or.inl ⟨P_f, hst1, hpc1, hrun1, hm1, hp1⟩)
  · intro s1 ⟨P_f, hst1, hpc1, hrun1, hm1, hp1⟩
    exact hnext s1 P_f hst1 hpc1 hrun1 hm1 hp1

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP
  ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32
  ProofLib.reduceStateReadReg

theorem memRegion_bottom_open_split (sp0 sp1 : BitVec 64) (k : Nat)
    (hsp : sp1 = sp0 - 0x3f0#64) (hk : k + (openStack - 0x3f0 - k) = openStack - 0x3f0)
    (hle : k + (openStack - 0x3f0 - k) ≤ 2 ^ 64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - k) ∗
      stackAt sp1 k := by
  subst hsp
  have h1 := stackAt_split_bottom_open (sp0 - 0x3f0#64) k (openStack - 0x3f0 - k) hle
  rw [hk] at h1
  have h2 : sp0 - 0x3f0#64 - BitVec.ofNat 64 (openStack - 0x3f0) = sp0 - openStack := by
    change sp0 - 0x3f0#64 - BitVec.ofNat 64 (openStack - 0x3f0) = sp0 - BitVec.ofNat 64 openStack
    simp only [openStack, recordDeserializeStack, Nat.reduceAdd, Nat.reduceSub]
    bv_lin
  dsimp only [stackAt] at h1
  rw [h2] at h1
  exact h1

/-! ## Segment 2: `open_seg_deserialize` (`+0x054..+0x080`) -/

theorem sessionRecordAt_eq_bytes368_sep_heap (A : RustAlloc) (r : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8))) :
    sessionRecordAt A r ⟨0#64, 8#64, some G⟩ ⟨some sess⟩ =
      ∃∗ bs : List (BitVec 8),
        ⌜bs.length = 344 ∧ RawByteMove.SessionInline G sess.state bs⌝ ∗
        (r ↦ₛ (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs)) ∗
        sessionRecordHeap A G sess := by
  rw [sessionRecordAt_eq_word0_sep_tail_sep_heap A r G sess]
  apply RawByteMove.sepExists_congr; intro bs
  have h0_8 : r + BitVec.ofNat 64 (unpack64 0#64).length = r + 8#64 := by
    rw [unpack64_length]
  rw [pointsTo64_eq_pointsToBytes r 0#64,
      List.append_assoc (unpack64 0#64), List.append_assoc (unpack64 0#64),
      pointsToBytes_append r (unpack64 0#64), h0_8]
  ac_rfl

theorem sessionRecordBytes368_length {bs : List (BitVec 8)} (h : bs.length = 344) :
    (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs).length = 0x170 := by
  simp [unpack64_length, h]

theorem sessionRecordAt_move_368 (A : RustAlloc) (src dst : BitVec 64)
    (G : SessionGhost) (sess : Session (List (BitVec 8)))
    {bs : List (BitVec 8)} (hlen : bs.length = 344) (hinl : RawByteMove.SessionInline G sess.state bs) :
    ((dst ↦ₛ (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs)) ∗
     (src ↦ₛ (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs)) ∗
     sessionRecordHeap A G sess) ⊢
      sessionRecordAt A dst ⟨0#64, 8#64, some G⟩ ⟨some sess⟩ ∗ memRegion src 0x170 := by
  have hpull :
      ((dst ↦ₛ (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs)) ∗
       (src ↦ₛ (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs)) ∗
       sessionRecordHeap A G sess) =
      (((dst ↦ₛ (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs)) ∗
        sessionRecordHeap A G sess) ∗
       (src ↦ₛ (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs))) := by ac_rfl
  rw [hpull]
  refine sepConj_mono ?_ ?_
  · rw [sessionRecordAt_eq_bytes368_sep_heap A dst G sess]
    exact Entails.sepExists_right bs (Entails.pure_right ⟨hlen, hinl⟩ (Entails.refl _))
  · have hreg := ProofLib.pointsToBytes_entails_memRegion src
      (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs)
    rwa [sessionRecordBytes368_length hlen] at hreg

def openMemcpySpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ₛ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ₛ bs)

theorem openMemcpy_hookOk : HookOk hookMemcpy openMemcpySpec := by
  refine HookOk.of_trace hookMemcpy_region_ok fun _ _ _ ht hpost => ?_
  simp only [memcpyRegionSpec, openMemcpySpec, sepConj_assoc, satisfies_pure_sepConj] at hpost ⊢
  exact ⟨⟨hpost.1, ht, rfl⟩, hpost.2⟩

theorem memRegion_open_0x080_join (sp : BitVec 64) :
    memRegion (sp + 0x170#64) 0x170 ∗ memRegion (sp + 0x2e0#64) 0xb0 =
      memRegion (sp + 0x170#64) 0x220 := by
  symm
  exact memRegion_split' (b := sp + 0x170#64) (b' := sp + 0x2e0#64)
    (N := 0x220) (n := 0x170) (k := 0xb0) (by decide) (by bv_lin) (by decide)

theorem memRegion_open_0x054_split (sp : BitVec 64) :
    memRegion sp 0x390 =
      memRegion sp 0x170 ∗ memRegion (sp + 0x170#64) 0x170 ∗ memRegion (sp + 0x2e0#64) 0xb0 := by
  rw [memRegion_split' (b := sp) (b' := sp + 0x170#64)
        (N := 0x390) (n := 0x170) (k := 0x220) (by decide) (by bv_lin) (by decide),
      ← memRegion_open_0x080_join sp]

theorem memRegion_bottom_open_deserialize (sp0 sp1 : BitVec 64)
    (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - recordDeserializeStack) ∗
      stackAt sp1 recordDeserializeStack :=
  memRegion_bottom_open_split sp0 sp1 recordDeserializeStack hsp (by decide) (by decide)

theorem memRegion_bottom_open_identityKeyDecode (sp0 sp1 : BitVec 64)
    (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - 0x60) ∗
      stackAt sp1 0x60 :=
  memRegion_bottom_open_split sp0 sp1 0x60 hsp (by decide) (by decide)

theorem memRegion_bottom_open_extHook (sp0 sp1 : BitVec 64)
    (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - extHookStack) ∗
      stackAt sp1 extHookStack :=
  memRegion_bottom_open_split sp0 sp1 extHookStack hsp (by decide) (by decide)

theorem memRegion_bottom_open_sessionStoreNew (sp0 sp1 : BitVec 64)
    (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - (0x20 + extHookStack)) ∗
      stackAt sp1 (0x20 + extHookStack) :=
  memRegion_bottom_open_split sp0 sp1 (0x20 + extHookStack) hsp (by decide) (by decide)

theorem memRegion_bottom_open_identityStoreNew (sp0 sp1 : BitVec 64)
    (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - (0x30 + extHookStack)) ∗
      stackAt sp1 (0x30 + extHookStack) :=
  memRegion_bottom_open_split sp0 sp1 (0x30 + extHookStack) hsp (by decide) (by decide)

theorem memRegion_bottom_open_poll800 (sp0 sp1 : BitVec 64)
    (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - (0x800 + extHookStack)) ∗
      stackAt sp1 (0x800 + extHookStack) :=
  memRegion_bottom_open_split sp0 sp1 (0x800 + extHookStack) hsp (by decide) (by decide)

theorem memRegion_bottom_open_pollC00 (sp0 sp1 : BitVec 64)
    (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - (0xc00 + extHookStack)) ∗
      stackAt sp1 (0xc00 + extHookStack) :=
  memRegion_bottom_open_split sp0 sp1 (0xc00 + extHookStack) hsp (by decide) (by decide)


theorem pointsTo64_append_sessionTail (r : BitVec 64) (bs : List (BitVec 8)) :
    (r ↦₆₄ 0#64) ∗ ((r + 8#64) ↦ₛ (unpack64 8#64 ++ unpack64 0#64 ++ bs)) =
      (r ↦ₛ (unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++ bs)) := by
  have h0_8 : r + BitVec.ofNat 64 (unpack64 0#64).length = r + 8#64 := by
    rw [unpack64_length]
  rw [pointsTo64_eq_pointsToBytes r 0#64,
      List.append_assoc (unpack64 0#64), List.append_assoc (unpack64 0#64),
      pointsToBytes_append r (unpack64 0#64), h0_8]

theorem recordDeserialize_fnAddr_eq (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr recordDeserializeName = b + deserializeOff := by
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, deserialize_fnOff]

theorem memRegion_bottom_open_split_0x60 (sp0 sp1 : BitVec 64)
    (hsp : sp1 = sp0 - 0x3f0#64) :
    memRegion (sp0 - openStack) (openStack - 0x3f0) =
      memRegion (sp0 - openStack) (openStack - 0x3f0 - 0x60) ∗
      stackAt sp1 0x60 :=
  memRegion_bottom_open_split sp0 sp1 0x60 hsp (by decide) (by decide)

end CryptoVerification.E2E.Bin
