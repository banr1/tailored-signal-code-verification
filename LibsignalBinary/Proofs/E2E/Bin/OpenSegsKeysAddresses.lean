/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.Bin.OpenSegsPartyRoData
import LibsignalBinary.Proofs.E2E.Bin.SegCommon

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

variable {C : Crypto} {A : RustAlloc} {S : SpqrModel} {img : Obj.Image} {ctl : BitVec 64}
  {abs : String → Option (State → State)}

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## Segment 3: `open_seg_keys` (`+0x080..+0x130`) -/

theorem segExit_call_identityKeyDecode_ro
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (img : Obj.Image)
    (abs : String → Option (State → State))
    (hloads : Obj.Loads libsignalSessionImage img)
    (g : OpenGhost) (R : SepProp) (out keyPtr : BitVec 64) (r : Role) (Rc : SepProp)
    {s0 s1 : State} {next : State → Prop}
    (hpc1 : s1.pc = (tripleRatchetProgAt img.base C ctl abs).fnAddr identityKeyDecodeName)
    (hrun1 : s1.status = .Running)
    (hal1 : s1.spAligned = true)
    (hx8 : s1.readReg64 .x8 = out)
    (hx0 : s1.readReg64 .x0 = keyPtr)
    (hx1 : s1.readReg64 .x1 = 33#64)
    (hm1 : s1.mem ⊨ ((keyPtr ↦ᵣ r.idPubWire) ∗ memRegion out 40 ∗ stackAt s1.sp 0x60) ∗ Rc)
    (hpost : ∀ s2, Steps (binProg img C ctl abs) s1 s2 →
      Returned s1 s2 → CallingConventionPreserved s1 s2 →
      s2.trace = s1.trace → s2.tpidrEl0 = s1.tpidrEl0 →
      s2.mem ⊨ ((keyPtr ↦ᵣ r.idPubWire) ∗
        (out ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((out + 8#64) ↦ₛ r.idKey.publicKey.bytes.toList) ∗
        stackAt s1.sp 0x60) ∗ Rc →
      SegExit (binProg img C ctl abs) (openSpec A img) g R s0 s2 next) :
    SegExit (binProg img C ctl abs) (openSpec A img) g R s0 s1 next := by
  have hCallee : subroutine_ok (binProg img C ctl abs)
      ((tripleRatchetProgAt img.base C ctl abs).fnAddr identityKeyDecodeName)
      identityKeyDecodeRoSpec := by
    rw [binProg, tripleRatchetProg_eq_tripleRatchetProgAt hloads]
    exact identityKey_decode_ro_tripleRatchetProgAt_ok img.base C ctl abs
  have hpre : s1.mem ⊨ identityKeyDecodeRoSpec.pre (out, keyPtr, r) s1 ∗ Rc := by
    dsimp only [identityKeyDecodeRoSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx8, hx0, hx1⟩, ?_⟩
    ac_sat hm1
  refine segExit_trans
    (mid := fun s2 => Steps (binProg img C ctl abs) s1 s2 ∧
      Returned s1 s2 ∧ CallingConventionPreserved s1 s2 ∧
      s2.trace = s1.trace ∧ s2.tpidrEl0 = s1.tpidrEl0 ∧
      s2.mem ⊨ ((keyPtr ↦ᵣ r.idPubWire) ∗
        (out ↦₆₄ 0xfffffffffffffffe#64) ∗
        ((out + 8#64) ↦ₛ r.idKey.publicKey.bytes.toList) ∗
        stackAt s1.sp 0x60) ∗ Rc)
    ?_ ?_
  · refine segExit_of_subroutine_ok hCallee hpc1 hrun1 hal1 hpre ?_ ?_ ?_
    · intro s2 hst2 ⟨hret, hcc, hmpost⟩
      dsimp only [identityKeyDecodeRoSpec] at hmpost
      rw [sepConj_assoc, satisfies_pure_sepConj] at hmpost
      rcases hmpost with ⟨⟨htp2, htr2⟩, hmpost⟩
      refine Or.inl ⟨hst2, hret, hcc, htr2, htp2, ?_⟩
      ac_sat hmpost
    · intro s2 _ hmp
      dsimp only [identityKeyDecodeRoSpec] at hmp
      rw [satisfies_pure_sepConj] at hmp
      exact False.elim hmp.1
    · intro code s2 hme
      dsimp only [identityKeyDecodeRoSpec] at hme
      rw [satisfies_pure_sepConj] at hme
      exact False.elim hme.1
  · intro s2 ⟨hst2, hret, hcc, htr2, htp2, hm2⟩
    exact hpost s2 hst2 hret hcc htr2 htp2 hm2

/-! ## Segment 4: `open_seg_addresses` (`+0x130..+0x1c4`) -/

def openSeamSlots_0x1c4_body (A : RustAlloc)
    (g : OpenGhost) (role : Role) (s : State) : SepProp :=
  (∃∗ mePtr : BitVec 64, ∃∗ peerPtr : BitVec 64,
    ⌜s.readReg64 .x20 = 36#64 ∧
      s.readReg64 .x21 = mePtr ∧
      s.readReg64 .x22 = 36#64 ∧
      s.readReg64 .x23 = peerPtr ∧
      s.readReg64 .x26 = 1#64 ∧
      mePtr ≠ 0#64 ∧
      peerPtr ≠ 0#64⌝ ∗
      (mePtr ↦ₛ role.nameBytes) ∗ A.live mePtr 36 1 ∗
      (peerPtr ↦ₛ role.peer.nameBytes) ∗ A.live peerPtr 36 1) ∗
    (∃∗ G, ⌜BinCanonSession G g.sess⌝ ∗ sessionRecordAt A s.sp ⟨0#64, 8#64, some G⟩ ⟨some g.sess⟩) ∗
    memRegion (s.sp + 0x170#64) 0x170 ∗
    ((s.sp + 0x2e0#64) ↦ₛ role.keyPairBytes) ∗
    ((s.sp + 0x320#64) ↦ₛ role.peer.idKey.publicKey.bytes.toList) ∗
    memRegion (s.sp + 0x340#64) 0x50

theorem openSeamSlots_0x1c4_of_regs (A : RustAlloc) (g : OpenGhost)
    (role : Role) (s : State) (mePtr peerPtr : BitVec 64)
    (hx20 : s.readReg64 .x20 = 36#64)
    (hx21 : s.readReg64 .x21 = mePtr)
    (hx22 : s.readReg64 .x22 = 36#64)
    (hx23 : s.readReg64 .x23 = peerPtr)
    (hx26 : s.readReg64 .x26 = 1#64)
    (hme : mePtr ≠ 0#64)
    (hpeer : peerPtr ≠ 0#64) :
    (((mePtr ↦ₛ role.nameBytes) ∗ A.live mePtr 36 1 ∗
      (peerPtr ↦ₛ role.peer.nameBytes) ∗ A.live peerPtr 36 1) ∗
     (∃∗ G, ⌜BinCanonSession G g.sess⌝ ∗ sessionRecordAt A s.sp ⟨0#64, 8#64, some G⟩ ⟨some g.sess⟩) ∗
     memRegion (s.sp + 0x170#64) 0x170 ∗
     ((s.sp + 0x2e0#64) ↦ₛ role.keyPairBytes) ∗
     ((s.sp + 0x320#64) ↦ₛ role.peer.idKey.publicKey.bytes.toList) ∗
     memRegion (s.sp + 0x340#64) 0x50) ⊢
      openSeamSlots_0x1c4_body A g role s := by
  unfold openSeamSlots_0x1c4_body
  refine sepConj_mono_left ?_
  refine Entails.sepExists_right mePtr (Entails.sepExists_right peerPtr ?_)
  exact Entails.pure_right ⟨hx20, hx21, hx22, hx23, hx26, hme, hpeer⟩ (Entails.refl _)

def openShimSpec : Spec Unit where
  pre := fun _ _ => emp
  post := fun _ s0 sf => ⌜sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝

theorem openShim_hookOk : HookOk hookNoop openShimSpec := by
  refine hookNoop_ok fun _ R s0 hpre => ?_
  dsimp only [openShimSpec, hookNoop, retHook, id_eq] at hpre ⊢
  rw [emp_sepConj] at hpre
  rw [satisfies_pure_sepConj]
  exact ⟨⟨State.trace_setPC _ _, tpidrEl0_setPC_pre_open _ _⟩, hpre⟩

theorem role_nameBytes_length (r : Role) : r.nameBytes.length = 36 := by
  cases r <;> decide +kernel

theorem allocFailedIn_panicked {s0 s1 sf : State}
    (htr1 : s1.trace = s0.trace)
    (htr : sf.trace = s1.trace ++ [allocFailedEvent]) :
    allocFailedIn s0 (Rust.panicked sf) ∧ s0.trace <+: (Rust.panicked sf).trace := by
  have htr' : sf.trace = s0.trace ++ [allocFailedEvent] := by rw [htr, htr1]
  have hpan_tr : (Rust.panicked sf).trace = sf.trace := rfl
  refine ⟨?_, ?_⟩
  · unfold allocFailedIn
    rw [hpan_tr, htr', List.drop_left]
    exact List.Mem.head []
  · rw [hpan_tr, htr']
    exact List.prefix_append s0.trace [allocFailedEvent]

theorem layoutOk_36_1 : LayoutOk 36 1 := by
  refine ⟨by decide, ⟨0, rfl⟩, by decide⟩

end CryptoVerification.E2E.Bin
