/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
import LibsignalBinary.Proofs.Common.CallInv
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.ChainMergeAux.Pure
import ProofLib.SepLogic.WPp

/-!
# Frame, Layout, and Callee Helpers for Seed `message::merge<Chain>`

Defines the 256-byte stack frame (`chainMergeSavedRegs`), cursor and `prostChainAt` decomposition
lemmas, and `SepWPp` callee wrappers for `bytes::merge` and `int32::merge` inside
`prost::encoding::message::merge::<Chain>` (`0x3974`, block `11`).
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Stack Frame and Saved Registers -/

abbrev chainMergeSubStack : Nat := 12032

/-- Local frame `[sp0 - 256#64 .. sp0 - 96#64)` and the 12 saved register words at
`[sp0 - 96#64 .. sp0)` written by the prologue (`+0x000..+0x018`). -/
def chainMergeSavedRegs (sp0 : BitVec 64) (s0 : State) : SepProp :=
  memRegion (sp0 - 256#64) 160 ∗
  ((sp0 - 96#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 88#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x28) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x27) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x26) ∗
  ((sp0 - 56#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

theorem stackAt_sub_split_seedChain (sp : BitVec 64) (M N : Nat)
    (hMN : (N - M) + M = N := by decide)
    (hle : N ≤ 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) (N - M) ∗ stackAt sp M := by
  unfold stackAt
  refine memRegion_split' (n := N - M) (k := M) hMN.symm ?_ hle
  have hN : BitVec.ofNat 64 N = BitVec.ofNat 64 (N - M) + BitVec.ofNat 64 M := by
    rw [← BitVec.ofNat_add, hMN]
  rw [hN, BitVec.add_comm (BitVec.ofNat 64 (N - M)), ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem stackAt_chainMergeStack_split_seedChain (sp0 : BitVec 64) :
    stackAt sp0 chainMergeStack =
      stackAt (sp0 - 256#64) chainMergeSubStack ∗
        memRegion (sp0 - 256#64) 160 ∗
        (∃∗ w96 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64,
         ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64,
         ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
  have heq : chainMergeStack = 12192 + 8 * 12 := by decide
  have hsub : stackAt (sp0 - 96#64) 12192 =
      stackAt (sp0 - 256#64) chainMergeSubStack ∗ memRegion (sp0 - 256#64) 160 := by
    change memRegion (sp0 - 96#64 - 12192#64) 12192 =
      memRegion (sp0 - 256#64 - 12032#64) 12032 ∗ memRegion (sp0 - 256#64) 160
    have h1 : sp0 - 96#64 - 12192#64 = sp0 - 256#64 - 12032#64 := by bv_omega
    have h2 : (sp0 - 256#64 - 12032#64) + 12032#64 = sp0 - 256#64 := by bv_omega
    have hsplit := memRegion_split (sp0 - 256#64 - 12032#64) 12032 160 (by decide)
    rw [show (12032 : Nat) + 160 = 12192 by decide,
        show BitVec.ofNat 64 12032 = 12032#64 from rfl, h2] at hsplit
    rw [h1, hsplit]
  have h12 : stackAt sp0 chainMergeStack =
      stackAt (sp0 - 96#64) 12192 ∗
        (∃∗ w96 : BitVec 64, ∃∗ w88 : BitVec 64, ∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64,
         ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64, ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64,
         ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
    rw [heq, LibsignalTripleRatchet.stackAt_split_cells sp0 12192 12 (by decide)]
    have h96 : sp0 - BitVec.ofNat 64 (8 * 12) = sp0 - 96#64 := rfl
    rw [h96]
    congr 1
    simp (disch := decide) only [cells, sepConj_emp, bv_sub_add_lit,
      sepExists_sepConj_right]
  rw [h12, hsub, sepConj_assoc]

theorem stackAt_sub_to_bytesMerge_seedChain (sp : BitVec 64) :
    stackAt sp chainMergeSubStack =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStack) (chainMergeSubStack - bytesMergeStack) ∗
        stackAt sp bytesMergeStack :=
  stackAt_sub_split_seedChain sp bytesMergeStack chainMergeSubStack

theorem stackAt_sub_to_int32Merge_seedChain (sp : BitVec 64) :
    stackAt sp chainMergeSubStack =
      memRegion (sp - BitVec.ofNat 64 chainMergeSubStack) (chainMergeSubStack - int32MergeStack) ∗
        stackAt sp int32MergeStack :=
  stackAt_sub_split_seedChain sp int32MergeStack chainMergeSubStack

theorem sp_sub_256_aligned_seedChain {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 256#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

/-! ## Cursor and `prostChainAt` Layout Helpers -/

theorem sliceCursorAfter_append_eq_seedChain (slot ptr : BitVec 64) (pfx rest : List (BitVec 8)) :
    sliceCursorAfter slot ptr (pfx ++ rest) rest =
      (ptr ↦ₛ pfx) ∗ sliceCursorAt slot (ptr + BitVec.ofNat 64 pfx.length) rest := by
  unfold sliceCursorAfter sliceCursorAt
  rw [List.length_append, Nat.add_sub_cancel_right, pointsToBytes_append]
  ac_rfl

theorem prostChainAt_ck_none_eq_seedChain (a : BitVec 64) (srk priv : List (BitVec 8)) :
    prostChainAt A0 a ⟨srk, priv, none⟩ =
      vecU8 A0 a srk ∗ vecU8 A0 (a + 0x18#64) priv ∗
      vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
      ((a + 0x48#64) ↦₆₄ noneCap) ∗ memRegion (a + 0x50#64) 24 := by
  unfold prostChainAt
  dsimp only

theorem prostChainAt_ck_some_eq_seedChain (a : BitVec 64) (srk priv : List (BitVec 8))
    (i : BitVec 32) (k : List (BitVec 8)) :
    prostChainAt A0 a ⟨srk, priv, some (i, k)⟩ =
      vecU8 A0 a srk ∗ vecU8 A0 (a + 0x18#64) priv ∗
      vecOf A0 104 8 (fun (_ : Unit) _ => emp) (a + 0x30#64) [] ∗
      vecU8 A0 (a + 0x48#64) k ∗ ((a + 0x60#64) ↦₃₂ i) ∗ memRegion (a + 0x64#64) 4 := by
  unfold prostChainAt
  dsimp only

theorem memRegion24_split_ck_seedChain (a : BitVec 64) :
    memRegion (a + 0x50#64) 24 =
      (∃∗ w1 : BitVec 64, (a + 0x50#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 0x58#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 32, (a + 0x60#64) ↦₃₂ w3) ∗
      memRegion (a + 0x64#64) 4 := by
  have h1 := memRegion_split (a + 0x50#64) 8 16 (by decide)
  have h2 := memRegion_split (a + 0x58#64) 8 8 (by decide)
  have h3 := memRegion_split (a + 0x60#64) 4 4 (by decide)
  have ha1 : (a + 0x50#64) + BitVec.ofNat 64 8 = a + 0x58#64 := by bv_omega
  have ha2 : (a + 0x58#64) + BitVec.ofNat 64 8 = a + 0x60#64 := by bv_omega
  have ha3 : (a + 0x60#64) + BitVec.ofNat 64 4 = a + 0x64#64 := by bv_omega
  rw [show (8 : Nat) + 16 = 24 by decide,
      show BitVec.ofNat 64 8 = 8#64 from rfl, ha1] at h1
  rw [show (8 : Nat) + 8 = 16 by decide,
      show BitVec.ofNat 64 8 = 8#64 from rfl, ha2] at h2
  rw [show (4 : Nat) + 4 = 8 by decide,
      show BitVec.ofNat 64 4 = 4#64 from rfl, ha3] at h3
  rw [h1, h2, h3, ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_four]

private theorem pure_true_emp_seedChain {φ : Prop} (h : φ) : (⌜φ⌝ : SepProp) = emp := by
  simp [h]

theorem emptyVec_eq_vecU8At_seedChain (addr : BitVec 64) :
    (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 1#64) ∗ ((addr + 16#64) ↦₆₄ 0#64) =
      vecU8At A0 addr 0#64 1#64 [] := by
  unfold vecU8At vecHeader
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  simp only [pure_true_emp_seedChain hp, emp_sepConj]
  ac_rfl

theorem emptyVec_entails_vecU8_seedChain (addr : BitVec 64) :
    (addr ↦₆₄ 0#64) ∗ ((addr + 8#64) ↦₆₄ 1#64) ∗ ((addr + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A0 addr [] := by
  rw [emptyVec_eq_vecU8At_seedChain]
  unfold vecU8
  exact Entails.sepExists_right 0#64 (Entails.sepExists_right 1#64 (Entails.refl _))

/-! ## `SepWPp` Callee Wrappers -/

theorem SepWPp.mono_pre_seedChain {prog : Program} {ret : BitVec 64} {s : State}
    {P P' : SepProp} {Q Qp : State → SepProp → Prop}
    (hent : P ⊢ P') (h : SepWPp prog ret s P' Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  exact h R (Satisfies.mono (sepConj_mono_left hent) hm) hL

theorem SepWPp.of_sepWP_frozen_seedChain {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_frozen hF hsym h

theorem SepWPp.call_frozen_seedChain {α : Type} {prog : Program} {img : Obj.Image}
    {ret entry ret_pc : BitVec 64} {s : State} {P F : SepProp}
    {Q Qp : State → SepProp → Prop} {spec : Spec α} (x : α)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hpre : ∀ R : SepProp, (s.mem ⊨ P ∗ R) → (s.mem ⊨ spec.pre x s ∗ (F ∗ R)))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → img.FrozenLoaded sf → sf.symtab = img.symtab →
      CalleeSavedPreserved s sf →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q Qp := by
  refine ProofLib.SepWPp.call_wpp_frozen (x := x) (F := F) hcall hF hsym hpc hrun hsp hlr hpre hexit
    (fun sf hpan _ => hpanic sf hpan)
    (fun sf hpcm hrunm hspm hcsm hFm hsymm => hnext sf hpcm hrunm hspm hFm hsymm hcsm)
    (fun sf R' _ hoom_post => by
      rw [hoom sf] at hoom_post
      exact (not_satisfies_false_sepConj hoom_post).elim)

/-- Steps a `bl bytes::merge` call inside `message::merge<Chain>` on a `< 128`-byte length-delimited
field `[BitVec.ofNat 8 b.length] ++ b`. -/
theorem step_chainMerge_bytesMerge_seedChain (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hBM : BytesMergeOk sessionImg0 C A0 ctl abs)
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (bs0 b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 32)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName +
      bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s)
    (hsym : s.symtab = sessionImg0.symtab)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = (vecU8 A0 v bs0 ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
      stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        ((vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R)) := by
  have hcall := bytesMerge_ok_sub_seedChain hBM
  rw [hP]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun cap0 => SepWPp.exists_elim fun ptr0 => ?_
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_frozen_seedChain
    (x := BytesMergeGhost.mk .lengthDelimited v cap0 ptr0 bs0 bufRef slot curPtr
      ([BitVec.ofNat 8 b.length] ++ b ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
      (chainMergeSubStack - bytesMergeStack) ∗ F)
    hcall hpc hrun hsp_aligned hF hsym hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_sub_to_bytesMerge_seedChain (sp0 - 256#64)] at hm
    dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hF, hsym⟩, ⟨hx0, hx1, hx2, Nat.lt_of_lt_of_le hlen_lt (by decide),
      bytesMergeCapOk_of_len_lt32 hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec, chainMergeSeedSpec,
      Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hFm hsymm hcsm
    rw [hsp] at hspm
    have hmB := mergeBytes_lt128_seedChain b rest hb
    dsimp only [bytesMergeSpec, Spec.inImage, bytesMergeRawSpec]
    rw [hmB, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun _hcapOk => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    have hlen1 : ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 := by simp
    rw [hlen1] at hcur
    have hv : vecU8At A0 v cap' ptr' b ⊢ vecU8 A0 v b :=
      Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.mono_pre_seedChain ?_ (hnext sm hpcm hrunm hspm hFm hsymm (htrm.trans htr) hcsm hx0m)
    rw [hcur, stackAt_sub_to_bytesMerge_seedChain (sp0 - 256#64)]
    have hEq1 :
        (bufRef ↦₆₄ slot) ∗ emp ∗ stackAt (sp0 - 256#64) bytesMergeStack ∗
          vecU8At A0 v cap' ptr' b ∗
          ((curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest) ∗
          memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
            (chainMergeSubStack - bytesMergeStack) ∗ F =
        vecU8At A0 v cap' ptr' b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
              (chainMergeSubStack - bytesMergeStack) ∗
              stackAt (sp0 - 256#64) bytesMergeStack) ∗ F) := by ac_rfl
    have hEq2 :
        vecU8 A0 v b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
              (chainMergeSubStack - bytesMergeStack) ∗
              stackAt (sp0 - 256#64) bytesMergeStack) ∗ F) =
        (vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
            (chainMergeSubStack - bytesMergeStack) ∗
            stackAt (sp0 - 256#64) bytesMergeStack)) ∗ F := by ac_rfl
    rw [hEq1, ← hEq2]
    exact sepConj_mono_left hv

/-- Steps a `bl int32::merge` call inside `message::merge<Chain>` on `pbVarintBody 5 i.toNat ++ rest`. -/
theorem step_chainMerge_int32Merge_seedChain (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hIM : Int32MergeOk sessionImg0.base C A0 ctl abs)
    (dst bufRef slot curPtr sp0 ret_pc : BitVec 64) (w0 : BitVec 32)
    (i : BitVec 32) (rest : List (BitVec 8))
    (hlen_lt : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 32)
    {x : ChainMergeGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr chainMergeName +
      bv% (2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") - (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hF : sessionImg0.FrozenLoaded s)
    (hsym : s.symtab = sessionImg0.symtab)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 0#8)
    (hx1 : s.readReg64 .x1 = dst)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = ((dst ↦₃₂ w0) ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr (pbVarintBody 5 i.toNat ++ rest) ∗
      stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      sessionImg0.FrozenLoaded sm →
      sm.symtab = sessionImg0.symtab →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret sm
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ chainMergeSeedSpec.onPanic x s0 sf ∗ R)) := by
  have hcall := int32Merge_ok_sub_seedChain hIM
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_frozen_seedChain
    (x := Int32MergeGhost.mk .varint dst bufRef slot curPtr (pbVarintBody 5 i.toNat ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
      (chainMergeSubStack - int32MergeStack) ∗ F)
    hcall hpc hrun hsp_aligned hF hsym hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_int32Merge_seedChain (sp0 - 256#64)] at hm
    simp only [sepConj_assoc] at hm
    have hcell : (dst ↦₃₂ w0) ⊢ memRegion dst 4 := by
      rw [ProofLib.memRegion_four]
      exact Entails.sepExists_right w0 (Entails.refl _)
    have hm1 := Satisfies.mono (sepConj_mono_left hcell) hm
    dsimp only [int32MergeSpec]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, Nat.lt_of_lt_of_le hlen_lt (by decide)⟩, ?_⟩
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [int32MergeSpec, chainMergeSeedSpec, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hFm hsymm hcsm
    rw [hsp] at hspm
    have hmI := mergeUint32_pbVarintBody_seedChain i rest
    dsimp only [int32MergeSpec]
    rw [hmI, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr (pbVarintBody 5 i.toNat) rest
    have hGoalEq :
        ((bufRef ↦₆₄ slot) ∗ emp ∗ stackAt (sp0 - 256#64) int32MergeStack ∗
          (dst ↦₃₂ i) ∗
          sliceCursorAfter slot curPtr (pbVarintBody 5 i.toNat ++ rest) rest ∗
          memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
            (chainMergeSubStack - int32MergeStack) ∗ F) =
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F) := by
      rw [hcur, stackAt_sub_to_int32Merge_seedChain (sp0 - 256#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm hFm hsymm (htrm.trans htr) hcsm hx0m

/-! ## Relocatable `[LibsignalPlacement]` Callee Wrappers -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem step_chainMerge_bytesMerge_placed_seedChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hBM : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (bytesMergeRawSpec A0)))
    (v bufRef slot curPtr sp0 ret_pc : BitVec 64) (bs0 b rest : List (BitVec 8))
    (hb : b.length < 128)
    (hlen_lt : ([BitVec.ofNat 8 b.length] ++ b ++ rest).length < 2 ^ 32)
    {α : Type} {x : α} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 7)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 2#8)
    (hx1 : s.readReg64 .x1 = v)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = (vecU8 A0 v bs0 ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr ([BitVec.ofNat 8 b.length] ++ b ++ rest) ∗
      stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_11 H) ret sm
        ((vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall := bytesMerge_placed_ok_sub_seedChain hBM
  rw [hP]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun cap0 => SepWPp.exists_elim fun ptr0 => ?_
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_lscro
    (x := BytesMergeGhost.mk .lengthDelimited v cap0 ptr0 bs0 bufRef slot curPtr
      ([BitVec.ofNat 8 b.length] ++ b ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
      (chainMergeSubStack - bytesMergeStack) ∗ F)
    hcall hpc hrun hsp_aligned hcrl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [stackAt_sub_to_bytesMerge_seedChain (sp0 - 256#64)] at hm
    dsimp only [bytesMergeRawSpec]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, Nat.lt_of_lt_of_le hlen_lt (by decide),
      bytesMergeCapOk_of_len_lt32 hlen_lt⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [bytesMergeRawSpec, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcrlm hcsm
    rw [hsp] at hspm
    have hmB := mergeBytes_lt128_seedChain b rest hb
    dsimp only [bytesMergeRawSpec]
    rw [hmB, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun cap' => SepWPp.exists_elim fun ptr' => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun _hcapOk => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr ([BitVec.ofNat 8 b.length] ++ b) rest
    have hlen1 : ([BitVec.ofNat 8 b.length] ++ b).length = b.length + 1 := by simp
    rw [hlen1] at hcur
    have hv : vecU8At A0 v cap' ptr' b ⊢ vecU8 A0 v b :=
      Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.mono_pre_seedChain ?_ (hnext sm hpcm hrunm hspm hcrlm (htrm.trans htr) hcsm hx0m)
    rw [hcur, stackAt_sub_to_bytesMerge_seedChain (sp0 - 256#64)]
    have hEq1 :
        (bufRef ↦₆₄ slot) ∗ emp ∗ stackAt (sp0 - 256#64) bytesMergeStack ∗
          vecU8At A0 v cap' ptr' b ∗
          ((curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest) ∗
          memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
            (chainMergeSubStack - bytesMergeStack) ∗ F =
        vecU8At A0 v cap' ptr' b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
              (chainMergeSubStack - bytesMergeStack) ∗
              stackAt (sp0 - 256#64) bytesMergeStack) ∗ F) := by ac_rfl
    have hEq2 :
        vecU8 A0 v b ∗
          ((bufRef ↦₆₄ slot) ∗
            (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
            sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
            (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
              (chainMergeSubStack - bytesMergeStack) ∗
              stackAt (sp0 - 256#64) bytesMergeStack) ∗ F) =
        (vecU8 A0 v b ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ ([BitVec.ofNat 8 b.length] ++ b)) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (b.length + 1)) rest ∗
          (memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
            (chainMergeSubStack - bytesMergeStack) ∗
            stackAt (sp0 - 256#64) bytesMergeStack)) ∗ F := by ac_rfl
    rw [hEq1, ← hEq2]
    exact sepConj_mono_left hv

theorem step_chainMerge_int32Merge_placed_seedChain [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hIM : subroutine_ok ((blkPC_8).rebase (blkPl_8).base H) (blkPl_8).base
      (withLsCodeLoaded lsmpl (int32MergeSpec A0)))
    (dst bufRef slot curPtr sp0 ret_pc : BitVec 64) (w0 : BitVec 32)
    (i : BitVec 32) (rest : List (BitVec 8))
    (hlen_lt : (pbVarintBody 5 i.toNat ++ rest).length < 2 ^ 32)
    {α : Type} {x : α} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 8)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 256#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s.trace = s0.trace)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : (s.readReg64 .x0).setWidth 8 = 0#8)
    (hx1 : s.readReg64 .x1 = dst)
    (hx2 : s.readReg64 .x2 = bufRef)
    (hP : P = ((dst ↦₃₂ w0) ∗ (bufRef ↦₆₄ slot) ∗
      sliceCursorAt slot curPtr (pbVarintBody 5 i.toNat ++ rest) ∗
      stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 256#64 →
      LibsignalCodeRoLoaded lsmpl sm.mem →
      sm.trace = s0.trace →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = 0#64 →
      SepWPp (lsProg_11 H) ret sm
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_11 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall := int32Merge_placed_ok_sub_seedChain hIM
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_256_aligned_seedChain halign
  refine SepWPp.call_lscro
    (x := Int32MergeGhost.mk .varint dst bufRef slot curPtr (pbVarintBody 5 i.toNat ++ rest))
    (F := memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
      (chainMergeSubStack - int32MergeStack) ∗ F)
    hcall hpc hrun hsp_aligned hcrl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_int32Merge_seedChain (sp0 - 256#64)] at hm
    simp only [sepConj_assoc] at hm
    have hcell : (dst ↦₃₂ w0) ⊢ memRegion dst 4 := by
      rw [ProofLib.memRegion_four]
      exact Entails.sepExists_right w0 (Entails.refl _)
    have hm1 := Satisfies.mono (sepConj_mono_left hcell) hm
    dsimp only [int32MergeSpec]
    have hpool : A0.pool = emp := rfl
    rw [hpool, hsp]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx1, hx2, Nat.lt_of_lt_of_le hlen_lt (by decide)⟩, ?_⟩
    convert hm1 using 1; ac_rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    dsimp only [int32MergeSpec, Serialization.allocPanic] at hm ⊢
    simp only [allocFailedIn, htr] at hm ⊢
    exact allowPanic_frame id hm
  · intro sm hpcm hrunm hspm hcrlm hcsm
    rw [hsp] at hspm
    have hmI := mergeUint32_pbVarintBody_seedChain i rest
    dsimp only [int32MergeSpec]
    rw [hmI, hsp]
    dsimp only
    have hpool : A0.pool = emp := rfl
    rw [hpool]
    simp only [sepConj_assoc]
    refine SepWPp.pure_elim fun htrm => ?_
    simp only [sepConj_pure_left_comm]
    refine SepWPp.pure_elim fun hx0m => ?_
    have hcur := sliceCursorAfter_append_eq_seedChain slot curPtr (pbVarintBody 5 i.toNat) rest
    have hGoalEq :
        ((bufRef ↦₆₄ slot) ∗ emp ∗ stackAt (sp0 - 256#64) int32MergeStack ∗
          (dst ↦₃₂ i) ∗
          sliceCursorAfter slot curPtr (pbVarintBody 5 i.toNat ++ rest) rest ∗
          memRegion (sp0 - 256#64 - BitVec.ofNat 64 chainMergeSubStack)
            (chainMergeSubStack - int32MergeStack) ∗ F) =
        (((dst ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
          (curPtr ↦ₛ pbVarintBody 5 i.toNat) ∗
          sliceCursorAt slot (curPtr + BitVec.ofNat 64 (pbVarintBody 5 i.toNat).length) rest ∗
          stackAt (sp0 - 256#64) chainMergeSubStack) ∗ F) := by
      rw [hcur, stackAt_sub_to_int32Merge_seedChain (sp0 - 256#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm hcrlm (htrm.trans htr) hcsm hx0m

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
