/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.FinishGrow
public import LibsignalBinary.Proofs.SpqrV1.Chain.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.FnOffEq
import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
import LibsignalBinary.Proofs.SpqrV1.Alloc.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]`

Verifies 2-slice and 3-slice byte concatenation (`sliceConcat2Spec*`, `sliceConcat3Spec*`) on
`tripleRatchetProgAtExt` under `AllocContracts` (`allocHookStack = 4096`) and `AllocContractsX`
(`extHookStack = 16384`), as well as relocatable `[LibsignalPlacement]` contracts for block 386.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SpqrV1.Alloc

open Arm64 ProofLib ProofLib.ProgramReflection CryptoVerification.RustHeap
  CryptoGames.LibsignalSession CryptoVerification.LibsignalSessionRepr
  CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalSession
  CryptoVerification.LibsignalTripleRatchet CryptoVerification.CodeLayout
  DoReserveNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

abbrev concat2Name : String :=
  "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"

@[simp, arm64_norm] theorem concat2_fnOff :
    libsignalSessionCode.fnOff concat2Name =
      ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" :=
  ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"

open Lean Elab Tactic in
/-- Instruction-fetch tactic for `[k0, k0 + len)` inside `concat2Name`. -/
elab "concat_fetches_range " b:term:max H:term:max hfn:ident k0:num len:num : tactic => do
  let eOff ← CodeLookup.lookup ``CryptoVerification.libsignalSessionCode .fnOff
    "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
  let offLit := Syntax.mkNumLit (toString eOff.val)
  evalTactic (← `(tactic|
    code_fetches_range CryptoVerification.libsignalSessionCode spqrAllocBin $b $H $hfn
      $offLit $k0 $len))

/-- Stack budget of `Concat<u8>::concat [local#2]` at `allocHookStack` (`allocHookStack + 96`). -/
abbrev concatStack : Nat := allocHookStack + 96

/-- Stack budget of `Concat<u8>::concat [local#2]` at `extHookStack` (`extHookStack + 96`). -/
abbrev concatStackXA : Nat := extHookStack + 96

private theorem stackAt_concat_gen (sp : BitVec 64) {hookStack : Nat}
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64) :
    stackAt sp (hookStack + 96) =
      stackAt (sp - 96#64) hookStack ∗
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
  have h1 := ProofLib.stackAt_split_cells sp hookStack 12 hhook
  change stackAt sp (hookStack + 96) =
    stackAt (sp - 96#64) hookStack ∗ cells (sp - 96#64) 12 at h1
  have hc12 : cells (sp - 96#64) 12 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
        ((sp - 96#64) ↦₆₄ v0) ∗ ((sp - 88#64) ↦₆₄ v1) ∗
        ((sp - 80#64) ↦₆₄ v2) ∗ ((sp - 72#64) ↦₆₄ v3) ∗
        ((sp - 64#64) ↦₆₄ v4) ∗ ((sp - 56#64) ↦₆₄ v5) ∗
        ((sp - 48#64) ↦₆₄ v6) ∗ ((sp - 40#64) ↦₆₄ v7) ∗
        ((sp - 32#64) ↦₆₄ v8) ∗ ((sp - 24#64) ↦₆₄ v9) ∗
        ((sp - 16#64) ↦₆₄ v10) ∗ ((sp - 8#64) ↦₆₄ v11)) := by
    cells_unfold
  rw [h1, hc12]

private theorem stackAt_extHookStack_eq_concatStack (sp : BitVec 64) :
    stackAt sp extHookStack =
      memRegion (sp - 16384#64) 12192 ∗ stackAt sp concatStack :=
  ProofLib.stackAt_split_bottom sp concatStack 12192 (by decide)

private theorem ofNat_getLsbD_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n).getLsbD 63 = false := by
  rw [BitVec.getLsbD_eq_getElem (by decide), BitVec.getElem_eq_testBit_toNat,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact Nat.testBit_lt_two_pow h

private theorem ofNat_getElem_63_false {n : Nat} (h : n < 2 ^ 63) :
    (BitVec.ofNat 64 n)[63] = false :=
  ofNat_getLsbD_63_false h

private theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_ult_of_le {a b : Nat} (hle : a ≤ b) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 b).ult (BitVec.ofNat 64 a) = false := by
  have ha : a < 2 ^ 64 := by omega
  simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb,
    decide_eq_false_iff_not]
  omega

private theorem pull_alloc_pure (P1 P2 R : SepProp) (φ : Prop) :
    P1 ∗ P2 ∗ ⌜φ⌝ ∗ R = ⌜φ⌝ ∗ (P1 ∗ P2 ∗ R) := by ac_rfl

private theorem pointsToBytes_append3 (p : BitVec 64) (bs0 bs1 bs2 : List (BitVec 8)) :
    (p ↦ₛ (bs0 ++ bs1 ++ bs2)) =
      (p ↦ₛ bs0) ∗ ((p + BitVec.ofNat 64 bs0.length) ↦ₛ bs1) ∗
        ((p + BitVec.ofNat 64 (bs0.length + bs1.length)) ↦ₛ bs2) := by
  rw [pointsToBytes_append p (bs0 ++ bs1) bs2, List.length_append, pointsToBytes_append p bs0 bs1,
    sepConj_assoc]

/-! ## Shared `memcpy` and `vecU8` Helpers -/

theorem subroutine_ok_inImage {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  rw [Spec.inImage, sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hsp (fun _ hout => hout)

/-- Read-only `memcpy(dst, src, len)` region contract (`src ↦ᵣ bs`) with trace preservation. -/
def sessionMemcpyRegionROSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ᵣ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗ (dst ↦ₛ bs) ∗ (src ↦ᵣ bs)

theorem hookMemcpy_region_ro_trace_ok : HookOk hookMemcpy sessionMemcpyRegionROSpec := by
  refine retHook_ok fun ⟨dst, src, bs⟩ R s0 _ hpre _ => ?_
  simp only [sessionMemcpyRegionROSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hsrc_front : s0.mem ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  have hread := (IsBlockRO.pointsToBytesRO src bs hlen).read hsrc_front
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only; rw [hx0, hx1, hx2, hread]; exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  · simp only [sessionMemcpyRegionROSpec, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2, hread, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨trivial, rfl⟩, satisfies_writeBytes bs hlen hmem⟩

/-- `ChainProofs.bytesAt` `memcpy(dst, src, len)` region contract with trace preservation. -/
def sessionMemcpyBytesAtSpec (ro : Bool) : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    ChainProofs.bytesAt ro src bs
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    ChainProofs.bytesAt ro src bs

def sessionMemcpyRegionROSpecWithStack (hookStack : Nat) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp hookStack

def sessionMemcpyRegionROSpecX : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧ s0.readReg64 .x1 = src ∧ (s0.readReg64 .x2).toNat = bs.length ∧
      bs.length ≤ 2 ^ 64⌝ ∗
      memRegion dst bs.length ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp extHookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
      (dst ↦ₛ bs) ∗ (src ↦ᵣ bs) ∗ stackAt s0.sp extHookStack

/-- `.inImage img` contract for read-only `memcpy` at `extHookStack`. -/
def MemcpyROOkExtX (img : Obj.Image) (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
    (sessionMemcpyRegionROSpecX.inImage img)

def sessionMemcpyBytesAtSpecWithStack (hookStack : Nat) (ro : Bool) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp hookStack
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace⌝ ∗
    (dst ↦ₛ bs) ∗
    ChainProofs.bytesAt ro src bs ∗
    stackAt s0.sp hookStack

private theorem session_memcpy_bytesAt_opt_ok_at {hookStack : Nat} {img? : Option Obj.Image}
    {prog : Program} {addr : BitVec 64}
    (hmc : subroutine_ok prog addr (Spec.withOptInv (session2MemcpySpecWithStack hookStack) img?))
    (hmc_ro : subroutine_ok prog addr (Spec.withOptInv (sessionMemcpyRegionROSpecWithStack hookStack) img?))
    (ro : Bool) :
    subroutine_ok prog addr (Spec.withOptInv (sessionMemcpyBytesAtSpecWithStack hookStack ro) img?) := by
  cases ro
  · refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
    dsimp only [Spec.withOptInv, sessionMemcpyBytesAtSpecWithStack, ChainProofs.bytesAt_false] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨hinv, hpre⟩ := hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    have hpre' : s0.mem ⊨ (Spec.withOptInv (session2MemcpySpecWithStack hookStack) img?).pre
        (dst, src, bs) s0 ∗ R := by
      dsimp only [Spec.withOptInv, session2MemcpySpecWithStack]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      refine ⟨hinv, ?_⟩
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hpre.1.1, hpre.1.2.1, hpre.1.2.2.1⟩, hpre.2⟩
    exact hmc.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hsp (fun _ hout => hout)
  · exact hmc_ro

theorem session_memcpy_region_ro_ok_at {b : BitVec 64} {ext : String → Option (State → State)}
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      sessionMemcpyRegionROSpec :=
  hook_ok_at (hname := memcpyName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName]) hRO

private theorem memcpy_ro_ok_opt_of_hookSat {b : BitVec 64} {ext : String → Option (State → State)}
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec)
    {name : String} {k : Nat} (hookStack : Nat := allocHookStack)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (sessionMemcpyRegionROSpecWithStack hookStack) none) := by
  refine subroutine_ok_withOptInv_none_of ?_
  have h := subroutine_ok_withStack_of_subroutine_ok
    (session_memcpy_region_ro_ok_at (b := b) hRO name k hk) hookStack
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionMemcpyRegionROSpec hookStack).pre (dst, src, bs) s0 ∗ R := by
    dsimp only [withStack, sessionMemcpyRegionROSpec, sessionMemcpyRegionROSpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionROSpec, sessionMemcpyRegionROSpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem session_memcpy_region_ro_ok_at_x_of_roX {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hRO : MemcpyROOkExtX img ext) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpyRegionROSpecX.inImage img) :=
  sub_ok_at_of_fnAddr hRO name k hk

theorem memcpyROOkExtX_of_hookSat {img : Obj.Image} {ext : String → Option (State → State)}
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    MemcpyROOkExtX img ext := by
  have h0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      sessionMemcpyRegionROSpec := by
    have h := session_memcpy_region_ro_ok_at (b := img.base) hRO memcpyName 0 (Nat.add_zero _)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  unfold MemcpyROOkExtX
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, sessionMemcpyRegionROSpecX] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨_, hpre⟩ := hpre
  have hpre' : s0.mem ⊨ sessionMemcpyRegionROSpec.pre (dst, src, bs) s0 ∗
      (stackAt s0.sp extHookStack ∗ R) := by
    dsimp only [sessionMemcpyRegionROSpec]
    simpa only [sepConj_assoc] using hpre
  refine h0.mono_outcome (dst, src, bs) (stackAt s0.sp extHookStack ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hmem⟩ | ⟨code, _, hmem⟩ | ⟨_, hmem⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, sessionMemcpyRegionROSpecX, sessionMemcpyRegionROSpec] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · rw [show sessionMemcpyRegionROSpec.onPanic (dst, src, bs) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · rw [show sessionMemcpyRegionROSpec.onExit (dst, src, bs) code s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · rw [show sessionMemcpyRegionROSpec.onOom (dst, src, bs) s0 sf = ⌜False⌝ from rfl,
      satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1

theorem session_memcpy_region_ro_withStack_ok_at {b : BitVec 64}
    {ext : String → Option (State → State)} {stk : Nat}
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack stk))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpyRegionROSpecWithStack stk) :=
  hook_ok_at (hname := memcpyName) rfl hk (by simp only [arm64_norm])
    (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName]) hRO

private theorem memcpy_ro_withStack_ok_opt_of_hookSat {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat}
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack hookStack))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (sessionMemcpyRegionROSpecWithStack hookStack) none) :=
  subroutine_ok_withOptInv_none_of
    (session_memcpy_region_ro_withStack_ok_at (b := b) hRO name k hk)

theorem memcpyROOkExtX_of_hookSat_withStack {img : Obj.Image}
    {ext : String → Option (State → State)} {stk : Nat}
    (hstk : stk ≤ extHookStack)
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack stk)) :
    MemcpyROOkExtX img ext := by
  have h0 : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr memcpyName)
      (sessionMemcpyRegionROSpecWithStack stk) := by
    have h := session_memcpy_region_ro_withStack_ok_at (b := img.base) hRO memcpyName 0
      (Nat.add_zero _)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
  unfold MemcpyROOkExtX
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [Spec.inImage, sessionMemcpyRegionROSpecX, sessionMemcpyRegionROSpecWithStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨_, hpre⟩ := hpre
  have hsplit : stackAt s0.sp extHookStack =
      memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - stk) ∗
      stackAt s0.sp stk := by
    have heq : stk + (extHookStack - stk) = extHookStack := Nat.add_sub_of_le hstk
    have hle64 : stk + (extHookStack - stk) ≤ 2 ^ 64 := by
      rw [heq]; decide
    have hb := ProofLib.stackAt_split_bottom s0.sp stk (extHookStack - stk) hle64
    simpa only [heq] using hb
  let btm := memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - stk)
  have hpre' : s0.mem ⊨ (sessionMemcpyRegionROSpecWithStack stk).pre (dst, src, bs) s0 ∗
      (btm ∗ R) := by
    rw [hsplit] at hpre
    dsimp only [sessionMemcpyRegionROSpecWithStack, btm] at hpre ⊢
    ac_nf at hpre ⊢
  refine h0.mono_outcome (dst, src, bs) (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hpost⟩ | ⟨_, hmem⟩ | ⟨code, _, hmem⟩ | ⟨_, hmem⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [Spec.inImage, sessionMemcpyRegionROSpecX,
      sessionMemcpyRegionROSpecWithStack, btm] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · rw [show (sessionMemcpyRegionROSpecWithStack stk).onPanic (dst, src, bs) s0 sf = ⌜False⌝
      from rfl, satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · rw [show (sessionMemcpyRegionROSpecWithStack stk).onExit (dst, src, bs) code s0 sf = ⌜False⌝
      from rfl, satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1
  · rw [show (sessionMemcpyRegionROSpecWithStack stk).onOom (dst, src, bs) s0 sf = ⌜False⌝
      from rfl, satisfies_pure_sepConj] at hmem
    exact False.elim hmem.1

private theorem shim_withStack_ok_opt_of_hookSat {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat}
    (hshim : HookSat ext shimName (session2ShimSpecWithStack hookStack))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) none) :=
  subroutine_ok_withOptInv_none_of
    (hook_ok_at (hname := shimName) rfl hk (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, shimName]) hshim)

private theorem alloc_withStack_ok_opt_of_hookSat {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat}
    (halloc : HookSat ext allocName (rustAllocSpecWithStack A hookStack))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff allocName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) none) :=
  subroutine_ok_withOptInv_none_of
    (hook_ok_at (hname := allocName) rfl hk (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, allocName]) halloc)

private theorem memcpy_withStack_ok_opt_of_hookSat {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat}
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack hookStack))
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (session2MemcpySpecWithStack hookStack) none) :=
  subroutine_ok_withOptInv_none_of
    (hook_ok_at (hname := memcpyName) rfl hk (by simp only [arm64_norm])
      (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, memcpyName]) hmc)

theorem session_memcpy_region_ro_ok_at_x {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff memcpyName := by
      simp only [arm64_norm]) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr name + BitVec.ofNat 64 k)
      (sessionMemcpyRegionROSpecX.inImage img) :=
  session_memcpy_region_ro_ok_at_x_of_roX (memcpyROOkExtX_of_hookSat hRO) name k hk

theorem hookSat_memcpy_ro_tripleRatchetExterns (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    HookSat (tripleRatchetExterns C ctl abs) memcpyName sessionMemcpyRegionROSpec :=
  ⟨hookMemcpy, rfl, hookMemcpy_region_ro_trace_ok⟩

private theorem vecU8_of_zero (A : RustAlloc) (v : BitVec 64) :
    (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ⊢
      vecU8 A v [] := by
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
  refine Entails.trans ?_ (Entails.sepExists_intro 1#64)
  simp only [List.length_nil, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.le_refl, true_and, ↓reduceIte, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64) ∗
        ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ =
      ⌜(0 : Nat) < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0#64⌝ ∗
        ((v ↦₆₄ 0#64) ∗ ((v + 8#64) ↦₆₄ 1#64) ∗ ((v + 16#64) ↦₆₄ 0#64)) by ac_rfl]
  exact Entails.pure_right ⟨by decide, by decide⟩ (Entails.refl _)

private theorem vecU8_of_pos (A : RustAlloc) (v p' : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 63) (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live p' bs.length 1 ∗ (p' ↦ₛ bs) ⊢
      vecU8 A v bs := by
  have hne0 : BitVec.ofNat 64 bs.length ≠ 0 := by
    intro h
    have ht := congrArg BitVec.toNat h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at ht
    change bs.length = 0 at ht
    omega
  have htoNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold vecU8 vecU8At vecHeader
  refine Entails.trans ?_ (Entails.sepExists_intro (BitVec.ofNat 64 bs.length))
  refine Entails.trans ?_ (Entails.sepExists_intro p')
  simp only [hne0, htoNat, Nat.le_refl, hlt, ↓reduceIte,
    Nat.sub_self, memRegion_zero, sepConj_emp, sepConj_assoc]
  rw [show (v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ⌜True ∧ True ∧ p' ≠ 0⌝ ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs) =
      ⌜True ∧ True ∧ p' ≠ 0⌝ ∗ ((v ↦₆₄ BitVec.ofNat 64 bs.length) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        A.live p' bs.length 1 ∗ (p' ↦ₛ bs)) by ac_rfl]
  exact Entails.pure_right ⟨trivial, trivial, hp'⟩ (Entails.refl _)

private theorem vecU8_of_append_pos (A : RustAlloc) (v p' : BitVec 64)
    (bs0 bs1 : List (BitVec 8))
    (hpos : 0 < bs0.length + bs1.length) (hlt : bs0.length + bs1.length < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length)) ∗
      A.live p' (bs0.length + bs1.length) 1 ∗ (p' ↦ₛ (bs0 ++ bs1)) ⊢
      vecU8 A v (bs0 ++ bs1) := by
  rw [← List.length_append]
  exact vecU8_of_pos A v p' (bs0 ++ bs1) (by rw [List.length_append]; exact hpos)
    (by rw [List.length_append]; exact hlt) hp'

private theorem vecU8_of_append3_pos (A : RustAlloc) (v p' : BitVec 64)
    (bs0 bs1 bs2 : List (BitVec 8))
    (hpos : 0 < bs0.length + bs1.length + bs2.length)
    (hlt : bs0.length + bs1.length + bs2.length < 2 ^ 63)
    (hp' : p' ≠ 0#64) :
    (v ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)) ∗ ((v + 8#64) ↦₆₄ p') ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)) ∗
      A.live p' (bs0.length + bs1.length + bs2.length) 1 ∗ (p' ↦ₛ (bs0 ++ bs1 ++ bs2)) ⊢
      vecU8 A v (bs0 ++ bs1 ++ bs2) := by
  have hlen : (bs0 ++ bs1 ++ bs2).length = bs0.length + bs1.length + bs2.length := by
    simp only [List.length_append]
  rw [← hlen]
  exact vecU8_of_pos A v p' (bs0 ++ bs1 ++ bs2) (by rw [hlen]; exact hpos)
    (by rw [hlen]; exact hlt) hp'

/-! ## 2-Slice Concatenation -/

/-- 2-slice concatenation specification parameterized by callee `hookStack`. -/
def sliceConcat2SpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec ChainProofs.SliceConcat2Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      x.bs0.length + x.bs1.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗ ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s.sp (hookStack + 96)
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (x.bs0 ++ x.bs1) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗ ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s0.sp (hookStack + 96)
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- 2-slice concatenation specification at stack budget `concatStackXA` (`extHookStack + 96`). -/
def sliceConcat2SpecXA (A : RustAlloc) : Spec ChainProofs.SliceConcat2Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.outVec ∧ s.readReg64 .x1 = x.slicesA ∧ s.readReg64 .x2 = 2#64 ∧
      x.bs0.length + x.bs1.length < 2 ^ 63⌝ ∗
      memRegion x.outVec 24 ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗ ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s.sp concatStackXA
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      vecU8 A x.outVec (x.bs0 ++ x.bs1) ∗
      (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
      ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
      ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗ ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
      A.pool ∗ stackAt s0.sp concatStackXA
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `.inImage img` contract proposition for `sliceConcat2SpecXA`. -/
def SliceConcat2OkXA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ChainProofs.sliceConcatName)
    ((sliceConcat2SpecXA A).inImage img)

set_option maxHeartbeats 1600000 in
private theorem slice_concat_2_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr concat2Name +
        BitVec.ofNat 64 (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr concat2Name +
        BitVec.ofNat 64 (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
          "__rustc::__rust_alloc"))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?))
    (hmc_any : ∀ ro, subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr concat2Name +
        BitVec.ofNat 64 (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy"))
      (Spec.withOptInv (sessionMemcpyBytesAtSpecWithStack hookStack ro) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ChainProofs.sliceConcatName)
      (Spec.withOptInv (sliceConcat2SpecWithStack A hookStack) img?) := by
  change subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr concat2Name)
    (Spec.withOptInv (sliceConcat2SpecWithStack A hookStack) img?)
  unfold Spec.withOptInv
  simp only [sliceConcat2SpecWithStack, memRegion_24, stackAt_concat_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff concat2Name =
      ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" :=
    concat2_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := concat2Name)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
      "alloc::raw_vec::handle_error")
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  concat_fetches_range b (Rust.withPanics ext) hfn 0 364
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmc_any hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr concat2Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : OptCallInv img? s0 := by assumption
  obtain ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1⟩ := x
  dsimp only at *
  have hmax : bs0.length + bs1.length < 2 ^ 63 := ‹_›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have htot_lt63 : bs1.length + bs0.length < 2 ^ 63 := by omega
  have htot_lt64 : bs1.length + bs0.length < 2 ^ 64 := by omega
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have hadd_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add]
  have hsub_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length))[63] = false :=
    ofNat_getElem_63_false (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi1 : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have h0_eq : bs0 = [] ∨ 0 < bs0.length := by cases bs0 <;> simp
  have h1_eq : bs1 = [] ∨ 0 < bs1.length := by cases bs1 <;> simp
  rcases h0_eq with rfl | hpos0 <;> rcases h1_eq with rfl | hpos1
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.nil_append] at *
    apply SepWPp.of_sepWP_ret; wp_steps
    apply SepWP.fold (vecU8_of_zero A outVec) (by sep_focus); wp_done
  ·
    simp only [List.length_nil, Nat.zero_add, BitVec.ofNat_eq_ofNat, List.nil_append] at *
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk bs1.length 1 := ⟨hpos1, hpow1, by omega⟩
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      wp_apply using (hmc_any ro1); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs1 hpos1 hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have hlay : LayoutOk bs0.length 1 := ⟨hpos0, hpow1, by omega⟩
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      wp_apply using (hmc_any ro0); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs0 hpos0 hmax hoom) (by sep_focus)
      wp_done
  ·
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk (bs0.length + bs1.length) 1 := ⟨by omega, hpow1, by omega⟩
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      apply SepWP.seq_optInv (mid := entry + 172#64) hinv4
      wp_apply using (hmc_any ro0); apply SepWP.done (by assumption) (by wp_norm_lhs); intro hinv4b
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv4b
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv5
      wp_apply using (hmc_any ro1); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs1).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs1
        (by omega) hmax hoom) (by sep_focus)
      wp_done

private theorem sliceConcat2Spec_of_withStack {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (sliceConcat2SpecWithStack A allocHookStack)) :
    subroutine_ok P addr (ChainProofs.sliceConcat2Spec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [ChainProofs.sliceConcat2Spec, stackAt_extHookStack_eq_concatStack, sepConj_assoc]
    at hpre
  let btm := memRegion (s0.sp - 16384#64) 12192
  have hpre' : s0.mem ⊨ (sliceConcat2SpecWithStack A allocHookStack).pre x s0 ∗ (btm ∗ R) := by
    simp only [sliceConcat2SpecWithStack, btm, sepConj_assoc]
    ac_nf at hpre ⊢
  refine h.mono_outcome x (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [sliceConcat2SpecWithStack, ChainProofs.sliceConcat2Spec,
      stackAt_extHookStack_eq_concatStack, btm, sepConj_assoc] at hq ⊢
    ac_nf at hq ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [sliceConcat2SpecWithStack, ChainProofs.sliceConcat2Spec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

/-- `Concat<u8>::concat [local#2]` meets `ChainProofs.sliceConcat2Spec A`. -/
theorem slice_concat_2_spec_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ChainProofs.sliceConcatName)
      (ChainProofs.sliceConcat2Spec A) := by
  refine sliceConcat2Spec_of_withStack (subroutine_ok_of_withOptInv_none ?_)
  exact slice_concat_2_opt_ok (hookStack := allocHookStack) (by decide)
    (shim_ok_opt_of_contracts hA (hookStack := allocHookStack) (by fnoff_eq))
    (alloc_ok_opt_of_contracts hA (by fnoff_eq))
    (session_memcpy_bytesAt_opt_ok_at
      (memcpy_ok_opt_of_contracts hA (hookStack := allocHookStack) (by fnoff_eq))
      (memcpy_ro_ok_opt_of_hookSat hRO (hookStack := allocHookStack) (by fnoff_eq)))

/-- `Concat<u8>::concat [local#2]` meets `(sliceConcat2SpecXA A).inImage img`. -/
theorem slice_concat_2_spec_ok_ext_roX {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : MemcpyROOkExtX img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ChainProofs.sliceConcatName)
      ((sliceConcat2SpecXA A).inImage img) :=
  slice_concat_2_opt_ok (A := A) (b := img.base) (ext := ext)
    (hookStack := extHookStack) (img? := some img) (by decide)
    (shim_ok_at2_ext_x hA (name := concat2Name)
      (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by fnoff_eq))
    (alloc_ok_at_norm_ext_x hA (name := concat2Name)
      (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
        "__rustc::__rust_alloc") (by fnoff_eq))
    (session_memcpy_bytesAt_opt_ok_at (hookStack := extHookStack) (img? := some img)
      (memcpy_ok_at2_ext_x hA (name := concat2Name)
        (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")
        (by fnoff_eq))
      (session_memcpy_region_ro_ok_at_x_of_roX hRO concat2Name
        (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")
        (by fnoff_eq)))

theorem slice_concat_2_spec_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ChainProofs.sliceConcatName)
      ((sliceConcat2SpecXA A).inImage img) :=
  slice_concat_2_spec_ok_ext_roX hA (memcpyROOkExtX_of_hookSat hRO)

theorem slice_concat_2_ok_x_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : MemcpyROOkExtX img ext) :
    SliceConcat2OkXA img A ext :=
  slice_concat_2_spec_ok_ext_roX hA hRO

theorem slice_concat_2_ok_x_xa {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    SliceConcat2OkXA img A ext :=
  slice_concat_2_spec_ok_ext_xa hA hRO

theorem slice_concat_2_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    ChainProofs.SliceConcat2OkX img A ext :=
  subroutine_ok_inImage img (slice_concat_2_spec_ok_ext hA hRO)

theorem slice_concat_2_ok_x_tripleRatchetExterns {img : Obj.Image} (C : Crypto) {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    ChainProofs.SliceConcat2OkX img A (tripleRatchetExterns C ctl abs) :=
  slice_concat_2_ok_x (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA)
    (hookSat_memcpy_ro_tripleRatchetExterns C ctl abs)

/-- `slice_concat_2_spec_ok_ext` from 4 KiB `HookSat` contracts. -/
theorem slice_concat_2_spec_ok_ext_withStack {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext shimName (session2ShimSpecWithStack allocHookStack))
    (halloc : HookSat ext allocName (rustAllocSpecWithStack A allocHookStack))
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack))
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ChainProofs.sliceConcatName)
      (ChainProofs.sliceConcat2Spec A) := by
  refine sliceConcat2Spec_of_withStack (subroutine_ok_of_withOptInv_none ?_)
  exact slice_concat_2_opt_ok (hookStack := allocHookStack) (by decide)
    (shim_withStack_ok_opt_of_hookSat hshim (by fnoff_eq))
    (alloc_withStack_ok_opt_of_hookSat halloc (by fnoff_eq))
    (session_memcpy_bytesAt_opt_ok_at
      (memcpy_withStack_ok_opt_of_hookSat hmc (by fnoff_eq))
      (memcpy_ro_withStack_ok_opt_of_hookSat hRO (by fnoff_eq)))

theorem slice_concat_2_ok_x_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext shimName (session2ShimSpecWithStack allocHookStack))
    (halloc : HookSat ext allocName (rustAllocSpecWithStack A allocHookStack))
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack))
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack)) :
    ChainProofs.SliceConcat2OkX img A ext :=
  subroutine_ok_inImage img (slice_concat_2_spec_ok_ext_withStack hshim halloc hmc hRO)

private theorem shim_ok_opt_of_noAllocShim_hookSat {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat}
    (hshim : HookSat ext shimName noAllocShimSpec)
    {name : String} {k : Nat}
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff shimName) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) none) := by
  have hshim0 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k)
      (withStack noAllocShimSpec hookStack) :=
    subroutine_ok_withStack_of_subroutine_ok
      (hook_ok_at (hname := shimName) rfl hk (by simp only [arm64_norm])
        (fun _ => by simp only [arm64_norm]) (by simp [Rust.isPanicSymbol, shimName]) hshim)
      hookStack
  refine subroutine_ok_withOptInv_none_of
    (subroutine_ok_outcome_intro fun u R s0 hpc hrun hpre hal => ?_)
  have hpre' : s0.mem ⊨ (withStack noAllocShimSpec hookStack).pre u s0 ∗ R := by
    dsimp only [withStack, noAllocShimSpec, session2ShimSpecWithStack] at hpre ⊢
    rw [emp_sepConj]; exact hpre
  exact hshim0.mono_outcome u R s0 hpc hrun hpre' hal (fun _ hout => hout)

/-- `SliceConcat2OkX` from 0-stack `noAllocShimSpec` and `rustAllocSpec A`. -/
theorem slice_concat_2_ok_x_of_hooks {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext shimName noAllocShimSpec)
    (halloc : HookSat ext allocName (rustAllocSpec A))
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack))
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack)) :
    ChainProofs.SliceConcat2OkX img A ext := by
  refine subroutine_ok_inImage img (sliceConcat2Spec_of_withStack (subroutine_ok_of_withOptInv_none ?_))
  exact slice_concat_2_opt_ok (hookStack := allocHookStack) (by decide)
    (shim_ok_opt_of_noAllocShim_hookSat hshim (by fnoff_eq))
    (alloc_withStack_ok_opt_of_hookSat halloc (by fnoff_eq))
    (session_memcpy_bytesAt_opt_ok_at
      (memcpy_withStack_ok_opt_of_hookSat hmc (by fnoff_eq))
      (memcpy_ro_withStack_ok_opt_of_hookSat hRO (by fnoff_eq)))

/-! ## 3-Slice Concatenation -/

/-- Ghost input for 3-slice `Concat<u8>::concat [local#2]` (`x2 = 3#64`). -/
structure SliceConcat3Ghost where
  outVec  : BitVec 64
  slicesA : BitVec 64
  ro0     : Bool
  p0      : BitVec 64
  bs0     : List (BitVec 8)
  ro1     : Bool
  p1      : BitVec 64
  bs1     : List (BitVec 8)
  ro2     : Bool
  p2      : BitVec 64
  bs2     : List (BitVec 8)

/-- 3-slice concatenation specification parameterized by callee `hookStack`. -/
def sliceConcat3SpecWithStack (A : RustAlloc) (hookStack : Nat) : Spec SliceConcat3Ghost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.outVec ∧
      s.readReg64 .x1 = x.slicesA ∧
      s.readReg64 .x2 = 3#64 ∧
      x.bs0.length + x.bs1.length + x.bs2.length < 2 ^ 63⌝ ∗
    memRegion x.outVec 24 ∗
    (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
    ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
    ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
    ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗
    ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
    ChainProofs.bytesAt x.ro2 x.p2 x.bs2 ∗
    A.pool ∗ stackAt s.sp (hookStack + 96)
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
    vecU8 A x.outVec (x.bs0 ++ x.bs1 ++ x.bs2) ∗
    (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
    ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
    ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
    ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗
    ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
    ChainProofs.bytesAt x.ro2 x.p2 x.bs2 ∗
    A.pool ∗ stackAt s0.sp (hookStack + 96)
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- 3-slice concatenation specification at `extHookStack` supporting read-only or mutable slice backing via `ChainProofs.bytesAt`. -/
def sliceConcat3Spec (A : RustAlloc) : Spec SliceConcat3Ghost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.outVec ∧
      s.readReg64 .x1 = x.slicesA ∧
      s.readReg64 .x2 = 3#64 ∧
      x.bs0.length + x.bs1.length + x.bs2.length < 2 ^ 63⌝ ∗
    memRegion x.outVec 24 ∗
    (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
    ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
    ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
    ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗
    ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
    ChainProofs.bytesAt x.ro2 x.p2 x.bs2 ∗
    A.pool ∗ stackAt s.sp extHookStack
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
    vecU8 A x.outVec (x.bs0 ++ x.bs1 ++ x.bs2) ∗
    (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
    ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
    ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
    ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗
    ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
    ChainProofs.bytesAt x.ro2 x.p2 x.bs2 ∗
    A.pool ∗ stackAt s0.sp extHookStack
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- 3-slice concatenation specification at `concatStackXA` (`extHookStack + 96`). -/
def sliceConcat3SpecXA (A : RustAlloc) : Spec SliceConcat3Ghost where
  pre x s :=
    ⌜s.readReg64 .x0 = x.outVec ∧
      s.readReg64 .x1 = x.slicesA ∧
      s.readReg64 .x2 = 3#64 ∧
      x.bs0.length + x.bs1.length + x.bs2.length < 2 ^ 63⌝ ∗
    memRegion x.outVec 24 ∗
    (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
    ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
    ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
    ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗
    ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
    ChainProofs.bytesAt x.ro2 x.p2 x.bs2 ∗
    A.pool ∗ stackAt s.sp concatStackXA
  post x s0 sf :=
    ⌜sf.trace = s0.trace⌝ ∗
    vecU8 A x.outVec (x.bs0 ++ x.bs1 ++ x.bs2) ∗
    (x.slicesA ↦₆₄ x.p0) ∗ ((x.slicesA + 8#64) ↦₆₄ BitVec.ofNat 64 x.bs0.length) ∗
    ((x.slicesA + 16#64) ↦₆₄ x.p1) ∗ ((x.slicesA + 24#64) ↦₆₄ BitVec.ofNat 64 x.bs1.length) ∗
    ((x.slicesA + 32#64) ↦₆₄ x.p2) ∗ ((x.slicesA + 40#64) ↦₆₄ BitVec.ofNat 64 x.bs2.length) ∗
    ChainProofs.bytesAt x.ro0 x.p0 x.bs0 ∗
    ChainProofs.bytesAt x.ro1 x.p1 x.bs1 ∗
    ChainProofs.bytesAt x.ro2 x.p2 x.bs2 ∗
    A.pool ∗ stackAt s0.sp concatStackXA
  onPanic _ s0 sf := ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- `.inImage img` contract proposition for `sliceConcat3Spec`. -/
def SliceConcat3OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ChainProofs.sliceConcatName)
    ((sliceConcat3Spec A).inImage img)

/-- `.inImage img` contract proposition for `sliceConcat3SpecXA`. -/
def SliceConcat3OkXA (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr ChainProofs.sliceConcatName)
    ((sliceConcat3SpecXA A).inImage img)

set_option maxHeartbeats 3200000 in
private theorem slice_concat_3_opt_ok {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} {hookStack : Nat} {img? : Option Obj.Image}
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr concat2Name +
        BitVec.ofNat 64 (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
          "__rustc::__rust_no_alloc_shim_is_unstable_v2"))
      (Spec.withOptInv (session2ShimSpecWithStack hookStack) img?))
    (halloc : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr concat2Name +
        BitVec.ofNat 64 (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
          "__rustc::__rust_alloc"))
      (Spec.withOptInv (rustAllocSpecWithStack A hookStack) img?))
    (hmc_any : ∀ ro, subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr concat2Name +
        BitVec.ofNat 64 (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy"))
      (Spec.withOptInv (sessionMemcpyBytesAtSpecWithStack hookStack ro) img?)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ChainProofs.sliceConcatName)
      (Spec.withOptInv (sliceConcat3SpecWithStack A hookStack) img?) := by
  change subroutine_ok (tripleRatchetProgAtExt b ext)
    ((tripleRatchetProgAtExt b ext).fnAddr concat2Name)
    (Spec.withOptInv (sliceConcat3SpecWithStack A hookStack) img?)
  unfold Spec.withOptInv
  simp only [sliceConcat3SpecWithStack, memRegion_24, stackAt_concat_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hfn : libsignalSessionCode.fnOff concat2Name =
      ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" :=
    concat2_fnOff
  have hpanic := panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := concat2Name)
    (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
      "alloc::raw_vec::handle_error")
    (by rw [hfn, (ls_stub% "alloc::raw_vec::handle_error")])
  concat_fetches_range b (Rust.withPanics ext) hfn 0 364
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmc_any hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr concat2Name = entry
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : OptCallInv img? s0 := by assumption
  obtain ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1, ro2, p2, bs2⟩ := x
  dsimp only at *
  have hmax : bs0.length + bs1.length + bs2.length < 2 ^ 63 := ‹_›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h2_lt64 : bs2.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have h2_le64 : bs2.length ≤ 2 ^ 64 := by omega
  have hadd10_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd201_bv : BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 (bs0.length + bs1.length) =
      BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd20_bv : BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs2.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd21_bv : BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs1.length + bs2.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add]
  have hadd02_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs2.length =
      BitVec.ofNat 64 (bs0.length + bs2.length) := by rw [← BitVec.ofNat_add]
  have hadd12_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs2.length =
      BitVec.ofNat 64 (bs1.length + bs2.length) := by rw [← BitVec.ofNat_add]
  have hadd012_bv : BitVec.ofNat 64 (bs0.length + bs1.length) + BitVec.ofNat 64 bs2.length =
      BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) := by rw [← BitVec.ofNat_add]
  have hsub0_bv : BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs1.length + bs2.length) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub01_bv : BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) -
      BitVec.ofNat 64 (bs0.length + bs1.length) = BitVec.ofNat 64 bs2.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub0_01_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub0_02_bv : BitVec.ofNat 64 (bs0.length + bs2.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs2.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub1_bv : BitVec.ofNat 64 (bs1.length + bs2.length) - BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 bs2.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h1_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hcs2 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs2.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hcs02 : (BitVec.ofNat 64 (bs0.length + bs2.length)).ult (BitVec.ofNat 64 bs2.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hcs12 : (BitVec.ofNat 64 (bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs2.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length))[63] = false :=
    ofNat_getElem_63_false (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).toNat =
      bs0.length + bs1.length + bs2.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h01_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h02_toNat : (BitVec.ofNat 64 (bs0.length + bs2.length)).toNat = bs0.length + bs2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h12_toNat : (BitVec.ofNat 64 (bs1.length + bs2.length)).toNat = bs1.length + bs2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have h2_toNat : (BitVec.ofNat 64 bs2.length).toNat = bs2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi0_01 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi0_02 : (BitVec.ofNat 64 (bs0.length + bs2.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi0_self : (BitVec.ofNat 64 bs0.length).ult (BitVec.ofNat 64 bs0.length) = false :=
    ProofLib.bitvec_ult_self _
  have hhi1 : (BitVec.ofNat 64 (bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi1_self : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have hhi2 : (BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 bs2.length) = false :=
    ProofLib.bitvec_ult_self _
  have h0_eq : bs0 = [] ∨ 0 < bs0.length := by cases bs0 <;> simp
  have h1_eq : bs1 = [] ∨ 0 < bs1.length := by cases bs1 <;> simp
  have h2_eq : bs2 = [] ∨ 0 < bs2.length := by cases bs2 <;> simp
  rcases h0_eq with rfl | hpos0 <;> rcases h1_eq with rfl | hpos1 <;> rcases h2_eq with rfl | hpos2
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    apply SepWPp.of_sepWP_ret; wp_steps
    apply SepWP.fold (vecU8_of_zero A outVec) (by sep_focus); wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat,
      List.nil_append, List.append_nil] at *
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have hlay : LayoutOk bs2.length 1 := ⟨hpos2, hpow1, by omega⟩
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      wp_apply using (hmc_any ro2); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs2 hpos2 hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat,
      List.nil_append, List.append_nil] at *
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk bs1.length 1 := ⟨hpos1, hpow1, by omega⟩
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      wp_apply using (hmc_any ro1); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs1 hpos1 hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.zero_add, BitVec.ofNat_eq_ofNat, List.nil_append] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs1.length + bs2.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have hlay : LayoutOk (bs1.length + bs2.length) 1 := ⟨by omega, hpow1, by omega⟩
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs1.length bs2.length (by omega)]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      apply SepWP.seq_optInv (mid := entry + 228#64) hinv4
      wp_apply using (hmc_any ro1); apply SepWP.done (by assumption) (by wp_norm_lhs); intro hinv4b
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv4b
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv5
      wp_apply using (hmc_any ro2); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs1 bs2).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs1 bs2
        (by omega) hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have hlay : LayoutOk bs0.length 1 := ⟨hpos0, hpow1, by omega⟩
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      wp_apply using (hmc_any ro0); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs0 hpos0 hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs2.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have hlay : LayoutOk (bs0.length + bs2.length) 1 := ⟨by omega, hpow1, by omega⟩
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs2.length (by omega)]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      apply SepWP.seq_optInv (mid := entry + 172#64) hinv4
      wp_apply using (hmc_any ro0); apply SepWP.done (by assumption) (by wp_norm_lhs); intro hinv4b
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv4b
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv5
      wp_apply using (hmc_any ro2); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs2).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs2
        (by omega) hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk (bs0.length + bs1.length) 1 := ⟨by omega, hpow1, by omega⟩
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      apply SepWP.seq_optInv (mid := entry + 172#64) hinv4
      wp_apply using (hmc_any ro0); apply SepWP.done (by assumption) (by wp_norm_lhs); intro hinv4b
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv4b
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv5
      wp_apply using (hmc_any ro1); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs1).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs1
        (by omega) hmax hoom) (by sep_focus)
      wp_done
  ·
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have hlay : LayoutOk (bs0.length + bs1.length + bs2.length) 1 := ⟨by omega, hpow1, by omega⟩
    have ⟨hlay_pos, _, hlay_max⟩ := hlay
    apply SepWPp.of_sepWP_optInv (mid := entry + 108#64) hinv0
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_no_alloc_shim_is_unstable_v2")) hinv0
    wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv1
    apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "__rustc::__rust_alloc")) hinv1
    wp_apply; wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv2
    wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs); intro hinv3
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "alloc::raw_vec::handle_error"))
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) (bs0.length + bs1.length) bs2.length (by omega),
        ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
      apply SepWPp.of_sepWP_ret
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv3
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv4
      apply SepWP.seq_optInv (mid := entry + 172#64) hinv4
      wp_apply using (hmc_any ro0); apply SepWP.done (by assumption) (by wp_norm_lhs); intro hinv4b
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv4b
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv5
      apply SepWP.seq_optInv (mid := entry + 228#64) hinv5
      wp_apply using (hmc_any ro1); apply SepWP.done (by assumption) (by wp_norm_lhs); intro hinv5b
      apply SepWP.seq_optInv (mid := entry + bv% (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")) hinv5b
      wp_steps; apply SepWP.done (by rfl) (by wp_norm_lhs); intro hinv6
      wp_apply using (hmc_any ro2); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append3 (sf_1.readReg64 Reg.x0) bs0 bs1 bs2).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append3_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs1 bs2
        (by omega) hmax hoom) (by sep_focus)
      wp_done

private theorem sliceConcat3Spec_of_withStack {A : RustAlloc} {P : Program} {addr : BitVec 64}
    (h : subroutine_ok P addr (sliceConcat3SpecWithStack A allocHookStack)) :
    subroutine_ok P addr (sliceConcat3Spec A) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hsp => ?_
  simp only [sliceConcat3Spec, stackAt_extHookStack_eq_concatStack, sepConj_assoc] at hpre
  let btm := memRegion (s0.sp - 16384#64) 12192
  have hpre' : s0.mem ⊨ (sliceConcat3SpecWithStack A allocHookStack).pre x s0 ∗ (btm ∗ R) := by
    simp only [sliceConcat3SpecWithStack, btm, sepConj_assoc]
    ac_nf at hpre ⊢
  refine h.mono_outcome x (btm ∗ R) s0 hpc hrun hpre' hsp ?_
  rintro sf (⟨hret, hcc, hq⟩ | ⟨hpan, hq⟩ | ⟨code, _hex, hq⟩ | ⟨_hoom, hq⟩)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [sliceConcat3SpecWithStack, sliceConcat3Spec,
      stackAt_extHookStack_eq_concatStack, btm, sepConj_assoc] at hq ⊢
    ac_nf at hq ⊢
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [sliceConcat3SpecWithStack, sliceConcat3Spec] at hq ⊢
    exact allowPanic_frame id (by rwa [sepConj_assoc])
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hq).elim

/-- `Concat<u8>::concat [local#2]` meets `sliceConcat3Spec A`. -/
theorem slice_concat_3_spec_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ChainProofs.sliceConcatName)
      (sliceConcat3Spec A) := by
  refine sliceConcat3Spec_of_withStack (subroutine_ok_of_withOptInv_none ?_)
  exact slice_concat_3_opt_ok (hookStack := allocHookStack) (by decide)
    (shim_ok_opt_of_contracts hA (hookStack := allocHookStack) (by fnoff_eq))
    (alloc_ok_opt_of_contracts hA (by fnoff_eq))
    (session_memcpy_bytesAt_opt_ok_at
      (memcpy_ok_opt_of_contracts hA (hookStack := allocHookStack) (by fnoff_eq))
      (memcpy_ro_ok_opt_of_hookSat hRO (hookStack := allocHookStack) (by fnoff_eq)))

/-- `Concat<u8>::concat [local#2]` meets `(sliceConcat3SpecXA A).inImage img`. -/
theorem slice_concat_3_spec_ok_ext_roX {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : MemcpyROOkExtX img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ChainProofs.sliceConcatName)
      ((sliceConcat3SpecXA A).inImage img) :=
  slice_concat_3_opt_ok (A := A) (b := img.base) (ext := ext)
    (hookStack := extHookStack) (img? := some img) (by decide)
    (shim_ok_at2_ext_x hA (name := concat2Name)
      (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
        "__rustc::__rust_no_alloc_shim_is_unstable_v2") (by fnoff_eq))
    (alloc_ok_at_norm_ext_x hA (name := concat2Name)
      (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]"
        "__rustc::__rust_alloc") (by fnoff_eq))
    (session_memcpy_bytesAt_opt_ok_at (hookStack := extHookStack) (img? := some img)
      (memcpy_ok_at2_ext_x hA (name := concat2Name)
        (k := ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")
        (by fnoff_eq))
      (session_memcpy_region_ro_ok_at_x_of_roX hRO concat2Name
        (ls_rel% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" "memcpy")
        (by fnoff_eq)))

theorem slice_concat_3_spec_ok_ext_xa {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr ChainProofs.sliceConcatName)
      ((sliceConcat3SpecXA A).inImage img) :=
  slice_concat_3_spec_ok_ext_roX hA (memcpyROOkExtX_of_hookSat hRO)

theorem slice_concat_3_ok_x_roX {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : MemcpyROOkExtX img ext) :
    SliceConcat3OkXA img A ext :=
  slice_concat_3_spec_ok_ext_roX hA hRO

theorem slice_concat_3_ok_x_xa {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    SliceConcat3OkXA img A ext :=
  slice_concat_3_spec_ok_ext_xa hA hRO

theorem slice_concat_3_ok_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName sessionMemcpyRegionROSpec) :
    SliceConcat3OkX img A ext :=
  subroutine_ok_inImage img (slice_concat_3_spec_ok_ext hA hRO)

theorem slice_concat_3_ok_x_tripleRatchetExterns {img : Obj.Image} (C : Crypto) {A : RustAlloc}
    (ctl : BitVec 64) {abs : String → Option (State → State)} (hA : AllocHooks A abs) :
    SliceConcat3OkX img A (tripleRatchetExterns C ctl abs) :=
  slice_concat_3_ok_x (AllocContracts.of_tripleRatchetProgAt img.base C A ctl abs hA)
    (hookSat_memcpy_ro_tripleRatchetExterns C ctl abs)

/-- `slice_concat_3_spec_ok_ext` from 4 KiB `HookSat` contracts. -/
theorem slice_concat_3_spec_ok_ext_withStack {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext shimName (session2ShimSpecWithStack allocHookStack))
    (halloc : HookSat ext allocName (rustAllocSpecWithStack A allocHookStack))
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack))
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr ChainProofs.sliceConcatName)
      (sliceConcat3Spec A) := by
  refine sliceConcat3Spec_of_withStack (subroutine_ok_of_withOptInv_none ?_)
  exact slice_concat_3_opt_ok (hookStack := allocHookStack) (by decide)
    (shim_withStack_ok_opt_of_hookSat hshim (by fnoff_eq))
    (alloc_withStack_ok_opt_of_hookSat halloc (by fnoff_eq))
    (session_memcpy_bytesAt_opt_ok_at
      (memcpy_withStack_ok_opt_of_hookSat hmc (by fnoff_eq))
      (memcpy_ro_withStack_ok_opt_of_hookSat hRO (by fnoff_eq)))

theorem slice_concat_3_ok_x_withStack {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext shimName (session2ShimSpecWithStack allocHookStack))
    (halloc : HookSat ext allocName (rustAllocSpecWithStack A allocHookStack))
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack))
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack)) :
    SliceConcat3OkX img A ext :=
  subroutine_ok_inImage img (slice_concat_3_spec_ok_ext_withStack hshim halloc hmc hRO)

/-- `SliceConcat3OkX` from 0-stack `noAllocShimSpec` and `rustAllocSpec A`. -/
theorem slice_concat_3_ok_x_of_hooks {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : HookSat ext shimName noAllocShimSpec)
    (halloc : HookSat ext allocName (rustAllocSpec A))
    (hmc : HookSat ext memcpyName (session2MemcpySpecWithStack allocHookStack))
    (hRO : HookSat ext memcpyName (sessionMemcpyRegionROSpecWithStack allocHookStack)) :
    SliceConcat3OkX img A ext := by
  refine subroutine_ok_inImage img (sliceConcat3Spec_of_withStack (subroutine_ok_of_withOptInv_none ?_))
  exact slice_concat_3_opt_ok (hookStack := allocHookStack) (by decide)
    (shim_ok_opt_of_noAllocShim_hookSat hshim (by fnoff_eq))
    (alloc_withStack_ok_opt_of_hookSat halloc (by fnoff_eq))
    (session_memcpy_bytesAt_opt_ok_at
      (memcpy_withStack_ok_opt_of_hookSat hmc (by fnoff_eq))
      (memcpy_ro_withStack_ok_opt_of_hookSat hRO (by fnoff_eq)))

/-! ## Relocatable Contracts (Block 386) -/

private theorem sessionMemcpyRegionROWithStack_of_ro {prog : Program} {addr : BitVec 64}
    (hro : subroutine_ok prog addr sessionMemcpyRegionROSpec) (hookStack : Nat) :
    subroutine_ok prog addr (sessionMemcpyRegionROSpecWithStack hookStack) := by
  have h := subroutine_ok_withStack_of_subroutine_ok hro hookStack
  refine subroutine_ok_outcome_intro fun ⟨dst, src, bs⟩ R s0 hpc hrun hpre hal => ?_
  have hpre' : s0.mem ⊨ (withStack sessionMemcpyRegionROSpec hookStack).pre (dst, src, bs) s0 ∗ R := by
    dsimp only [withStack, sessionMemcpyRegionROSpec, sessionMemcpyRegionROSpecWithStack] at hpre ⊢
    simpa only [sepConj_assoc] using hpre
  refine h.mono_outcome (dst, src, bs) R s0 hpc hrun hpre' hal ?_
  rintro sf (⟨hret, hcc, hpost⟩ | hpan | hex)
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStack, sessionMemcpyRegionROSpec, sessionMemcpyRegionROSpecWithStack] at hpost ⊢
    simpa only [sepConj_assoc] using hpost
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

private theorem session_memcpy_bytesAt_ok_at {hookStack : Nat}
    {prog : Program} {addr : BitVec 64}
    (hmc : subroutine_ok prog addr (session2MemcpySpecWithStack hookStack))
    (hmc_ro : subroutine_ok prog addr (sessionMemcpyRegionROSpecWithStack hookStack))
    (ro : Bool) :
    subroutine_ok prog addr (sessionMemcpyBytesAtSpecWithStack hookStack ro) :=
  subroutine_ok_of_withOptInv_none
    (session_memcpy_bytesAt_opt_ok_at
      (subroutine_ok_withOptInv_none_of hmc)
      (subroutine_ok_withOptInv_none_of hmc_ro) ro)

set_option maxHeartbeats 1600000 in
/-- Block 386 meets `sliceConcat2SpecWithStack A hookStack` given callee hook contracts. -/
theorem slice_concat_2_withStack_placed_ok_of_hooks [lsmpl : LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hmc_any : ∀ ro, subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrMemcpySym) (sessionMemcpyBytesAtSpecWithStack hookStack ro)) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat2SpecWithStack A hookStack) := by
  simp only [sliceConcat2SpecWithStack, memRegion_24, stackAt_concat_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hpanic : ((blkPC_386).rebase (blkPl_386).base H).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1⟩ := x
  dsimp only at *
  have hmax : bs0.length + bs1.length < 2 ^ 63 := ‹_›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have htot_lt63 : bs1.length + bs0.length < 2 ^ 63 := by omega
  have htot_lt64 : bs1.length + bs0.length < 2 ^ 64 := by omega
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have hadd_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add]
  have hsub_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length))[63] = false :=
    ofNat_getElem_63_false (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi1 : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have h0_eq : bs0 = [] ∨ 0 < bs0.length := by cases bs0 <;> simp
  have h1_eq : bs1 = [] ∨ 0 < bs1.length := by cases bs1 <;> simp
  rcases h0_eq with rfl | hpos0 <;> rcases h1_eq with rfl | hpos1
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.nil_append] at *
    apply SepWPp.of_sepWP_ret; wp_steps
    apply SepWP.fold (vecU8_of_zero A outVec) (by sep_focus); wp_done
  ·
    simp only [List.length_nil, Nat.zero_add, BitVec.ofNat_eq_ofNat, List.nil_append] at *
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk bs1.length 1 := ⟨hpos1, hpow1, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro1); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs1 hpos1 hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have hlay : LayoutOk bs0.length 1 := ⟨hpos0, hpow1, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro0); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs0 hpos0 hmax hoom) (by sep_focus)
      wp_done
  ·
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk (bs0.length + bs1.length) 1 := ⟨by omega, hpow1, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro0); wp_steps; wp_apply using (hmc_any ro1); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs1).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs1
        (by omega) hmax hoom) (by sep_focus)
      wp_done

theorem slice_concat_2_withStack_placed_ok [lsmpl : LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hge : hookStack ≥ allocHookStack)
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat2SpecWithStack A hookStack) :=
  slice_concat_2_withStack_placed_ok_of_hooks hhook h_panic
    (session2ShimWithStack_of_noAllocShim hookStack (spqr_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (spqr_hook_ok_of_mem halloc) hge (by omega))
    (session_memcpy_bytesAt_ok_at
      (session2MemcpyWithStack_of_framelessMemcpy hookStack (spqr_hook_ok_of_mem hmemcpy))
      (sessionMemcpyRegionROWithStack_of_ro (spqr_hook_ok_of_mem hRO) hookStack))

/-- Block 386 meets `ChainProofs.sliceConcat2Spec A` under `HookSat`. -/
theorem slice_concat_2_placed_ok [lsmpl : LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (ChainProofs.sliceConcat2Spec A) :=
  sliceConcat2Spec_of_withStack
    (slice_concat_2_withStack_placed_ok (hookStack := allocHookStack) (by decide) (by decide)
      h_panic hshim halloc hmemcpy hRO)

/-- Block 386 meets `sliceConcat2SpecXA A` under `HookSat`. -/
theorem slice_concat_2_placed_ok_xa [lsmpl : LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat2SpecXA A) :=
  slice_concat_2_withStack_placed_ok (hookStack := extHookStack) (by decide) (by decide)
    h_panic hshim halloc hmemcpy hRO

set_option maxHeartbeats 3200000 in
/-- Block 386 meets `sliceConcat3SpecWithStack A hookStack` given callee hook contracts. -/
theorem slice_concat_3_withStack_placed_ok_of_hooks [lsmpl : LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrRustNoAllocShimSym) (session2ShimSpecWithStack hookStack))
    (halloc : subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrRustAllocSym) (rustAllocSpecWithStack A hookStack))
    (hmc_any : ∀ ro, subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (lsρ spqrMemcpySym) (sessionMemcpyBytesAtSpecWithStack hookStack ro)) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat3SpecWithStack A hookStack) := by
  simp only [sliceConcat3SpecWithStack, memRegion_24, stackAt_concat_gen _ hhook,
    sepExists_sepConj_left, sepExists_sepConj_right]
  have hpanic : ((blkPC_386).rebase (blkPl_386).base H).externAt?
      (lsρ spqrHandleErrorSym) = some Rust.panicked :=
    (spqr_externAt?_of_mem).trans h_panic
  wpp_init x s0
  obtain ⟨outVec, slicesA, ro0, p0, bs0, ro1, p1, bs1, ro2, p2, bs2⟩ := x
  dsimp only at *
  have hmax : bs0.length + bs1.length + bs2.length < 2 ^ 63 := ‹_›
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have h0_lt64 : bs0.length < 2 ^ 64 := by omega
  have h1_lt64 : bs1.length < 2 ^ 64 := by omega
  have h2_lt64 : bs2.length < 2 ^ 64 := by omega
  have h0_le64 : bs0.length ≤ 2 ^ 64 := by omega
  have h1_le64 : bs1.length ≤ 2 ^ 64 := by omega
  have h2_le64 : bs2.length ≤ 2 ^ 64 := by omega
  have hadd10_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd201_bv : BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 (bs0.length + bs1.length) =
      BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd20_bv : BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs0.length + bs2.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd21_bv : BitVec.ofNat 64 bs2.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs1.length + bs2.length) := by rw [← BitVec.ofNat_add, Nat.add_comm]
  have hadd01_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 (bs0.length + bs1.length) := by rw [← BitVec.ofNat_add]
  have hadd02_bv : BitVec.ofNat 64 bs0.length + BitVec.ofNat 64 bs2.length =
      BitVec.ofNat 64 (bs0.length + bs2.length) := by rw [← BitVec.ofNat_add]
  have hadd12_bv : BitVec.ofNat 64 bs1.length + BitVec.ofNat 64 bs2.length =
      BitVec.ofNat 64 (bs1.length + bs2.length) := by rw [← BitVec.ofNat_add]
  have hadd012_bv : BitVec.ofNat 64 (bs0.length + bs1.length) + BitVec.ofNat 64 bs2.length =
      BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) := by rw [← BitVec.ofNat_add]
  have hsub0_bv : BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 (bs1.length + bs2.length) := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub01_bv : BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) -
      BitVec.ofNat 64 (bs0.length + bs1.length) = BitVec.ofNat 64 bs2.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub0_01_bv : BitVec.ofNat 64 (bs0.length + bs1.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs1.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub0_02_bv : BitVec.ofNat 64 (bs0.length + bs2.length) - BitVec.ofNat 64 bs0.length =
      BitVec.ofNat 64 bs2.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h0_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hsub1_bv : BitVec.ofNat 64 (bs1.length + bs2.length) - BitVec.ofNat 64 bs1.length =
      BitVec.ofNat 64 bs2.length := by
    apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_sub_of_le]
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt h1_lt64, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]; omega
    · simp only [BitVec.le_def, BitVec.toNat_ofNat]; omega
  have hcs1 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hcs2 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs2.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hcs02 : (BitVec.ofNat 64 (bs0.length + bs2.length)).ult (BitVec.ofNat 64 bs2.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hcs12 : (BitVec.ofNat 64 (bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs2.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hbit63 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).getLsbD 63 = false :=
    ofNat_getLsbD_63_false (by omega)
  have helem63 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length))[63] = false :=
    ofNat_getElem_63_false (by omega)
  have htot_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).toNat =
      bs0.length + bs1.length + bs2.length := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h01_toNat : (BitVec.ofNat 64 (bs0.length + bs1.length)).toNat = bs0.length + bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h02_toNat : (BitVec.ofNat 64 (bs0.length + bs2.length)).toNat = bs0.length + bs2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h12_toNat : (BitVec.ofNat 64 (bs1.length + bs2.length)).toNat = bs1.length + bs2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have h0_toNat : (BitVec.ofNat 64 bs0.length).toNat = bs0.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0_lt64]
  have h1_toNat : (BitVec.ofNat 64 bs1.length).toNat = bs1.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1_lt64]
  have h2_toNat : (BitVec.ofNat 64 bs2.length).toNat = bs2.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2_lt64]
  have hhi0 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi0_01 : (BitVec.ofNat 64 (bs0.length + bs1.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi0_02 : (BitVec.ofNat 64 (bs0.length + bs2.length)).ult (BitVec.ofNat 64 bs0.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi0_self : (BitVec.ofNat 64 bs0.length).ult (BitVec.ofNat 64 bs0.length) = false :=
    ProofLib.bitvec_ult_self _
  have hhi1 : (BitVec.ofNat 64 (bs1.length + bs2.length)).ult (BitVec.ofNat 64 bs1.length) = false :=
    ofNat_ult_of_le (by omega) (by omega)
  have hhi1_self : (BitVec.ofNat 64 bs1.length).ult (BitVec.ofNat 64 bs1.length) = false :=
    ProofLib.bitvec_ult_self _
  have hhi2 : (BitVec.ofNat 64 bs2.length).ult (BitVec.ofNat 64 bs2.length) = false :=
    ProofLib.bitvec_ult_self _
  have h0_eq : bs0 = [] ∨ 0 < bs0.length := by cases bs0 <;> simp
  have h1_eq : bs1 = [] ∨ 0 < bs1.length := by cases bs1 <;> simp
  have h2_eq : bs2 = [] ∨ 0 < bs2.length := by cases bs2 <;> simp
  rcases h0_eq with rfl | hpos0 <;> rcases h1_eq with rfl | hpos1 <;> rcases h2_eq with rfl | hpos2
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    apply SepWPp.of_sepWP_ret; wp_steps
    apply SepWP.fold (vecU8_of_zero A outVec) (by sep_focus); wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat,
      List.nil_append, List.append_nil] at *
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have hlay : LayoutOk bs2.length 1 := ⟨hpos2, hpow1, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro2); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs2 hpos2 hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat,
      List.nil_append, List.append_nil] at *
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk bs1.length 1 := ⟨hpos1, hpow1, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro1); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs1 hpos1 hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.zero_add, BitVec.ofNat_eq_ofNat, List.nil_append] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs1.length + bs2.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have hlay : LayoutOk (bs1.length + bs2.length) 1 := ⟨by omega, hpow1, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs1.length bs2.length (by omega)]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro1); wp_steps; wp_apply using (hmc_any ro2); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs1 bs2).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs1 bs2
        (by omega) hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have hlay : LayoutOk bs0.length 1 := ⟨hpos0, hpow1, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro0); wp_steps
      apply SepWP.fold (vecU8_of_pos A outVec (sf_1.readReg64 Reg.x0) bs0 hpos0 hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs2.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have hlay : LayoutOk (bs0.length + bs2.length) 1 := ⟨by omega, hpow1, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs2.length (by omega)]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro0); wp_steps; wp_apply using (hmc_any ro2); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs2).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs2
        (by omega) hmax hoom) (by sep_focus)
      wp_done
  ·
    simp only [List.length_nil, Nat.add_zero, BitVec.ofNat_eq_ofNat, List.append_nil] at *
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have hlay : LayoutOk (bs0.length + bs1.length) 1 := ⟨by omega, hpow1, by omega⟩
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro0); wp_steps; wp_apply using (hmc_any ro1); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append (sf_1.readReg64 Reg.x0) bs0 bs1).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs1
        (by omega) hmax hoom) (by sep_focus)
      wp_done
  ·
    have htot_ne0 : (BitVec.ofNat 64 (bs0.length + bs1.length + bs2.length) == 0#64) = false :=
      ofNat_beq_zero_false (by omega) (by omega)
    have h0_ne0 : (BitVec.ofNat 64 bs0.length == 0#64) = false := ofNat_beq_zero_false hpos0 h0_lt64
    have h1_ne0 : (BitVec.ofNat 64 bs1.length == 0#64) = false := ofNat_beq_zero_false hpos1 h1_lt64
    have h2_ne0 : (BitVec.ofNat 64 bs2.length == 0#64) = false := ofNat_beq_zero_false hpos2 h2_lt64
    have hlay : LayoutOk (bs0.length + bs1.length + bs2.length) 1 := ⟨by omega, hpow1, by omega⟩
    have ⟨hlay_pos, _, hlay_max⟩ := hlay
    apply SepWPp.of_sepWP (mid := (blkPl_386).base + 108#64)
    wp_steps; wp_apply; wp_steps; wp_apply; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom : sf_1.readReg64 Reg.x0 = 0#64
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_true, sepConj_assoc]; rw [pull_alloc_pure]
      refine SepWPp.pure_elim fun htrace => ?_
      apply SepWPp.of_sepWP (mid := lsρ spqrHandleErrorSym)
      wp_steps; apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
      simpa only [sepConj_assoc] using
        allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
    · simp only [hoom, BitVec.ofNat_eq_ofNat, ite_false, sepConj_assoc]
      have hoom_beq : (sf_1.readReg64 Reg.x0 == 0#64) = false := beq_false_of_ne hoom
      rw [pull_alloc_pure]; refine SepWPp.pure_elim fun ⟨_, htr1⟩ => ?_
      have htr_sf1 : sf_1.trace = s0.trace := by rw [htr1]; simp only [wp_norm, arm64_norm, *]
      rw [ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) (bs0.length + bs1.length) bs2.length (by omega),
        ProofLib.memRegion_split (sf_1.readReg64 Reg.x0) bs0.length bs1.length (by omega)]
      apply SepWPp.of_sepWP_ret
      wp_steps; wp_apply using (hmc_any ro0); wp_steps; wp_apply using (hmc_any ro1); wp_steps
      wp_apply using (hmc_any ro2); wp_steps
      apply SepWP.fold (Entails.of_eq (pointsToBytes_append3 (sf_1.readReg64 Reg.x0) bs0 bs1 bs2).symm) (by sep_focus)
      apply SepWP.fold (vecU8_of_append3_pos A outVec (sf_1.readReg64 Reg.x0) bs0 bs1 bs2
        (by omega) hmax hoom) (by sep_focus)
      wp_done

theorem slice_concat_3_withStack_placed_ok [lsmpl : LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)} {hookStack : Nat}
    (hge : hookStack ≥ allocHookStack)
    (hhook : hookStack + 12 * 8 ≤ 2 ^ 64)
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat3SpecWithStack A hookStack) :=
  slice_concat_3_withStack_placed_ok_of_hooks hhook h_panic
    (session2ShimWithStack_of_noAllocShim hookStack (spqr_hook_ok_of_mem hshim))
    (rustAllocWithStack_of_rustAlloc (spqr_hook_ok_of_mem halloc) hge (by omega))
    (session_memcpy_bytesAt_ok_at
      (session2MemcpyWithStack_of_framelessMemcpy hookStack (spqr_hook_ok_of_mem hmemcpy))
      (sessionMemcpyRegionROWithStack_of_ro (spqr_hook_ok_of_mem hRO) hookStack))

/-- Block 386 meets `sliceConcat3Spec A` under `HookSat`. -/
theorem slice_concat_3_placed_ok [lsmpl : LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat3Spec A) :=
  sliceConcat3Spec_of_withStack
    (slice_concat_3_withStack_placed_ok (hookStack := allocHookStack) (by decide) (by decide)
      h_panic hshim halloc hmemcpy hRO)

/-- Block 386 meets `sliceConcat3SpecXA A` under `HookSat`. -/
theorem slice_concat_3_placed_ok_xa [lsmpl : LibsignalPlacement]
    {A : RustAlloc} {H : String → Option (State → State)}
    (h_panic : H spqrHandleErrorSym = some Rust.panicked)
    (hshim : HookSat H spqrRustNoAllocShimSym noAllocShimSpec)
    (halloc : HookSat H spqrRustAllocSym (rustAllocSpec A))
    (hmemcpy : HookSat H spqrMemcpySym framelessMemcpySpec)
    (hRO : HookSat H spqrMemcpySym sessionMemcpyRegionROSpec) :
    subroutine_ok ((blkPC_386).rebase (blkPl_386).base H)
      (blkPl_386).base (sliceConcat3SpecXA A) :=
  slice_concat_3_withStack_placed_ok (hookStack := extHookStack) (by decide) (by decide)
    h_panic hshim halloc hmemcpy hRO

end CryptoVerification.SpqrV1.Alloc

namespace CryptoVerification.SpqrV1.ChainProofs

export Alloc (SliceConcat3Ghost sliceConcat3Spec SliceConcat3OkX
  slice_concat_3_spec_ok_ext slice_concat_3_ok_x slice_concat_3_ok_x_tripleRatchetExterns
  slice_concat_3_spec_ok_ext_withStack slice_concat_3_ok_x_withStack slice_concat_3_ok_x_of_hooks
  slice_concat_2_placed_ok slice_concat_2_placed_ok_xa
  slice_concat_3_placed_ok slice_concat_3_placed_ok_xa)

end CryptoVerification.SpqrV1.ChainProofs
