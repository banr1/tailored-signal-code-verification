/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.IfaceBudget
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
public import LibsignalBinary.Proofs.Placed.GenLsBlock
public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.Defs
import LibsignalBinary.Proofs.Common.SharedHelpers
import ProofLib.SepLogic.WPp

/-!
# `VmPreserved` Specifications and Lifting Bridges for `ProtoRepr`

Defines `withVmPreserved`, block-subset code-loading combinators (`LsBlocksCodeLoaded`,
`ls_subroutine_ok_blocks_vmPreserved`, `ls_subroutine_ok_plain_vmPreserved`), and
`VmPreserved`-augmented `Epoch::encoded_len` and `Chain::encoded_len` Hoare contracts for
zero-allocation budget transport.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget

open Arm64 ProofLib SepProp
open LibsignalBinary.Heap (VmPreserved)
open CryptoVerification
  (LibsignalPlacement LibsignalHooks IsLsBlockProg LibsignalCodeLoaded LibsignalRoLoaded
   lsmpl withLsCodeLoaded extract_withLsCodeLoaded libsignalSessionLib libsignalMutatedBlocks
   ls_externAt?_blockProgram_eq_of_externs_eq lsBlocksTree blockLib_eq_of_lsBlocksTree)
open CryptoVerification.RustHeap (RustAlloc)
open CryptoVerification.SpqrV1.ProtoRepr
  (EpochEncodedLenPinnedGhost EpochEncodedLenGhost
   ChainEncodedLenPinnedGhost ChainEncodedLenGhost)

/-! ## 1. `withVmPreserved` Combinator & Block-Subset `VmPreserved` Lifting Bridges -/

/-- Strengthen `spec : Spec α` with `⌜VmPreserved s0 sf⌝` in `post` while preserving `pre`,
`onPanic`, `onExit`, and `onOom` verbatim (definitionally equal to `SpecBudget.withVmPreserved`). -/
def withVmPreserved {α : Type} (spec : Spec α) : Spec α :=
  { spec with post := fun x s0 sf => ⌜VmPreserved s0 sf⌝ ∗ spec.post x s0 sf }

/-- Forget `⌜VmPreserved s0 sf⌝` on a `subroutine_ok` witness. -/
theorem subroutine_ok_of_withVmPreserved {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (h : subroutine_ok prog entry (withVmPreserved spec)) :
    subroutine_ok prog entry spec :=
  subroutine_ok_mono h (fun _ _ _ hp => hp) fun _ _ _ _ hq => by
    dsimp only [withVmPreserved] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    exact hq.2

/-- Add `⌜LibsignalRoLoaded pl s0.mem⌝` to `spec`'s precondition (definitionally equal to
`CryptoVerification.Cli.SpqrV1.ProtoRepr.withLsRoLoaded`). -/
abbrev withLsRoLoaded {α : Type} (pl : Obj.MultiPlacement) (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LibsignalRoLoaded pl s0.mem⌝ }

/-- Code-loaded predicate restricted to a finite list `blks` of `libsignalSessionLib` block indices. -/
def LsBlocksCodeLoaded (blks : List Nat) (pl : Obj.MultiPlacement) (m : Memory) : Prop :=
  ∀ j ∈ blks, ∀ (X O : String → Option (State → State)) (svc : State → State),
    (libsignalSessionLib.blockProgram pl j X O svc).CodeLoaded m

/-- Add `⌜LsBlocksCodeLoaded blks pl s0.mem⌝` to `spec`'s precondition. -/
abbrev withLsBlocksCodeLoaded {α : Type} (blks : List Nat) (pl : Obj.MultiPlacement)
    (spec : Spec α) : Spec α :=
  { spec with pre := fun x s0 => spec.pre x s0 ∗ ⌜LsBlocksCodeLoaded blks pl s0.mem⌝ }

theorem LsBlocksCodeLoaded.of_keepsFrozen {blks : List Nat} {pl : Obj.MultiPlacement}
    {m m' : Memory} (hcl : LsBlocksCodeLoaded blks pl m) (hk : m.KeepsFrozen m') :
    LsBlocksCodeLoaded blks pl m' :=
  fun j hj X O svc => (hcl j hj X O svc).of_keepsFrozen hk

theorem LsBlocksCodeLoaded.of_lsCodeLoaded {blks : List Nat} {pl : Obj.MultiPlacement}
    {m : Memory}
    (hvalid : blks.all (fun j => decide (j < 619) && !(decide (j ∈ libsignalMutatedBlocks))) = true)
    (hcl : LibsignalCodeLoaded pl m) : LsBlocksCodeLoaded blks pl m := by
  intro j hj X O svc
  have hjv := List.all_eq_true.mp hvalid j hj
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not] at hjv
  exact hcl j (Nat.lt_of_lt_of_le hjv.1 (by decide)) (by simp [hjv.2]) X O svc

theorem ls_subroutine_ok_of_block_in {α : Type} [LibsignalPlacement]
    {callerProg calleeProg : Program} {blks : List Nat} {i j : Nat} {H : LibsignalHooks}
    [hcaller : IsLsBlockProg callerProg i H] [hcallee_prog : IsLsBlockProg calleeProg j H]
    {entry : BitVec 64} {spec : Spec α}
    (hj : j ∈ blks)
    (hcallee : subroutine_ok calleeProg entry spec) :
    subroutine_ok callerProg entry (withLsBlocksCodeLoaded blks lsmpl spec) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [withLsBlocksCodeLoaded] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hcl0, hpre'⟩
  have hQL : calleeProg.CodeLoaded s0.mem :=
    hcallee_prog.eq_blockProgram ▸ hcl0 j hj H (fun _ => none) Syscall.standard
  obtain ⟨sf, hstepsQ, hout, _⟩ := hcallee.no_fault_before_outcome x R s0 hpc hrun hpre' hsp hQL
  have hext : ∀ pc, calleeProg.externAt? pc = callerProg.externAt? pc := fun pc => by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee_prog.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : calleeProg.svc = callerProg.svc := by
    rw [hcallee_prog.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext hsvc hstepsQ) (reaches_outcome.of_outcome hout)

def checkBytesNoMsr (blk : Obj.CodeBlock) : Nat → List (BitVec 8) → Bool
  | _, [] => true
  | off, b0 :: b1 :: b2 :: b3 :: rest =>
    let w := Obj.wordOfBytesLE [b0, b1, b2, b3] 0
    (match blk.relocAt? off with
     | none => (w &&& 0xffff_ffe0#32) != 0xd51b_d040#32
     | some r => VerifiedLibraries.RustStd.checkRelocWordNoSvc0 w r) &&
    checkBytesNoMsr blk (off + 4) rest
  | _, _ => false

def checkBlockNoSvcNoMsr (blk : Obj.CodeBlock) : Bool :=
  VerifiedLibraries.RustStd.checkBlockNoSvc0 blk && checkBytesNoMsr blk 0 blk.code

noncomputable def checkTreeBlocksNoSvcNoMsr (blks : List Nat) : Bool :=
  blks.all fun j =>
    match lsBlocksTree.getFast? j with
    | some blk => checkBlockNoSvcNoMsr blk
    | none => false

private theorem checkBytesNoMsr_wordOfBytesLE (blk : Obj.CodeBlock) :
    ∀ (k off : Nat) (bs : List (BitVec 8)),
      checkBytesNoMsr blk off bs = true → 4 * k + 4 ≤ bs.length →
      (let w := Obj.wordOfBytesLE bs (4 * k)
       match blk.relocAt? (off + 4 * k) with
       | none => (w &&& 0xffff_ffe0#32) != 0xd51b_d040#32
       | some r => VerifiedLibraries.RustStd.checkRelocWordNoSvc0 w r) = true
  | 0, _, bs, hchk, hlen => by
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: _ =>
      simp only [checkBytesNoMsr, Bool.and_eq_true] at hchk; simpa [Obj.wordOfBytesLE] using hchk.1
  | k + 1, off, bs, hchk, hlen => by
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [checkBytesNoMsr, Bool.and_eq_true] at hchk
      have ih := checkBytesNoMsr_wordOfBytesLE blk k (off + 4) rest hchk.2
        (by simp only [List.length_cons] at hlen; omega)
      have h0 : 4 * (k + 1) = 4 * k + 4 := by omega
      have heq_w : Obj.wordOfBytesLE (b0 :: b1 :: b2 :: b3 :: rest) (4 * (k + 1)) =
          Obj.wordOfBytesLE rest (4 * k) := by simp only [Obj.wordOfBytesLE, h0]; rfl
      have heq_off : off + 4 * (k + 1) = off + 4 + 4 * k := by omega
      simpa [heq_w, heq_off] using ih

private theorem not_isMsrTpidrEl0Word_of_top6 {v : BitVec 32}
    (h : v &&& 0xfc00_0000#32 ≠ 0xd400_0000#32) :
    Arm64.isMsrTpidrEl0Word v = false := by
  cases hm : Arm64.isMsrTpidrEl0Word v with
  | false => rfl
  | true =>
    unfold Arm64.isMsrTpidrEl0Word at hm; rw [beq_iff_eq] at hm
    have htop : (v &&& 0xffff_ffe0#32) &&& 0xfc00_0000#32 = 0xd400_0000#32 := by rw [hm]; decide
    rw [BitVec.and_assoc] at htop
    have hmask : (0xffff_ffe0#32 : BitVec 32) &&& 0xfc00_0000#32 = 0xfc00_0000#32 := by decide
    rw [hmask] at htop; exact False.elim (h htop)

private theorem not_isMsrTpidrEl0Word_of_b26_false {v : BitVec 32}
    (h : v.getLsbD 26 = false) : Arm64.isMsrTpidrEl0Word v = false := by
  cases hm : Arm64.isMsrTpidrEl0Word v with
  | false => rfl
  | true =>
    unfold Arm64.isMsrTpidrEl0Word at hm; rw [beq_iff_eq] at hm
    have hb := congrArg (fun x => x.getLsbD 26) hm
    rw [BitVec.getLsbD_and, h, Bool.false_and] at hb
    exact absurd hb.symm (by decide)

private theorem not_isMsrTpidrEl0Word_of_b29_true {v : BitVec 32}
    (h : v.getLsbD 29 = true) : Arm64.isMsrTpidrEl0Word v = false := by
  cases hm : Arm64.isMsrTpidrEl0Word v with
  | false => rfl
  | true =>
    unfold Arm64.isMsrTpidrEl0Word at hm; rw [beq_iff_eq] at hm
    have hb := congrArg (fun x => x.getLsbD 29) hm
    rw [BitVec.getLsbD_and, h, Bool.true_and] at hb
    exact absurd hb (by decide)

private theorem mask_top6_shiftLeft_10_local (x : BitVec 32) :
    ((x &&& 0xfff#32) <<< 10) &&& 0xfc00_0000#32 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : (!decide (i < 10) && (0xfff#32).getLsbD (i - 10) && (0xfc00_0000#32).getLsbD i) = false := by
    revert hi; revert i; decide
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_zero]
  simp only [hi, decide_true, Bool.true_and]
  cases h1 : (!decide (i < 10)) <;> cases h2 : (0xfff#32).getLsbD (i - 10) <;>
    cases h3 : (0xfc00_0000#32).getLsbD i <;> (rw [h1, h2, h3] at hm; first | contradiction | simp)

private theorem branchWord_top6_eq (w : BitVec 32) (place target : BitVec 64) :
    Obj.branchWord w place target &&& 0xfc00_0000#32 = w &&& 0xfc00_0000#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hf : ((0x03ff_ffff#32).getLsbD i && (0xfc00_0000#32).getLsbD i) = false := by
    revert hi; revert i; decide
  dsimp only [Obj.branchWord]
  rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and]
  cases h1 : (0x03ff_ffff#32).getLsbD i <;> cases h2 : (0xfc00_0000#32).getLsbD i <;>
    (rw [h1, h2] at hf; first | contradiction | simp)

private theorem lo12Word_top6_eq (scale : Nat) (w : BitVec 32) (target : BitVec 64) :
    Obj.lo12Word scale w target &&& 0xfc00_0000#32 = w &&& 0xfc00_0000#32 := by
  dsimp only [Obj.lo12Word]
  rw [BitVec.and_or_distrib_right, mask_top6_shiftLeft_10_local, BitVec.or_zero, BitVec.and_assoc]; rfl

private theorem ldrToAddWord_top6_ne (w : BitVec 32) :
    Obj.ldrToAddWord w &&& 0xfc00_0000#32 ≠ 0xd400_0000#32 := by
  intro h; have hb := congrArg (fun v => v.getLsbD 26) h; simp [Obj.ldrToAddWord] at hb

private theorem adrpWord_b26_false {w : BitVec 32} (hw26 : w &&& 0x0400_0000#32 = 0#32)
    (place target : BitVec 64) : (Obj.adrpWord w place target).getLsbD 26 = false := by
  have hb26 : w[26] = false := by
    have := congrArg (fun v => v.getLsbD 26) hw26
    simpa [BitVec.getLsbD_eq_getElem (by decide : 26 < 32)] using this
  simp [Obj.adrpWord, Obj.adrpWordOff, BitVec.getLsbD_eq_getElem, hb26]

private theorem patchedWord_not_isMsrTpidrEl0 {blk : Obj.CodeBlock} (pl : Obj.Placement)
    (hchk : checkBlockNoSvcNoMsr blk = true) {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    Arm64.isMsrTpidrEl0Word (blk.patchedWord pl off) = false := by
  unfold checkBlockNoSvcNoMsr VerifiedLibraries.RustStd.checkBlockNoSvc0 at hchk
  simp only [Bool.and_eq_true, List.all_eq_true] at hchk
  rcases hchk with ⟨⟨_, hrelocs⟩, hbytes⟩
  have hoff_eq : 4 * (off / 4) = off := by omega
  have hw_off := checkBytesNoMsr_wordOfBytesLE blk (off / 4) 0 blk.code hbytes (by omega)
  simp only [Nat.zero_add, hoff_eq] at hw_off
  change (match blk.relocAt? off with
    | none => (blk.wordAt off &&& 0xffff_ffe0#32) != 0xd51b_d040#32
    | some r => VerifiedLibraries.RustStd.checkRelocWordNoSvc0 (blk.wordAt off) r) = true at hw_off
  unfold Obj.CodeBlock.patchedWord
  cases hr : blk.relocAt? off with
  | none =>
    rw [hr] at hw_off
    unfold Arm64.isMsrTpidrEl0Word
    exact beq_false_of_ne (bne_iff_ne.mp hw_off)
  | some r =>
    dsimp only; rw [hr] at hw_off; dsimp only at hw_off
    have hrmem : r ∈ blk.relocs := List.mem_of_find?_eq_some hr
    have hksafe := hrelocs r hrmem
    split
    · decide
    · split
      · exact not_isMsrTpidrEl0Word_of_b26_false
          (by simp [Obj.adrWord, Obj.adrWordOff, Obj.adrTemplate, BitVec.getLsbD_eq_getElem])
      · split
        · exact not_isMsrTpidrEl0Word_of_b26_false
            (by simp [Obj.adrWord, Obj.adrWordOff, Obj.adrTemplate, BitVec.getLsbD_eq_getElem])
        · split
          · rename_i _ _ _ hgot
            simp only [Bool.and_eq_true] at hgot
            have hisgot : r.kind.isGotOrTlsIe = true := hgot.1.1
            cases hk : r.kind
            all_goals rw [hk] at hisgot; try contradiction
            · simp [Obj.CodeBlock.patchGotOrTlsIeRelaxed, Obj.nopWord, Arm64.isMsrTpidrEl0Word]
            · dsimp only [Obj.CodeBlock.patchGotOrTlsIeRelaxed]
              exact not_isMsrTpidrEl0Word_of_top6 (by rw [lo12Word_top6_eq]; exact ldrToAddWord_top6_ne _)
            · dsimp only [Obj.CodeBlock.patchGotOrTlsIeRelaxed]
              exact not_isMsrTpidrEl0Word_of_b26_false
                (by simp [Obj.tlsieMovzWord, BitVec.getLsbD_eq_getElem])
            · dsimp only [Obj.CodeBlock.patchGotOrTlsIeRelaxed]
              exact not_isMsrTpidrEl0Word_of_b29_true
                (by simp [Obj.tlsieMovkWord, BitVec.getLsbD_eq_getElem])
          · unfold VerifiedLibraries.RustStd.checkRelocWordNoSvc0 at hw_off
            cases hk : r.kind
            all_goals rw [hk] at hksafe; try contradiction
            all_goals rw [hk] at hw_off; simp only [VerifiedLibraries.RustStd.isTlsdescKind,
              VerifiedLibraries.RustStd.isAdrpRelocKind, Bool.false_or, Bool.true_or,
              Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_eq_true,
              bne_iff_ne, beq_iff_eq] at hw_off
            all_goals dsimp only [Obj.patchRelocWord]
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [branchWord_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [branchWord_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_b26_false (adrpWord_b26_false hw_off.2 _ _)
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [lo12Word_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [lo12Word_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [lo12Word_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [lo12Word_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [lo12Word_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [lo12Word_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_b26_false (adrpWord_b26_false hw_off.2 _ _)
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [lo12Word_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_b26_false (adrpWord_b26_false hw_off.2 _ _)
            · exact not_isMsrTpidrEl0Word_of_top6 (by rw [lo12Word_top6_eq]; exact hw_off)
            · exact not_isMsrTpidrEl0Word_of_b26_false
                (by simp [Obj.tlsdescAdrPage21Word, BitVec.getLsbD_eq_getElem])
            · exact not_isMsrTpidrEl0Word_of_b29_true
                (by simp [Obj.tlsdescLd64Lo12Word, BitVec.getLsbD_eq_getElem])
            · simp [Obj.nopWord, Arm64.isMsrTpidrEl0Word]
            · simp [Obj.nopWord, Arm64.isMsrTpidrEl0Word]

private theorem checkBytesNoMsr_mod4 (blk : Obj.CodeBlock) :
    ∀ (off : Nat) (bs : List (BitVec 8)), checkBytesNoMsr blk off bs = true → bs.length % 4 = 0
  | _, [], _ => rfl
  | _, [_], h | _, [_, _], h | _, [_, _, _], h => by simp [checkBytesNoMsr] at h
  | off, _ :: _ :: _ :: _ :: rest, h => by
    simp only [checkBytesNoMsr, Bool.and_eq_true] at h
    have ih := checkBytesNoMsr_mod4 blk (off + 4) rest h.2; simp only [List.length_cons]; omega

private theorem bytesAllWords_of_drop4_local {pw : BitVec 32 → Bool} :
    ∀ (n : Nat) (bs : List (BitVec 8)), bs.length = 4 * n →
      (∀ k < n, match bs.drop (4 * k) with
        | b0 :: b1 :: b2 :: b3 :: _ => pw (b3 ++ b2 ++ b1 ++ b0) = true | _ => True) →
      Arm64.bytesAllWords pw bs = true
  | 0, bs, hlen, _ => by cases bs with | nil => rfl | cons _ _ => simp at hlen
  | n + 1, bs, hlen, h => by
    match bs with
    | [] => simp at hlen
    | [_] | [_, _] | [_, _, _] => simp at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      have h0 : pw (b3 ++ b2 ++ b1 ++ b0) = true := by simpa using h 0 (Nat.zero_lt_succ n)
      have hrest : Arm64.bytesAllWords pw rest = true :=
        bytesAllWords_of_drop4_local n rest (by simp at hlen; omega) fun k hk => by
          have hk' := h (k + 1) (Nat.succ_lt_succ hk); have heq : 4 * (k + 1) = 4 + 4 * k := by omega
          rw [heq, ← List.drop_drop] at hk'; simpa using hk'
      simp [Arm64.bytesAllWords, h0, hrest]

private theorem blockProgram_rebase_allInstrs_not_isMsrTpidrEl0 (lib : Obj.MultiPlacedLib)
    (mpl : Obj.MultiPlacement) (j : Nat) (hchk : checkBlockNoSvcNoMsr (lib.blockLib j).text = true) :
    ((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)).allInstrs
      (fun i => !i.isMsrTpidrEl0) = true := by
  let prog := (lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let blk := (lib.blockLib j).text
  let pl := lib.blockPlacement mpl j
  have hcode : prog.code = blk.patched pl := rfl
  have hmod4 : blk.code.length % 4 = 0 := by
    unfold checkBlockNoSvcNoMsr at hchk; simp only [Bool.and_eq_true] at hchk
    exact checkBytesNoMsr_mod4 blk 0 blk.code hchk.2
  have hdiv : prog.code.length = 4 * (blk.code.length / 4) := by rw [hcode, Obj.CodeBlock.length_patched]
  refine Program.allInstrs_of_allWords (pw := Arm64.isMsrTpidrEl0Word)
    (fun _ _ hd hpw => by simp [Arm64.decode_not_isMsrTpidrEl0 hd hpw]) ?_
  unfold Program.allWords
  refine bytesAllWords_of_drop4_local (blk.code.length / 4) prog.code hdiv fun k hk => ?_
  have hal : (4 * k) % 4 = 0 := by omega
  have hlen : 4 * k + 4 ≤ blk.code.length := by omega
  have hrw : prog.readWordOff (4 * k) = some (blk.patchedWord pl (4 * k)) :=
    Obj.CodeBlock.readWordOff_patched hcode hal hlen
  unfold Program.readWordOff at hrw; simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hrw
  match hdrop : prog.code.drop (4 * k) with
  | [] | [_] | [_, _] | [_, _, _] => simp [hdrop] at hrw
  | b0 :: b1 :: b2 :: b3 :: _ =>
    rw [hdrop] at hrw; injection hrw with hw; dsimp only
    rw [hw, patchedWord_not_isMsrTpidrEl0 pl hchk hal hlen]; rfl

private theorem blockLib_text_of_checkTree {blks : List Nat}
    (hchk : checkTreeBlocksNoSvcNoMsr blks = true) {j : Nat} (hj : j ∈ blks) :
    checkBlockNoSvcNoMsr (libsignalSessionLib.blockLib j).text = true := by
  unfold checkTreeBlocksNoSvcNoMsr at hchk
  have hj_ok := List.all_eq_true.mp hchk j hj
  cases hget : lsBlocksTree.getFast? j with
  | none => rw [hget] at hj_ok; cases hj_ok
  | some blk =>
    rw [hget] at hj_ok
    have hlib := blockLib_eq_of_lsBlocksTree hget rfl
    have htxt : (libsignalSessionLib.blockLib j).text = blk := congrArg Obj.PlacedLib.text hlib.symm
    rwa [htxt]

private def lsBlocksKeep (blks : List Nat) (pl : Obj.MultiPlacement) (a : BitVec 64) : Bool :=
  blks.any fun j => ProofLib.progKeep (libsignalSessionLib.blockProgram pl j (fun _ => none)) a

private theorem strip_lsBlocksCodeLoaded {blks : List Nat} {pl : Obj.MultiPlacement} {m : Memory}
    (hcl : LsBlocksCodeLoaded blks pl m) :
    LsBlocksCodeLoaded blks pl (ProofLib.stripExecOutside (lsBlocksKeep blks pl) m) := by
  intro j hj X O svc
  have hL := hcl j hj X O svc
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  let Pj := libsignalSessionLib.blockProgram pl j X O svc
  let Pj0 := libsignalSessionLib.blockProgram pl j (fun _ => none)
  have hbase_eq : Pj.base = Pj0.base := rfl
  have hcode_eq : Pj.code = Pj0.code := rfl
  have hsub : Pj0.base + BitVec.ofNat 64 k - Pj0.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep0 : ProofLib.progKeep Pj0 (Pj.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    rw [hbase_eq, hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), ← hcode_eq]
    exact decide_eq_true hk
  have hkeep : lsBlocksKeep blks pl (Pj.base + BitVec.ofNat 64 k) = true :=
    List.any_eq_true.mpr ⟨j, hj, hkeep0⟩
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem option_or_isSome_local {α : Type} (o₁ o₂ : Option α) :
    (o₁.or o₂).isSome = (o₁.isSome || o₂.isSome) := by cases o₁ <;> rfl

private theorem findSome?_isSome_congr_local {α β γ : Type} (l : List α)
    (f : α → Option β) (g : α → Option γ) (h : ∀ x, (f x).isSome = (g x).isSome) :
    (l.findSome? f).isSome = (l.findSome? g).isSome := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.findSome?]
    cases hf : f x <;> cases hg : g x
    · exact ih
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · have hx := h x; rw [hf, hg] at hx; cases hx
    · rfl

private theorem findSome?_ite_map_status_local {α : Type} (l : List (String × Nat)) (off : Nat)
    (tbl : String → Option α) {f : State → State}
    (h : (l.findSome? fun x =>
      if (x.2 == off) = true then (tbl x.1).map (fun _ (s : State) => s.setStatus (.Exception "ext")) else none) =
      some f)
    (s : State) : (f s).status = .Exception "ext" := by
  induction l with
  | nil => simp [List.findSome?] at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    simp only [List.findSome?] at h
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h; exact ih h
    · simp only [ho, ↓reduceIte] at h
      cases htn : tbl n with
      | none => simp only [htn, Option.map] at h; exact ih h
      | some _ => simp only [htn, Option.map] at h; injection h with hf; subst hf; cases s; rfl

private theorem ls_hooksException_externAt?_isSome (pl : Obj.MultiPlacement)
    (i : Nat) (H : LibsignalHooks) (pc : BitVec 64) :
    ((libsignalSessionLib.blockProgram pl i
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H)).externAt? pc).isSome =
      ((libsignalSessionLib.blockProgram pl i H).externAt? pc).isSome := by
  unfold Program.externAt? Program.hookAtOff? Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
  dsimp only
  rw [option_or_isSome_local, option_or_isSome_local]
  rw [findSome?_isSome_congr_local _
    (fun x : String × Nat =>
      if (x.2 == (pc - (libsignalSessionLib.blockPlacement pl i).base).toNat) = true then
        LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H x.1 else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (libsignalSessionLib.blockPlacement pl i).base).toNat) = true then H x.1 else none)]
  intro x
  cases (x.2 == (pc - (libsignalSessionLib.blockPlacement pl i).base).toNat) <;>
    simp [LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException]

private theorem findSome?_const_none_local {α β : Type} (l : List α) :
    l.findSome? (fun _ => (none : Option β)) = none := by
  induction l with
  | nil => rfl
  | cons _ _ ih => exact ih

private theorem ls_hooksException_externAt?_not_running {pl : Obj.MultiPlacement}
    {i : Nat} {H : LibsignalHooks} {pc : BitVec 64} {f : State → State}
    (h : (libsignalSessionLib.blockProgram pl i
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H)).externAt? pc = some f)
    (s : State) : (f s).status ≠ .Running := by
  unfold Program.externAt? Program.hookAtOff? Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program at h
  dsimp only [LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException] at h
  simp only [ite_self, findSome?_const_none_local, Option.or_none] at h
  rw [findSome?_ite_map_status_local _ _ _ h]
  decide

private theorem steps_start_running_ls {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem rebase_none_externAt? (P : Program) (b pc : BitVec 64) :
    (P.rebase b (fun _ => none)).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase
  dsimp only
  simp only [ite_self, findSome?_const_none_local, Option.or_none]

private theorem steps_ls_blocks_lift_strip {blks : List Nat} (pl : Obj.MultiPlacement) (i : Nat)
    (H : LibsignalHooks)
    (hchk : ∀ j ∈ blks, checkBlockNoSvcNoMsr (libsignalSessionLib.blockLib j).text = true)
    {s1' sf' : State}
    (hsteps : Steps (libsignalSessionLib.blockProgram pl i
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H)) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let P := libsignalSessionLib.blockProgram pl i H
    let keep := lsBlocksKeep blks pl
    ∀ (s1 : State), s1' = ProofLib.stripS keep s1 → LsBlocksCodeLoaded blks pl s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS keep sf ∧
        Steps P s1 sf ∧ VmPreserved s1 sf := by
  intro P keep
  let Q := libsignalSessionLib.blockProgram pl i
    (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H)
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, VmPreserved.refl s1⟩
  | @step sa' sb' _ h1 hrest ih =>
    intro s1 hsa hcl1
    have hrb' : sb'.status = .Running := steps_start_running_ls hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ =>
      exact False.elim (ls_hooksException_externAt?_not_running he _ hrb')
    | extern_fault _ _ _ => cases s1; cases hrb'
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := (by cases s1; exact hr1')
      have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := (by cases s1; rfl)
      have hmem_eq : (ProofLib.stripS keep s1).mem =
          ProofLib.stripExecOutside keep s1.mem := (by cases s1; rfl)
      rw [hpc_eq, hmem_eq] at hfe'
      have hfe_parts : (Q.externAt? s1.pc).isSome = false ∧ s1.pc.toNat % 4 = 0 ∧
          (ProofLib.stripExecOutside keep s1.mem).canExec s1.pc 4 = true := by
        unfold Program.fetchMem at hfe'
        split at hfe'; · contradiction
        rename_i hex_q
        split at hfe'; · contradiction
        rename_i hal_q
        split at hfe'; · contradiction
        rename_i hce_q
        exact ⟨by simpa using hex_q, by simpa using hal_q, by simpa using hce_q⟩
      rcases hfe_parts with ⟨hex_q, hal_pc, hce'⟩
      have hkeep_pc : keep s1.pc = true := by
        have hcx := hce'
        unfold Memory.canExec at hcx
        rw [Memory.allPerm_iff] at hcx
        have hx0 := hcx 0 (by omega)
        simpa using (ProofLib.strip_perm_x_imp hx0).2
      obtain ⟨j, hj, hkeep_j⟩ := List.any_eq_true.mp hkeep_pc
      have hchk_j := hchk j hj
      let Rj := (libsignalSessionLib.blockProgram pl j).rebase (pl.base j) (fun _ => none)
      have hcl_strip := strip_lsBlocksCodeLoaded hcl1
      have hLj : Rj.CodeLoaded (ProofLib.stripExecOutside keep s1.mem) :=
        (hcl_strip j hj _ _ _).of_base_code rfl rfl
      have hmod4_j : Rj.code.length % 4 = 0 := by
        have hc : Rj.code = (libsignalSessionLib.blockLib j).text.patched
            (libsignalSessionLib.blockPlacement pl j) := rfl
        rw [hc, Obj.CodeBlock.length_patched]
        omega
      have hin_j : (s1.pc - Rj.base).toNat + 4 ≤ Rj.code.length := by
        unfold ProofLib.progKeep at hkeep_j
        have hb_eq : (libsignalSessionLib.blockProgram pl j (fun _ => none)).base = Rj.base := rfl
        have hc_eq : (libsignalSessionLib.blockProgram pl j (fun _ => none)).code = Rj.code := rfl
        rw [hb_eq, hc_eq, decide_eq_true_eq] at hkeep_j
        have hal_base : Rj.base.toNat % 4 = 0 := hLj.aligned
        have hal_off : (s1.pc - Rj.base).toNat % 4 = 0 := by bv_omega
        omega
      have hfm_Rj : Rj.fetchMem (ProofLib.stripExecOutside keep s1.mem) s1.pc = some inst := by
        unfold Program.fetchMem at hfe' ⊢
        rw [hex_q] at hfe'
        rw [rebase_none_externAt?]
        exact hfe'
      have hall_svc : Rj.allInstrs (fun ins => !ins.isSvc0) = true :=
        VerifiedLibraries.RustStd.blockProgram_rebase_allInstrs_not_isSvc0
          libsignalSessionLib pl j (by
            unfold checkBlockNoSvcNoMsr at hchk_j; simp only [Bool.and_eq_true] at hchk_j; exact hchk_j.1)
      have hall_msr : Rj.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true :=
        blockProgram_rebase_allInstrs_not_isMsrTpidrEl0 libsignalSessionLib pl j hchk_j
      have hHj : Obj.HoldsBytes (ProofLib.stripExecOutside keep s1.mem) Rj.base Rj.code
          (fun _ => Perm.rx) :=
        fun k hk => ⟨hLj.byte_eq k hk, hLj.perm_eq k hk, hLj.isLazyFree_eq k hk⟩
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs_holdsBytes_in_code
          hall_svc hLj.aligned hLj.no_wrap hHj hin_j hfm_Rj
      have hnmsr : inst.isMsrTpidrEl0 = false := by
        simpa using Program.fetchMem_of_allInstrs_holdsBytes_in_code
          hall_msr hLj.aligned hLj.no_wrap hHj hin_j hfm_Rj
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        unfold Program.fetchMem at hfe' ⊢
        have his := ls_hooksException_externAt?_isSome pl i H s1.pc
        rw [hex_q] at hfe'
        rw [← his, hex_q]
        simp only [Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq, not_true_eq_false] at hfe' ⊢
        have hce : s1.mem.canExec s1.pc 4 = true := by
          unfold Memory.canExec at hce' ⊢
          rw [Memory.allPerm_iff] at hce' ⊢
          intro k hk
          have hxk := hce' k hk
          rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
        have hr32 : (ProofLib.stripExecOutside keep s1.mem).read32 s1.pc = s1.mem.read32 s1.pc := by
          simp [Memory.read32, ProofLib.strip_read8]
        simp only [hce', hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
        rwa [hr32] at hfe'
      have hev_Q : Q.evalInst inst (ProofLib.stripS keep s1) =
          ProofLib.stripS keep (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have hcl_next : LsBlocksCodeLoaded blks pl (execInst inst s1).mem :=
        fun j' hj' X O svc => hstep_P.codeLoaded (hcl1 j' hj' X O svc)
      obtain ⟨sf, hsf_eq, hsteps_P, hvm_rest⟩ :=
        ih hrun_f (execInst inst s1) hev_Q hcl_next
      have hvm1 : VmPreserved s1 (execInst inst s1) :=
        ProofLib.NonSyscallPreserved.toVmPreserved
          (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1)
          (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P, hvm1.trans hvm_rest⟩

/-- Lift a `withLsBlocksCodeLoaded blks lsmpl spec` proof on `hooksException H` to
`withLsCodeLoaded lsmpl (withVmPreserved spec)` on `H`, checking only the blocks in `blks`
for absence of `svc #0` and `msr tpidr_el0`. -/
theorem ls_subroutine_ok_blocks_vmPreserved {α : Type} [LibsignalPlacement]
    {prog progQ : Program} {blks : List Nat} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg prog i H]
    [hQ : IsLsBlockProg progQ i (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H)]
    {entry : BitVec 64} {spec : Spec α}
    (hi : i ∈ blks)
    (hvalid : blks.all (fun j => decide (j < 619) && !(decide (j ∈ libsignalMutatedBlocks))) = true)
    (hchk : checkTreeBlocksNoSvcNoMsr blks = true)
    (hpre_mem : ∀ x (s : State) m, spec.pre x (s.setMem m) = spec.pre x s := by intros; rfl)
    (hpost_mem : ∀ x (s sf : State) m mf,
      spec.post x (s.setMem m) (sf.setMem mf) = spec.post x s sf := by intros; rfl)
    (h_no_panic : ∀ x R' s0 sf, ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf, ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ ho; exact not_satisfies_false_sepConj ho)
    (hok : subroutine_ok progQ entry (withLsBlocksCodeLoaded blks lsmpl spec)) :
    subroutine_ok prog entry (withLsCodeLoaded lsmpl (withVmPreserved spec)) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  obtain ⟨hcl_ls, hpre0⟩ := extract_withLsCodeLoaded hpre
  dsimp only [withVmPreserved] at hpre0
  have hcl0 : LsBlocksCodeLoaded blks lsmpl s0.mem :=
    LsBlocksCodeLoaded.of_lsCodeLoaded hvalid hcl_ls
  let keep := lsBlocksKeep blks lsmpl
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hpre0
  let s0' := ProofLib.stripS keep s0
  have hs0'_setMem : s0' = s0.setMem (ProofLib.stripExecOutside keep s0.mem) := by cases s0; rfl
  have hpc' : s0'.pc = entry := by cases s0; exact hpc
  have hrun' : s0'.status = .Running := by cases s0; exact hrun
  have hsp' : s0'.spAligned = true := by cases s0; exact hsp
  have hcl_strip : LsBlocksCodeLoaded blks lsmpl s0'.mem := by
    change LsBlocksCodeLoaded blks lsmpl (ProofLib.stripExecOutside keep s0.mem)
    exact strip_lsBlocksCodeLoaded hcl0
  have hpre_strip : s0'.mem ⊨ (withLsBlocksCodeLoaded blks lsmpl spec).pre x s0' ∗ R_view := by
    dsimp only [withLsBlocksCodeLoaded]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcl_strip, ?_⟩
    rw [hs0'_setMem, hpre_mem]
    exact hm_strip
  have hQL : progQ.CodeLoaded s0'.mem :=
    hQ.eq_blockProgram ▸ hcl_strip i hi
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none) Syscall.standard
  obtain ⟨sf', hstepsQ0, hout, _⟩ :=
    hok.no_fault_before_outcome x R_view s0' hpc' hrun' hpre_strip hsp' hQL
  rcases hout with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨code, _, hex'⟩ | ⟨_, hoom'⟩
  · have hrun_sf' : sf'.status = .Running := hret'.2.2
    have hstepsQ : Steps (libsignalSessionLib.blockProgram lsmpl i
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H)) s0' sf' :=
      hQ.eq_blockProgram ▸ hstepsQ0
    obtain ⟨sf, hsf_eq, hstepsP0, hvm⟩ :=
      steps_ls_blocks_lift_strip lsmpl i H (fun j hj => blockLib_text_of_checkTree hchk hj)
        hstepsQ hrun_sf' s0 rfl hcl0
    have hstepsP : Steps prog s0 sf := hprog.eq_blockProgram.symm ▸ hstepsP0
    have hsf'_setMem : sf' = sf.setMem (ProofLib.stripExecOutside keep sf.mem) := by
      rw [hsf_eq]; cases sf; rfl
    have hret : Returned s0 sf := by
      rw [hsf_eq] at hret'; cases s0; cases sf; exact hret'
    have hcc : CallingConventionPreserved s0 sf := by
      rw [hsf_eq] at hcc'; cases s0; cases sf; exact hcc'
    have hpost_strip : ProofLib.stripExecOutside keep sf.mem ⊨ spec.post x s0 sf ∗ R_view := by
      have hp := hpost'
      have hmem_sf' : sf'.mem = ProofLib.stripExecOutside keep sf.mem := by rw [hsf_eq]; cases sf; rfl
      rw [hmem_sf', hs0'_setMem, hsf'_setMem, hpost_mem] at hp
      exact hp
    have hpost : sf.mem ⊨ (withVmPreserved spec).post x s0 sf ∗ R := by
      dsimp only [withVmPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hvm, hunstrip hvm.perm_eq hpost_strip⟩
    exact reaches_outcome_steps hstepsP (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hpost⟩))
  · exact False.elim (h_no_panic x R_view s0' sf' hpan')
  · exact False.elim (h_no_exit x code R_view s0' sf' hex')
  · exact False.elim (h_no_oom x R_view s0' sf' hoom')

/-- Single-block specialization of `ls_subroutine_ok_blocks_vmPreserved`: lifts a plain
`subroutine_ok progQ entry spec` on block `i` directly to `subroutine_ok prog entry (withVmPreserved spec)`
using `subroutine_ok.of_codeLoaded` (no `LibsignalCodeLoaded` assumption required). -/
theorem ls_subroutine_ok_plain_vmPreserved {α : Type} [LibsignalPlacement]
    {prog progQ : Program} {i : Nat} {H : LibsignalHooks}
    [hprog : IsLsBlockProg prog i H]
    [hQ : IsLsBlockProg progQ i (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H)]
    {entry : BitVec 64} {spec : Spec α}
    (hchk : checkTreeBlocksNoSvcNoMsr [i] = true)
    (hpre_mem : ∀ x (s : State) m, spec.pre x (s.setMem m) = spec.pre x s := by intros; rfl)
    (hpost_mem : ∀ x (s sf : State) m mf,
      spec.post x (s.setMem m) (sf.setMem mf) = spec.post x s sf := by intros; rfl)
    (h_no_panic : ∀ x R' s0 sf, ¬(sf.mem ⊨ spec.onPanic x s0 sf ∗ R') := by
      intro _ _ _ _ hp; exact not_satisfies_false_sepConj hp)
    (h_no_exit : ∀ x code R' s0 sf, ¬(sf.mem ⊨ spec.onExit x code s0 sf ∗ R') := by
      intro _ _ _ _ _ he; exact not_satisfies_false_sepConj he)
    (h_no_oom : ∀ x R' s0 sf, ¬(sf.mem ⊨ spec.onOom x s0 sf ∗ R') := by
      intro _ _ _ _ ho; exact not_satisfies_false_sepConj ho)
    (hok : subroutine_ok progQ entry spec) :
    subroutine_ok prog entry (withVmPreserved spec) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp hL
  dsimp only [withVmPreserved] at hpre
  have hcl0 : LsBlocksCodeLoaded [i] lsmpl s0.mem := by
    intro j hj X O svc
    simp only [List.mem_singleton] at hj; subst j
    have hLi : (libsignalSessionLib.blockProgram lsmpl i H).CodeLoaded s0.mem :=
      hprog.eq_blockProgram ▸ hL
    exact hLi.of_base_code rfl rfl
  let keep := lsBlocksKeep [i] lsmpl
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hpre
  let s0' := ProofLib.stripS keep s0
  have hs0'_setMem : s0' = s0.setMem (ProofLib.stripExecOutside keep s0.mem) := by cases s0; rfl
  have hpc' : s0'.pc = entry := by cases s0; exact hpc
  have hrun' : s0'.status = .Running := by cases s0; exact hrun
  have hsp' : s0'.spAligned = true := by cases s0; exact hsp
  have hcl_strip : LsBlocksCodeLoaded [i] lsmpl s0'.mem :=
    strip_lsBlocksCodeLoaded hcl0
  have hpre_strip : s0'.mem ⊨ spec.pre x s0' ∗ R_view := by
    rw [hs0'_setMem, hpre_mem]; exact hm_strip
  have hQL : progQ.CodeLoaded s0'.mem :=
    hQ.eq_blockProgram ▸ hcl_strip i (List.mem_singleton_self i)
      (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H) (fun _ => none) Syscall.standard
  obtain ⟨sf', hstepsQ0, hout, _⟩ :=
    hok.no_fault_before_outcome x R_view s0' hpc' hrun' hpre_strip hsp' hQL
  rcases hout with ⟨hret', hcc', hpost'⟩ | ⟨_, hpan'⟩ | ⟨code, _, hex'⟩ | ⟨_, hoom'⟩
  · have hrun_sf' : sf'.status = .Running := hret'.2.2
    have hstepsQ : Steps (libsignalSessionLib.blockProgram lsmpl i
        (LibsignalBinary.Proofs.Placed.BudgetPoolSync.hooksException H)) s0' sf' :=
      hQ.eq_blockProgram ▸ hstepsQ0
    obtain ⟨sf, hsf_eq, hstepsP0, hvm⟩ :=
      steps_ls_blocks_lift_strip lsmpl i H (fun j hj => blockLib_text_of_checkTree hchk hj)
        hstepsQ hrun_sf' s0 rfl hcl0
    have hstepsP : Steps prog s0 sf := hprog.eq_blockProgram.symm ▸ hstepsP0
    have hsf'_setMem : sf' = sf.setMem (ProofLib.stripExecOutside keep sf.mem) := by
      rw [hsf_eq]; cases sf; rfl
    have hret : Returned s0 sf := by
      rw [hsf_eq] at hret'; cases s0; cases sf; exact hret'
    have hcc : CallingConventionPreserved s0 sf := by
      rw [hsf_eq] at hcc'; cases s0; cases sf; exact hcc'
    have hpost_strip : ProofLib.stripExecOutside keep sf.mem ⊨ spec.post x s0 sf ∗ R_view := by
      have hp := hpost'
      have hmem_sf' : sf'.mem = ProofLib.stripExecOutside keep sf.mem := by rw [hsf_eq]; cases sf; rfl
      rw [hmem_sf', hs0'_setMem, hsf'_setMem, hpost_mem] at hp
      exact hp
    have hpost : sf.mem ⊨ (withVmPreserved spec).post x s0 sf ∗ R := by
      dsimp only [withVmPreserved]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨hvm, hunstrip hvm.perm_eq hpost_strip⟩
    exact reaches_outcome_steps hstepsP (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, hpost⟩))
  · exact False.elim (h_no_panic x R_view s0' sf' hpan')
  · exact False.elim (h_no_exit x code R_view s0' sf' hex')
  · exact False.elim (h_no_oom x R_view s0' sf' hoom')

/-! ## 2. `VmPreserved`-Augmented `Epoch::encoded_len` and `Chain::encoded_len` Hoare Specs -/

/-- `VmPreserved`-strengthened contract of `<Epoch as Message>::encoded_len` (pinned). -/
def epochEncodedLenPinnedSpec (A : RustAlloc) : Spec EpochEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLenPinnedSpec A)

/-- `VmPreserved`-strengthened contract of `<Epoch as Message>::encoded_len` (unpinned). -/
def epochEncodedLenSpec (A : RustAlloc) : Spec EpochEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.epochEncodedLenSpec A)

/-- `VmPreserved`-strengthened contract of `<Chain as Message>::encoded_len` (pinned). -/
def chainEncodedLenPinnedSpec (A : RustAlloc) : Spec ChainEncodedLenPinnedGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenPinnedSpec A)

/-- `VmPreserved`-strengthened contract of `<Chain as Message>::encoded_len` (unpinned). -/
def chainEncodedLenSpec (A : RustAlloc) : Spec ChainEncodedLenGhost :=
  withVmPreserved (CryptoVerification.SpqrV1.ProtoRepr.chainEncodedLenSpec A)

end LibsignalBinary.Proofs.SpqrV1.ProtoRepr.DefsBudget
