/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Defs
public import LibsignalBinary.Heap.SpecBudget
import ProofLib.OpcodeExclusion
import VerifiedLibraries.RustStd.Proofs.ExecSegSym

/-!
# Budget-Threaded Specifications and `VmPreserved` Lifter for `<PolyEncoder as Encoder>::encode_bytes`

Block-level black-box `VmPreserved` lifters (`sepWP_block_vmPreserved`, `sepWP_lsBlock_vmPreserved`),
allocator event envelopes (`encodeBytesAllocEvents`, `EncodeBytesEnv`), and `RustCliAllocBudget`-threaded
specifications (`encodeBytesSpec`, `encodeBytesSpecX`) for Block `417`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget

open Arm64 ProofLib
open CryptoVerification
  (IsLsBlockProg LibsignalHooks LibsignalPlacement
   blkLib_417 blkLib_eq_417 blkPC_417 blkPl_417 libsignalSessionLib lsmpl prog_eq_blockProgram)
open CryptoVerification.RustHeap (RustAlloc allocHookStack)
open CryptoVerification.SpqrV1.Poly (polyEncoderSize resultPolyEncoderAt)
open CryptoVerification.SpqrV1.Poly.EncodeBytes
  (EncodeBytesGhost bytesAt encodeBytesResult encodeBytesStack encodeBytesStackX savedCells)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FdsHiFrame FitsEnv RustCliAllocBudget VmPreserved rustAllocEvents)

/-! ## Reusable Block-Level `VmPreserved` Lifter for Relocatable `SepWP` Segments -/

/-- Scan all 4-byte words of `blk` to verify absence of both `SVC #0` and `MSR TPIDR_EL0, Xt`
    under any `Obj.Placement`. -/
def checkBytesSafeVm (blk : Obj.CodeBlock) : Nat → List (BitVec 8) → Bool
  | _, [] => true
  | off, b0 :: b1 :: b2 :: b3 :: rest =>
    let w := Obj.wordOfBytesLE [b0, b1, b2, b3] 0
    (match blk.relocAt? off with
     | none => (w != 0xd400_0001#32) && !Arm64.isMsrTpidrEl0Word w
     | some r => VerifiedLibraries.RustStd.checkRelocWordNoSvc0 w r) &&
    checkBytesSafeVm blk (off + 4) rest
  | _, _ => false

/-- Decidable check that `blk.patched pl` contains neither `SVC #0` nor `MSR TPIDR_EL0, Xt`
    for any `pl : Obj.Placement`. -/
def checkBlockSafeVm (blk : Obj.CodeBlock) : Bool :=
  checkBytesSafeVm blk 0 blk.code &&
  blk.relocs.all (fun r => VerifiedLibraries.RustStd.relocKindSafeNoSvc0 r.kind)

private theorem checkBytesSafeVm_wordOfBytesLE (blk : Obj.CodeBlock) :
    ∀ (k off : Nat) (bs : List (BitVec 8)),
      checkBytesSafeVm blk off bs = true → 4 * k + 4 ≤ bs.length →
      (let w := Obj.wordOfBytesLE bs (4 * k)
       match blk.relocAt? (off + 4 * k) with
       | none => (w != 0xd400_0001#32) && !Arm64.isMsrTpidrEl0Word w
       | some r => VerifiedLibraries.RustStd.checkRelocWordNoSvc0 w r) = true
  | 0, off, bs, hchk, hlen => by
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [checkBytesSafeVm, Bool.and_eq_true] at hchk; simpa [Obj.wordOfBytesLE] using hchk.1
  | k + 1, off, bs, hchk, hlen => by
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [checkBytesSafeVm, Bool.and_eq_true] at hchk
      have ih := checkBytesSafeVm_wordOfBytesLE blk k (off + 4) rest hchk.2
        (by simp only [List.length_cons] at hlen; omega)
      have h0 : 4 * (k + 1) = 4 * k + 4 := by omega
      have heq_w : Obj.wordOfBytesLE (b0 :: b1 :: b2 :: b3 :: rest) (4 * (k + 1)) =
          Obj.wordOfBytesLE rest (4 * k) := by
        simp only [Obj.wordOfBytesLE, h0]; rfl
      have heq_off : off + 4 * (k + 1) = off + 4 + 4 * k := by omega
      simpa [heq_w, heq_off] using ih

private theorem checkBytesSafeVm_mod4 (blk : Obj.CodeBlock) :
    ∀ (off : Nat) (bs : List (BitVec 8)), checkBytesSafeVm blk off bs = true → bs.length % 4 = 0
  | _, [], _ => rfl
  | _, [_], h | _, [_, _], h | _, [_, _, _], h => by simp [checkBytesSafeVm] at h
  | off, _ :: _ :: _ :: _ :: rest, h => by
    simp only [checkBytesSafeVm, Bool.and_eq_true] at h
    have ih := checkBytesSafeVm_mod4 blk (off + 4) rest h.2; simp only [List.length_cons]; omega

private def safeVmWord (w : BitVec 32) : Bool :=
  !Arm64.isSvc0Word w && !Arm64.isMsrTpidrEl0Word w

private theorem safeVmWord_nopWord : safeVmWord Obj.nopWord = true := by decide

private theorem safeVmWord_of_bit26_false {w : BitVec 32} (hb : w.getLsbD 26 = false) :
    safeVmWord w = true := by
  unfold safeVmWord
  have h1 : Arm64.isSvc0Word w = false := by
    cases hs : Arm64.isSvc0Word w with
    | false => rfl
    | true =>
      unfold Arm64.isSvc0Word at hs
      have heq : w = 0xd400_0001#32 := beq_iff_eq.mp hs
      have hb' := congrArg (fun v => v.getLsbD 26) heq
      rw [hb] at hb'
      exact absurd hb'.symm (by decide)
  have h2 : Arm64.isMsrTpidrEl0Word w = false := by
    cases hm : Arm64.isMsrTpidrEl0Word w with
    | false => rfl
    | true =>
      unfold Arm64.isMsrTpidrEl0Word at hm
      have heq : w &&& 0xffff_ffe0#32 = 0xd51b_d040#32 := beq_iff_eq.mp hm
      have hb' := congrArg (fun v => v.getLsbD 26) heq
      rw [BitVec.getLsbD_and, hb, Bool.false_and] at hb'
      exact absurd hb'.symm (by decide)
  simp [h1, h2]

private theorem safeVmWord_of_bit29_true {w : BitVec 32} (hb : w.getLsbD 29 = true) :
    safeVmWord w = true := by
  unfold safeVmWord
  have h1 : Arm64.isSvc0Word w = false := by
    cases hs : Arm64.isSvc0Word w with
    | false => rfl
    | true =>
      unfold Arm64.isSvc0Word at hs
      have heq : w = 0xd400_0001#32 := beq_iff_eq.mp hs
      have hb' := congrArg (fun v => v.getLsbD 29) heq
      rw [hb] at hb'
      exact absurd hb' (by decide)
  have h2 : Arm64.isMsrTpidrEl0Word w = false := by
    cases hm : Arm64.isMsrTpidrEl0Word w with
    | false => rfl
    | true =>
      unfold Arm64.isMsrTpidrEl0Word at hm
      have heq : w &&& 0xffff_ffe0#32 = 0xd51b_d040#32 := beq_iff_eq.mp hm
      have hb' := congrArg (fun v => v.getLsbD 29) heq
      rw [BitVec.getLsbD_and, hb, Bool.true_and] at hb'
      exact absurd hb' (by decide)
  simp [h1, h2]

private theorem safeVmWord_of_top6_ne {w : BitVec 32}
    (hw : w &&& 0xfc00_0000#32 ≠ 0xd400_0000#32) :
    safeVmWord w = true := by
  unfold safeVmWord
  have h1 : Arm64.isSvc0Word w = false := by
    cases hs : Arm64.isSvc0Word w with
    | false => rfl
    | true =>
      unfold Arm64.isSvc0Word at hs
      have heq : w = 0xd400_0001#32 := beq_iff_eq.mp hs
      subst heq
      exact False.elim (hw (by decide))
  have h2 : Arm64.isMsrTpidrEl0Word w = false := by
    cases hm : Arm64.isMsrTpidrEl0Word w with
    | false => rfl
    | true =>
      unfold Arm64.isMsrTpidrEl0Word at hm
      have heq : w &&& 0xffff_ffe0#32 = 0xd51b_d040#32 := beq_iff_eq.mp hm
      have htop := congrArg (· &&& 0xfc00_0000#32) heq
      rw [BitVec.and_assoc] at htop
      have hm1 : (0xffff_ffe0#32 : BitVec 32) &&& 0xfc00_0000#32 = 0xfc00_0000#32 := by decide
      have hm2 : (0xd51b_d040#32 : BitVec 32) &&& 0xfc00_0000#32 = 0xd400_0000#32 := by decide
      rw [hm1, hm2] at htop
      exact False.elim (hw htop)
  simp [h1, h2]

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
  rw [BitVec.and_or_distrib_right, mask_top6_shiftLeft_10_local, BitVec.or_zero, BitVec.and_assoc]
  rfl

private theorem adrpWord_bit26_false {w : BitVec 32} (hw26 : w &&& 0x0400_0000#32 = 0#32)
    (place target : BitVec 64) :
    (Obj.adrpWord w place target).getLsbD 26 = false := by
  have hb26 : w[26] = false := by
    have := congrArg (fun v => v.getLsbD 26) hw26
    simpa [BitVec.getLsbD_eq_getElem (by decide : 26 < 32)] using this
  simp [Obj.adrpWord, Obj.adrpWordOff, hb26]

private theorem patchedWord_safeVm {blk : Obj.CodeBlock} (pl : Obj.Placement)
    (hchk : checkBlockSafeVm blk = true) {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    safeVmWord (blk.patchedWord pl off) = true := by
  unfold checkBlockSafeVm at hchk; simp only [Bool.and_eq_true, List.all_eq_true] at hchk
  rcases hchk with ⟨hbytes, hrelocs⟩
  have hoff_eq : 4 * (off / 4) = off := by omega
  have hw_off := checkBytesSafeVm_wordOfBytesLE blk (off / 4) 0 blk.code hbytes (by omega)
  simp only [Nat.zero_add, hoff_eq] at hw_off
  change (match blk.relocAt? off with
    | none => (blk.wordAt off != 0xd400_0001#32) && !Arm64.isMsrTpidrEl0Word (blk.wordAt off)
    | some r => VerifiedLibraries.RustStd.checkRelocWordNoSvc0 (blk.wordAt off) r) = true at hw_off
  unfold Obj.CodeBlock.patchedWord
  cases hr : blk.relocAt? off with
  | none =>
    rw [hr] at hw_off
    unfold safeVmWord Arm64.isSvc0Word
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, beq_eq_false_iff_ne] at hw_off ⊢
    exact hw_off
  | some r =>
    dsimp only; rw [hr] at hw_off; dsimp only at hw_off
    have hrmem : r ∈ blk.relocs := List.mem_of_find?_eq_some hr
    have hksafe := hrelocs r hrmem
    split
    · exact safeVmWord_nopWord
    · split
      · exact safeVmWord_of_bit26_false (by simp [Obj.adrWord, Obj.adrWordOff, Obj.adrTemplate])
      · split
        · exact safeVmWord_of_bit26_false (by simp [Obj.adrWord, Obj.adrWordOff, Obj.adrTemplate])
        · split
          · rename_i _ _ _ hgot
            simp only [Bool.and_eq_true] at hgot
            have hisgot : r.kind.isGotOrTlsIe = true := hgot.1.1
            cases hk : r.kind
            all_goals rw [hk] at hisgot; try contradiction
            all_goals dsimp only [Obj.CodeBlock.patchGotOrTlsIeRelaxed]
            · exact safeVmWord_nopWord
            · refine safeVmWord_of_top6_ne ?_
              rw [lo12Word_top6_eq]
              intro h; have hb := congrArg (fun v => v.getLsbD 26) h
              simp [Obj.ldrToAddWord] at hb
            · exact safeVmWord_of_bit26_false (by simp [Obj.tlsieMovzWord])
            · exact safeVmWord_of_bit29_true (by simp [Obj.tlsieMovkWord])
          · unfold VerifiedLibraries.RustStd.checkRelocWordNoSvc0 at hw_off
            cases hk : r.kind
            all_goals rw [hk] at hksafe; try contradiction
            all_goals rw [hk] at hw_off; simp only [VerifiedLibraries.RustStd.isTlsdescKind,
              VerifiedLibraries.RustStd.isAdrpRelocKind, Bool.false_or, Bool.true_or,
              Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_eq_true,
              bne_iff_ne, beq_iff_eq] at hw_off
            all_goals dsimp only [Obj.patchRelocWord]
            · exact safeVmWord_of_top6_ne (by rwa [branchWord_top6_eq])
            · exact safeVmWord_of_top6_ne (by rwa [branchWord_top6_eq])
            · exact safeVmWord_of_bit26_false (adrpWord_bit26_false hw_off.2 _ _)
            · exact safeVmWord_of_top6_ne (by rwa [lo12Word_top6_eq])
            · exact safeVmWord_of_top6_ne (by rwa [lo12Word_top6_eq])
            · exact safeVmWord_of_top6_ne (by rwa [lo12Word_top6_eq])
            · exact safeVmWord_of_top6_ne (by rwa [lo12Word_top6_eq])
            · exact safeVmWord_of_top6_ne (by rwa [lo12Word_top6_eq])
            · exact safeVmWord_of_top6_ne (by rwa [lo12Word_top6_eq])
            · exact safeVmWord_of_bit26_false (adrpWord_bit26_false hw_off.2 _ _)
            · exact safeVmWord_of_top6_ne (by rwa [lo12Word_top6_eq])
            · exact safeVmWord_of_bit26_false (adrpWord_bit26_false hw_off.2 _ _)
            · exact safeVmWord_of_top6_ne (by rwa [lo12Word_top6_eq])
            · exact safeVmWord_of_bit26_false (by simp [Obj.tlsdescAdrPage21Word])
            · exact safeVmWord_of_bit29_true (by simp [Obj.tlsdescLd64Lo12Word])
            · exact safeVmWord_nopWord
            · exact safeVmWord_nopWord

private theorem bytesAllWords_of_drop4_local {pw : BitVec 32 → Bool} :
    ∀ (n : Nat) (bs : List (BitVec 8)), bs.length = 4 * n →
      (∀ k < n, match bs.drop (4 * k) with
        | b0 :: b1 :: b2 :: b3 :: _ => pw (b3 ++ b2 ++ b1 ++ b0) = true | _ => True) →
      Arm64.bytesAllWords pw bs = true
  | 0, bs, hlen, _ => by cases bs with | nil => rfl | cons _ _ => simp at hlen
  | n + 1, bs, hlen, h => by
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      have h0 : pw (b3 ++ b2 ++ b1 ++ b0) = true := by simpa using h 0 (by omega)
      have hrest := bytesAllWords_of_drop4_local n rest
        (by simp only [List.length_cons] at hlen; omega) fun k hk => by
          have hk' := h (k + 1) (by omega)
          have hd : (b0 :: b1 :: b2 :: b3 :: rest).drop (4 * (k + 1)) = rest.drop (4 * k) := by
            rw [show 4 * (k + 1) = 4 + 4 * k by omega, ← List.drop_drop]; rfl
          rwa [hd] at hk'
      simp [Arm64.bytesAllWords, h0, hrest]

theorem placedLib_rebase_allInstrs_safeVm (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (H : String → Option (State → State))
    (hchk : checkBlockSafeVm lib.text = true) :
    ((lib.program pl).rebase pl.base H).allInstrs
      (fun i => !(i.isSvc0 || i.isMsrTpidrEl0)) = true := by
  let prog := (lib.program pl).rebase pl.base H
  have hcode : prog.code = lib.text.patched pl := rfl
  have hmod4 : lib.text.code.length % 4 = 0 := by
    unfold checkBlockSafeVm at hchk; simp only [Bool.and_eq_true] at hchk
    exact checkBytesSafeVm_mod4 lib.text 0 lib.text.code hchk.1
  have hdiv : prog.code.length = 4 * (lib.text.code.length / 4) := by
    rw [hcode, Obj.CodeBlock.length_patched]
  refine Program.allInstrs_of_allWords
    (p := fun i => i.isSvc0 || i.isMsrTpidrEl0)
    (pw := fun w => !safeVmWord w)
    (fun w i hd hpw => ?_) ?_
  · have hs : safeVmWord w = true := by cases h : safeVmWord w <;> simp_all
    unfold safeVmWord at hs
    simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at hs ⊢
    exact ⟨Arm64.decode_not_isSvc0 hd hs.1, Arm64.decode_not_isMsrTpidrEl0 hd hs.2⟩
  · unfold Program.allWords
    refine bytesAllWords_of_drop4_local (lib.text.code.length / 4) prog.code hdiv fun k hk => ?_
    have hal : (4 * k) % 4 = 0 := by omega
    have hlen : 4 * k + 4 ≤ lib.text.code.length := by omega
    have hrw : prog.readWordOff (4 * k) = some (lib.text.patchedWord pl (4 * k)) :=
      Obj.CodeBlock.readWordOff_patched hcode hal hlen
    unfold Program.readWordOff at hrw
    simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hrw
    match hdrop : prog.code.drop (4 * k) with
    | [] | [_] | [_, _] | [_, _, _] => simp [hdrop] at hrw
    | b0 :: b1 :: b2 :: b3 :: _ =>
      rw [hdrop] at hrw; injection hrw with hw; dsimp only
      rw [hw, Bool.not_not]
      exact patchedWord_safeVm pl hchk hal hlen

/-- Total trap hook table mapping every symbol to an immediate `.Exception`. -/
def vmTrapHooks : String → Option (State → State) :=
  fun _ => some (fun s => s.setStatus (.Exception "extern_trap"))

/-- A hook table `Htrap` traps every symbol: every `sym` maps to `some f` that never leaves
    `status = .Running`. Satisfied by both `vmTrapHooks` and `Rust.withPanics vmTrapHooks`. -/
def IsTotalTrapHooks (Htrap : String → Option (State → State)) : Prop :=
  ∀ sym : String, ∃ f : State → State, Htrap sym = some f ∧ ∀ s : State, (f s).status ≠ .Running

theorem isTotalTrapHooks_vmTrapHooks : IsTotalTrapHooks vmTrapHooks :=
  fun _ => ⟨_, rfl, fun s => by cases s; simp⟩

theorem isTotalTrapHooks_withPanics_vmTrapHooks : IsTotalTrapHooks (Rust.withPanics vmTrapHooks) := by
  intro sym
  unfold Rust.withPanics
  split
  · exact ⟨Rust.panicked, rfl, fun s => by cases s; simp [Rust.panicked]⟩
  · exact isTotalTrapHooks_vmTrapHooks sym

private theorem findSome?_symbols_none :
    ∀ (syms : List (String × Nat)) (off : Nat),
      (syms.findSome? fun x => if x.2 == off then (none : Option (State → State)) else none) = none
  | [], _ => rfl
  | hd :: rest, off => by
    rw [List.findSome?_cons, ite_self]
    exact findSome?_symbols_none rest off

private theorem findSome?_stubs_totalTrap {Htrap : String → Option (State → State)}
    (htrap : IsTotalTrapHooks Htrap) :
    ∀ (stubs : List (String × Nat)) (off : Nat) {f : State → State},
      (stubs.findSome? fun x => if x.2 == off then Htrap x.1 else none) = some f →
      ∀ s : State, (f s).status ≠ .Running
  | [], _, _, h => by cases h
  | (n, o) :: rest, off, f, h => by
    dsimp only [List.findSome?] at h
    by_cases ho : o == off
    · obtain ⟨g, hg, hnr⟩ := htrap n
      simp only [ho, ↓reduceIte, hg] at h
      injection h with hgf; subst hgf; exact hnr
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      exact findSome?_stubs_totalTrap htrap rest off h

private theorem findSome?_stubs_none_of_totalTrap {Htrap Hk : String → Option (State → State)}
    (htrap : IsTotalTrapHooks Htrap) :
    ∀ (stubs : List (String × Nat)) (off : Nat),
      (stubs.findSome? fun x => if x.2 == off then Htrap x.1 else none) = none →
      (stubs.findSome? fun x => if x.2 == off then Hk x.1 else none) = none
  | [], _, _ => rfl
  | (n, o) :: rest, off, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : o == off
    · obtain ⟨g, hg, _⟩ := htrap n
      simp [ho, hg] at h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_stubs_none_of_totalTrap htrap rest off h

private theorem externAt?_rebase_totalTrap_not_running {P : Program} {b pc : BitVec 64}
    {Htrap : String → Option (State → State)} (htrap : IsTotalTrapHooks Htrap)
    {f : State → State} (hext : (P.rebase b Htrap).externAt? pc = some f) :
    ∀ s : State, (f s).status ≠ .Running := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext
  dsimp only at hext
  rw [findSome?_symbols_none P.symbols (pc - b).toNat, Option.or_none] at hext
  exact findSome?_stubs_totalTrap htrap P.stubs (pc - b).toNat hext

private theorem externAt?_rebase_none_of_totalTrap {P : Program} {b pc : BitVec 64}
    {Htrap Hk : String → Option (State → State)} (htrap : IsTotalTrapHooks Htrap)
    (hext : (P.rebase b Htrap).externAt? pc = none) :
    (P.rebase b Hk).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none P.symbols (pc - b).toNat, Option.or_none] at hext ⊢
  exact findSome?_stubs_none_of_totalTrap htrap P.stubs (pc - b).toNat hext

private theorem strip_codeLoaded_of_keep_local {prog : Program} {m : Memory}
    (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_of_keep_local (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_local {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem steps_rebase_lift_strip_vm {P : Program} {b : BitVec 64}
    {Htrap Hk : String → Option (State → State)}
    (htrap : IsTotalTrapHooks Htrap)
    (hall : (P.rebase b Htrap).allInstrs (fun i => !(i.isSvc0 || i.isMsrTpidrEl0)) = true)
    {s1' sf' : State}
    (hsteps : Steps (P.rebase b Htrap) s1' sf')
    (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep (P.rebase b Htrap)) s1 →
      (P.rebase b Htrap).CodeLoaded s1.mem →
      ∃ sf : State,
        sf' = ProofLib.stripS (ProofLib.progKeep (P.rebase b Htrap)) sf ∧
        Steps (P.rebase b Hk) s1 sf ∧
        VmPreserved s1 sf := by
  let R_j := P.rebase b Htrap
  let Q_j := P.rebase b Hk
  induction hsteps with
  | refl =>
    intro s1 hs1 _
    exact ⟨s1, hs1, .refl s1, VmPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1
    have hrb' : sb'.status = .Running := steps_start_running_local hrest hrun_f
    subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern_fault _ _ _ => cases s1; cases hrb'
    | extern _ hext _ _ =>
      exact False.elim (externAt?_rebase_totalTrap_not_running htrap hext _ hrb')
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := by cases s1; exact hr1'
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_codeLoaded_of_keep_local hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_execOnlyIn_of_keep_local R_j s1.mem
      have hboth : (!(inst.isSvc0 || inst.isMsrTpidrEl0)) = true :=
        Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hboth
      rcases hboth with ⟨hnsvc0, hnmsr⟩
      have hext_R : R_j.externAt? s1.pc = none := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by cases s1; rfl
        rw [hpc_eq] at hfe'
        cases he : R_j.externAt? s1.pc with
        | none => rfl
        | some g =>
          unfold Program.fetchMem at hfe'
          rw [he] at hfe'
          simp at hfe'
      have hext_Q : Q_j.externAt? s1.pc = none :=
        externAt?_rebase_none_of_totalTrap htrap hext_R
      have hfe_Q : Q_j.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := by cases s1; rfl
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := by cases s1; rfl
        rw [hpc_eq, hmem_eq] at hfe'
        unfold Program.fetchMem at hfe' ⊢
        rw [hext_R] at hfe'; rw [hext_Q]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
          split at hfe'
          · contradiction
          · rename_i hce'
            have hce : s1.mem.canExec s1.pc 4 = true := by
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
              unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢; intro k hk
              have hxk := hce' k hk
              rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                s1.mem.read32 s1.pc := by
              simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'
            simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
            exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
      have hev_R : R_j.evalInst inst (ProofLib.stripS (ProofLib.progKeep R_j) s1) =
          ProofLib.stripS (ProofLib.progKeep R_j) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_Q : Step Q_j s1 (execInst inst s1) := by
        have := Step.exec (prog := Q_j) hr1 hfe_Q
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      have hL_next : R_j.CodeLoaded (execInst inst s1).mem :=
        (hstep_Q.codeLoaded (hL1.of_base_code rfl rfl)).of_base_code rfl rfl
      have hvm1 : VmPreserved s1 (execInst inst s1) :=
        VmPreserved.of_vm_tpidr
          (VerifiedLibraries.RustStd.nonSyscallPreserved_toVmFields
            (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1))
          (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
          (FdsHiFrame.of_fs_eq
            (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2.2)
      obtain ⟨sf, hsf_eq, hsteps_Q, hvm_rest⟩ := ih hrun_f (execInst inst s1) hev_R hL_next
      exact ⟨sf, hsf_eq, .step hstep_Q hsteps_Q, hvm1.trans hvm_rest⟩

/-- Lifts a single-block `SepWP (P.rebase pl.base Htrap)` proof on total-trap hooks `Htrap` to `SepWP (P.rebase pl.base Hk)` while supplying `VmPreserved`. -/
theorem sepWP_block_vmPreserved {P : Program} (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (hprog : P = lib.program pl)
    {Htrap Hk : String → Option (State → State)}
    (htrap : IsTotalTrapHooks Htrap)
    (hchk : checkBlockSafeVm lib.text = true)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post' : State → SepProp → Prop} {post : State → SepProp → Prop}
    (hwp : SepWP (P.rebase pl.base Htrap) target_pc
      (ProofLib.stripS (ProofLib.progKeep (P.rebase pl.base Htrap)) s) Pre post')
    (hpost : ∀ (sm : State) (Pm : SepProp),
      VmPreserved s sm →
      post' (ProofLib.stripS (ProofLib.progKeep (P.rebase pl.base Htrap)) sm) Pm →
      post sm Pm) :
    SepWP (P.rebase pl.base Hk) target_pc s Pre post := by
  let R_j := P.rebase pl.base Htrap
  let keep := ProofLib.progKeep R_j
  have hall : R_j.allInstrs (fun i => !(i.isSvc0 || i.isMsrTpidrEl0)) = true := by
    dsimp only [R_j]; rw [hprog]
    exact placedLib_rebase_allInstrs_safeVm lib pl Htrap hchk
  refine SepWP.of_reaches_pc fun R hm hL => ?_
  have hL_R : R_j.CodeLoaded s.mem := hL.of_base_code rfl rfl
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  obtain ⟨sm', hsteps', hout'⟩ :=
    SepWP.to_reaches_pc hwp hm_strip (strip_codeLoaded_of_keep_local hL_R)
  rcases hout' with ⟨hpc_m', hrun_m', Pm, hmm', hpost_m'⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_Q, hvm⟩ :=
      steps_rebase_lift_strip_vm htrap hall hsteps' hrun_m' s rfl hL_R
    have hpc_m : sm.pc = target_pc := by cases sm; simpa [hsm_eq, ProofLib.stripS] using hpc_m'
    have hrun_m : sm.status = .Running := by cases sm; simpa [hsm_eq, ProofLib.stripS] using hrun_m'
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := by rw [hsm_eq]; rfl
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hvm.2.2.1 hmm'_mem
    subst hsm_eq
    exact ⟨sm, hsteps_Q, Or.inl ⟨hpc_m, hrun_m, Pm, hmm, hpost sm Pm hvm hpost_m'⟩⟩
  · exact False.elim (not_satisfies_false_sepConj hoom)

/-- Lifts an `[IsLsBlockProg]` `SepWP Ptrap` segment on total-trap hooks directly to `SepWP Pk` on the same block `i` while supplying `VmPreserved s sm`. -/
theorem sepWP_lsBlock_vmPreserved [LibsignalPlacement]
    {Ptrap Pk : Program} {i : Nat} {Htrap Hk : LibsignalHooks}
    [hIt : IsLsBlockProg Ptrap i Htrap] [hIk : IsLsBlockProg Pk i Hk]
    {lib : Obj.PlacedLib} (hlib : lib = libsignalSessionLib.blockLib i)
    (htrap : IsTotalTrapHooks Htrap)
    (hchk : checkBlockSafeVm lib.text = true)
    {target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post' : State → SepProp → Prop} {post : State → SepProp → Prop}
    (hwp : SepWP Ptrap target_pc (ProofLib.stripS (ProofLib.progKeep Ptrap) s) Pre post')
    (hpost : ∀ (sm : State) (Pm : SepProp),
      VmPreserved s sm →
      post' (ProofLib.stripS (ProofLib.progKeep Ptrap) sm) Pm →
      post sm Pm) :
    SepWP Pk target_pc s Pre post := by
  let pl := libsignalSessionLib.blockPlacement lsmpl i
  have hPt : Ptrap = (lib.program pl).rebase pl.base Htrap :=
    hIt.eq_blockProgram.trans (prog_eq_blockProgram hlib).symm
  have hPk : Pk = (lib.program pl).rebase pl.base Hk :=
    hIk.eq_blockProgram.trans (prog_eq_blockProgram hlib).symm
  subst hPt; subst hPk
  exact sepWP_block_vmPreserved lib pl rfl htrap hchk hwp hpost

theorem blk417_safeVm : checkBlockSafeVm blkLib_417.text = true := by decide +kernel

@[simp] theorem stripS_pc (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).pc = s.pc := rfl

@[simp] theorem stripS_status (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).status = s.status := rfl

@[simp] theorem stripS_sp (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).sp = s.sp := rfl

@[simp] theorem stripS_trace (keep : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS keep s).trace = s.trace := rfl

@[simp] theorem stripS_readReg64 (keep : BitVec 64 → Bool) (s : State) (r : Reg) :
    (ProofLib.stripS keep s).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[simp] theorem stripS_calleeSavedVRegs (keep : BitVec 64 → Bool) (s : State) :
    calleeSavedVRegs (ProofLib.stripS keep s) = calleeSavedVRegs s := rfl

theorem calleeSavedPreserved_of_stripS_right {keep : BitVec 64 → Bool} {s0 sm : State}
    (h : CalleeSavedPreserved s0 (ProofLib.stripS keep sm)) :
    CalleeSavedPreserved s0 sm := by
  simpa [CalleeSavedPreserved.iff_regs] using h

/-! ## Allocator Event Envelope and Budget-Threaded Specifications of `encode_bytes` -/

/-- Exact allocator event sequence of
    `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes`:
    16 calls to `__rust_alloc(msgLen, 2)` when `msgLen ≤ 1048576 ∧ msgLen % 2 = 0 ∧ 0 < msgLen`,
    and `[]` on the empty (`msgLen = 0`), odd-length, and too-long (`> 1048576`) branches. -/
def encodeBytesAllocEvents (msgLen : Nat) : List AllocEvent :=
  if msgLen ≤ 1048576 ∧ msgLen % 2 = 0 ∧ 0 < msgLen then
    (List.replicate 16 (rustAllocEvents msgLen 2)).flatten
  else
    []

def EncodeBytesEnv (msgLen : Nat) (evs : List AllocEvent) : Prop :=
  evs = encodeBytesAllocEvents msgLen

/-- Envelope-parameterized budget-threaded specification of
    `<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes`
    (Block `417`, 209 instructions). -/
def encodeBytesSpecOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : EncodeBytesGhost → List AllocEvent → Prop) :
    Spec (EncodeBytesGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = BitVec.ofNat 64 x.msg.length ∧
      x.msg.length < 2 ^ 64 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.out polyEncoderSize ∗
      bytesAt x.msgRO x.msgA x.msg ∗
      A.pool lim st s ∗ stackAt s.sp encodeBytesStack
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyEncoderAt A.repAlloc x.out (encodeBytesResult x.msg) ∗
      bytesAt x.msgRO x.msgA x.msg ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp encodeBytesStack

/-- Canonical budget-threaded specification of `<PolyEncoder as Encoder>::encode_bytes`
    (`onPanic = ⌜False⌝`, `onOom = ⌜False⌝`). -/
def encodeBytesSpec {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeBytesGhost × M.σ) :=
  encodeBytesSpecOfEnv A lim
    (fun x => EncodeBytesEnv x.msg.length)
    (fun x => EncodeBytesEnv x.msg.length)

/-- Extended-stack (`encodeBytesStackX = 560 + extHookStack`) envelope-parameterized
    budget-threaded specification of `<PolyEncoder as Encoder>::encode_bytes`. -/
def encodeBytesSpecXOfEnv {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits)
    (PreEnv PostEnv : EncodeBytesGhost → List AllocEvent → Prop) :
    Spec (EncodeBytesGhost × M.σ) where
  pre := fun (x, st) s =>
    ⌜s.readReg64 .x8 = x.out ∧ s.readReg64 .x0 = x.msgA ∧
      s.readReg64 .x1 = BitVec.ofNat 64 x.msg.length ∧
      x.msg.length < 2 ^ 64 ∧
      FitsEnv M lim st (PreEnv x)⌝ ∗
      memRegion x.out polyEncoderSize ∗
      bytesAt x.msgRO x.msgA x.msg ∗
      A.pool lim st s ∗ stackAt s.sp encodeBytesStackX
  post := fun (x, st) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      resultPolyEncoderAt A.repAlloc x.out (encodeBytesResult x.msg) ∗
      bytesAt x.msgRO x.msgA x.msg ∗
      (∃∗ evs : List AllocEvent, ⌜PostEnv x evs⌝ ∗
        A.pool lim (M.stepEvents evs st) sf) ∗
      stackAt s0.sp encodeBytesStackX

/-- Extended-stack canonical budget-threaded specification of
    `<PolyEncoder as Encoder>::encode_bytes`. -/
def encodeBytesSpecX {M : AllocCostModel} (A : RustCliAllocBudget M)
    (lim : BudgetLimits) : Spec (EncodeBytesGhost × M.σ) :=
  encodeBytesSpecXOfEnv A lim
    (fun x => EncodeBytesEnv x.msg.length)
    (fun x => EncodeBytesEnv x.msg.length)

/-- `encodeBytesSpecOfEnv` entails `encodeBytesSpecXOfEnv` by framing the unused bottom stack region. -/
theorem encodeBytesSpecXOfEnv_of_encodeBytesSpecOfEnv {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    {PreEnv PostEnv : EncodeBytesGhost → List AllocEvent → Prop}
    (h : subroutine_ok P addr (encodeBytesSpecOfEnv A lim PreEnv PostEnv)) :
    subroutine_ok P addr (encodeBytesSpecXOfEnv A lim PreEnv PostEnv) := by
  refine subroutine_ok_outcome_intro fun (x, st) R s0 hpc hrun hpre hal => ?_
  have hle : encodeBytesStack ≤ encodeBytesStackX := by decide
  have hsplit : stackAt s0.sp encodeBytesStackX =
      memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
        (encodeBytesStackX - encodeBytesStack) ∗
        stackAt s0.sp encodeBytesStack := by
    have h1 := stackAt_split_bottom s0.sp encodeBytesStack
      (encodeBytesStackX - encodeBytesStack) (by decide)
    rwa [Nat.add_sub_of_le hle] at h1
  let R' : SepProp :=
    memRegion (s0.sp - BitVec.ofNat 64 encodeBytesStackX)
      (encodeBytesStackX - encodeBytesStack) ∗ R
  have hpre' : s0.mem ⊨ (encodeBytesSpecOfEnv A lim PreEnv PostEnv).pre (x, st) s0 ∗ R' := by
    dsimp only [encodeBytesSpecXOfEnv, encodeBytesSpecOfEnv, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  refine (h.to_outcome (x, st) R' s0 hpc hrun hpre' hal).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpost⟩ | ⟨code, _, hex⟩ | ⟨_, hpost⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [encodeBytesSpecXOfEnv, encodeBytesSpecOfEnv, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · exact (not_satisfies_false_sepConj hpost).elim
  · dsimp only [encodeBytesSpecOfEnv] at hex
    rw [satisfies_pure_sepConj] at hex
    exact False.elim hex.1
  · exact (not_satisfies_false_sepConj hpost).elim

theorem encodeBytesSpecX_of_encodeBytesSpec {P : Program} {addr : BitVec 64}
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (h : subroutine_ok P addr (encodeBytesSpec A lim)) :
    subroutine_ok P addr (encodeBytesSpecX A lim) :=
  encodeBytesSpecXOfEnv_of_encodeBytesSpecOfEnv h

def EncodeBytesPlacedOkExt [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
    (blkPl_417).base
    (encodeBytesSpec A lim)

def EncodeBytesPlacedOkX [LibsignalPlacement] {M : AllocCostModel}
    (A : RustCliAllocBudget M) (lim : BudgetLimits)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
    (blkPl_417).base
    (encodeBytesSpecX A lim)

/-! ## `VmPreserved`-Strengthened Placed Epilogue and Error-Return Lemmas -/

section PlacedEpilogue
variable [LibsignalPlacement]

theorem encode_bytes_epilogue_placed {ext : String → Option (State → State)}
    (s0 s : State) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_417).base + 692#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 560#64) (htrace : s.trace = s0.trace)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        VmPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_epilogue_placed
      (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics vmTrapHooks))) s)
      Frame hsp0_align hpc hrun hsp htrace hvregs)
    fun sf Pf hvm ⟨hPf, hcs, hsp_f, htr_f⟩ =>
      ⟨hPf, hvm, calleeSavedPreserved_of_stripS_right hcs, hsp_f, htr_f⟩

theorem encode_bytes_err_odd_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_417).base + 72#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 560#64) (hx19 : s.readReg64 .x19 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗ savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderAt A out (.error (.polynomialError .messageLengthEven)) ∗
          Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        VmPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_err_odd_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics vmTrapHooks))) s)
      out Frame hsp0_align hpc hrun hsp (by simpa using hx19) htrace hvregs)
    fun sf Pf hvm ⟨hPf, hcs, hsp_f, htr_f⟩ =>
      ⟨hPf, hvm, calleeSavedPreserved_of_stripS_right hcs, hsp_f, htr_f⟩

theorem encode_bytes_err_too_long_placed {A : RustAlloc} {ext : String → Option (State → State)}
    (s0 s : State) (out : BitVec 64) (Frame : SepProp)
    (hsp0_align : (s0.sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (blkPl_417).base + 52#64) (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 560#64) (hx19 : s.readReg64 .x19 = out)
    (htrace : s.trace = s0.trace) (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0) :
    SepWP ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics ext))
      (s0.readReg64 (Reg.gpr 30#5)) s
      (memRegion out polyEncoderSize ∗ savedCells s0 ∗ stackAt (s0.sp - 96#64) (allocHookStack + 464) ∗ Frame)
      (fun sf Pf =>
        (Pf ⊢ resultPolyEncoderAt A out (.error (.polynomialError .messageLengthTooLong)) ∗
          Frame ∗ stackAt s0.sp encodeBytesStack) ∧
        VmPreserved s sf ∧
        CalleeSavedPreserved s0 sf ∧ sf.sp = s0.sp ∧ sf.trace = s0.trace) := by
  refine sepWP_lsBlock_vmPreserved blkLib_eq_417
    isTotalTrapHooks_withPanics_vmTrapHooks blk417_safeVm
    (CryptoVerification.SpqrV1.Poly.EncodeBytes.encode_bytes_err_too_long_placed
      (A := A) (ext := vmTrapHooks) s0
      (ProofLib.stripS (ProofLib.progKeep ((blkPC_417).rebase (blkPl_417).base (Rust.withPanics vmTrapHooks))) s)
      out Frame hsp0_align hpc hrun hsp (by simpa using hx19) htrace hvregs)
    fun sf Pf hvm ⟨hPf, hcs, hsp_f, htr_f⟩ =>
      ⟨hPf, hvm, calleeSavedPreserved_of_stripS_right hcs, hsp_f, htr_f⟩

end PlacedEpilogue

end LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
