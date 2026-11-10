/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.Hmac
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
public import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.EntryAndKeyBlock
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
public import LibsignalBinary.Proofs.Placed.BudgetPoolSync
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep

/-!
# `VmPreserved` Block-Lifting Helpers for `AssemblyBudget`

Relocation-safe `MSR TPIDR_EL0` block scanner (`checkBlockNoMsrTpidrEl0`) and single-block
`RunsTo` to `Steps` + `VmPreserved` lifting (`runsTo_block_lift_vm`) across `memcpy`, `memset`, and
`compress256` hooks.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux

open Arm64 Arm64.Obj ProofLib
open CryptoGames.HMAC (ShaState chunks64)
open CryptoVerification (
  LibsignalHooks LibsignalPlacement libsignalSessionLib lsmpl
)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256 (
  Frame HmacPlacedPre RunsTo hookMemcpy_eq_memcpyHook hookMemset_eq_memsetHook
  lsCompress256Sym lsMemcpySym lsMemsetSym
)
open VerifiedLibraries.RustStd (
  blockProgram_rebase_allInstrs_not_isSvc0 checkBlockNoSvc0 checkRelocWordNoSvc0
  isAdrpRelocKind isTlsdescKind relocKindSafeNoSvc0
)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps (
  vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC
)

/-! ## Relocation-Safe `MSR TPIDR_EL0` Block Scanner -/

def checkBytesNoMsrTpidrEl0 (blk : CodeBlock) : Nat → List (BitVec 8) → Bool
  | _, [] => true
  | off, b0 :: b1 :: b2 :: b3 :: rest =>
    let w := wordOfBytesLE [b0, b1, b2, b3] 0
    (match blk.relocAt? off with
     | none => !Arm64.isMsrTpidrEl0Word w
     | some r => checkRelocWordNoSvc0 w r) &&
    checkBytesNoMsrTpidrEl0 blk (off + 4) rest
  | _, _ => false

def checkBlockNoMsrTpidrEl0 (blk : CodeBlock) : Bool :=
  checkBytesNoMsrTpidrEl0 blk 0 blk.code && blk.relocs.all (fun r => relocKindSafeNoSvc0 r.kind)

private theorem checkBytesNoMsrTpidrEl0_wordOfBytesLE (blk : CodeBlock) :
    ∀ (k off : Nat) (bs : List (BitVec 8)),
      checkBytesNoMsrTpidrEl0 blk off bs = true → 4 * k + 4 ≤ bs.length →
      (let w := wordOfBytesLE bs (4 * k)
       match blk.relocAt? (off + 4 * k) with
       | none => !Arm64.isMsrTpidrEl0Word w
       | some r => checkRelocWordNoSvc0 w r) = true
  | 0, off, bs, hchk, hlen => by
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [checkBytesNoMsrTpidrEl0, Bool.and_eq_true] at hchk
      simpa [wordOfBytesLE] using hchk.1
  | k + 1, off, bs, hchk, hlen => by
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [checkBytesNoMsrTpidrEl0, Bool.and_eq_true] at hchk
      have ih := checkBytesNoMsrTpidrEl0_wordOfBytesLE blk k (off + 4) rest hchk.2
        (by simp only [List.length_cons] at hlen; omega)
      have h0 : 4 * (k + 1) = 4 * k + 4 := by omega
      have heq_w : wordOfBytesLE (b0 :: b1 :: b2 :: b3 :: rest) (4 * (k + 1)) =
          wordOfBytesLE rest (4 * k) := by simp only [wordOfBytesLE, h0]; rfl
      have heq_off : off + 4 * (k + 1) = off + 4 + 4 * k := by omega
      simpa [heq_w, heq_off] using ih

private theorem checkBytesNoMsrTpidrEl0_mod4 (blk : CodeBlock) :
    ∀ (off : Nat) (bs : List (BitVec 8)), checkBytesNoMsrTpidrEl0 blk off bs = true → bs.length % 4 = 0
  | _, [], _ => rfl
  | _, [_], h | _, [_, _], h | _, [_, _, _], h => by simp [checkBytesNoMsrTpidrEl0] at h
  | off, _ :: _ :: _ :: _ :: rest, h => by
    simp only [checkBytesNoMsrTpidrEl0, Bool.and_eq_true] at h
    have ih := checkBytesNoMsrTpidrEl0_mod4 blk (off + 4) rest h.2
    simp only [List.length_cons]; omega

private theorem not_isMsr_of_bit26_false {w : BitVec 32} (hb : w.getLsbD 26 = false) :
    Arm64.isMsrTpidrEl0Word w = false := by
  unfold Arm64.isMsrTpidrEl0Word
  apply beq_false_of_ne; intro hm
  have h26 := congrArg (fun v => v.getLsbD 26) hm
  rw [BitVec.getLsbD_and, hb, Bool.false_and] at h26
  exact absurd h26.symm (by decide)

private theorem not_isMsr_of_bit29_true {w : BitVec 32} (hb : w.getLsbD 29 = true) :
    Arm64.isMsrTpidrEl0Word w = false := by
  unfold Arm64.isMsrTpidrEl0Word
  apply beq_false_of_ne; intro hm
  have h29 := congrArg (fun v => v.getLsbD 29) hm
  have hmask : (0xffffffe0#32 : BitVec 32).getLsbD 29 = true := by decide
  rw [BitVec.getLsbD_and, hb, hmask, Bool.and_self] at h29
  exact absurd h29 (by decide)

private theorem adrWord_not_isMsr (w : BitVec 32) (place target : BitVec 64) :
    Arm64.isMsrTpidrEl0Word (adrWord (adrTemplate w) place target) = false :=
  not_isMsr_of_bit26_false (by simp [adrWord, adrWordOff, adrTemplate])

private theorem adrpWord_not_isMsr {w : BitVec 32} (hw26 : w &&& 0x0400_0000#32 = 0#32)
    (place target : BitVec 64) :
    Arm64.isMsrTpidrEl0Word (adrpWord w place target) = false := by
  have hb26 : w[26] = false := by
    have := congrArg (fun v => v.getLsbD 26) hw26
    simpa [BitVec.getLsbD_eq_getElem (by decide : 26 < 32)] using this
  exact not_isMsr_of_bit26_false (by simp [adrpWord, adrpWordOff, hb26])

private theorem tlsieMovzWord_not_isMsr (w : BitVec 32) (target : BitVec 64) :
    Arm64.isMsrTpidrEl0Word (tlsieMovzWord w target) = false :=
  not_isMsr_of_bit26_false (by simp [tlsieMovzWord])

private theorem tlsieMovkWord_not_isMsr (w : BitVec 32) (target : BitVec 64) :
    Arm64.isMsrTpidrEl0Word (tlsieMovkWord w target) = false :=
  not_isMsr_of_bit29_true (by simp [tlsieMovkWord])

private theorem tlsdescAdrPage21Word_not_isMsr (target : BitVec 64) :
    Arm64.isMsrTpidrEl0Word (tlsdescAdrPage21Word target) = false :=
  not_isMsr_of_bit26_false (by simp [tlsdescAdrPage21Word])

private theorem tlsdescLd64Lo12Word_not_isMsr (target : BitVec 64) :
    Arm64.isMsrTpidrEl0Word (tlsdescLd64Lo12Word target) = false :=
  not_isMsr_of_bit29_true (by simp [tlsdescLd64Lo12Word])

private theorem not_isMsrTpidrEl0Word_of_top6 {w : BitVec 32}
    (h : w &&& 0xfc00_0000#32 ≠ 0xd400_0000#32) :
    Arm64.isMsrTpidrEl0Word w = false := by
  unfold Arm64.isMsrTpidrEl0Word
  apply beq_false_of_ne; intro hm
  apply h
  have h1 := congrArg (· &&& 0xfc00_0000#32) hm
  simpa [BitVec.and_assoc] using h1

private theorem mask_top6_shiftLeft_10 (x : BitVec 32) :
    ((x &&& 0xfff#32) <<< 10) &&& 0xfc00_0000#32 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : (!decide (i < 10) && (0xfff#32).getLsbD (i - 10) && (0xfc00_0000#32).getLsbD i) = false := by
    revert hi; revert i; decide
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_zero]
  simp only [hi, decide_true, Bool.true_and]
  cases h1 : (!decide (i < 10)) <;> cases h2 : (0xfff#32).getLsbD (i - 10) <;>
    cases h3 : (0xfc00_0000#32).getLsbD i <;> (rw [h1, h2, h3] at hm; first | contradiction | simp)

private theorem branchWord_top6 {w : BitVec 32} (hw : w &&& 0xfc00_0000#32 ≠ 0xd400_0000#32)
    (place target : BitVec 64) : branchWord w place target &&& 0xfc00_0000#32 ≠ 0xd400_0000#32 := by
  have hr : ((branchWord w place target) &&& 0xfc00_0000#32) = w &&& 0xfc00_0000#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hf : ((0x03ff_ffff#32).getLsbD i && (0xfc00_0000#32).getLsbD i) = false := by
      revert hi; revert i; decide
    dsimp only [branchWord]
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and]
    cases h1 : (0x03ff_ffff#32).getLsbD i <;> cases h2 : (0xfc00_0000#32).getLsbD i <;>
      (rw [h1, h2] at hf; first | contradiction | simp)
  rwa [hr]

private theorem lo12Word_top6 (scale : Nat) {w : BitVec 32}
    (hw : w &&& 0xfc00_0000#32 ≠ 0xd400_0000#32) (target : BitVec 64) :
    lo12Word scale w target &&& 0xfc00_0000#32 ≠ 0xd400_0000#32 := by
  have hr : (lo12Word scale w target &&& 0xfc00_0000#32) = w &&& 0xfc00_0000#32 := by
    dsimp only [lo12Word]
    rw [BitVec.and_or_distrib_right, mask_top6_shiftLeft_10, BitVec.or_zero, BitVec.and_assoc]; rfl
  rwa [hr]

private theorem ldrToAddWord_top6 (w : BitVec 32) :
    ldrToAddWord w &&& 0xfc00_0000#32 ≠ 0xd400_0000#32 := by
  intro h; have hb := congrArg (fun v => v.getLsbD 26) h
  simp [ldrToAddWord] at hb

private theorem patchedWord_not_isMsrTpidrEl0 {blk : CodeBlock} (pl : Placement)
    (hchk : checkBlockNoMsrTpidrEl0 blk = true) {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    Arm64.isMsrTpidrEl0Word (blk.patchedWord pl off) = false := by
  unfold checkBlockNoMsrTpidrEl0 at hchk; simp only [Bool.and_eq_true, List.all_eq_true] at hchk
  rcases hchk with ⟨hbytes, hrelocs⟩
  have hoff_eq : 4 * (off / 4) = off := by omega
  have hw_off := checkBytesNoMsrTpidrEl0_wordOfBytesLE blk (off / 4) 0 blk.code hbytes (by omega)
  simp only [Nat.zero_add, hoff_eq] at hw_off
  change (match blk.relocAt? off with
    | none => !Arm64.isMsrTpidrEl0Word (blk.wordAt off)
    | some r => checkRelocWordNoSvc0 (blk.wordAt off) r) = true at hw_off
  unfold CodeBlock.patchedWord
  cases hr : blk.relocAt? off with
  | none =>
    rw [hr] at hw_off
    cases h : Arm64.isMsrTpidrEl0Word (blk.wordAt off) <;> simp_all
  | some r =>
    dsimp only; rw [hr] at hw_off; dsimp only at hw_off
    have hrmem : r ∈ blk.relocs := List.mem_of_find?_eq_some hr
    have hksafe := hrelocs r hrmem
    split
    · decide
    · split
      · exact adrWord_not_isMsr _ _ _
      · split
        · exact adrWord_not_isMsr _ _ _
        · split
          · rename_i _ _ _ hgot
            simp only [Bool.and_eq_true] at hgot
            have hisgot : r.kind.isGotOrTlsIe = true := hgot.1.1
            cases hk : r.kind
            all_goals rw [hk] at hisgot; try contradiction
            · simp [CodeBlock.patchGotOrTlsIeRelaxed, nopWord, Arm64.isMsrTpidrEl0Word]
            · exact not_isMsrTpidrEl0Word_of_top6 (lo12Word_top6 0 (ldrToAddWord_top6 _) _)
            · exact tlsieMovzWord_not_isMsr _ _
            · exact tlsieMovkWord_not_isMsr _ _
          · unfold checkRelocWordNoSvc0 at hw_off
            cases hk : r.kind
            all_goals rw [hk] at hksafe; try contradiction
            all_goals rw [hk] at hw_off; simp only [isTlsdescKind, isAdrpRelocKind, Bool.false_or,
              Bool.true_or, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_eq_true,
              bne_iff_ne, beq_iff_eq] at hw_off
            · exact not_isMsrTpidrEl0Word_of_top6 (branchWord_top6 hw_off _ _)
            · exact not_isMsrTpidrEl0Word_of_top6 (branchWord_top6 hw_off _ _)
            · exact adrpWord_not_isMsr hw_off.2 _ _
            · exact not_isMsrTpidrEl0Word_of_top6 (lo12Word_top6 0 hw_off _)
            · exact not_isMsrTpidrEl0Word_of_top6 (lo12Word_top6 0 hw_off _)
            · exact not_isMsrTpidrEl0Word_of_top6 (lo12Word_top6 1 hw_off _)
            · exact not_isMsrTpidrEl0Word_of_top6 (lo12Word_top6 2 hw_off _)
            · exact not_isMsrTpidrEl0Word_of_top6 (lo12Word_top6 3 hw_off _)
            · exact not_isMsrTpidrEl0Word_of_top6 (lo12Word_top6 4 hw_off _)
            · exact adrpWord_not_isMsr hw_off.2 _ _
            · exact not_isMsrTpidrEl0Word_of_top6 (lo12Word_top6 3 hw_off _)
            · exact adrpWord_not_isMsr hw_off.2 _ _
            · exact not_isMsrTpidrEl0Word_of_top6 (lo12Word_top6 3 hw_off _)
            · exact tlsdescAdrPage21Word_not_isMsr _
            · exact tlsdescLd64Lo12Word_not_isMsr _
            · simp [patchRelocWord, nopWord, Arm64.isMsrTpidrEl0Word]
            · simp [patchRelocWord, nopWord, Arm64.isMsrTpidrEl0Word]

private theorem bytesAllWords_of_drop4 {pw : BitVec 32 → Bool} :
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
        bytesAllWords_of_drop4 n rest (by simp at hlen; omega) fun k hk => by
          have hk' := h (k + 1) (Nat.succ_lt_succ hk); have heq : 4 * (k + 1) = 4 + 4 * k := by omega
          rw [heq, ← List.drop_drop] at hk'; simpa using hk'
      simp [Arm64.bytesAllWords, h0, hrest]

private theorem blockProgram_allInstrs_not_isMsrTpidrEl0 (lib : MultiPlacedLib) (mpl : MultiPlacement)
    (j : Nat) (X : String → Option (State → State))
    (hchk : checkBlockNoMsrTpidrEl0 (lib.blockLib j).text = true) :
    (lib.blockProgram mpl j X).allInstrs (fun i => !i.isMsrTpidrEl0) = true := by
  let prog := lib.blockProgram mpl j X
  let blk := (lib.blockLib j).text; let pl := lib.blockPlacement mpl j
  have hcode : prog.code = blk.patched pl := rfl
  have hmod4 : blk.code.length % 4 = 0 := by
    unfold checkBlockNoMsrTpidrEl0 at hchk; simp only [Bool.and_eq_true] at hchk
    exact checkBytesNoMsrTpidrEl0_mod4 blk 0 blk.code hchk.1
  have hdiv : prog.code.length = 4 * (blk.code.length / 4) := by rw [hcode, CodeBlock.length_patched]
  refine Program.allInstrs_of_allWords (fun _ _ hd hpw => Arm64.decode_not_isMsrTpidrEl0 hd hpw) ?_
  unfold Program.allWords; refine bytesAllWords_of_drop4 (blk.code.length / 4) prog.code hdiv fun k hk => ?_
  have hal : (4 * k) % 4 = 0 := by omega
  have hlen : 4 * k + 4 ≤ blk.code.length := by omega
  have hrw : prog.readWordOff (4 * k) = some (blk.patchedWord pl (4 * k)) :=
    CodeBlock.readWordOff_patched hcode hal hlen
  unfold Program.readWordOff at hrw; simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hrw
  match hdrop : prog.code.drop (4 * k) with
  | [] | [_] | [_, _] | [_, _, _] => simp [hdrop] at hrw
  | b0 :: b1 :: b2 :: b3 :: _ =>
    rw [hdrop] at hrw; injection hrw with hw; dsimp only
    rw [hw, patchedWord_not_isMsrTpidrEl0 pl hchk hal hlen]; rfl

/-! ## `VmPreserved` Lifting for `RunsTo` on Placed Blocks -/

def hmacExcHooks (F : ShaState → List (BitVec 8) → ShaState) (H : LibsignalHooks) :
    LibsignalHooks :=
  fun n =>
    if n = lsMemcpySym then some memcpyHook
    else if n = lsMemsetSym then some memsetHook
    else if n = lsCompress256Sym then some (compress256Hook F)
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

theorem hmacExcHooks_memcpy (F : ShaState → List (BitVec 8) → ShaState) (H : LibsignalHooks) :
    hmacExcHooks F H lsMemcpySym = some memcpyHook := by
  simp [hmacExcHooks]

theorem hmacExcHooks_memset (F : ShaState → List (BitVec 8) → ShaState) (H : LibsignalHooks) :
    hmacExcHooks F H lsMemsetSym = some memsetHook := by
  have hne : lsMemsetSym ≠ lsMemcpySym := by decide
  simp [hmacExcHooks, hne]

theorem hmacExcHooks_compress (F : ShaState → List (BitVec 8) → ShaState) (H : LibsignalHooks) :
    hmacExcHooks F H lsCompress256Sym = some (compress256Hook F) := by
  have hne1 : lsCompress256Sym ≠ lsMemcpySym := by decide
  have hne2 : lsCompress256Sym ≠ lsMemsetSym := by decide
  simp [hmacExcHooks, hne1, hne2]

private theorem stripExecOutside_writeBytes (p : BitVec 64 → Bool) :
    ∀ (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)),
      (ProofLib.stripExecOutside p m).writeBytes a bs =
        ProofLib.stripExecOutside p (m.writeBytes a bs)
  | m, _, [] => rfl
  | m, a, b :: bs => by
    simp only [Memory.writeBytes, ProofLib.strip_write8,
      stripExecOutside_writeBytes p (m.write8 a b) (a + 1#64) bs]

theorem stripExecOutside_readBytes (p : BitVec 64 → Bool) :
    ∀ (m : Memory) (a : BitVec 64) (n : Nat),
      (ProofLib.stripExecOutside p m).readBytes a n = m.readBytes a n
  | _, _, 0 => rfl
  | m, a, n + 1 => by
    simp only [Memory.readBytes, ProofLib.strip_read8,
      stripExecOutside_readBytes p m (a + 1#64) n]

private theorem stripExecOutside_readShaState (p : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    readShaState (ProofLib.stripExecOutside p m) a = readShaState m a := by
  simp [readShaState, Memory.read32, ProofLib.strip_read8]

private theorem stripS_memcpyHook (p : BitVec 64 → Bool) (s : State) :
    memcpyHook (ProofLib.stripS p s) = ProofLib.stripS p (memcpyHook s) := by
  rw [← hookMemcpy_eq_memcpyHook]
  cases s
  dsimp only [ProofLib.stripS, ProofLib.hookMemcpy, ProofLib.retHook, State.setMem, State.setPC,
    State.readReg64]
  rw [stripExecOutside_readBytes, stripExecOutside_writeBytes]

private theorem stripS_memsetHook (p : BitVec 64 → Bool) (s : State) :
    memsetHook (ProofLib.stripS p s) = ProofLib.stripS p (memsetHook s) := by
  cases s
  dsimp only [ProofLib.stripS, memsetHook, returnToLinkRegister, State.setMem, State.setPC,
    State.readReg64]
  rw [stripExecOutside_writeBytes]

private theorem stripS_compress256Hook (F : ShaState → List (BitVec 8) → ShaState)
    (p : BitVec 64 → Bool) (s : State) :
    compress256Hook F (ProofLib.stripS p s) = ProofLib.stripS p (compress256Hook F s) := by
  cases s
  dsimp only [ProofLib.stripS, compress256Hook, returnToLinkRegister, State.setMem, State.setPC,
    State.readReg64]
  rw [stripExecOutside_readShaState, stripExecOutside_readBytes, stripExecOutside_writeBytes]

private theorem vmPreserved_memcpyHook (s : State) : VmPreserved s (memcpyHook s) := by
  rw [← hookMemcpy_eq_memcpyHook]
  dsimp only [ProofLib.hookMemcpy, ProofLib.retHook]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem vmPreserved_memsetHook (s : State) : VmPreserved s (memsetHook s) := by
  rw [← hookMemset_eq_memsetHook]
  dsimp only [ProofLib.hookMemset, ProofLib.retHook]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem vmPreserved_compress256Hook (F : ShaState → List (BitVec 8) → ShaState) (s : State) :
    VmPreserved s (compress256Hook F s) := by
  dsimp only [compress256Hook, returnToLinkRegister]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem option_or_isSome {α : Type} (o₁ o₂ : Option α) :
    (o₁.or o₂).isSome = (o₁.isSome || o₂.isSome) := by cases o₁ <;> rfl

private theorem findSome?_isSome_congr {α β γ : Type} (l : List α)
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

private theorem hmacExcHooks_isSome {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks}
    (h_mc : H lsMemcpySym = some memcpyHook)
    (h_ms : H lsMemsetSym = some memsetHook)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (n : String) :
    (hmacExcHooks F H n).isSome = (H n).isSome := by
  unfold hmacExcHooks
  by_cases h1 : n = lsMemcpySym
  · subst h1; simp [h_mc]
  · by_cases h2 : n = lsMemsetSym
    · subst h2; simp [h1, h_ms]
    · by_cases h3 : n = lsCompress256Sym
      · subst h3; simp [h1, h2, h_c256]
      · simp [h1, h2, h3]

private theorem blockProgram_hmacExcHooks_externAt?_isSome
    (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_mc : H lsMemcpySym = some memcpyHook)
    (h_ms : H lsMemsetSym = some memsetHook)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (pc : BitVec 64) :
    ((lib.blockProgram pl i (hmacExcHooks F H)).externAt? pc).isSome =
      ((lib.blockProgram pl i H).externAt? pc).isSome := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program
  dsimp only
  rw [option_or_isSome, option_or_isSome]
  rw [findSome?_isSome_congr _
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then hmacExcHooks F H x.1 else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then H x.1 else none)]
  intro x
  cases h : (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) <;>
    simp [hmacExcHooks_isSome h_mc h_ms h_c256]

private theorem findSome?_hmacExcHooks_cases {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks}
    (h_mc : H lsMemcpySym = some memcpyHook)
    (h_ms : H lsMemsetSym = some memsetHook)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then hmacExcHooks F H n else none) = some f →
      (∀ s, (f s).status = .Exception "ext") ∨
      ((f = memcpyHook ∨ f = memsetHook ∨ f = compress256Hook F) ∧
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f)
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons] at h ⊢
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_hmacExcHooks_cases h_mc h_ms h_c256 tl h
    · simp only [ho, ↓reduceIte] at h ⊢
      unfold hmacExcHooks at h
      by_cases h1 : n = lsMemcpySym
      · subst h1; simp only [↓reduceIte, Option.some.injEq] at h; subst h
        rw [h_mc]; exact Or.inr ⟨Or.inl rfl, rfl⟩
      · by_cases h2 : n = lsMemsetSym
        · subst h2; simp only [h1, ↓reduceIte, Option.some.injEq] at h; subst h
          rw [h_ms]; exact Or.inr ⟨Or.inr (Or.inl rfl), rfl⟩
        · by_cases h3 : n = lsCompress256Sym
          · subst h3; simp only [h1, h2, ↓reduceIte, Option.some.injEq] at h; subst h
            rw [h_c256]; exact Or.inr ⟨Or.inr (Or.inr rfl), rfl⟩
          · simp only [h1, h2, h3, ↓reduceIte] at h
            cases hHn : H n with
            | none =>
              rw [hHn] at h
              dsimp only [Option.map] at h ⊢
              exact findSome?_hmacExcHooks_cases h_mc h_ms h_c256 tl h
            | some g =>
              rw [hHn] at h; simp only [Option.map, Option.some.injEq] at h; subst h
              exact Or.inl fun s => by cases s; rfl

private theorem blockProgram_hmacExcHooks_externAt?_cases
    {lib : MultiPlacedLib} {pl : MultiPlacement} {i : Nat}
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_mc : H lsMemcpySym = some memcpyHook)
    (h_ms : H lsMemsetSym = some memsetHook)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram pl i (hmacExcHooks F H)).externAt? pc = some f) :
    (∀ s, (f s).status = .Exception "ext") ∨
    ((f = memcpyHook ∨ f = memsetHook ∨ f = compress256Hook F) ∧
      (lib.blockProgram pl i H).externAt? pc = some f) := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program at h ⊢
  dsimp only at h ⊢
  have hnone : ∀ (l : List (String × Nat)),
      (l.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro l; induction l with | nil => rfl | cons _ _ ih => exact ih
  simp only [ite_self, hnone, Option.or_none] at h ⊢
  exact findSome?_hmacExcHooks_cases h_mc h_ms h_c256 _ h

private theorem strip_codeLoaded_of_keep {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem strip_execOnlyIn_of_keep (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with
  | refl => exact hr
  | step h1 _ => cases h1 <;> assumption

private theorem step_P_extern_eq {P : Program} {s1 s2 : State} {f : State → State}
    (hstep : Step P s1 s2) (hrun2 : s2.status = .Running)
    (heP : P.externAt? s1.pc = some f) :
    s2 = f s1 ∧ s1.mem.KeepsFrozen (f s1).mem ∧ (f s1).symtab = s1.symtab := by
  cases hstep with
  | @exec inst _ hfe =>
    unfold Program.fetchMem at hfe
    rw [heP] at hfe; simp at hfe
  | halt_unmapped _ _ he =>
    rw [heP] at he; cases he
  | extern _ he hkf hsym =>
    rw [heP] at he; injection he with hff; subst hff
    exact ⟨rfl, hkf, hsym⟩
  | extern_fault _ _ _ =>
    cases s1; cases hrun2

private theorem step_P_exec_eq {P : Program} {s1 s2 : State} {inst : Instr}
    (hstep : Step P s1 s2)
    (hfeP : P.fetchMem s1.mem s1.pc = some inst)
    (hnsvc0 : inst.isSvc0 = false) :
    s2 = execInst inst s1 := by
  have heP_none : P.externAt? s1.pc = none := by
    unfold Program.fetchMem at hfeP
    cases he : P.externAt? s1.pc with
    | none => rfl
    | some _ => simp [he] at hfeP
  cases hstep with
  | @exec inst' _ hfe' =>
    rw [hfeP] at hfe'; injection hfe' with hi; subst hi
    exact Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
  | halt_unmapped _ hfe' _ =>
    rw [hfeP] at hfe'; cases hfe'
  | extern _ he _ _ =>
    rw [heP_none] at he; cases he
  | extern_fault _ he _ =>
    rw [heP_none] at he; cases he

private theorem steps_hmacExc_lift_strip (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_mc : H lsMemcpySym = some memcpyHook)
    (h_ms : H lsMemsetSym = some memsetHook)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (hall_svc : (lib.blockProgram pl i (hmacExcHooks F H)).allInstrs (fun ins => !ins.isSvc0) = true)
    (hall_msr : (lib.blockProgram pl i (hmacExcHooks F H)).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true)
    {s1' sf' : State}
    (hsteps : Steps (lib.blockProgram pl i (hmacExcHooks F H)) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let Q := lib.blockProgram pl i (hmacExcHooks F H)
    let P := lib.blockProgram pl i H
    ∀ (s1 sfP : State),
      s1' = ProofLib.stripS (ProofLib.progKeep Q) s1 →
      Q.CodeLoaded s1.mem →
      Steps P s1 sfP →
      sfP.status = .Running →
      ∃ sf : State,
        Steps P s1 sf ∧
        VmPreserved s1 sf ∧
        (sf' = ProofLib.stripS (ProofLib.progKeep Q) sf ∨ sf = sfP) := by
  intro Q P
  induction hsteps with
  | refl =>
    intro s1 _ hs1 _ _ _
    exact ⟨s1, .refl s1, VmPreserved.refl s1, Or.inl hs1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 sfP hsa hL1 hstepsP hrun_sfP
    cases hstepsP with
    | refl =>
      exact ⟨s1, .refl s1, VmPreserved.refl s1, Or.inr rfl⟩
    | @step _ s2P _ h1_P hrest_P =>
      have hr2P : s2P.status = .Running := steps_start_running hrest_P hrun_sfP
      have hrb' : sb'.status = .Running := steps_start_running hrest hrun_f
      subst hsa
      cases h1 with
      | halt_unmapped _ _ _ => cases s1; cases hrb'
      | extern_fault _ _ _ => cases s1; cases hrb'
      | extern hr1' he _ _ =>
        have hr1 : s1.status = .Running := by cases s1; exact hr1'
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := by cases s1; rfl
        rw [hpc_eq] at he
        rcases blockProgram_hmacExcHooks_externAt?_cases h_mc h_ms h_c256 he with
          htrap | ⟨hf_which, heP⟩
        · rw [htrap] at hrb'; cases hrb'
        · obtain ⟨hs2P, hkf1, hsym1⟩ := step_P_extern_eq h1_P hr2P heP
          rw [hs2P] at hrest_P
          have hstepP := Step.extern hr1 heP hkf1 hsym1
          rcases hf_which with rfl | rfl | rfl
          · obtain ⟨sf, hsteps_rest, hvm_rest, hor⟩ :=
              ih hrun_f (memcpyHook s1) sfP (stripS_memcpyHook (ProofLib.progKeep Q) s1)
                (hL1.of_keepsFrozen hkf1) hrest_P hrun_sfP
            exact ⟨sf, .step hstepP hsteps_rest, (vmPreserved_memcpyHook s1).trans hvm_rest, hor⟩
          · obtain ⟨sf, hsteps_rest, hvm_rest, hor⟩ :=
              ih hrun_f (memsetHook s1) sfP (stripS_memsetHook (ProofLib.progKeep Q) s1)
                (hL1.of_keepsFrozen hkf1) hrest_P hrun_sfP
            exact ⟨sf, .step hstepP hsteps_rest, (vmPreserved_memsetHook s1).trans hvm_rest, hor⟩
          · obtain ⟨sf, hsteps_rest, hvm_rest, hor⟩ :=
              ih hrun_f (compress256Hook F s1) sfP
                (stripS_compress256Hook F (ProofLib.progKeep Q) s1)
                (hL1.of_keepsFrozen hkf1) hrest_P hrun_sfP
            exact ⟨sf, .step hstepP hsteps_rest,
              (vmPreserved_compress256Hook F s1).trans hvm_rest, hor⟩
      | @exec inst hr1' hfe' =>
        have hr1 : s1.status = .Running := by cases s1; exact hr1'
        have hL1' : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
          strip_codeLoaded_of_keep hL1
        have hexec' : Q.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep Q) s1).mem :=
          strip_execOnlyIn_of_keep Q s1.mem
        have hnsvc0 : inst.isSvc0 = false := by
          simpa using Program.fetchMem_of_allInstrs hall_svc hL1' hexec' _ inst hfe'
        have hnmsr : inst.isMsrTpidrEl0 = false := by
          simpa using Program.fetchMem_of_allInstrs hall_msr hL1' hexec' _ inst hfe'
        have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
          have hpc_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).pc = s1.pc := by cases s1; rfl
          have hmem_eq : (ProofLib.stripS (ProofLib.progKeep Q) s1).mem =
              ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem := by cases s1; rfl
          rw [hpc_eq, hmem_eq] at hfe'
          unfold Program.fetchMem at hfe' ⊢
          have his : (Q.externAt? s1.pc).isSome = (P.externAt? s1.pc).isSome :=
            blockProgram_hmacExcHooks_externAt?_isSome lib pl i h_mc h_ms h_c256 s1.pc
          rw [his] at hfe'
          cases heP : (P.externAt? s1.pc).isSome
          · simp only [heP, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
            by_cases hal_pc : s1.pc.toNat % 4 = 0
            · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
              split at hfe'
              · contradiction
              · rename_i hce'
                have hce : s1.mem.canExec s1.pc 4 = true := by
                  simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
                  unfold Memory.canExec at hce' ⊢
                  rw [Memory.allPerm_iff] at hce' ⊢
                  intro k hk
                  have hxk := hce' k hk
                  rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
                have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep Q) s1.mem).read32 s1.pc =
                    s1.mem.read32 s1.pc := by
                  simp [Memory.read32, ProofLib.strip_read8]
                rw [hr32] at hfe'
                simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
                exact hfe'
            · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'
              contradiction
          · simp only [heP, ↓reduceIte] at hfe'
            contradiction
        have hev_Q : Q.evalInst inst (ProofLib.stripS (ProofLib.progKeep Q) s1) =
            ProofLib.stripS (ProofLib.progKeep Q) (execInst inst s1) := by
          rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
        have hs2P := step_P_exec_eq h1_P hfe_P hnsvc0
        rw [hs2P] at hrest_P
        have hstep_P : Step P s1 (execInst inst s1) := by
          have := Step.exec (prog := P) hr1 hfe_P
          rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
        have hLQ_next : Q.CodeLoaded (execInst inst s1).mem := hstep_P.codeLoaded hL1
        obtain ⟨sf, hsteps_rest, hvm_rest, hor⟩ :=
          ih hrun_f (execInst inst s1) sfP hev_Q hLQ_next hrest_P hrun_sfP
        have hnsp1 := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1
        have htp1 := Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1
        exact ⟨sf, .step hstep_P hsteps_rest, (hnsp1.toVmPreserved htp1).trans hvm_rest, hor⟩

theorem runsTo_block_lift_vm [LibsignalPlacement] {blkLib : PlacedLib}
    {i : Nat} {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_mc : H lsMemcpySym = some memcpyHook)
    (h_ms : H lsMemsetSym = some memsetHook)
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (hlib : blkLib = libsignalSessionLib.blockLib i)
    (hchk_svc : checkBlockNoSvc0 blkLib.text = true := by rfl)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true := by rfl)
    {s : State} {PostP PostQ : State → Prop}
    (hL : (libsignalSessionLib.blockProgram lsmpl i H).CodeLoaded s.mem)
    (hrunsP : RunsTo (libsignalSessionLib.blockProgram lsmpl i H) s PostP)
    (hrunsQ : RunsTo (libsignalSessionLib.blockProgram lsmpl i (hmacExcHooks F H))
      (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl i (hmacExcHooks F H))) s) PostQ)
    (hPostP_run : ∀ s', PostP s' → s'.status = .Running)
    (hPostQ_run : ∀ s', PostQ s' → s'.status = .Running) :
    let Q := libsignalSessionLib.blockProgram lsmpl i (hmacExcHooks F H)
    ∃ sf : State,
      Steps (libsignalSessionLib.blockProgram lsmpl i H) s sf ∧
      VmPreserved s sf ∧
      sf.trace = s.trace ∧
      calleeSavedVRegs sf = calleeSavedVRegs s ∧
      (PostQ (ProofLib.stripS (ProofLib.progKeep Q) sf) ∨ PostP sf) := by
  subst hlib
  intro Q
  have hall0 := blockProgram_rebase_allInstrs_not_isSvc0 libsignalSessionLib lsmpl i hchk_svc
  have hall_svc : Q.allInstrs (fun ins => !ins.isSvc0) = true := hall0
  have hall_msr : Q.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true :=
    blockProgram_allInstrs_not_isMsrTpidrEl0 libsignalSessionLib lsmpl i (hmacExcHooks F H) hchk_msr
  have hLQ : Q.CodeLoaded s.mem := hL.of_base_code rfl rfl
  have hLQ_strip : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s).mem := by
    have hm : (ProofLib.stripS (ProofLib.progKeep Q) s).mem =
        ProofLib.stripExecOutside (ProofLib.progKeep Q) s.mem := by cases s; rfl
    rw [hm]; exact strip_codeLoaded_of_keep hLQ
  obtain ⟨sfP, hstepsP, htrP, hvregsP, hPostP, _⟩ := hrunsP hL
  obtain ⟨sf', hstepsQ, htr', hvregs', hPost', _⟩ := hrunsQ hLQ_strip
  obtain ⟨sf, hsteps_out, hvm, hsf_eq | rfl⟩ :=
    steps_hmacExc_lift_strip libsignalSessionLib lsmpl i h_mc h_ms h_c256 hall_svc hall_msr
      hstepsQ (hPostQ_run sf' hPost') s sfP rfl hLQ hstepsP (hPostP_run sfP hPostP)
  · have htr : sf.trace = s.trace := by
      have h1 : sf'.trace = sf.trace := by rw [hsf_eq]; cases sf; rfl
      have h2 : (ProofLib.stripS (ProofLib.progKeep Q) s).trace = s.trace := by cases s; rfl
      exact h1.symm.trans (htr'.trans h2)
    have hvregs : calleeSavedVRegs sf = calleeSavedVRegs s := by
      have h1 : calleeSavedVRegs sf' = calleeSavedVRegs sf := by
        rw [hsf_eq]; cases sf; rfl
      have h2 : calleeSavedVRegs (ProofLib.stripS (ProofLib.progKeep Q) s) = calleeSavedVRegs s := by
        cases s; rfl
      exact h1.symm.trans (hvregs'.trans h2)
    exact ⟨sf, hsteps_out, hvm, htr, hvregs, Or.inl (hsf_eq ▸ hPost')⟩
  · exact ⟨sf, hsteps_out, hvm, htrP, hvregsP, Or.inr hPostP⟩

theorem stripExecOutside_readable (p : BitVec 64 → Bool) (m : Memory)
    (a : BitVec 64) (n : Nat) (h : m.Readable a n) :
    (ProofLib.stripExecOutside p m).Readable a n := by
  intro x hx
  obtain ⟨hr, hnl⟩ := h x hx
  exact ⟨(ProofLib.strip_perm_props p m x).1.trans hr, (ProofLib.strip_isLazyFree p m x).trans hnl⟩

theorem stripExecOutside_rw (p : BitVec 64 → Bool) (m : Memory)
    (a : BitVec 64) (n : Nat) (h : Memory.RW m a n) :
    Memory.RW (ProofLib.stripExecOutside p m) a n := fun x hx => by
  rw [Memory.permNoLazy_eq_some_rw_iff]
  have ⟨hrw, hnl⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (h x hx)
  exact ⟨(ProofLib.strip_perm_props p m x).2.2.2.mpr hrw,
    (ProofLib.strip_isLazyFree p m x).trans hnl⟩

theorem hmacPlacedPre_stripS [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {key inp : List (BitVec 8)} {s0 : State} (p : BitVec 64 → Bool)
    (hpre : HmacPlacedPre F key inp s0) :
    HmacPlacedPre F key inp (ProofLib.stripS p s0) := by
  have hmem : (ProofLib.stripS p s0).mem = ProofLib.stripExecOutside p s0.mem := by cases s0; rfl
  have hr64 : ∀ r, (ProofLib.stripS p s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsp : (ProofLib.stripS p s0).sp = s0.sp := by cases s0; rfl
  exact {
    pc_eq := (by cases s0; rfl : (ProofLib.stripS p s0).pc = s0.pc).trans hpre.pc_eq
    status := (by cases s0; rfl : (ProofLib.stripS p s0).status = s0.status).trans hpre.status
    sp_aligned := hsp.symm ▸ hpre.sp_aligned
    x2_eq := (hr64 .x2).trans hpre.x2_eq
    x4_eq := (hr64 .x4).trans hpre.x4_eq
    key_len := hpre.key_len
    inp_len := hpre.inp_len
    key_eq := by rw [hmem, hr64, stripExecOutside_readBytes]; exact hpre.key_eq
    inp_eq := by rw [hmem, hr64, stripExecOutside_readBytes]; exact hpre.inp_eq
    iv_eq := by rw [hmem, stripExecOutside_readBytes]; exact hpre.iv_eq
    read_iv := by rw [hmem]; exact stripExecOutside_readable p s0.mem _ _ hpre.read_iv
    read_inp := by rw [hmem, hr64]; exact stripExecOutside_readable p s0.mem _ _ hpre.read_inp
    rw_out := by rw [hmem, hr64]; exact stripExecOutside_rw p s0.mem _ _ hpre.rw_out
    rw_stack := by rw [hmem, hsp]; exact stripExecOutside_rw p s0.mem _ _ hpre.rw_stack
    disj_iv_stack := hsp.symm ▸ hpre.disj_iv_stack
    disj_out_stack := by rw [hr64, hsp]; exact hpre.disj_out_stack
    disj_key_stack := by rw [hr64, hsp]; exact hpre.disj_key_stack
    disj_inp_stack := by rw [hr64, hsp]; exact hpre.disj_inp_stack
  }

theorem unstrip_frame {p : BitVec 64 → Bool} {m m' : Memory} {rs : List (BitVec 64 × Nat)}
    (hf : Frame (ProofLib.stripExecOutside p m) (ProofLib.stripExecOutside p m') rs)
    (hperm : ∀ a, m'.perm a = m.perm a) :
    Frame m m' rs :=
  ⟨fun a hout => by simpa only [ProofLib.strip_read8] using hf.1 a hout,
   funext hperm,
   fun a hout => by simpa only [ProofLib.strip_isLazyFree] using hf.2.2.1 a hout,
   fun a hlf => by
     simpa only [ProofLib.strip_isLazyFree] using
       hf.2.2.2.1 a (by simpa only [ProofLib.strip_isLazyFree] using hlf),
   fun a ha => by
     simpa only [ProofLib.strip_isAnon] using
       hf.2.2.2.2 a (by simpa only [ProofLib.strip_isAnon] using ha)⟩

end LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
