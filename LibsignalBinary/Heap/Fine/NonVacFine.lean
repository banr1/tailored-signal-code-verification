/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Spec.Top
public import VerifiedLibraries.Mallocng.Proofs.Common
public import VerifiedLibraries.Mallocng.Proofs.BridgeHelpers
public import VerifiedLibraries.Mallocng.Proofs.RdlAllocProof
public import VerifiedLibraries.RustStd.Proofs.MallocngBridgeCommon
public import ProofLib
public import ProofLib.Disproof
public import ProofLib.Placed.Multi
public import LibsignalBinary.Heap.Fine.RustEntriesFine
public import LibsignalBinary.Heap.IfaceBudgetBase

/-!
# Sub-`1 GiB` Non-Vacuity and Total-Correctness Witnesses for `fineCostModel`

Constructs a concrete placed program containing `VerifiedLibraries.mallocngLib`, `__rdl_*` shims,
and `__rust_*` `B`-thunks under enforced `512 MiB` (`< 1 GiB`) physical-memory limits, proving:
- `FitsTraceOf fineCostModel` on `[.alloc 72]`, `workedCallerTrace`, and `2 ^ 20` 8-byte
  allocations (whereas `coarseCostModel` rejects `workedCallerTrace` for every `physCap < 4 GiB`).
- Joint satisfiability of startup pool state, `RustCliAllocBudgetEntries`, and
  `RustCliAllocNoOomEntries`, yielding unconditional normal return of `__rust_alloc(72, 8)`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000

@[expose] public noncomputable section

namespace LibsignalBinary.Heap.Fine

open Arm64 Arm64.Obj ProofLib.SepLogic ProofLib.ProgramReflection
open ProofLib hiding MallocngMinBlockCost mallocngSizeClassUnits mallocngRoTablesBytes
  MallocngAddrs MallocngIface
open ProofLib.StdStartup (hasInstrs hasWords_of_wordTree)
open CryptoVerification.RustHeap (allocHookStack)
open VerifiedLibraries VerifiedLibraries.Mallocng.Proofs
open VerifiedLibraries.Mallocng hiding AllocCostModel AllocEvent MallocngCostModelIface
  MallocngCostModelSound MallocngModelEnv MallocngModelPlacedEntryContracts
  MallocngModelPostEnv MallocngStepOomCond
open LibsignalBinary.Heap

/-! ## Concrete Placed `mallocngLib` and Rust Shim Program -/

private theorem drop_append_of_cons4 {α : Type} :
    ∀ (xs ys : List α) (k : Nat) {b0 b1 b2 b3 : α} {rest : List α},
      xs.drop k = b0 :: b1 :: b2 :: b3 :: rest →
      (xs ++ ys).drop k = b0 :: b1 :: b2 :: b3 :: (rest ++ ys)
  | [], _, _, _, _, _, _, _, h => by simp at h
  | _ :: _, _, 0, _, _, _, _, _, h => by cases h; rfl
  | _ :: xs, ys, k + 1, _, _, _, _, _, h => drop_append_of_cons4 xs ys k h

private theorem readWordOff_append_right {P : Program} {tail : List (BitVec 8)}
    {off : Nat} {w : BitVec 32}
    (h : P.readWordOff off = some w) :
    ({ P with code := P.code ++ tail }).readWordOff off = some w := by
  unfold Program.readWordOff at h ⊢
  by_cases hmod : off % 4 ≠ 0
  · simp [hmod] at h
  · simp only [hmod, ↓reduceIte] at h ⊢
    cases hdrop : P.code.drop off with
    | nil => rw [hdrop] at h; cases h
    | cons b0 r0 =>
      cases r0 with
      | nil => rw [hdrop] at h; cases h
      | cons b1 r1 =>
        cases r1 with
        | nil => rw [hdrop] at h; cases h
        | cons b2 r2 =>
          cases r2 with
          | nil => rw [hdrop] at h; cases h
          | cons b3 rest =>
            rw [hdrop] at h
            rw [drop_append_of_cons4 P.code tail off hdrop]
            exact h

private theorem fetch_append_right {P : Program} {tail : List (BitVec 8)}
    {pc : BitVec 64} {inst : Instr}
    (h : P.fetch pc = some inst) :
    ({ P with code := P.code ++ tail }).fetch pc = some inst := by
  unfold Program.fetch at h ⊢
  have hext : ({ P with code := P.code ++ tail }).externAt? pc = P.externAt? pc := rfl
  rw [hext]
  by_cases hs : (P.externAt? pc).isSome = true
  · simp [hs] at h
  · simp only [hs] at h ⊢
    cases hrw : P.readWordOff (pc - P.base).toNat with
    | none => rw [hrw] at h; cases h
    | some w =>
      rw [hrw] at h
      have hrw' : ({ P with code := P.code ++ tail }).readWordOff (pc - P.base).toNat = some w :=
        readWordOff_append_right hrw
      change (({ P with code := P.code ++ tail }).readWordOff (pc - P.base).toNat).bind decode =
        some inst
      rw [hrw']
      exact h

private theorem hasInstrs_append_right {P : Program} {tail : List (BitVec 8)}
    {addr : BitVec 64} {is : List Instr}
    (h : hasInstrs P addr is) :
    hasInstrs { P with code := P.code ++ tail } addr is :=
  fun i hi => fetch_append_right (h i hi)

private theorem hasWords_append_right {P : Program} {tail : List (BitVec 8)}
    {addr : BitVec 64} {ws : List (BitVec 32)}
    (h : P.hasWords addr ws) :
    ({ P with code := P.code ++ tail }).hasWords addr ws := by
  obtain ⟨hbnd, hwords, hhf⟩ := h
  exact ⟨hbnd, fun i hi => readWordOff_append_right (hwords i hi), hhf⟩

private def witnessCodeBase : BitVec 64 := BitVec.ofNat 64 (16 * 4096)

private def witnessRdlAllocOff : Nat := 0
private def witnessRdlDeallocOff : Nat := 96
private def witnessRdlReallocOff : Nat := 128
private def witnessThunkAllocOff : Nat := 320
private def witnessThunkDeallocOff : Nat := 324
private def witnessThunkReallocOff : Nat := 328
private def witnessMemcpyOff : Nat := 352
private def witnessBlocksStartOff : Nat := 768

private def mallocngBlockRelOff : Nat → Nat
  | 0 => 0
  | i + 1 =>
    let prev := mallocngBlockRelOff i +
      (VerifiedLibraries.mallocngLib.blocks[i]?.map (·.code.length)).getD 0
    ((prev + 63) / 64) * 64

private def mallocngBlockOff (i : Nat) : Nat :=
  witnessBlocksStartOff + mallocngBlockRelOff i

private def witnessCodeEndOff : Nat :=
  mallocngBlockOff VerifiedLibraries.mallocngLib.blocks.length

private def witnessRdlAddrs : RustAllocAddrs where
  alloc   := witnessCodeBase + BitVec.ofNat 64 witnessRdlAllocOff
  dealloc := witnessCodeBase + BitVec.ofNat 64 witnessRdlDeallocOff
  realloc := witnessCodeBase + BitVec.ofNat 64 witnessRdlReallocOff

private def witnessThunkAddrs : RustAllocAddrs where
  alloc   := witnessCodeBase + BitVec.ofNat 64 witnessThunkAllocOff
  dealloc := witnessCodeBase + BitVec.ofNat 64 witnessThunkDeallocOff
  realloc := witnessCodeBase + BitVec.ofNat 64 witnessThunkReallocOff

private def witnessMemcpyAddr : BitVec 64 :=
  witnessCodeBase + BitVec.ofNat 64 witnessMemcpyOff

private def witnessMpl : Obj.MultiPlacement where
  base i := witnessCodeBase + BitVec.ofNat 64 (mallocngBlockOff i)
  ρ sym :=
    if sym == "__malloc_size_classes" then BitVec.ofNat 64 (24 * 4096)
    else if sym == "debruijn32.4681" then BitVec.ofNat 64 (25 * 4096)
    else if sym == "med_cnt_tab" then BitVec.ofNat 64 (26 * 4096)
    else if sym == "small_cnt_tab" then BitVec.ofNat 64 (27 * 4096)
    else if sym == "debruijn32.5048" then BitVec.ofNat 64 (28 * 4096)
    else if sym == "__malloc_context" then BitVec.ofNat 64 (29 * 4096)
    else if sym == "__libc" then BitVec.ofNat 64 (30 * 4096)
    else if sym == "__malloc_lock" then BitVec.ofNat 64 (31 * 4096)
    else if sym == "__malloc_replaced" then BitVec.ofNat 64 (32 * 4096)
    else if sym == "__aligned_alloc_replaced" then BitVec.ofNat 64 (33 * 4096)
    else BitVec.ofNat 64 (34 * 4096)

private theorem witnessMpl_placeable : VerifiedLibraries.mallocngLib.Placeable witnessMpl :=
  Obj.MultiPlacedLib.placeable_of_checkPlaceable (by decide +kernel)

private def rdlAllocRelocs : List Obj.RelocEntry :=
  [{ off := 24, kind := .jump26, sym := "malloc" },
   { off := 60, kind := .call26, sym := "posix_memalign" }]

private def rdlAllocWords : List (BitVec 32) :=
  [0xf100403f#32, 0xaa0003e2#32, 0x540000a8#32, 0xeb02003f#32, 0x54000068#32, 0xaa0203e0#32,
   0x17fff645#32, 0xd10083ff#32, 0xa9017bfd#32, 0x910043fd#32, 0xf100203f#32, 0x52800108#32,
   0x910023e0#32, 0x9a888021#32, 0xf90007ff#32, 0x97fffeec#32, 0xf94007e8#32, 0x7100001f#32,
   0x9a9f0100#32, 0xa9417bfd#32, 0x910083ff#32, 0xd65f03c0#32]

private def rdlDeallocRelocs : List Obj.RelocEntry :=
  [{ off := 0, kind := .jump26, sym := "free" }]

private def rdlDeallocWords : List (BitVec 32) :=
  [0x17fff552#32]

private def rdlReallocRelocs : List Obj.RelocEntry :=
  [{ off := 64, kind := .jump26, sym := "realloc" },
   { off := 96, kind := .call26, sym := "posix_memalign" },
   { off := 136, kind := .call26, sym := "memcpy" },
   { off := 144, kind := .call26, sym := "free" }]

private def rdlReallocWords : List (BitVec 32) :=
  [0xd10103ff#32, 0xa9017bfd#32, 0xa90257f6#32, 0xa9034ff4#32, 0x910043fd#32, 0xaa0303f3#32,
   0xaa0103f4#32, 0xf100405f#32, 0x54000128#32, 0xeb13005f#32, 0x540000e8#32, 0xaa1303e1#32,
   0xa9434ff4#32, 0xa94257f6#32, 0xa9417bfd#32, 0x910103ff#32, 0x17fffeea#32, 0xf100205f#32,
   0x52800108#32, 0xaa0003f6#32, 0x9a888041#32, 0x910023e0#32, 0xaa1303e2#32, 0xf90007ff#32,
   0x97fffecc#32, 0x2a0003e8#32, 0xaa1f03e0#32, 0x35000168#32, 0xf94007f5#32, 0xb4000135#32,
   0xeb14027f#32, 0xaa1503e0#32, 0xaa1603e1#32, 0x9a943262#32, 0x97fff44b#32, 0xaa1603e0#32,
   0x97fff52d#32, 0xaa1503e0#32, 0xa9434ff4#32, 0xa94257f6#32, 0xa9417bfd#32, 0x910103ff#32,
   0xd65f03c0#32]

private def padBytesTo (bs : List (BitVec 8)) (targetLen : Nat) : List (BitVec 8) :=
  bs ++ List.replicate (targetLen - bs.length) 0#8

private def patchThunkBytes (thunkAddr targetAddr : BitVec 64) : List (BitVec 8) :=
  (Obj.patchRelocs [{ off := 0, kind := .jump26, sym := "t" }] rdlDeallocWords thunkAddr
    (fun _ => targetAddr)).flatMap Program.wordToBytesLE

private def witnessShimResolve (sym : String) : BitVec 64 :=
  if sym == "memcpy" then witnessMemcpyAddr
  else VerifiedLibraries.mallocngLib.resolve witnessMpl sym

private def witnessShimCode : List (BitVec 8) :=
  padBytesTo
    ((Obj.patchRelocs rdlAllocRelocs rdlAllocWords witnessRdlAddrs.alloc
      witnessShimResolve).flatMap Program.wordToBytesLE) 96 ++
  padBytesTo
    ((Obj.patchRelocs rdlDeallocRelocs rdlDeallocWords witnessRdlAddrs.dealloc
      witnessShimResolve).flatMap Program.wordToBytesLE) 32 ++
  padBytesTo
    ((Obj.patchRelocs rdlReallocRelocs rdlReallocWords witnessRdlAddrs.realloc
      witnessShimResolve).flatMap Program.wordToBytesLE) 192 ++
  patchThunkBytes witnessThunkAddrs.alloc witnessRdlAddrs.alloc ++
  patchThunkBytes witnessThunkAddrs.dealloc witnessRdlAddrs.dealloc ++
  padBytesTo (patchThunkBytes witnessThunkAddrs.realloc witnessRdlAddrs.realloc) 24 ++
  padBytesTo (memcpySymWords.flatMap Program.wordToBytesLE) 416

private def witnessShimProg : Program where
  base := witnessCodeBase
  code := witnessShimCode
  symbols := []
  stubs := []
  externs := fun _ => none
  overrides := fun _ => none
  svc := Syscall.standard

private def witnessShimTree : WordTree :=
  word_tree_of% witnessShimProg

private def witnessShimWordCount : Nat := 192

private theorem witnessShimTree_eq : witnessShimProg.code = witnessShimTree.toBytes := by
  rfl_kernel

private theorem witnessShimTree_size :
    witnessShimTree.checkSize? = some witnessShimWordCount := by
  decide +kernel

private theorem witnessShimCode_length : witnessShimCode.length = witnessBlocksStartOff := by
  change witnessShimProg.code.length = witnessBlocksStartOff
  rw [witnessShimTree_eq]
  decide +kernel

private def witnessBlockChunk (i : Nat) : List (BitVec 8) :=
  padBytesTo
    ((VerifiedLibraries.mallocngLib.blocks[i]?.getD { code := [] }).patched
      (VerifiedLibraries.mallocngLib.blockPlacement witnessMpl i))
    (mallocngBlockRelOff (i + 1) - mallocngBlockRelOff i)

private def witnessBlocksCode : List (BitVec 8) :=
  (List.range VerifiedLibraries.mallocngLib.blocks.length).flatMap witnessBlockChunk

private def witnessProg : Program :=
  { witnessShimProg with code := witnessShimProg.code ++ witnessBlocksCode }

private theorem padBytesTo_length {bs : List (BitVec 8)} {targetLen : Nat}
    (hle : bs.length ≤ targetLen) :
    (padBytesTo bs targetLen).length = targetLen := by
  simp only [padBytesTo, List.length_append, List.length_replicate]
  omega

private theorem blockProgram_code_eq {i : Nat}
    (hi : i < VerifiedLibraries.mallocngLib.blocks.length) :
    (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code =
      VerifiedLibraries.mallocngLib.blocks[i].patched
        (VerifiedLibraries.mallocngLib.blockPlacement witnessMpl i) := by
  unfold Obj.MultiPlacedLib.blockProgram Obj.PlacedLib.program
  dsimp only
  rw [VerifiedLibraries.mallocngLib.blockLib_text hi]

private theorem blockProgram_code_length {i : Nat}
    (hi : i < VerifiedLibraries.mallocngLib.blocks.length) :
    (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code.length =
      VerifiedLibraries.mallocngLib.blocks[i].code.length := by
  rw [blockProgram_code_eq hi]
  exact Obj.CodeBlock.length_patched_of_aligned _
    (witnessMpl_placeable.blocks_ok i hi).len_aligned

private theorem mallocngBlockRelOff_succ_of_lt {i : Nat}
    (hi : i < VerifiedLibraries.mallocngLib.blocks.length) :
    mallocngBlockRelOff (i + 1) =
      ((mallocngBlockRelOff i + VerifiedLibraries.mallocngLib.blocks[i].code.length + 63) / 64) * 64 := by
  simp [mallocngBlockRelOff, List.getElem?_eq_getElem hi]

private theorem mallocngBlockRelOff_add_code_le_succ {i : Nat}
    (hi : i < VerifiedLibraries.mallocngLib.blocks.length) :
    mallocngBlockRelOff i + VerifiedLibraries.mallocngLib.blocks[i].code.length ≤
      mallocngBlockRelOff (i + 1) := by
  rw [mallocngBlockRelOff_succ_of_lt hi]
  omega

private theorem mallocngBlockRelOff_le_succ (i : Nat) :
    mallocngBlockRelOff i ≤ mallocngBlockRelOff (i + 1) := by
  simp only [mallocngBlockRelOff]
  omega

private theorem mallocngBlockRelOff_mono {i j : Nat} (hij : i ≤ j) :
    mallocngBlockRelOff i ≤ mallocngBlockRelOff j := by
  induction hij with
  | refl => exact Nat.le_refl _
  | @step m _ ih => exact Nat.le_trans ih (mallocngBlockRelOff_le_succ m)

private theorem witnessBlockChunk_eq {i : Nat}
    (hi : i < VerifiedLibraries.mallocngLib.blocks.length) :
    witnessBlockChunk i =
      padBytesTo (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code
        (mallocngBlockRelOff (i + 1) - mallocngBlockRelOff i) := by
  unfold witnessBlockChunk
  rw [List.getElem?_eq_getElem hi]
  dsimp only [Option.getD]
  rw [blockProgram_code_eq hi]

private theorem witnessBlockChunk_length {i : Nat}
    (hi : i < VerifiedLibraries.mallocngLib.blocks.length) :
    (witnessBlockChunk i).length = mallocngBlockRelOff (i + 1) - mallocngBlockRelOff i := by
  rw [witnessBlockChunk_eq hi]
  apply padBytesTo_length
  rw [blockProgram_code_length hi]
  have hle := mallocngBlockRelOff_add_code_le_succ hi
  omega

private theorem range_flatMap_witnessBlockChunk_length :
    ∀ n, n ≤ VerifiedLibraries.mallocngLib.blocks.length →
      ((List.range n).flatMap witnessBlockChunk).length = mallocngBlockRelOff n
  | 0, _ => rfl
  | n + 1, hn => by
    rw [List.range_succ, List.flatMap_append, List.length_append,
      range_flatMap_witnessBlockChunk_length n (Nat.le_of_succ_le hn)]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [witnessBlockChunk_length hn]
    have hle := mallocngBlockRelOff_le_succ n
    omega

private theorem witnessBlocksCode_length :
    witnessBlocksCode.length = mallocngBlockRelOff VerifiedLibraries.mallocngLib.blocks.length :=
  range_flatMap_witnessBlockChunk_length VerifiedLibraries.mallocngLib.blocks.length (Nat.le_refl _)

private theorem witnessProg_code_length : witnessProg.code.length = witnessCodeEndOff := by
  change (witnessShimCode ++ witnessBlocksCode).length =
    witnessBlocksStartOff + mallocngBlockRelOff VerifiedLibraries.mallocngLib.blocks.length
  rw [List.length_append, witnessShimCode_length, witnessBlocksCode_length]

private theorem witnessBlockChunk_getElem?_of_lt {i k : Nat}
    (hi : i < VerifiedLibraries.mallocngLib.blocks.length)
    (hk : k < (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code.length) :
    (witnessBlockChunk i)[k]? = (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code[k]? := by
  rw [witnessBlockChunk_eq hi]
  exact List.getElem?_append_left hk

private theorem range_flatMap_witnessBlockChunk_getElem? :
    ∀ n, n ≤ VerifiedLibraries.mallocngLib.blocks.length → ∀ {i k : Nat},
      i < n →
      k < (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code.length →
      ((List.range n).flatMap witnessBlockChunk)[mallocngBlockRelOff i + k]? =
        (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code[k]?
  | 0, _, _, _, hi_n, _ => False.elim (Nat.not_lt_zero _ hi_n)
  | n + 1, hn, i, k, hi_n, hk => by
    have hi : i < VerifiedLibraries.mallocngLib.blocks.length := Nat.lt_of_lt_of_le hi_n hn
    have hpre_len := range_flatMap_witnessBlockChunk_length n (Nat.le_of_succ_le hn)
    rw [List.range_succ, List.flatMap_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
    cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi_n) with
    | inl hi_lt =>
      have hk_raw : k < VerifiedLibraries.mallocngLib.blocks[i].code.length := by
        rwa [blockProgram_code_length hi] at hk
      have h1 := mallocngBlockRelOff_add_code_le_succ hi
      have h2 := mallocngBlockRelOff_mono (i := i + 1) (j := n) hi_lt
      rw [List.getElem?_append_left (by omega)]
      exact range_flatMap_witnessBlockChunk_getElem? n (Nat.le_of_succ_le hn) hi_lt hk
    | inr heq =>
      subst heq
      rw [List.getElem?_append_right (by omega), hpre_len, Nat.add_sub_cancel_left]
      exact witnessBlockChunk_getElem?_of_lt hi hk

private theorem witnessProg_codeLoaded_imp_mallocngLib {m : Memory}
    (hL : witnessProg.CodeLoaded m) :
    VerifiedLibraries.mallocngLib.CodeLoaded witnessMpl m := by
  intro i hi
  have hp := witnessMpl_placeable.blocks_ok i hi
  have hal : (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).base.toNat % 4 = 0 :=
    Nat.mod_eq_zero_of_dvd
      (Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hp.align_pos.2)
        (Nat.dvd_of_mod_eq_zero hp.base_aligned))
  have hnw : (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).base.toNat +
      (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code.length ≤ 2 ^ 64 := by
    rw [blockProgram_code_length hi]
    exact hp.no_wrap
  refine Program.CodeLoaded.intro hal hnw fun k hk => ?_
  have hk_raw : k < VerifiedLibraries.mallocngLib.blocks[i].code.length := by
    rwa [blockProgram_code_length hi] at hk
  have h1 := mallocngBlockRelOff_add_code_le_succ hi
  have h2 : mallocngBlockRelOff (i + 1) ≤
      mallocngBlockRelOff VerifiedLibraries.mallocngLib.blocks.length :=
    mallocngBlockRelOff_mono (Nat.succ_le_of_lt hi)
  have hcl_eq : witnessProg.code.length = witnessCodeEndOff := witnessProg_code_length
  have hstart : witnessBlocksStartOff = 768 := rfl
  have hend_eq : witnessCodeEndOff =
      witnessBlocksStartOff + mallocngBlockRelOff VerifiedLibraries.mallocngLib.blocks.length := rfl
  have hkW : mallocngBlockOff i + k < witnessProg.code.length := by
    unfold mallocngBlockOff; omega
  have hcl_lt : witnessCodeEndOff < 2 ^ 32 := by decide +kernel
  have haddr : (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).base + BitVec.ofNat 64 k =
      witnessProg.base + BitVec.ofNat 64 (mallocngBlockOff i + k) := by
    change witnessCodeBase + BitVec.ofNat 64 (mallocngBlockOff i) + BitVec.ofNat 64 k =
      witnessCodeBase + BitVec.ofNat 64 (mallocngBlockOff i + k)
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    have hcb : witnessCodeBase.toNat = 16 * 4096 := by decide +kernel
    omega
  have hshim_len : witnessShimCode.length = witnessBlocksStartOff := witnessShimCode_length
  have hall : witnessProg.code[mallocngBlockOff i + k]? =
      (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code[k]? := by
    change (witnessShimCode ++ witnessBlocksCode)[witnessBlocksStartOff + mallocngBlockRelOff i + k]? =
      (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code[k]?
    rw [Nat.add_assoc, List.getElem?_append_right (by omega), hshim_len, Nat.add_sub_cancel_left]
    exact range_flatMap_witnessBlockChunk_getElem?
      VerifiedLibraries.mallocngLib.blocks.length (Nat.le_refl _) hi hk
  rw [List.getElem?_eq_getElem hkW, List.getElem?_eq_getElem hk] at hall
  have hc_eq : witnessProg.code[mallocngBlockOff i + k] =
      (VerifiedLibraries.mallocngLib.blockProgram witnessMpl i).code[k] :=
    Option.some.inj hall
  rw [haddr, ← hc_eq]
  exact ⟨hL.byte_eq _ hkW, hL.perm_eq _ hkW, hL.isLazyFree_eq _ hkW⟩

private theorem witnessProg_externAt_none (pc : BitVec 64) :
    witnessProg.externAt? pc = none := rfl

private theorem witnessProg_contains_mallocng :
    VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng witnessProg witnessMpl :=
  VerifiedLibraries.Mallocng.Proofs.ProgContainsMultiLib.of_noExterns
    witnessMpl_placeable
    rfl
    (fun _ hL => witnessProg_codeLoaded_imp_mallocngLib hL)
    witnessProg_externAt_none

private theorem witnessShims_shimProg_ok :
    VerifiedLibraries.RustStd.RustStdRdlShimCode witnessShimProg witnessRdlAddrs.toRustStd
      (VerifiedLibraries.RustStd.mallocngPlacedCAddrs witnessMpl) witnessMemcpyAddr :=
  VerifiedLibraries.RustStd.rustStdRdlShimCode_of_wordTree
    witnessShimWordCount witnessShimTree_eq witnessShimTree_size
    (hok := by decide +kernel)

private theorem witnessShims_ok :
    VerifiedLibraries.RustStd.RustStdRdlShimCode witnessProg witnessRdlAddrs.toRustStd
      (VerifiedLibraries.RustStd.mallocngPlacedCAddrs witnessMpl) witnessMemcpyAddr where
  alloc_instrs := hasInstrs_append_right witnessShims_shimProg_ok.alloc_instrs
  dealloc_instrs := hasInstrs_append_right witnessShims_shimProg_ok.dealloc_instrs
  realloc_instrs := hasInstrs_append_right witnessShims_shimProg_ok.realloc_instrs

private theorem witnessThunks_shimProg_ok :
    VerifiedLibraries.RustStd.RustStdThunkCode witnessShimProg
      witnessThunkAddrs.toRustStd witnessRdlAddrs.toRustStd :=
  VerifiedLibraries.RustStd.rustStdThunkCode_of_wordTree
    witnessShimWordCount witnessShimTree_eq witnessShimTree_size
    (hok := by decide +kernel)

private theorem witnessThunks_ok :
    VerifiedLibraries.RustStd.RustStdThunkCode witnessProg
      witnessThunkAddrs.toRustStd witnessRdlAddrs.toRustStd where
  alloc_thunk := hasInstrs_append_right witnessThunks_shimProg_ok.alloc_thunk
  dealloc_thunk := hasInstrs_append_right witnessThunks_shimProg_ok.dealloc_thunk
  realloc_thunk := hasInstrs_append_right witnessThunks_shimProg_ok.realloc_thunk

private theorem witnessMemcpy_words_shimProg :
    witnessShimProg.hasWords witnessMemcpyAddr memcpySymWords :=
  hasWords_of_wordTree
    witnessShimWordCount witnessShimTree_eq witnessShimTree_size
    (baseOff := witnessMemcpyOff)
    (by decide +kernel) (by decide +kernel) rfl rfl (by decide +kernel)

private theorem witnessMemcpyVm_ok :
    subroutine_ok witnessProg witnessMemcpyAddr allocMemcpyVmSpec :=
  allocMemcpyVm_ok_of_hasWords
    witnessProg witnessMemcpyAddr witnessProg_externAt_none
    (hasWords_append_right witnessMemcpy_words_shimProg)

/-! ## Initial Startup Memory and `512 MiB` Budget State -/

private abbrev witnessAuxvPtr  : BitVec 64 := BitVec.ofNat 64 (35 * 4096)
private abbrev witnessRandPtr  : BitVec 64 := BitVec.ofNat 64 (36 * 4096)
private abbrev witnessTp       : BitVec 64 := BitVec.ofNat 64 (40 * 4096)
private abbrev witnessBrkStart : BitVec 64 := BitVec.ofNat 64 (64 * 4096)
private abbrev witnessSp0      : BitVec 64 := BitVec.ofNat 64 (128 * 4096)
private abbrev witnessLr       : BitVec 64 := BitVec.ofNat 64 (200 * 4096 + 1)

private def witnessRegions : List ProofLib.Disproof.DisproofRegion :=
  let A := mallocngAddrsOfPlacement witnessMpl
  [ .roBytes A.sizeClasses mallocngSizeClassBytes,
    .roBytes A.debruijnFree mallocngDebruijn32Table,
    .roBytes A.medCntTab mallocngMedCntTabBytes,
    .roBytes A.smallCntTab mallocngSmallCntTabBytes,
    .roBytes A.debruijnAlloc mallocngDebruijn32Table,
    .rwBytes A.ctx (List.replicate 928 0#8),
    .rw32 A.lock 0#32,
    .rw32 A.replaced 0#32,
    .rw32 A.aaReplaced 0#32,
    .rw32 (witnessTp - 0xa4#64) 0#32,
    .rw8 (A.libc + 3#64) 0#8,
    .rw64 (A.libc + 48#64) 4096#64,
    .rw64 (A.libc + 8#64) witnessAuxvPtr,
    .rw64 witnessAuxvPtr 25#64,
    .rw64 (witnessAuxvPtr + 8#64) witnessRandPtr,
    .rw64 ((witnessAuxvPtr + 8#64) + 8#64) 0#64,
    .rw64 (((witnessAuxvPtr + 8#64) + 8#64) + 8#64) 0#64,
    .rwBytes (witnessRandPtr + 8#64) (List.replicate 8 0#8),
    .rwRegion (witnessSp0 - BitVec.ofNat 64 allocHookStack) allocHookStack ]

private def witnessStaticIvs : List (BitVec 64 × Nat) :=
  (witnessCodeBase, witnessCodeEndOff) ::
    (witnessRegions.map fun r => (r.toSpec.base, r.toSpec.len))

/-- Sub-`1 GiB` (`512 MiB < 2 ^ 30`) physical-memory budget limits for `fineCostModel` smoke and
    scaling witnesses. -/
def fineWitnessBudgetLimits : BudgetLimits :=
  { staticCount := 32
    staticBytes := 256 * 1024
    physCap     := 512 * 1024 * 1024
    enforced    := true }

private def witnessState : State :=
  { (ProofLib.Disproof.mkDisproofState witnessProg witnessRdlAddrs.alloc witnessSp0 witnessLr
      [(.x0, 72#64), (.x1, 8#64)] witnessRegions) with
    tpidrEl0     := witnessTp
    brkStart     := witnessBrkStart
    brk          := witnessBrkStart
    physMemAvail := 512 * 1024 * 1024 }

private theorem witnessRegions_valid :
    ProofLib.Disproof.DisproofRegionsValidB witnessCodeBase witnessCodeEndOff witnessRegions =
      true := by
  decide +kernel

private theorem witnessState_codeLoaded : witnessProg.CodeLoaded witnessState.mem :=
  ProofLib.Disproof.buildDisproofMem_codeLoaded_of_valid
    witnessProg witnessRegions rfl witnessProg_code_length witnessRegions_valid

private theorem witnessState_x0 : witnessState.readReg64 .x0 = 72#64 := rfl

private theorem witnessState_x1 : witnessState.readReg64 .x1 = 8#64 := rfl

private theorem witnessState_spAligned : witnessState.spAligned = true := by
  have hsp : witnessState.sp = witnessSp0 := rfl
  unfold State.spAligned
  rw [hsp]
  decide

private theorem witnessBrkStart_wf : MallocngBrkStartWf witnessBrkStart := by
  unfold MallocngBrkStartWf
  exact ⟨by decide, by decide, by decide⟩

private theorem mapped_false_of_perm_none {m : Memory} {a : BitVec 64}
    (hnone : m.perm a = none) (hmap : (m.perm a).mapped = true) : False := by
  rw [hnone] at hmap
  cases hmap

private theorem le_physPlusRw_of_le_avail {cap : Nat} {s : State}
    (h : cap ≤ s.physMemAvail) : cap ≤ physPlusRw s :=
  Nat.le_trans h (Nat.le_add_right s.physMemAvail (rwBytes s.mem))

private theorem witnessState_poolInv :
    mallocngBudgetPoolInv fineWitnessBudgetLimits witnessStaticIvs [] witnessState := by
  intro _
  refine ⟨⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩, ?_⟩
  · intro a hmap
    refine Or.inl (Classical.byContradiction fun hnot => ?_)
    have hNotCode : ¬ InRegion witnessCodeBase witnessCodeEndOff a := fun hc =>
      hnot ⟨(witnessCodeBase, witnessCodeEndOff), List.Mem.head _, hc⟩
    have hNotRs : ∀ r ∈ witnessRegions.map ProofLib.Disproof.DisproofRegion.toSpec,
        ¬ InRegion r.base r.len a := by
      intro r hr hin
      rcases List.mem_map.mp hr with ⟨dr, hdr, rfl⟩
      exact hnot ⟨(dr.toSpec.base, dr.toSpec.len),
        List.Mem.tail _ (List.mem_map.mpr ⟨dr, hdr, rfl⟩), hin⟩
    exact mapped_false_of_perm_none
      (ProofLib.Disproof.buildDisproofMem_perm_none
        witnessProg (witnessRegions.map ProofLib.Disproof.DisproofRegion.toSpec) a
        rfl witnessProg_code_length hNotCode hNotRs)
      hmap
  · exact le_physPlusRw_of_le_avail (by decide)

private theorem witnessState_satisfies_init :
    witnessState.mem ⊨
      VerifiedLibraries.mallocngLib.dataInit witnessMpl ∗
        MallocngRuntime (mallocngAddrsOfPlacement witnessMpl) witnessTp ∗
        (((mallocngAddrsOfPlacement witnessMpl).libc + 8#64) ↦₆₄ witnessAuxvPtr) ∗
        MallocngAuxvAt witnessAuxvPtr ∗
        stackAt witnessSp0 allocHookStack := by
  have hRaw : witnessState.mem ⊨ ProofLib.Disproof.DisproofRegion.listToSepProp witnessRegions :=
    ProofLib.Disproof.buildDisproofMem_satisfies
      witnessProg witnessRegions rfl witnessProg_code_length witnessRegions_valid
  let A := mallocngAddrsOfPlacement witnessMpl
  have hAuxvPure :
      (∀ e ∈ ([] : List (BitVec 64 × BitVec 64)), e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
      (∀ e ∈ ([] : List (BitVec 64 × BitVec 64)), e.1 ≠ 0#64 ∧ e.1 ≠ 25#64) ∧
      ([] : List (BitVec 64 × BitVec 64)).length + ([] : List (BitVec 64 × BitVec 64)).length ≤ 64 ∧
      witnessAuxvPtr.toNat + 16 *
        (([] : List (BitVec 64 × BitVec 64)).length +
          ([] : List (BitVec 64 × BitVec 64)).length + 2) ≤ 2 ^ 48 ∧
      witnessRandPtr.toNat + 16 ≤ 2 ^ 48 ∧
      (List.replicate 8 0#8).length = 8 :=
    ⟨(fun _ h => nomatch h), (fun _ h => nomatch h), by decide, by decide, by decide, rfl⟩
  have hAuxvEnt :
      (witnessAuxvPtr ↦₆₄ 25#64) ∗
      ((witnessAuxvPtr + 8#64) ↦₆₄ witnessRandPtr) ∗
      (((witnessAuxvPtr + 8#64) + 8#64) ↦₆₄ 0#64) ∗
      ((((witnessAuxvPtr + 8#64) + 8#64) + 8#64) ↦₆₄ 0#64) ∗
      ((witnessRandPtr + 8#64) ↦ₛ List.replicate 8 0#8) ⊢
      MallocngAuxvAt witnessAuxvPtr := by
    unfold MallocngAuxvAt
    refine Entails.trans ?_ (Entails.sepExists_intro ([] : List (BitVec 64 × BitVec 64)))
    refine Entails.trans ?_ (Entails.sepExists_intro ([] : List (BitVec 64 × BitVec 64)))
    refine Entails.trans ?_ (Entails.sepExists_intro witnessRandPtr)
    refine Entails.trans ?_ (Entails.sepExists_intro 0#64)
    refine Entails.trans ?_ (Entails.sepExists_intro (List.replicate 8 0#8))
    refine Entails.pure_right hAuxvPure ?_
    show _ ⊢ (pointsToWords64 witnessAuxvPtr [25#64, witnessRandPtr, 0#64, 0#64]) ∗
      ((witnessRandPtr + 8#64) ↦ₛ List.replicate 8 0#8)
    simp only [pointsToWords64_cons, pointsToWords64_nil, sepConj_emp, sepConj_assoc]
    exact Entails.refl _
  refine Satisfies.mono ?_ hRaw
  dsimp only [witnessRegions, ProofLib.Disproof.DisproofRegion.listToSepProp,
    ProofLib.Disproof.DisproofRegion.toSepProp, stackAt]
  rw [mallocngLib_dataInit_eq witnessMpl]
  have hReassoc :
      ((A.sizeClasses ↦ᵣ mallocngSizeClassBytes) ∗
       (A.debruijnFree ↦ᵣ mallocngDebruijn32Table) ∗
       (A.medCntTab ↦ᵣ mallocngMedCntTabBytes) ∗
       (A.smallCntTab ↦ᵣ mallocngSmallCntTabBytes) ∗
       (A.debruijnAlloc ↦ᵣ mallocngDebruijn32Table) ∗
       (A.ctx ↦ₛ List.replicate 928 0#8) ∗
       (A.lock ↦₃₂ 0#32) ∗
       (A.replaced ↦₃₂ 0#32) ∗
       (A.aaReplaced ↦₃₂ 0#32) ∗
       ((witnessTp - 0xa4#64) ↦₃₂ 0#32) ∗
       ((A.libc + 3#64) ↦₈ 0#8) ∗
       ((A.libc + 48#64) ↦₆₄ 4096#64) ∗
       ((A.libc + 8#64) ↦₆₄ witnessAuxvPtr) ∗
       (witnessAuxvPtr ↦₆₄ 25#64) ∗
       ((witnessAuxvPtr + 8#64) ↦₆₄ witnessRandPtr) ∗
       (((witnessAuxvPtr + 8#64) + 8#64) ↦₆₄ 0#64) ∗
       ((((witnessAuxvPtr + 8#64) + 8#64) + 8#64) ↦₆₄ 0#64) ∗
       ((witnessRandPtr + 8#64) ↦ₛ List.replicate 8 0#8) ∗
       memRegion (witnessSp0 - BitVec.ofNat 64 allocHookStack) allocHookStack) =
      ((MallocngRoTablesAt A ∗
         (A.ctx ↦ₛ List.replicate 928 0#8) ∗
         (A.lock ↦₃₂ 0#32) ∗
         (A.replaced ↦₃₂ 0#32) ∗
         (A.aaReplaced ↦₃₂ 0#32)) ∗
        (((witnessTp - 0xa4#64) ↦₃₂ 0#32) ∗
         ((A.libc + 3#64) ↦₈ 0#8) ∗
         ((A.libc + 48#64) ↦₆₄ 4096#64)) ∗
        ((A.libc + 8#64) ↦₆₄ witnessAuxvPtr) ∗
        ((witnessAuxvPtr ↦₆₄ 25#64) ∗
         ((witnessAuxvPtr + 8#64) ↦₆₄ witnessRandPtr) ∗
         (((witnessAuxvPtr + 8#64) + 8#64) ↦₆₄ 0#64) ∗
         ((((witnessAuxvPtr + 8#64) + 8#64) + 8#64) ↦₆₄ 0#64) ∗
         ((witnessRandPtr + 8#64) ↦ₛ List.replicate 8 0#8)) ∗
        memRegion (witnessSp0 - BitVec.ofNat 64 allocHookStack) allocHookStack) := by
    unfold MallocngRoTablesAt
    simp only [sepConj_assoc]
  rw [hReassoc]
  refine sepConj_mono_right (sepConj_mono ?_ (sepConj_mono_right (sepConj_mono_left hAuxvEnt)))
  unfold MallocngRuntime
  exact sepConj_mono_left (Entails.sepExists_intro 0#32)

/-! ## `FitsTraceOf` Witnesses and Separation from `coarseCostModel` -/

theorem fineWitnessFits_alloc72 :
    FitsTraceOf fineCostModel fineWitnessBudgetLimits [.alloc 72] := by
  unfold FitsTraceOf FitsTrace FitsStep AllocEvent.withinMaxAlloc
  refine ⟨fun ev hev => ?_, by decide, by decide, by decide⟩
  simp only [List.mem_singleton] at hev
  subst hev
  exact ⟨by decide, by decide⟩

theorem fineWitnessFits_workedCallerTrace :
    FitsTraceOf fineCostModel fineWitnessBudgetLimits workedCallerTrace := by
  have hEq : workedCallerTrace = [.alloc 32, .realloc 8 32 64, .free 8 64] := by decide
  rw [hEq]
  unfold FitsTraceOf FitsTrace FitsStep
  refine ⟨fun ev hev => ?_, by decide, by decide, by decide⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
  rcases hev with rfl | rfl | rfl
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

/-- Under `coarseCostModel`, `workedCallerTrace` fails `FitsTraceOf` whenever `lim.physCap < 2 ^ 32`
    (`4 GiB`) because `coarseStepReserve (.realloc ...)` charges `MaxAlignedAllocAlign = 2 GiB`,
    whereas `fineCostModel` admits the trace within `512 MiB`. -/
theorem coarseCostModel_not_fits_workedCallerTrace_under_4GiB {lim : BudgetLimits}
    (hCap : lim.physCap < 2 ^ 32) :
    ¬ FitsTraceOf coarseCostModel lim workedCallerTrace := by
  intro ⟨_, _, hRam, _⟩
  have hMem : AllocEvent.realloc 8 32 64 ∈ workedCallerTrace := by decide
  have hStepLe := stepReserve_le_maxStepOf (M := coarseCostModel)
    (st := coarseCostModel.evalLog workedCallerTrace) hMem
  have hStepGe : 2 ^ 31 ≤
      coarseCostModel.stepReserve (.realloc 8 32 64)
        (coarseCostModel.evalLog workedCallerTrace) := by
    dsimp only [coarseCostModel, coarseStepReserve]
    unfold MallocngStepBound MaxAlignedAllocAlign pageAlignUp PAGE_SIZE
    omega
  omega

private def small8State (n : Nat) : fineCostModel.σ :=
  ({ cumSmallBytes   := 179 * n
     cumSmallGroupsS := 4737 * n
     live63Bytes     := 0
     peak63Bytes     := 0
     live63Count     := 0
     peak63Count     := 0
     liveUserBytes   := 8 * n } : FineBudget)

private theorem replicate_append_singleton {α : Type} (x : α) :
    ∀ n : Nat, List.replicate (n + 1) x = List.replicate n x ++ [x]
  | 0 => rfl
  | n + 1 => by
    simp only [List.replicate_succ, List.cons_append]
    exact congrArg (x :: ·) (replicate_append_singleton x n)

private theorem small8State_step (n : Nat) :
    fineCostModel.step (.alloc 8) (small8State n) = small8State (n + 1) := by
  have hNot63 : ¬ (Guaranteed63Threshold ≤ 8) := by decide
  have hSm : 8 ≤ MmapThresholdReq := by decide
  have hDiv : (8 + 3) / 16 = 0 := by decide
  have hSlot : coarseSlotWt (sizeToClassUnits 0) = 179 := by decide
  have hGrp : coarseGrpWtS (sizeToClassUnits 0) = 4737 := by decide
  change FineBudget.stepAligned 16 8 _ = _
  dsimp only [FineBudget.stepAligned, small8State, finePeak63Bytes, finePeak63Count]
  simp only [Nat.max_self, Nat.sub_self, Nat.add_zero, hNot63, hSm, ↓reduceIte]
  rw [hDiv, hSlot, hGrp]
  simp only [Nat.mul_succ]

private theorem small8State_evalLog :
    ∀ n : Nat, fineCostModel.evalLog (List.replicate n (.alloc 8)) = small8State n
  | 0 => rfl
  | n + 1 =>
    (congrArg fineCostModel.evalLog (replicate_append_singleton (AllocEvent.alloc 8) n)).trans
      ((fineCostModel.evalLog_append (List.replicate n (.alloc 8)) [.alloc 8]).trans
        ((congrArg (fineCostModel.step (.alloc 8)) (small8State_evalLog n)).trans
          (small8State_step n)))

private theorem maxStepOf_replicate_le (M : AllocCostModel) (st : M.σ) (ev : AllocEvent) :
    ∀ n : Nat, maxStepOf M st (List.replicate n ev) ≤ M.stepReserve ev st
  | 0 => Nat.zero_le _
  | n + 1 => by
    unfold maxStepOf
    simp only [List.replicate_succ, List.map_cons, List.foldr_cons]
    exact Nat.max_le.mpr ⟨Nat.le_refl _, maxStepOf_replicate_le M st ev n⟩

/-- `2 ^ 20` small 8-byte allocations (`List.replicate (2 ^ 20) (.alloc 8)`) fit within `512 MiB`
    under `fineCostModel`. -/
theorem fineWitnessFits_million_alloc8 :
    FitsTraceOf fineCostModel fineWitnessBudgetLimits
      (List.replicate (2 ^ 20) (.alloc 8)) := by
  unfold FitsTraceOf FitsTrace
  refine ⟨fun ev hev => ?_, ?_⟩
  · have hEq : ev = .alloc 8 := List.eq_of_mem_replicate hev
    subst hEq
    exact ⟨by decide, stepReserve_le_maxStepOf hev⟩
  · have hEval := small8State_evalLog (2 ^ 20)
    have hMaxLe :
        maxStepOf fineCostModel (fineCostModel.evalLog (List.replicate (2 ^ 20) (.alloc 8)))
          (List.replicate (2 ^ 20) (.alloc 8)) ≤
        fineCostModel.stepReserve (.alloc 8) (small8State (2 ^ 20)) := by
      rw [hEval]
      exact maxStepOf_replicate_le fineCostModel (small8State (2 ^ 20)) (.alloc 8) (2 ^ 20)
    rw [hEval] at hMaxLe ⊢
    have hStep : FitsStep fineWitnessBudgetLimits
        (fineCostModel.stepReserve (.alloc 8) (small8State (2 ^ 20)))
        (fineCostModel.maxDynIvs (small8State (2 ^ 20)))
        (fineCostModel.footprint (small8State (2 ^ 20))) :=
      ⟨by decide, by decide, by decide⟩
    exact FitsStep.mono hStep hMaxLe (Nat.le_refl _) (Nat.le_refl _)

/-! ## Closed Non-Vacuity and Total-Correctness Witnesses -/

/-- Joint satisfiability of `Placeable`, `ProgContainsMallocng`, `CodeLoaded`, enforced `512 MiB`
    budget limits, `FitsTraceOf fineCostModel`, initial `A.pool` satisfaction,
    `RustCliAllocBudgetEntries`, and `RustCliAllocNoOomEntries`. -/
theorem fineRustCliAllocBudgetEntries_nonVacuous :
    ∃ (mpl : Obj.MultiPlacement) (P : Program) (addrs thunkAddrs : RustAllocAddrs)
      (γ : GhostName) (lim : BudgetLimits) (sInit : State),
      let A := fineRustCliAllocBudget γ mpl sInit.tpidrEl0 sInit.brkStart
      lim.enforced = true ∧
      lim.physCap < 2 ^ 30 ∧
      VerifiedLibraries.mallocngLib.Placeable mpl ∧
      VerifiedLibraries.Mallocng.Proofs.ProgContainsMallocng P mpl ∧
      P.svc = Syscall.standard ∧
      P.CodeLoaded sInit.mem ∧
      sInit.pc = addrs.alloc ∧
      sInit.readReg64 .x0 = 72#64 ∧
      sInit.readReg64 .x1 = 8#64 ∧
      sInit.status = .Running ∧
      sInit.spAligned = true ∧
      FitsTraceOf fineCostModel lim [.alloc 72] ∧
      FitsTraceOf fineCostModel lim workedCallerTrace ∧
      FitsTraceOf fineCostModel lim (List.replicate (2 ^ 20) (.alloc 8)) ∧
      (sInit.mem ⊨ A.pool lim fineCostModel.init sInit ∗ stackAt sInit.sp allocHookStack) ∧
      RustCliAllocBudgetEntriesBase fineCostModel A P addrs ∧
      RustCliAllocBudgetEntriesBase fineCostModel A P thunkAddrs ∧
      RustCliAllocNoOomEntriesBase fineCostModel A lim P addrs ∧
      RustCliAllocNoOomEntriesBase fineCostModel A lim P thunkAddrs := by
  obtain ⟨γ, hPoolInit, hEntriesRdl⟩ :=
    fineRustCliAllocBudgetEntries_of_placed_init
      witnessTp witnessBrkStart witnessAuxvPtr fineWitnessBudgetLimits witnessStaticIvs
      (stackAt witnessSp0 allocHookStack) witnessState
      witnessProg_contains_mallocng witnessShims_ok witnessMemcpyVm_ok
      (by decide) (by decide) witnessBrkStart_wf rfl rfl rfl
      witnessState_poolInv witnessState_satisfies_init
  have hEntriesThunks := RustCliAllocBudgetEntriesBase.of_thunks witnessThunks_ok hEntriesRdl
  exact ⟨witnessMpl, witnessProg, witnessRdlAddrs, witnessThunkAddrs, γ,
    fineWitnessBudgetLimits, witnessState,
    rfl, by decide, witnessMpl_placeable, witnessProg_contains_mallocng,
    rfl, witnessState_codeLoaded, rfl, witnessState_x0, witnessState_x1,
    rfl, witnessState_spAligned,
    fineWitnessFits_alloc72, fineWitnessFits_workedCallerTrace, fineWitnessFits_million_alloc8,
    hPoolInit, hEntriesRdl, hEntriesThunks,
    hEntriesRdl.toNoOom fineWitnessBudgetLimits,
    hEntriesThunks.toNoOom fineWitnessBudgetLimits⟩

/-- Total-correctness execution witness: under `lim.physCap < 2 ^ 30`, `__rust_alloc(72, 8)` returns
    normally (`Returned s0 sf`, with no `.OutOfMemory` branch) with a non-null, 8-byte-aligned
    72-byte live block and updated `A.pool`. -/
theorem fineRustCliAllocBudget_smoke_alloc72_nonVacuous :
    ∃ (mpl : Obj.MultiPlacement) (P : Program) (γ : GhostName)
      (lim : BudgetLimits) (s0 sf : State),
      let A := fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart
      lim.enforced = true ∧
      lim.physCap < 2 ^ 30 ∧
      Steps P s0 sf ∧
      Returned s0 sf ∧
      CallingConventionPreserved s0 sf ∧
      AllocCallPreserved s0 sf ∧
      sf.readReg64 .x0 ≠ 0#64 ∧
      (sf.readReg64 .x0).toNat % 8 = 0 ∧
      (sf.readReg64 .x0).toNat + 72 < 2 ^ 64 ∧
      (sf.mem ⊨ A.pool lim (fineCostModel.step (.alloc 72) fineCostModel.init) sf ∗
        stackAt s0.sp allocHookStack ∗
        A.live (sf.readReg64 .x0) 72 8 ∗
        memRegion (sf.readReg64 .x0) 72) := by
  obtain ⟨mpl, P, addrs, _, γ, lim, s0, henf, hcap, _, _, _, hCode, hpc, hx0, hx1, hrun, hsp,
    hFit, _, _, hPool, hEntries, _, _, _⟩ := fineRustCliAllocBudgetEntries_nonVacuous
  let A := fineRustCliAllocBudget γ mpl s0.tpidrEl0 s0.brkStart
  have hmemEmp : s0.mem ⊨ A.pool lim fineCostModel.init s0 ∗ stackAt s0.sp allocHookStack ∗ emp := by
    rwa [sepConj_emp]
  have hReach :=
    rustCliAllocBudget_smoke_alloc72 hEntries hFit emp s0 hpc hrun hsp hx0 hx1 hmemEmp
  have hReachPc : reaches_pc P (s0.readReg64 Reg.lr) s0
      (SubroutinePost (smokeAlloc72NoOomSpec fineCostModel A lim) fineCostModel.init emp s0)
      (fun _ => False) :=
    reaches_pc_of_reaches_outcome hReach
  obtain ⟨sf, hsteps, ⟨hpc_ret, hrun_ret, hpost, hcc⟩ | ⟨_, hfalse⟩⟩ := hReachPc hCode
  · have hret : Returned s0 sf := ⟨hpc_ret, hcc.1, hrun_ret⟩
    rw [sepConj_emp] at hpost
    dsimp only [smokeAlloc72NoOomSpec] at hpost
    obtain ⟨⟨hacp, hne0, hal8, hfit64⟩, hmemf⟩ := (satisfies_pure_sepConj _ _ _).1 hpost
    exact ⟨mpl, P, γ, lim, s0, sf,
      henf, hcap, hsteps, hret, hcc, hacp, hne0, hal8, hfit64, hmemf⟩
  · exact False.elim hfalse

end LibsignalBinary.Heap.Fine
