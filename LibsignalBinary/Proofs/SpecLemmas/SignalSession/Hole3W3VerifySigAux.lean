/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.Spec.Hoare
public import LibsignalBinary.Heap.IfaceBudgetLemmas
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
public import LibsignalBinary.Proofs.E2E.Pqxdh.Shared.VerifySignaturePlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import ProofLib.SepLogic.Fresh
import ProofLib.SepLogic.HeapIntro

/-!
# Block-203 `<PublicKey>::verify_signature` `VmPreserved` Contract

**Checked by Lean.**

Proves `w3m_verifySignature_vm_ok`, establishing `subroutine_ok` for block 203
(`<PublicKey>::verify_signature`) on `initProgPlaced mmpl ghFixed W` under
`withLsCodeRoLoaded`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3VerifySigAux

open Arm64 ProofLib SepProp
open Arm64.Obj (MultiPlacement)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalFullPlacement LibsignalHooks LibsignalPlacement
   LibsignalRoLoaded blkPC_203 blkPl_203 libsignalMutatedBlocks libsignalSessionLib
   libsignalSessionLib_blocks_length lsBlackBoxU8Sym lsMemcpySym lsmpl)
open CryptoVerification.E2E
  (UnreachedPqxdhPrimitives compress512Hook compressHook dsmbHook edNegHook modelPrims
   readSha512State readVecN scalarModHook scalarWideHook toEdwardsHook)
open CryptoVerification.E2E.Pqxdh.Initiator (structuralPrims_initiatorModelPrims)
open CryptoVerification.E2E.Pqxdh.Shared
  (VerifySignaturePlacedGhost VerifySignaturePlacedHooks VerifySignaturePrims
   lsDalekCompressSym lsDalekDoubleMulSym lsDalekEdNegSym lsDalekScalarModSym
   lsDalekScalarWideSym lsSha512CompressSym lsVerifyMemsetSym lsVerifyMontToEdSym
   pqxdhHookStack verifySignatureCallSpec verifySignature_placed_ok)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalPublicApi.StoreKit (extract_withLsCodeRoLoaded withLsCodeRoLoaded)
open CryptoVerification.LibsignalSession (blackBoxHook)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliHookTablePlaced lsReadFileSym lsReadStdinSym
   lsRustAllocSymCli lsRustAllocZeroedSymCli lsRustDeallocSymCli lsRustNoAllocShimSymCli
   lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_memcpy_some
   cliGhostExterns_memset_some cliGhostExterns_other)
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate
  (initProgPlaced transfer_withLsCodeRoLoaded)
open CryptoVerification.SignalSession.Cli.Slots
  (blackBox_row_placed cliExternsPlaced_compress512_sat cliExternsPlaced_compress_sat
   cliExternsPlaced_dsmb_sat cliExternsPlaced_edNeg_sat cliExternsPlaced_scalarMod_sat
   cliExternsPlaced_scalarWide_sat cliExternsPlaced_toEdwards_sat
   cliGhostExterns_sat_of_cliExternsPlaced compress512_row_placed compress_row_placed
   dsmb_row_placed edNeg_row_placed scalarMod_row_placed scalarWide_row_placed
   toEdwards_row_placed)
open CryptoVerification.LibsignalTripleRatchet
  (RW hookMemset_region_trace_ok sessionMemcpyRegionSpec sessionMemsetRegionSpec
   sessionMemsetSpec truncate8_truncate32)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (S2Frame disjoint_fullComplementHeap fullComplementHeap matches_fullComplementHeap)
open LibsignalBinary.Heap (AllocCostModel BudgetLimits RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookExactMemcpy hookMemcpy_exact)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCalleesPlacedBudget
  (verifySignatureInnerSpec)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (calleeSavedPreserved_of_stripS_right checkBlockSafeVm checkBytesSafeVm
   isTotalTrapHooks_vmTrapHooks placedLib_rebase_allInstrs_safeVm stripS_pc stripS_readReg64
   stripS_sp stripS_status vmTrapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (hookExactMemcpy_sessionMemcpyRegionBudget_ok hookExactMemcpy_vmPreserved
   hookOk_sessionMemsetRegion_elim)

private theorem cliGhost_row (mmpl : MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ lsReadFileSym := by decide) (h8 : sym ≠ lsReadStdinSym := by decide)
    (h9 : sym ≠ "memset" := by decide) (h10 : sym ≠ "memcpy" := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans (cliExternsPlaced_row mmpl W hrow)

private theorem hookSat_of_eq {α : Type} {H H' : LibsignalHooks} {sym : String} {spec : Spec α}
    (heq : H' sym = H sym) (hs : HookSat H sym spec) : HookSat H' sym spec := by
  rcases hs with ⟨f, hf, hok⟩
  exact ⟨f, heq.trans hf, hok⟩

private def vsigKeepSym (n : String) : Bool :=
  n == lsMemcpySym || n == lsVerifyMemsetSym || n == lsBlackBoxU8Sym ||
    n == lsVerifyMontToEdSym || n == lsDalekCompressSym || n == lsDalekEdNegSym ||
    n == lsSha512CompressSym || n == lsDalekScalarWideSym || n == lsDalekScalarModSym ||
    n == lsDalekDoubleMulSym

private def vsigOnlyHooks (H : LibsignalHooks) (n : String) : Option (State → State) :=
  if vsigKeepSym n then H n
  else match H n with
    | some _ => some (fun s => s.setStatus (.Exception "ext"))
    | none => none

private theorem w3VerifySigHooks_vsigOnly [LibsignalPlacement]
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh)
    (Y : UnreachedPqxdhPrimitives) :
    VerifySignaturePlacedHooks (modelPrims Y ⟨W.C, W.Q⟩)
      (vsigOnlyHooks (cliGhostExterns gh (cliExternsPlaced mmpl W))) where
  memcpy := by
    obtain ⟨f, hf, _, _, _, hok, _, _, _, _, _⟩ := hG.memcpy
    refine ⟨f, ?_, hok⟩
    exact (show vsigOnlyHooks (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsMemcpySym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) "memcpy" by
        simp [vsigOnlyHooks, vsigKeepSym, lsMemcpySym]).trans
      (cliGhostExterns_memcpy_some gh (cliExternsPlaced mmpl W) hf)
  memset := by
    obtain ⟨f, hf, _, hok, _, _, _, _, _⟩ := hG.memset
    refine ⟨f, ?_, hok pqxdhHookStack (by decide)⟩
    exact (show vsigOnlyHooks (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsVerifyMemsetSym =
        cliGhostExterns gh (cliExternsPlaced mmpl W) "memset" by
        simp [vsigOnlyHooks, vsigKeepSym, lsVerifyMemsetSym]).trans
      (cliGhostExterns_memset_some gh (cliExternsPlaced mmpl W) hf)
  blackBox := (show vsigOnlyHooks (cliGhostExterns gh (cliExternsPlaced mmpl W)) lsBlackBoxU8Sym =
      cliGhostExterns gh (cliExternsPlaced mmpl W) lsBlackBoxU8Sym by
      simp [vsigOnlyHooks, vsigKeepSym]).trans
    (cliGhost_row mmpl gh W (blackBox_row_placed mmpl W))
  montToEd := hookSat_of_eq (by simp [vsigOnlyHooks, vsigKeepSym])
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_toEdwards_sat mmpl W Y (img := default)))
  compress := hookSat_of_eq (by simp [vsigOnlyHooks, vsigKeepSym])
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_compress_sat mmpl W))
  edNeg := hookSat_of_eq (by simp [vsigOnlyHooks, vsigKeepSym])
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_edNeg_sat mmpl W))
  sha512Compress := hookSat_of_eq (by simp [vsigOnlyHooks, vsigKeepSym])
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_compress512_sat mmpl W Y (img := default)))
  scalarWide := hookSat_of_eq (by simp [vsigOnlyHooks, vsigKeepSym])
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_scalarWide_sat mmpl W))
  scalarMod := hookSat_of_eq (by simp [vsigOnlyHooks, vsigKeepSym])
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_scalarMod_sat mmpl W))
  doubleMul := hookSat_of_eq (by simp [vsigOnlyHooks, vsigKeepSym])
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl gh W
      (cliExternsPlaced_dsmb_sat mmpl W Y (img := default)))

private def keepLs [LibsignalPlacement] (pc : BitVec 64) : Bool :=
  (List.range libsignalSessionLib.blocks.length).any fun j =>
    !(decide (j ∈ libsignalMutatedBlocks)) &&
      ProofLib.progKeep (libsignalSessionLib.blockProgram lsmpl j vmTrapHooks) pc

private def relocsSorted : Nat → List Obj.RelocEntry → Bool
  | _, [] => true
  | bound, r :: rs => decide (bound ≤ r.off ∧ r.off % 4 = 0) && relocsSorted (r.off + 4) rs

private theorem find?_none_of_relocsSorted :
    ∀ {off bound : Nat} {rs : List Obj.RelocEntry},
      off < bound → relocsSorted bound rs = true → rs.find? (·.off == off) = none
  | _, _, [], _, _ => rfl
  | off, bound, r :: rs, hlt, hs => by
    simp only [relocsSorted, Bool.and_eq_true, decide_eq_true_eq] at hs
    dsimp only [List.find?]
    rw [beq_false_of_ne (by omega)]
    exact find?_none_of_relocsSorted (by omega) hs.2

private def scanWordsRelocs : Nat → List Obj.RelocEntry → List (BitVec 8) → Bool
  | _, _, [] => true
  | off, [], b0 :: b1 :: b2 :: b3 :: rest =>
    let w := Obj.wordOfBytesLE [b0, b1, b2, b3] 0
    ((w != 0xd400_0001#32) && !Arm64.isMsrTpidrEl0Word w) && scanWordsRelocs (off + 4) [] rest
  | off, r :: rs, b0 :: b1 :: b2 :: b3 :: rest =>
    let w := Obj.wordOfBytesLE [b0, b1, b2, b3] 0
    if r.off == off then
      VerifiedLibraries.RustStd.checkRelocWordNoSvc0 w r && scanWordsRelocs (off + 4) rs rest
    else
      decide (off < r.off) && ((w != 0xd400_0001#32) && !Arm64.isMsrTpidrEl0Word w) &&
        scanWordsRelocs (off + 4) (r :: rs) rest
  | _, _, _ => false

private theorem scanWordsRelocs_imp (blk : Obj.CodeBlock) :
    ∀ (bs : List (BitVec 8)) (off : Nat) (rs : List Obj.RelocEntry),
      off % 4 = 0 → relocsSorted off rs = true →
      (∀ k, off ≤ k → blk.relocAt? k = rs.find? (·.off == k)) →
      scanWordsRelocs off rs bs = true → checkBytesSafeVm blk off bs = true
  | [], _, _, _, _, _, _ => rfl
  | [_], _, rs, _, _, _, h | [_, _], _, rs, _, _, _, h | [_, _, _], _, rs, _, _, _, h => by
    cases rs <;> simp [scanWordsRelocs] at h
  | b0 :: b1 :: b2 :: b3 :: rest, off, [], hal, _, hrel, h => by
    simp only [scanWordsRelocs, Bool.and_eq_true] at h
    unfold checkBytesSafeVm
    rw [hrel off (Nat.le_refl off)]; dsimp only [List.find?]; simp only [Bool.and_eq_true]
    exact ⟨h.1, scanWordsRelocs_imp blk rest (off + 4) [] (by omega) rfl
      (fun k hk => hrel k (by omega)) h.2⟩
  | b0 :: b1 :: b2 :: b3 :: rest, off, r :: rs, hal, hsort, hrel, h => by
    simp only [relocsSorted, Bool.and_eq_true, decide_eq_true_eq] at hsort
    dsimp only [scanWordsRelocs] at h
    cases heq : r.off == off
    · rw [heq] at h
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
      have hsort' : relocsSorted (off + 4) (r :: rs) = true := by
        simp only [relocsSorted, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨⟨by omega, hsort.1.2⟩, hsort.2⟩
      unfold checkBytesSafeVm
      rw [hrel off (Nat.le_refl off), find?_none_of_relocsSorted (by omega) hsort']
      simp only [Bool.and_eq_true]
      exact ⟨h.1.2, scanWordsRelocs_imp blk rest (off + 4) (r :: rs) (by omega) hsort'
        (fun k hk => hrel k (by omega)) h.2⟩
    · rw [heq] at h
      simp only [↓reduceIte, Bool.and_eq_true] at h
      have hroff : r.off = off := beq_iff_eq.mp heq
      unfold checkBytesSafeVm
      rw [hrel off (Nat.le_refl off)]; dsimp only [List.find?]; rw [heq]
      simp only [Bool.and_eq_true]
      refine ⟨h.1, scanWordsRelocs_imp blk rest (off + 4) rs (by omega) (hroff ▸ hsort.2)
        (fun k hk => ?_) h.2⟩
      rw [hrel k (by omega)]; dsimp only [List.find?]; rw [beq_false_of_ne (by omega)]

private def checkBlockSafeVmFast (blk : Obj.CodeBlock) : Bool :=
  if relocsSorted 0 blk.relocs then
    scanWordsRelocs 0 blk.relocs blk.code &&
      blk.relocs.all (fun r => VerifiedLibraries.RustStd.relocKindSafeNoSvc0 r.kind)
  else checkBlockSafeVm blk

private theorem checkBlockSafeVmFast_imp {blk : Obj.CodeBlock}
    (h : checkBlockSafeVmFast blk = true) : checkBlockSafeVm blk = true := by
  unfold checkBlockSafeVmFast at h; split at h
  · rename_i hs; simp only [Bool.and_eq_true] at h; unfold checkBlockSafeVm
    simp only [Bool.and_eq_true]
    exact ⟨scanWordsRelocs_imp blk blk.code 0 blk.relocs rfl hs (fun _ _ => rfl) h.1, h.2⟩
  · exact h

private def checkBlocksAt : Nat → List Obj.CodeBlock → Bool
  | _, [] => true
  | j, b :: bs =>
    (decide (j ∈ libsignalMutatedBlocks) || checkBlockSafeVmFast b) && checkBlocksAt (j + 1) bs

private theorem checkBlocksAt_append :
    ∀ (k : Nat) (xs ys : List Obj.CodeBlock),
      checkBlocksAt k xs = true → checkBlocksAt (k + xs.length) ys = true →
      checkBlocksAt k (xs ++ ys) = true
  | _, [], _, _, hy => by simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hy
  | k, _ :: xs, ys, hx, hy => by
    simp only [List.cons_append, checkBlocksAt, Bool.and_eq_true] at hx ⊢
    exact ⟨hx.1, checkBlocksAt_append (k + 1) xs ys hx.2
      (by simpa only [List.length_cons, show k + 1 + xs.length = k + (xs.length + 1) by omega]
        using hy)⟩

private theorem checkBlocksAt_getD :
    ∀ (k : Nat) (bs : List Obj.CodeBlock) (i : Nat),
      i < bs.length → checkBlocksAt k bs = true →
      (decide ((k + i) ∈ libsignalMutatedBlocks) ||
        checkBlockSafeVmFast (bs.getD i { code := [] })) = true
  | _, [], _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | k, _ :: _, 0, _, h => by
    simp only [checkBlocksAt, Bool.and_eq_true] at h
    simpa only [Nat.add_zero, List.getD, List.getElem?_cons_zero, Option.getD_some] using h.1
  | k, b :: bs, i + 1, hi, h => by
    simp only [checkBlocksAt, Bool.and_eq_true] at h
    rw [show (b :: bs).getD (i + 1) { code := [] } = bs.getD i { code := [] } from rfl,
      show k + (i + 1) = k + 1 + i by omega]
    exact checkBlocksAt_getD (k + 1) bs i (by simp at hi; omega) h.2

private theorem safeVm_lo : checkBlocksAt 0 (libsignalSessionLib.blocks.take 310) = true := by
  decide +kernel
private theorem safeVm_hi : checkBlocksAt 310 (libsignalSessionLib.blocks.drop 310) = true := by
  decide +kernel
private theorem allUnmutated_safeVm : checkBlocksAt 0 libsignalSessionLib.blocks = true := by
  rw [← List.take_append_drop 310 libsignalSessionLib.blocks]
  exact checkBlocksAt_append 0 _ _ safeVm_lo
    (by rw [Nat.zero_add, List.length_take, libsignalSessionLib_blocks_length]; exact safeVm_hi)

private theorem align4_add4_le {pc b off clen : Nat}
    (hp : pc % 4 = 0) (hb : b % 4 = 0) (hc : clen % 4 = 0)
    (heq : pc = b + off) (hlt : off < clen) : off + 4 ≤ clen := by omega

private theorem libsignalRoLoaded_strip (kp : BitVec 64 → Bool) {pl : MultiPlacement} {m : Memory}
    (hro : LibsignalRoLoaded pl m) : LibsignalRoLoaded pl (ProofLib.stripExecOutside kp m) := by
  intro d hd hro_d k hk; obtain ⟨hb, hp, hlf⟩ := hro d hd hro_d k hk
  exact ⟨by simpa only [ProofLib.strip_read8] using hb,
    by rw [ProofLib.strip_perm, hp]; cases kp (pl.ρ d.sym + BitVec.ofNat 64 k) <;> rfl,
    by simpa only [ProofLib.strip_isLazyFree] using hlf⟩

private theorem libsignalCodeLoaded_strip [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) :
    LibsignalCodeLoaded lsmpl (ProofLib.stripExecOutside keepLs m) := fun j hj hunmut X O svc => by
  have hLj := hcl j hj hunmut X O svc
  have hno := hLj.no_wrap
  refine Program.CodeLoaded.intro hLj.aligned hLj.no_wrap fun k hk => ?_
  let P0 := libsignalSessionLib.blockProgram lsmpl j vmTrapHooks
  have hkeep :
      keepLs ((libsignalSessionLib.blockProgram lsmpl j X O svc).base + BitVec.ofNat 64 k) = true := by
    refine List.any_eq_true.mpr ⟨j, List.mem_range.mpr hj,
      Eq.mpr (Bool.and_eq_true _ _) ⟨by simp [hunmut], ?_⟩⟩
    unfold ProofLib.progKeep
    change decide ((P0.base + BitVec.ofNat 64 k - P0.base).toNat < P0.code.length) = true
    rw [show P0.base + BitVec.ofNat 64 k - P0.base = BitVec.ofNat 64 k by bv_omega,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hLj.byte_eq k hk, hLj.perm_eq k hk, hLj.isLazyFree_eq k hk⟩

private theorem findSome?_syms_none :
    ∀ (syms : List (String × Nat)) (off : Nat),
      (syms.findSome? fun x => if x.2 == off then (none : Option (State → State)) else none) = none
  | [], _ => rfl
  | _ :: tl, off => by rw [List.findSome?_cons, ite_self]; exact findSome?_syms_none tl off

private theorem safeVm_of_keepLs [LibsignalPlacement] {m : Memory} {pc : BitVec 64} {inst : Instr}
    (hcl : LibsignalCodeLoaded lsmpl m) (hkeep : keepLs pc = true) (hal_pc : pc.toNat % 4 = 0)
    (hdec : Arm64.decode (m.read32 pc) = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  obtain ⟨j, hj_mem, hboth⟩ := List.any_eq_true.mp hkeep
  have hj : j < libsignalSessionLib.blocks.length := List.mem_range.mp hj_mem
  obtain ⟨hunmut_b, hkp⟩ := Eq.mp (Bool.and_eq_true _ _) hboth
  have hunmut : (j ∈ libsignalMutatedBlocks) = false := by simpa using hunmut_b
  have hall_j := checkBlocksAt_getD 0 libsignalSessionLib.blocks j hj allUnmutated_safeVm
  simp only [Nat.zero_add, hunmut] at hall_j
  let lib := libsignalSessionLib.blockLib j
  let pl := libsignalSessionLib.blockPlacement lsmpl j
  let Q := (lib.program pl).rebase pl.base (fun _ => none)
  have hall := placedLib_rebase_allInstrs_safeVm lib pl (fun _ => none) (checkBlockSafeVmFast_imp hall_j)
  have hLQ : Q.CodeLoaded m :=
    (hcl j hj hunmut (fun _ => none) (fun _ => none) Syscall.standard).of_base_code rfl rfl
  have hlen_mod4 : Q.code.length % 4 = 0 := by
    have hc : Q.code = lib.text.patched pl := rfl
    rw [hc, Obj.CodeBlock.length_patched]; omega
  have hbase_al : Q.base.toNat % 4 = 0 := hLQ.aligned
  have hno_wrap : Q.base.toNat + Q.code.length ≤ 2 ^ 64 := hLQ.no_wrap
  have hoff_lt : (pc - Q.base).toNat < Q.code.length := of_decide_eq_true hkp
  have hpc_eq : pc = Q.base + BitVec.ofNat 64 (pc - Q.base).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm Q.base, BitVec.sub_add_cancel]
  have hpc_nat : pc.toNat = Q.base.toNat + (pc - Q.base).toNat := by
    conv_lhs => rw [hpc_eq]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (a := (pc - Q.base).toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hin : (pc - Q.base).toNat + 4 ≤ Q.code.length :=
    align4_add4_le hal_pc hbase_al hlen_mod4 hpc_nat hoff_lt
  have hfe_Q : Q.fetchMem m pc = some inst := by
    have hext_Q : Q.externAt? pc = none := by
      unfold Q Program.externAt? Program.hookAtOff? Program.rebase; dsimp only
      rw [findSome?_syms_none, findSome?_syms_none]; rfl
    have hce_Q : m.canExec pc 4 = true := by
      unfold Memory.canExec; rw [Memory.allPerm_iff]; intro k hk
      rw [show pc + BitVec.ofNat 64 k = Q.base + BitVec.ofNat 64 ((pc - Q.base).toNat + k) by
        conv_lhs => rw [hpc_eq]; rw [BitVec.add_assoc, ← BitVec.ofNat_add],
        hLQ.perm_eq _ (Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) hin)]; rfl
    unfold Program.fetchMem; rw [hext_Q]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
      not_true_eq_false, hce_Q, Bool.not_true]
    exact hdec
  simpa only [Bool.not_eq_true', Bool.or_eq_false_iff] using
    Program.fetchMem_of_allInstrs_holdsBytes_in_code hall hbase_al hno_wrap
      (fun k hk => ⟨hLQ.byte_eq k hk, hLQ.perm_eq k hk, hLQ.isLazyFree_eq k hk⟩) hin hfe_Q

private theorem strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ∀ n, (ProofLib.stripExecOutside keep m).readBytes a n = m.readBytes a n
  | 0 => rfl
  | n + 1 => by
    simp [Memory.readBytes, ProofLib.strip_read8, strip_readBytes keep m (a + 1#64) n]

private theorem strip_writeBytes_comm (keep : BitVec 64 → Bool) :
    ∀ (bs : List (BitVec 8)) (m : Memory) (a : BitVec 64),
      (ProofLib.stripExecOutside keep m).writeBytes a bs =
        ProofLib.stripExecOutside keep (m.writeBytes a bs)
  | [], _, _ => rfl
  | b :: bs, m, a => by
    simp only [Memory.writeBytes]
    rw [ProofLib.strip_write8, strip_writeBytes_comm keep bs (m.write8 a b) (a + 1#64)]

private theorem strip_write64_comm (keep : BitVec 64 → Bool) (m : Memory) (a v : BitVec 64) :
    (ProofLib.stripExecOutside keep m).write64 a v =
      ProofLib.stripExecOutside keep (m.write64 a v) := by
  simp only [Memory.write64, ProofLib.strip_write8]

private theorem writeBytes_perm_eq (m : Memory) (p : BitVec 64) (bs : List (BitVec 8))
    (a : BitVec 64) : (m.writeBytes p bs).perm a = m.perm a :=
  congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_writeBytes_norm m p bs) a

/-! ### `hideWx` + `stripWx` State Projection -/

private def hideWx (m : Memory) : Memory :=
  ⟨fun a => match m.cells a with
    | some (some p, b) =>
      if p.w && p.x then
        if p.r then some (some { p with r := false, w := false, x := false }, b)
        else some (none, b)
      else some (some p, b)
    | other => other⟩

private def hideWxS (s : State) : State := s.setMem (hideWx s.mem)

private def stripWx [LibsignalPlacement] (m : Memory) : Memory :=
  ProofLib.stripExecOutside keepLs (hideWx m)

private def stripWxS [LibsignalPlacement] (s : State) : State :=
  ProofLib.stripS keepLs (hideWxS s)

private theorem hideWx_read8 (m : Memory) (a : BitVec 64) : (hideWx m).read8 a = m.read8 a := by
  dsimp only [hideWx, Memory.read8]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · by_cases hw : (p.w && p.x) = true <;> by_cases hr : p.r = true <;> simp [hw, hr]

private theorem hideWx_readSized (m : Memory) (sz : MemWidth) (sg : Bool) (a : BitVec 64) :
    (hideWx m).readSized sz sg a = m.readSized sz sg a := by
  cases sz <;> simp [Memory.readSized, Memory.read16, Memory.read32, Memory.read64, hideWx_read8]

private theorem hideWx_readSimdSized (m : Memory) (sz : SimdMemSize) (a : BitVec 64) :
    (hideWx m).readSimdSized sz a = m.readSimdSized sz a := by
  cases sz <;>
    simp [Memory.readSimdSized, Memory.read16, Memory.read32, Memory.read64, Memory.read128,
      hideWx_read8]

private theorem hideWx_readBytes (m : Memory) (a : BitVec 64) :
    ∀ n, (hideWx m).readBytes a n = m.readBytes a n
  | 0 => rfl
  | n + 1 => by simp [Memory.readBytes, hideWx_read8, hideWx_readBytes m (a + 1#64) n]

private theorem stripWx_read8 [LibsignalPlacement] (m : Memory) (a : BitVec 64) :
    (stripWx m).read8 a = m.read8 a :=
  (ProofLib.strip_read8 keepLs (hideWx m) a).trans (hideWx_read8 m a)

private theorem stripWx_read32 [LibsignalPlacement] (m : Memory) (a : BitVec 64) :
    (stripWx m).read32 a = m.read32 a := by
  simp [Memory.read32, stripWx_read8]

private theorem stripWx_read64 [LibsignalPlacement] (m : Memory) (a : BitVec 64) :
    (stripWx m).read64 a = m.read64 a := by
  simp [Memory.read64, stripWx_read8]

private theorem stripWx_readBytes [LibsignalPlacement] (m : Memory) (a : BitVec 64) (n : Nat) :
    (stripWx m).readBytes a n = m.readBytes a n :=
  (strip_readBytes keepLs (hideWx m) a n).trans (hideWx_readBytes m a n)

private theorem stripWx_readVecN [LibsignalPlacement] (m : Memory) (a : BitVec 64) (n : Nat) :
    readVecN (stripWx m) a n = readVecN m a n :=
  Subtype.ext (stripWx_readBytes m a n)

private theorem stripWx_readSha512State [LibsignalPlacement] (m : Memory) (a : BitVec 64) :
    readSha512State (stripWx m) a = readSha512State m a := by
  unfold readSha512State; congr 1; funext i; exact stripWx_read64 m _

private theorem hideWx_write8 (m : Memory) (addr : BitVec 64) (val : BitVec 8) :
    (hideWx m).write8 addr val = hideWx (m.write8 addr val) := by
  unfold hideWx Memory.write8 Memory.rawPerm
  congr 1; funext a
  by_cases ha : a = addr
  · subst ha; simp only [↓reduceIte]
    rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, b⟩
    · rfl
    · rfl
    · cases r <;> cases w <;> cases x <;> rfl
  · simp [ha]

private theorem hideWx_write16 (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (hideWx m).write16 a v = hideWx (m.write16 a v) := by
  simp only [Memory.write16, hideWx_write8]

private theorem hideWx_write32 (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (hideWx m).write32 a v = hideWx (m.write32 a v) := by
  simp only [Memory.write32, hideWx_write8]

private theorem hideWx_write64 (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (hideWx m).write64 a v = hideWx (m.write64 a v) := by
  simp only [Memory.write64, hideWx_write8]

private theorem hideWx_writeSized (m : Memory) (sz : MemWidth) (a : BitVec 64) (v : BitVec 64) :
    (hideWx m).writeSized sz a v = hideWx (m.writeSized sz a v) := by
  cases sz <;>
    simp only [Memory.writeSized, hideWx_write8, hideWx_write16, hideWx_write32, hideWx_write64]

private theorem hideWx_writeSimdSized (m : Memory) (sz : SimdMemSize) (a : BitVec 64)
    (v : BitVec 128) :
    (hideWx m).writeSimdSized sz a v = hideWx (m.writeSimdSized sz a v) := by
  cases sz <;>
    simp only [Memory.writeSimdSized, Memory.write128, hideWx_write8, hideWx_write16,
      hideWx_write32, hideWx_write64]

private theorem hideWx_simdStoreRegs (sz : SimdMemSize) (vfn : BitVec 5 → BitVec 128) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (m : Memory),
      simdStoreRegs sz vfn n vt ea (hideWx m) = hideWx (simdStoreRegs sz vfn n vt ea m)
  | 0, _, _, _ => rfl
  | n + 1, _, _, m => by
    simp only [simdStoreRegs, hideWx_writeSimdSized, hideWx_simdStoreRegs sz vfn n]

private theorem hideWx_writeBytes :
    ∀ (bs : List (BitVec 8)) (m : Memory) (a : BitVec 64),
      (hideWx m).writeBytes a bs = hideWx (m.writeBytes a bs)
  | [], _, _ => rfl
  | b :: bs, m, a => by
    simp only [Memory.writeBytes, hideWx_write8, hideWx_writeBytes bs (m.write8 a b) (a + 1#64)]

private theorem stripWx_writeBytes [LibsignalPlacement] (bs : List (BitVec 8)) (m : Memory)
    (a : BitVec 64) :
    (stripWx m).writeBytes a bs = stripWx (m.writeBytes a bs) := by
  unfold stripWx
  rw [strip_writeBytes_comm, hideWx_writeBytes]

private theorem stripWx_write64 [LibsignalPlacement] (m : Memory) (a v : BitVec 64) :
    (stripWx m).write64 a v = stripWx (m.write64 a v) := by
  unfold stripWx
  rw [strip_write64_comm, hideWx_write64]

private theorem write8_isAnon (m : Memory) (addr : BitVec 64) (val : BitVec 8) (a : BitVec 64) :
    (m.write8 addr val).isAnon a = m.isAnon a := by
  unfold Memory.write8 Memory.isAnon Memory.rawPerm
  by_cases ha : a = addr
  · subst ha; simp only [↓reduceIte]; rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl
  · simp [ha]

private theorem writeBytes_isAnon :
    ∀ (bs : List (BitVec 8)) (m : Memory) (p a : BitVec 64),
      (m.writeBytes p bs).isAnon a = m.isAnon a
  | [], _, _, _ => rfl
  | b :: bs, m, p, a =>
    (writeBytes_isAnon bs (m.write8 p b) (p + 1#64) a).trans (write8_isAnon m p b a)

private theorem hideWx_perm (m : Memory) (a : BitVec 64) :
    (hideWx m).perm a =
      match m.perm a with
      | some p =>
        if p.w && p.x then
          if p.r then some Perm.protNone else none
        else some p
      | none => none := by
  dsimp only [hideWx, Memory.perm, Perm.rwx, Perm.protNone]
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩
  · rfl
  · rfl
  · cases r <;> cases w <;> cases x <;> rfl

private theorem stripWx_perm_congr [LibsignalPlacement] {m1 m2 : Memory} {a : BitVec 64}
    (h : m1.perm a = m2.perm a) :
    (stripWx m1).perm a = (stripWx m2).perm a := by
  unfold stripWx
  rw [ProofLib.strip_perm, ProofLib.strip_perm, hideWx_perm, hideWx_perm, h]

private theorem hideWx_of_not_wx {m : Memory} {a : BitVec 64}
    (hnwx : ((m.perm a).w && (m.perm a).x) = false) :
    (hideWx m).perm a = m.perm a ∧
    (hideWx m).isLazyFree a = m.isLazyFree a ∧
    (hideWx m).isAnon a = m.isAnon a := by
  dsimp only [hideWx, Memory.perm, Memory.isLazyFree, Memory.isAnon, Option.w, Option.x,
    Perm.rwx] at hnwx ⊢
  revert hnwx
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> intro hnwx
  · exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩
  · cases w <;> cases x <;> simp at hnwx ⊢

private theorem hideWx_canWrite (m : Memory) (addr : BitVec 64) (n : Nat) :
    (hideWx m).canWrite addr n = m.canWrite addr n := by
  unfold Memory.canWrite
  apply Bool.eq_iff_iff.mpr
  rw [Memory.allPerm_iff, Memory.allPerm_iff]
  refine ⟨fun h k hk => ?_, fun h k hk => ?_⟩ <;>
    (have hk' := h k hk; revert hk'; rw [hideWx_perm];
     rcases m.perm (addr + BitVec.ofNat 64 k) with _ | ⟨r, w, x, lf, an⟩ <;>
       [simp; (cases r <;> cases w <;> cases x <;> simp [Perm.protNone, Option.w, Option.x])])

private theorem hideWx_canRead_imp {m : Memory} {addr : BitVec 64} {n : Nat}
    (h : (hideWx m).canRead addr n = true) :
    m.canRead addr n = true := by
  unfold Memory.canRead at h ⊢
  rw [Bool.and_eq_true, Memory.allPerm_iff, Memory.allNoLazyFree_iff] at h ⊢
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have h1 := h.1 k hk
    rw [hideWx_perm] at h1
    revert h1
    rcases m.perm (addr + BitVec.ofNat 64 k) with _ | ⟨r, w, x, lf, an⟩ <;> intro h1
    · simp [Option.r] at h1
    · cases r <;> cases w <;> cases x <;> simp [Perm.protNone, Option.r] at h1 ⊢
  · have h1 := h.1 k hk
    have h2 := h.2 k hk
    dsimp only [hideWx, Memory.perm, Memory.isLazyFree, Option.r, Perm.rwx, Perm.protNone] at h1 h2 ⊢
    revert h1 h2
    rcases m.cells (addr + BitVec.ofNat 64 k) with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> intro h1 h2
    · rfl
    · rfl
    · cases r <;> cases w <;> cases x <;> simp at h1 h2 ⊢ <;> exact h2

private theorem stripWx_permNoLazy_rw_iff [LibsignalPlacement] (m : Memory) (a : BitVec 64) :
    (stripWx m).permNoLazy a = some Perm.rw ↔ m.permNoLazy a = some Perm.rw := by
  rw [Memory.permNoLazy_eq_some_rw_iff, Memory.permNoLazy_eq_some_rw_iff]
  unfold stripWx
  rw [(ProofLib.strip_perm_props keepLs (hideWx m) a).2.2.2, ProofLib.strip_isLazyFree]
  dsimp only [hideWx, Memory.perm, Memory.isLazyFree, Perm.rw, Perm.rwx, Perm.protNone]
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩
  · simp
  · simp
  · cases r <;> cases w <;> cases x <;> cases lf <;> simp

private theorem stripWx_rw_iff [LibsignalPlacement] (m : Memory) (base : BitVec 64) (len : Nat) :
    (stripWx m).RW base len ↔ m.RW base len :=
  ⟨fun h a ha => (stripWx_permNoLazy_rw_iff m a).mp (h a ha),
   fun h a ha => (stripWx_permNoLazy_rw_iff m a).mpr (h a ha)⟩

private theorem stripWx_readable_imp [LibsignalPlacement] {m : Memory} {base : BitVec 64}
    {len : Nat} (h : (stripWx m).Readable base len) :
    m.Readable base len := by
  intro a ha
  obtain ⟨hr, hlf⟩ := h a ha
  unfold stripWx at hr hlf
  rw [(ProofLib.strip_perm_props keepLs (hideWx m) a).1] at hr
  rw [ProofLib.strip_isLazyFree] at hlf
  dsimp only [hideWx, Memory.perm, Memory.isLazyFree, Option.r, Perm.rwx, Perm.protNone] at hr hlf ⊢
  revert hr hlf
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> intro hr hlf
  · simp at hr
  · simp at hr
  · cases r <;> cases w <;> cases x <;> cases lf <;> simp at hr hlf ⊢

private theorem stripWx_mapped_props [LibsignalPlacement] {m : Memory} {a : BitVec 64}
    (hm : ((stripWx m).perm a).mapped = true) :
    (m.perm a).mapped = true ∧
    (stripWx m).isLazyFree a = m.isLazyFree a ∧
    (stripWx m).isAnon a = m.isAnon a := by
  unfold stripWx at hm ⊢
  rw [(ProofLib.strip_perm_props keepLs (hideWx m) a).2.2.1] at hm
  rw [ProofLib.strip_isLazyFree, ProofLib.strip_isAnon]
  dsimp only [hideWx, Memory.perm, Memory.isLazyFree, Memory.isAnon, Option.mapped, Perm.rwx,
    Perm.protNone] at hm ⊢
  revert hm
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> intro hm
  · simp at hm
  · simp at hm
  · cases r <;> cases w <;> cases x <;> simp at hm ⊢

private theorem stripWx_keepsFrozen [LibsignalPlacement] {m1 m2 : Memory}
    (hkf : m1.KeepsFrozen m2) :
    (stripWx m1).KeepsFrozen (stripWx m2) := by
  intro a hfz
  have ⟨hm1_fz, hnwx1⟩ : m1.Frozen a ∧ ((m1.perm a).w && (m1.perm a).x) = false := by
    unfold Memory.Frozen stripWx at hfz
    rw [ProofLib.strip_perm, hideWx_perm] at hfz
    dsimp only [Memory.Frozen, Option.frozen, Perm.frozen, Option.w, Option.x, ProofLib.stripPerm,
      Perm.protNone] at hfz ⊢
    generalize keepLs a = ic at hfz
    revert hfz
    rcases m1.perm a with _ | ⟨r, w, x, lf, an⟩ <;> intro hfz
    · simp at hfz
    · cases ic <;> cases r <;> cases w <;> cases x <;>
        simp [ProofLib.stripPerm] at hfz ⊢
  obtain ⟨hrd, hpm, hlf, han⟩ := hkf a hm1_fz
  have hnwx2 : ((m2.perm a).w && (m2.perm a).x) = false := by rw [hpm]; exact hnwx1
  obtain ⟨hp1, hlf1, han1⟩ := hideWx_of_not_wx hnwx1
  obtain ⟨hp2, hlf2, han2⟩ := hideWx_of_not_wx hnwx2
  refine ⟨(stripWx_read8 m2 a).trans (hrd.trans (stripWx_read8 m1 a).symm),
    stripWx_perm_congr hpm, ?_, ?_⟩
  · unfold stripWx
    rw [ProofLib.strip_isLazyFree, ProofLib.strip_isLazyFree, hlf2, hlf1, hlf]
  · unfold stripWx
    rw [ProofLib.strip_isAnon, ProofLib.strip_isAnon, han2, han1, han]

private theorem libsignalRoLoaded_stripWx [LibsignalPlacement] {pl : MultiPlacement} {m : Memory}
    (hro : LibsignalRoLoaded pl m) : LibsignalRoLoaded pl (stripWx m) := by
  refine libsignalRoLoaded_strip keepLs fun d hd hro_d k hk => ?_
  obtain ⟨hb, hp, hlf⟩ := hro d hd hro_d k hk
  have hnwx : ((m.perm (pl.ρ d.sym + BitVec.ofNat 64 k)).w &&
      (m.perm (pl.ρ d.sym + BitVec.ofNat 64 k)).x) = false := by rw [hp]; rfl
  obtain ⟨hp', hlf', _⟩ := hideWx_of_not_wx hnwx
  exact ⟨(hideWx_read8 m _).trans hb, hp'.trans hp, hlf'.trans hlf⟩

private theorem libsignalCodeLoaded_stripWx [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) :
    LibsignalCodeLoaded lsmpl (stripWx m) := by
  refine libsignalCodeLoaded_strip fun j hj hunmut X O svc => ?_
  have hLj := hcl j hj hunmut X O svc
  refine Program.CodeLoaded.intro hLj.aligned hLj.no_wrap fun k hk => ?_
  have hp := hLj.perm_eq k hk
  have hnwx : ((m.perm ((libsignalSessionLib.blockProgram lsmpl j X O svc).base +
      BitVec.ofNat 64 k)).w &&
      (m.perm ((libsignalSessionLib.blockProgram lsmpl j X O svc).base +
      BitVec.ofNat 64 k)).x) = false := by rw [hp]; rfl
  obtain ⟨hp', hlf', _⟩ := hideWx_of_not_wx hnwx
  exact ⟨(hideWx_read8 m _).trans (hLj.byte_eq k hk), hp'.trans hp,
    hlf'.trans (hLj.isLazyFree_eq k hk)⟩

/-! ### `execInst` Commutation with `hideWxS` & `stripWxS` -/

private theorem hw_mem (s : State) : (hideWxS s).mem = hideWx s.mem := by cases s; rfl
private theorem hw_r64 (s : State) (r : Reg) : (hideWxS s).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem hw_r32 (s : State) (r : Reg) : (hideWxS s).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem hw_rr (s : State) (w : Width) (r : Reg) : (hideWxS s).readReg w r = s.readReg w r := by cases s; rfl
private theorem hw_rv128 (s : State) (r : BitVec 5) : (hideWxS s).readVReg128 r = s.readVReg128 r := by cases s; rfl
private theorem hw_rv128_eta (s : State) : (hideWxS s).readVReg128 = s.readVReg128 := by funext r; cases s; rfl
private theorem hw_rv64 (s : State) (r : BitVec 5) : (hideWxS s).readVReg64 r = s.readVReg64 r := by cases s; rfl
private theorem hw_rv32 (s : State) (r : BitVec 5) : (hideWxS s).readVReg32 r = s.readVReg32 r := by cases s; rfl
private theorem hw_pc (s : State) : (hideWxS s).pc = s.pc := by cases s; rfl
private theorem hw_sp (s : State) : (hideWxS s).sp = s.sp := by cases s; rfl
private theorem hw_ps (s : State) : (hideWxS s).pstate = s.pstate := by cases s; rfl
private theorem hw_fp (s : State) : (hideWxS s).fpsr = s.fpsr := by cases s; rfl
private theorem hw_tp (s : State) : (hideWxS s).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem hw_ewf (s : State) : (hideWxS s).exclWillFail = s.exclWillFail := by cases s; rfl
private theorem hw_csp (s : State) (r : Reg) : checkRegSPAligned (hideWxS s) r = checkRegSPAligned s r := by cases s; cases r <;> rfl
private theorem hw_casp (s : State) (a : AddrMode) : checkAddrSPAligned (hideWxS s) a = checkAddrSPAligned s a := by cases s; cases a <;> rfl
private theorem hw_eam (s : State) (a : AddrMode) : evalAddrMode (hideWxS s) a = evalAddrMode s a := by cases s; cases a <;> rfl
private theorem hw_adv (s : State) : (hideWxS s).advancePC = hideWxS s.advancePC := by cases s; rfl
private theorem hw_spc (s : State) (q : BitVec 64) : (hideWxS s).setPC q = hideWxS (s.setPC q) := by cases s; rfl
private theorem hw_w64 (s : State) (r : Reg) (v : BitVec 64) : (hideWxS s).writeReg64 r v = hideWxS (s.writeReg64 r v) := by cases s; cases r <;> rfl
private theorem hw_w32 (s : State) (r : Reg) (v : BitVec 32) : (hideWxS s).writeReg32 r v = hideWxS (s.writeReg32 r v) := hw_w64 s r _
private theorem hw_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (hideWxS s).writeReg w r v = hideWxS (s.writeReg w r v) := hw_w64 s r _
private theorem hw_wv128 (s : State) (r : BitVec 5) (v : BitVec 128) : (hideWxS s).writeVReg128 r v = hideWxS (s.writeVReg128 r v) := by cases s; rfl
private theorem hw_wv64 (s : State) (r : BitVec 5) (v : BitVec 64) : (hideWxS s).writeVReg64 r v = hideWxS (s.writeVReg64 r v) := hw_wv128 s r _
private theorem hw_wv32 (s : State) (r : BitVec 5) (v : BitVec 32) : (hideWxS s).writeVReg32 r v = hideWxS (s.writeVReg32 r v) := hw_wv128 s r _
private theorem hw_sps (s : State) (q : PState) : (hideWxS s).setPState q = hideWxS (s.setPState q) := by cases s; rfl
private theorem hw_sfp (s : State) (f : BitVec 32) : (hideWxS s).setFpsr f = hideWxS (s.setFpsr f) := by cases s; rfl
private theorem hw_sofp (s : State) (f : BitVec 32) : (hideWxS s).orFpsr f = hideWxS (s.orFpsr f) := by cases s; rfl
private theorem hw_sst (s : State) (st : ExecStatus) : (hideWxS s).setStatus st = hideWxS (s.setStatus st) := by cases s; rfl
private theorem hw_wst (s : State) (st : ExecStatus) : { hideWxS s with status := st } = hideWxS { s with status := st } := by cases s; rfl
private theorem hw_stp (s : State) (v : BitVec 64) : setTpidrEl0 (hideWxS s) v = hideWxS (setTpidrEl0 s v) := by cases s; rfl
private theorem hw_sex (s : State) : (hideWxS s).stepExclOracle = hideWxS s.stepExclOracle := by cases s; rfl
private theorem hw_smem (s : State) (m : Memory) : (hideWxS s).setMem (hideWx m) = hideWxS (s.setMem m) := by cases s; rfl
private theorem hw_as (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    applySimdResult (hideWxS s) rd r = hideWxS (applySimdResult s rd r) := by cases s; cases r <;> rfl
private theorem hw_ass (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    applySimdSatResult (hideWxS s) rd r sat = hideWxS (applySimdSatResult s rd r sat) := by cases s; cases r <;> cases sat <;> rfl
private theorem hw_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      simdLoadRegs sz (hideWx m) n vt ea (hideWxS s) = hideWxS (simdLoadRegs sz m n vt ea s)
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => by simp only [simdLoadRegs, hideWx_readSimdSized, hw_slr sz m n, hw_wv128]
private theorem hw_ite (c : Prop) [Decidable c] (a b : State) :
    (if c then hideWxS a else hideWxS b) = hideWxS (if c then a else b) := by split <;> rfl
private theorem hw_regs (s : State) : (hideWxS s).regs = s.regs := by cases s; rfl
private theorem hw_vregs (s : State) : (hideWxS s).vregs = s.vregs := by cases s; rfl
private theorem hw_bs (s : State) : (hideWxS s).brkStart = s.brkStart := by cases s; rfl
private theorem hw_brk (s : State) : (hideWxS s).brk = s.brk := by cases s; rfl
private theorem hw_fs (s : State) : (hideWxS s).fs = s.fs := by cases s; rfl
private theorem hw_orc (s : State) : (hideWxS s).oracle = s.oracle := by cases s; rfl
private theorem hw_oi (s : State) : (hideWxS s).oracleIdx = s.oracleIdx := by cases s; rfl
private theorem hw_ef (s : State) : (hideWxS s).exclFails = s.exclFails := by cases s; rfl
private theorem hw_tr (s : State) : (hideWxS s).trace = s.trace := by cases s; rfl
private theorem hw_st (s : State) : (hideWxS s).status = s.status := by cases s; rfl
private theorem hw_sym (s : State) : (hideWxS s).symtab = s.symtab := by cases s; rfl
private theorem hw_sig (s : State) : (hideWxS s).sigActions = s.sigActions := by cases s; rfl
private theorem hw_sas (s : State) : (hideWxS s).sigAltStack = s.sigAltStack := by cases s; rfl
private theorem hw_pma (s : State) : (hideWxS s).physMemAvail = s.physMemAvail := by cases s; rfl
private theorem hw_mk {rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma} :
    State.mk rg vr sp pc ps (hideWx m) tp fp bs b fs o oi ef tr st sym sig sas pma =
      hideWxS (State.mk rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma) := rfl

private theorem status_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).status = st := by cases s; rfl
private theorem status_mk {rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma} :
    (State.mk rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma).status = st := rfl
private theorem status_adv (s : State) : s.advancePC.status = s.status := by cases s; rfl
private theorem status_spc (s : State) (q : BitVec 64) : (s.setPC q).status = s.status := by cases s; rfl
private theorem status_w64 (s : State) (r : Reg) (v : BitVec 64) : (s.writeReg64 r v).status = s.status := by cases s; cases r <;> rfl
private theorem status_w32 (s : State) (r : Reg) (v : BitVec 32) : (s.writeReg32 r v).status = s.status := status_w64 s r _
private theorem status_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) : (s.writeReg w r v).status = s.status := status_w64 s r _
private theorem status_wv128 (s : State) (r : BitVec 5) (v : BitVec 128) : (s.writeVReg128 r v).status = s.status := by cases s; rfl
private theorem status_wv64 (s : State) (r : BitVec 5) (v : BitVec 64) : (s.writeVReg64 r v).status = s.status := status_wv128 s r _
private theorem status_wv32 (s : State) (r : BitVec 5) (v : BitVec 32) : (s.writeVReg32 r v).status = s.status := status_wv128 s r _
private theorem status_sps (s : State) (q : PState) : (s.setPState q).status = s.status := by cases s; rfl
private theorem status_sfp (s : State) (f : BitVec 32) : (s.setFpsr f).status = s.status := by cases s; rfl
private theorem status_sofp (s : State) (f : BitVec 32) : (s.orFpsr f).status = s.status := by cases s; rfl
private theorem status_stp (s : State) (v : BitVec 64) : (setTpidrEl0 s v).status = s.status := by cases s; rfl
private theorem status_sex (s : State) : s.stepExclOracle.status = s.status := by cases s; rfl
private theorem status_smem (s : State) (m : Memory) : (s.setMem m).status = s.status := by cases s; rfl
private theorem status_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      (simdLoadRegs sz m n vt ea s).status = s.status
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => by simp only [simdLoadRegs, status_slr sz m n, status_wv128]
private theorem ite_exc_running_iff (c : Prop) [Decidable c] (msg : String) (x : ExecStatus) :
    ((if c then ExecStatus.Exception msg else x) = ExecStatus.Running) ↔
      (¬c ∧ x = ExecStatus.Running) := by
  by_cases hc : c <;> simp [hc]

local macro "close_hideWxS_mem " h:ident : tactic => `(tactic| (
  try dsimp only [execInst, execInstWithSvc, execLdrLit, execLdp, execStp, evalAddrMode] at $h:ident ⊢
  simp only [hw_mem, hw_regs, hw_vregs, hw_bs, hw_brk, hw_fs, hw_orc, hw_oi, hw_ef, hw_tr,
    hw_st, hw_sym, hw_sig, hw_sas, hw_pma, hw_mk, hw_r64, hw_r32, hw_rr, hw_rv128, hw_rv128_eta,
    hw_rv64, hw_rv32, hw_pc, hw_sp, hw_ps, hw_fp, hw_tp, hw_ewf, hw_csp, hw_casp, hw_eam,
    hideWx_canWrite, hideWx_readSized, hideWx_readSimdSized,
    hideWx_write8, hideWx_write16, hideWx_write32, hideWx_write64, hideWx_writeSized,
    hideWx_writeSimdSized, hideWx_simdStoreRegs, hw_slr,
    hw_adv, hw_spc, hw_w64, hw_w32, hw_w, hw_wv128, hw_wv64, hw_wv32,
    hw_sps, hw_sfp, hw_sofp, hw_sst, hw_wst, hw_stp, hw_sex, hw_smem, hw_as, hw_ass,
    hw_ite, ↓reduceIte] at $h:ident ⊢
  try (
    simp only [apply_ite State.status, status_setStatus, status_mk, status_adv, status_spc,
      status_w64, status_w32, status_w, status_wv128, status_wv64, status_wv32, status_sps,
      status_sfp, status_sofp, status_stp, status_sex, status_smem, status_slr, ite_self,
      ↓reduceIte, ite_exc_running_iff, Bool.not_eq_true, Bool.not_eq_false',
      Bool.and_eq_true] at $h:ident
    simp_all only [ite_exc_running_iff, Bool.not_eq_true, Bool.not_eq_false', Bool.and_eq_true,
      hideWx_canRead_imp, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte])
))

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem execInst_hideWxS {inst : Instr} (h : inst.isSvc0 = false) (s : State)
    (hrun : (execInst inst (hideWxS s)).status = .Running) :
    execInst inst (hideWxS s) = hideWxS (execInst inst s) := by
  cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc] at hrun ⊢; simp [himm, hw_sst]
    · dsimp only [execInst, execInstWithSvc] at hrun ⊢
      by_cases himm : imm == 1#16 <;> simp [himm, hw_sst]
  case simdThreeSame q u size rm opcode rn rd =>
    by_cases hop : opcode == 0b00011#5
    · have hsz : size = 0#2 ∨ size = 1#2 ∨ size = 2#2 ∨ size = 3#2 := by
        clear h hrun; revert size; decide
      rcases hsz with rfl | rfl | rfl | rfl <;> cases u <;>
        (dsimp only [execInst, execInstWithSvc]; simp only [hop, ↓reduceIte, hw_rv128];
         split <;> simp only [hw_wv128, hw_adv, hw_ass])
    · dsimp only [execInst, execInstWithSvc]
      simp only [hop, Bool.false_eq_true, ↓reduceIte, hw_rv128, hw_regs, hw_vregs, hw_sp, hw_pc,
        hw_ps, hw_mem, hw_tp, hw_fp, hw_bs, hw_brk, hw_fs, hw_orc, hw_oi, hw_ef, hw_tr, hw_st,
        hw_sym, hw_sig, hw_sas, hw_pma, hw_mk, hw_adv, hw_wv128, hw_sst, hw_wst, hw_as, hw_ass,
        hw_ite]
  case st1SinglePost q rm opcode sBit size rn vt =>
    dsimp only [execInst, execInstWithSvc]
    by_cases h0 : opcode.extractLsb' 1 2 == 0#2 <;> by_cases h1 : opcode.extractLsb' 1 2 == 1#2 <;>
      by_cases hs0 : size.extractLsb' 0 1 == 0#1 <;>
      simp only [h0, h1, hs0, Bool.false_eq_true, ↓reduceIte, hw_mem, hw_regs, hw_vregs, hw_sp,
        hw_pc, hw_ps, hw_tp, hw_fp, hw_bs, hw_brk, hw_fs, hw_orc, hw_oi, hw_ef, hw_tr, hw_st,
        hw_sym, hw_sig, hw_sas, hw_pma, hw_mk, hw_r64, hw_rv128, hw_csp, hideWx_canWrite,
        hideWx_write8, hideWx_write16, hideWx_write32, hideWx_write64, hw_smem, hw_w64, hw_adv,
        hw_sst, hw_ite]
  case simdLdStMulti isLoad q size selem rn postIdx rm vt =>
    dsimp only [execInst, execInstWithSvc] at hrun ⊢
    by_cases hbad : (size == 3#2 && !q || !(selem == 2 || selem == 3 || selem == 4)) = true
    · simp only [hbad, ↓reduceIte, hw_regs, hw_vregs, hw_sp, hw_pc, hw_ps, hw_mem, hw_tp, hw_fp,
        hw_bs, hw_brk, hw_fs, hw_orc, hw_oi, hw_ef, hw_tr, hw_st, hw_sym, hw_sig, hw_sas, hw_pma,
        hw_mk, hw_wst]
    · cases isLoad <;> by_cases h3 : selem ≥ 3 <;> by_cases h4 : selem ≥ 4 <;>
        (simp only [hbad, h3, h4, Bool.false_eq_true, ↓reduceIte, hw_r64, hw_rv128_eta, hw_mem,
          hw_csp, hideWx_canWrite, hideWx_readSimdSized, hideWx_simdStoreRegs,
          hw_w64, hw_wv128, hw_adv, hw_smem, hw_sst, hw_ite] at hrun ⊢;
         try (rw [hw_st] at hrun; (repeat' split at hrun) <;>
           simp_all only [hw_st, status_setStatus, reduceCtorEq, not_true_eq_false,
             Bool.not_eq_true, Bool.not_eq_false, Bool.not_eq_false', Bool.and_eq_true,
             hideWx_canRead_imp, ↓reduceIte]))
  case ldr _ _ _ _ addr | str _ _ addr | ldp _ _ _ _ addr | stp _ _ _ addr
     | ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
    dsimp only [execInst, execInstWithSvc, execLdr, execStr, execLdp, execStp] at hrun ⊢
    rw [hw_casp, hw_eam] at hrun ⊢
    rcases hea : evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      (simp only [hea, hw_mem, hw_r64, hw_rv128, hideWx_canWrite, hideWx_readSized,
        hideWx_readSimdSized, hideWx_writeSized, hideWx_writeSimdSized,
        hw_w64, hw_w, hw_wv128, hw_smem, hw_adv, hw_sst, hw_ite] at hrun ⊢;
       try (rw [hw_st] at hrun; (repeat' split at hrun) <;>
         simp_all only [hw_st, status_setStatus, reduceCtorEq, not_true_eq_false,
           Bool.not_eq_true, Bool.not_eq_false, Bool.not_eq_false', Bool.and_eq_true,
           hideWx_canRead_imp, ↓reduceIte]))
  case addSubImm | logicalImm | moveWide | bitfield | extr | logicalShift | addSubShift
     | addSubExt | addSubCarry | condCompareReg | condCompareImm | condSelect
     | dataProc1 | dataProc2 | dataProc3 =>
    dsimp only [execInst, execInstWithSvc, execAddSubImm, execLogicalImm, execMoveWide,
      execBitfield, execLogicalShift, execAddSubShift, execAddSubExt, execAddSubCarry,
      execCondCompare, execCondSelect, execDataProc1, execDataProc2, execDataProc3]
    simp only [hw_r64, hw_r32, hw_rr, hw_pc, hw_sp, hw_ps, hw_w64, hw_w32, hw_w, hw_sps, hw_adv,
      hw_ite]
    try ((repeat' split) <;> simp only [hw_w64, hw_w32, hw_w, hw_sps, hw_adv, hw_ite])
  case ldarStlr _ isLoad _ _ =>
    cases isLoad <;> close_hideWxS_mem hrun
  case ldapurStlur _ opc _ _ _ =>
    by_cases hopc : (opc == 0#2) = true <;>
      (dsimp only [execInst, execInstWithSvc] at hrun ⊢;
       simp only [hopc, Bool.false_eq_true, ↓reduceIte] at hrun ⊢;
       close_hideWxS_mem hrun)
  case simdLdSt1Single isLoad _ _ _ _ _ _ _ _ =>
    cases isLoad <;> close_hideWxS_mem hrun
  case simdLdSt1Multi isLoad _ _ _ _ _ _ _ =>
    cases isLoad <;> close_hideWxS_mem hrun
  all_goals close_hideWxS_mem hrun

private theorem execInst_stripWxS [LibsignalPlacement] {inst : Instr} (h : inst.isSvc0 = false)
    (s : State) (hrun : (execInst inst (stripWxS s)).status = .Running) :
    execInst inst (stripWxS s) = stripWxS (execInst inst s) := by
  unfold stripWxS at hrun ⊢
  rw [ProofLib.execInst_stripS h] at hrun ⊢
  rw [stripS_status] at hrun
  rw [execInst_hideWxS h s hrun]

/-! ### Cycle-Free `StepsList` & Shadow `memcpy`/`memset` Hooks -/

private inductive StepsList (P : Program) : List State → State → State → Prop where
  | refl (s : State) : StepsList P [] s s
  | step {s1 s2 sf : State} {tr : List State} :
      Step P s1 s2 → StepsList P tr s2 sf → s1 ∉ tr → StepsList P (s1 :: tr) s1 sf

private theorem stepsList_drop_until {P : Program} {tr : List State} {s2 sf : State}
    (htr : StepsList P tr s2 sf) {s1 : State} (hmem : s1 ∈ tr) :
    ∃ tr', StepsList P tr' s1 sf := by
  induction htr with
  | refl => cases hmem
  | @step a _ _ tl hab htl hnot ih =>
    rcases List.mem_cons.mp hmem with rfl | hmem_tl
    · exact ⟨s1 :: tl, .step hab htl hnot⟩
    · exact ih hmem_tl

private theorem steps_to_stepsList {P : Program} {s1 sf : State} (h : Steps P s1 sf) :
    ∃ tr, StepsList P tr s1 sf := by
  induction h with
  | refl s => exact ⟨[], .refl s⟩
  | @step a _ _ hab _ ih =>
    rcases ih with ⟨tr, htr⟩
    by_cases hmem : a ∈ tr
    · exact stepsList_drop_until htr hmem
    · exact ⟨a :: tr, .step hab htr hmem⟩

private noncomputable def findState [LibsignalPlacement] (tr0 : List State) (s' : State) :
    Option State :=
  tr0.find? fun u => Classical.propDecidable (stripWxS u = s') |>.decide

private theorem findState_eq_head [LibsignalPlacement] {seen0 tl0 : List State} {s1 : State}
    (hnone : ∀ u ∈ seen0, stripWxS u ≠ stripWxS s1) :
    findState (seen0.reverse ++ s1 :: tl0) (stripWxS s1) = some s1 := by
  unfold findState
  rw [List.find?_append]
  have h1 : (seen0.reverse.find? fun u =>
      (Classical.propDecidable (stripWxS u = stripWxS s1)).decide) = none := by
    rw [List.find?_eq_none]
    intro u hu
    have hne := hnone u (List.mem_reverse.mp hu)
    simp [hne]
  rw [h1]
  simp

private noncomputable def shadowMemcpy [LibsignalPlacement] (tr0 : List State)
    (f_mc : State → State) (s' : State) : State :=
  match findState tr0 s' with
  | none => ProofLib.hookMemcpy s'
  | some u =>
    let dst := s'.readReg64 .x0
    let src := s'.readReg64 .x1
    let len := (s'.readReg64 .x2).toNat
    @ite State (s'.status = .Running ∧ s'.spAligned = true ∧ s'.mem.RW dst len ∧
        s'.mem.Readable src len ∧ (len = 0 ∨ DisjointRegions dst len src len))
      (Classical.propDecidable _)
      (stripWxS (f_mc u))
      (s'.setStatus (.Exception "ext"))

private noncomputable def shadowMemset [LibsignalPlacement] (tr0 : List State)
    (f_ms : State → State) (s' : State) : State :=
  match findState tr0 s' with
  | none => ProofLib.hookMemset s'
  | some u =>
    let dst := s'.readReg64 .x0
    let len := (s'.readReg64 .x2).toNat
    @ite State (s'.status = .Running ∧ s'.spAligned = true ∧ s'.mem.RW dst len)
      (Classical.propDecidable _)
      (stripWxS (f_ms u))
      (s'.setStatus (.Exception "ext"))

private theorem findState_some_stripWxS [LibsignalPlacement] {tr0 : List State} {s' u : State}
    (hf : findState tr0 s' = some u) :
    stripWxS u = s' := by
  have hp := List.find?_some hf
  simpa [decide_eq_true_eq] using hp

private theorem stripWxS_mem [LibsignalPlacement] (s : State) :
    (stripWxS s).mem = stripWx s.mem := by cases s; rfl
private theorem stripWxS_symtab [LibsignalPlacement] (s : State) :
    (stripWxS s).symtab = s.symtab := by cases s; rfl
private theorem stripWxS_trace [LibsignalPlacement] (s : State) :
    (stripWxS s).trace = s.trace := by cases s; rfl
private theorem stripWxS_readReg64 [LibsignalPlacement] (s : State) (r : Reg) :
    (stripWxS s).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem stripWxS_returned [LibsignalPlacement] {s1 s2 : State} (h : Returned s1 s2) :
    Returned (stripWxS s1) (stripWxS s2) := by cases s1; cases s2; exact h
private theorem stripWxS_ccPreserved [LibsignalPlacement] {s1 s2 : State}
    (h : CallingConventionPreserved s1 s2) :
    CallingConventionPreserved (stripWxS s1) (stripWxS s2) := by cases s1; cases s2; exact h

private theorem stripWxS_applyMemcpyClobber [LibsignalPlacement] (u : State) (dst : BitVec 64)
    (bs : List (BitVec 8)) (lr : BitVec 64) (c : LibsignalBinary.Heap.MuslMemOpsRunsTo.MemcpyClobber) :
    stripWxS (applyMemcpyClobber u (u.mem.writeBytes dst bs) lr c) =
      applyMemcpyClobber (stripWxS u) ((stripWxS u).mem.writeBytes dst bs) lr c := by
  rw [stripWxS_mem, stripWx_writeBytes]
  cases u; rfl

private theorem hookExactMemcpy_shadowMemcpy [LibsignalPlacement] (tr0 : List State)
    {f_mc : State → State} (hf_exact : HookExactMemcpy f_mc) :
    HookExactMemcpy (shadowMemcpy tr0 f_mc) := by
  intro s' dst src lr len bs hrun' hsp' hx0' hx1' hx2' hlr' hread' hrw' hreadable' hdisj'
  unfold shadowMemcpy
  cases hfs : findState tr0 s' with
  | none => exact hookMemcpy_exact hrun' hsp' hx0' hx1' hx2' hlr' hread' hrw' hreadable' hdisj'
  | some u =>
    have hus : stripWxS u = s' := findState_some_stripWxS hfs
    have hcond : s'.status = .Running ∧ s'.spAligned = true ∧
        s'.mem.RW (s'.readReg64 .x0) (s'.readReg64 .x2).toNat ∧
        s'.mem.Readable (s'.readReg64 .x1) (s'.readReg64 .x2).toNat ∧
        ((s'.readReg64 .x2).toNat = 0 ∨
          DisjointRegions (s'.readReg64 .x0) (s'.readReg64 .x2).toNat
            (s'.readReg64 .x1) (s'.readReg64 .x2).toNat) := by
      rw [hx0', hx1', hx2']
      exact ⟨hrun', hsp', hrw', hreadable', hdisj'⟩
    dsimp only []
    simp only [hcond, and_self, ↓reduceIte]
    subst hus
    have hu_run : u.status = .Running := by cases u; exact hrun'
    have hu_sp : u.spAligned = true := by cases u; exact hsp'
    have hu_x0 : u.readReg64 .x0 = dst := by cases u; exact hx0'
    have hu_x1 : u.readReg64 .x1 = src := by cases u; exact hx1'
    have hu_x2 : (u.readReg64 .x2).toNat = len := by cases u; exact hx2'
    have hu_lr : u.readReg64 .lr = lr := by cases u; exact hlr'
    rw [stripWxS_mem] at hread' hrw' hreadable'
    have hu_read : u.mem.readBytes src len = bs := (stripWx_readBytes u.mem src len).symm.trans hread'
    have hu_rw : u.mem.RW dst len := (stripWx_rw_iff u.mem dst len).mp hrw'
    have hu_readable : u.mem.Readable src len := stripWx_readable_imp hreadable'
    obtain ⟨c, hc⟩ :=
      hf_exact hu_run hu_sp hu_x0 hu_x1 hu_x2 hu_lr hu_read hu_rw hu_readable hdisj'
    exact ⟨c, by rw [hc, stripWxS_applyMemcpyClobber]⟩

private theorem hookOk_shadowMemcpy [LibsignalPlacement] (tr0 : List State)
    {f_mc : State → State} (hf_exact : HookExactMemcpy f_mc) :
    HookOk (shadowMemcpy tr0 f_mc) sessionMemcpyRegionSpec := by
  have hb := hookExactMemcpy_sessionMemcpyRegionBudget_ok (hookExactMemcpy_shadowMemcpy tr0 hf_exact)
  intro x R s0 hrun hpre hsp
  have hpre_b : s0.mem ⊨
      (LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec).pre x s0 ∗
        R := hpre
  rcases hb x R s0 hrun hpre_b hsp with ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | hrest⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget.sessionMemcpyRegionBudgetSpec,
      withVmPreserved] at hpost
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    exact hpost.2
  · exact ⟨hkf, hsym, Or.inr hrest⟩

private theorem hookOk_shadowMemset_region [LibsignalPlacement] (tr0 : List State)
    {f_ms : State → State} (hf_ms_reg : HookOk f_ms sessionMemsetRegionSpec)
    (hvm_ms : ∀ s, VmPreserved s (f_ms s)) :
    HookOk (shadowMemset tr0 f_ms) sessionMemsetRegionSpec := by
  rintro ⟨dst, val, len⟩ R' s' hrun' hpre' hsp'
  unfold shadowMemset
  cases hfs : findState tr0 s' with
  | none => exact hookMemset_region_trace_ok (dst, val, len) R' s' hrun' hpre' hsp'
  | some u =>
    have hus : stripWxS u = s' := findState_some_stripWxS hfs
    have hpre_open := hpre'
    dsimp only [sessionMemsetRegionSpec, memsetRegionSpec] at hpre_open
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_open
    rcases hpre_open with ⟨⟨hx0', hx1_32', hx2', hlen⟩, hmem'⟩
    have hrw' : s'.mem.RW dst len := (IsBlock.memRegion dst len).rw hmem'
    have hcond : s'.status = .Running ∧ s'.spAligned = true ∧
        s'.mem.RW (s'.readReg64 .x0) (s'.readReg64 .x2).toNat := by
      rw [hx0', hx2']; exact ⟨hrun', hsp', hrw'⟩
    dsimp only []
    simp only [hcond, and_self, ↓reduceIte]
    subst hus
    have hu_run : u.status = .Running := by cases u; exact hrun'
    have hu_x0 : u.readReg64 .x0 = dst := by cases u; exact hx0'
    have hu_x1 : (u.readReg64 .x1).truncate 8 = val := by
      have h32 : (u.readReg32 .x1).truncate 8 = val := by cases u; exact hx1_32'
      rwa [State.readReg32, truncate8_truncate32] at h32
    have hu_x2 : (u.readReg64 .x2).toNat = len := by cases u; exact hx2'
    have hu_sp_al : (u.sp &&& 15#64) = 0#64 := by
      have hsp_u : u.spAligned = true := by cases u; exact hsp'
      simpa [State.spAligned] using hsp_u
    rw [stripWxS_mem] at hrw' hmem'
    have hu_rw : u.mem.RW dst len := (stripWx_rw_iff u.mem dst len).mp hrw'
    obtain ⟨hkf_u, hsym_u, hret_u, hcc_u, hx0_ret, htr_u, hread_u, hs2_u, _⟩ :=
      hookOk_sessionMemsetRegion_elim hf_ms_reg hu_run hu_x0 hu_x1 hu_x2 hu_sp_al hu_rw
    have hperm_u : ∀ a, (f_ms u).mem.perm a = u.mem.perm a := (hvm_ms u).perm_eq
    have hkf' : (stripWxS u).mem.KeepsFrozen (stripWxS (f_ms u)).mem := by
      rw [stripWxS_mem, stripWxS_mem]; exact stripWx_keepsFrozen hkf_u
    have hsym' : (stripWxS (f_ms u)).symtab = (stripWxS u).symtab := by
      rw [stripWxS_symtab, stripWxS_symtab]; exact hsym_u
    refine ⟨hkf', hsym', Or.inl ⟨stripWxS_returned hret_u, stripWxS_ccPreserved hcc_u, ?_⟩⟩
    dsimp only [sessionMemsetRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨by rw [stripWxS_readReg64]; exact hx0_ret,
      by rw [stripWxS_trace, stripWxS_trace]; exact htr_u⟩, ?_⟩
    rw [stripWxS_mem]
    let h_pts : Heap := regionHeap dst len (stripWx (f_ms u).mem)
    have hrep_len : (List.replicate len val).length = len := List.length_replicate
    have hb_post := IsBlock.pointsToBytes_len (a := dst) hrep_len
    have hp_pts : (dst ↦ₛ List.replicate len val) h_pts :=
      (hb_post.iff h_pts).mpr ⟨stripWx (f_ms u).mem,
        ⟨by rw [hrep_len]; exact hlen,
         by rw [hrep_len, stripWx_readBytes]; exact hread_u⟩, rfl⟩
    have hrw_f_swx : (stripWx (f_ms u).mem).RW dst len :=
      (stripWx_rw_iff (f_ms u).mem dst len).mpr fun a ha => hs2_u.2.1.1.1 a (hu_rw a ha)
    have hm_pts_swx : h_pts.Matches (stripWx (f_ms u).mem) :=
      IsBlock.regionHeap_matches dst len (stripWx (f_ms u).mem) hrw_f_swx
    obtain ⟨h_reg, h_R', hdisj', hp_reg, hp_R', hm_both'⟩ := Satisfies.sepConj_elim hmem'
    have hm_R' : h_R'.Matches (stripWx u.mem) := Heap.Matches.of_union_right hdisj' hm_both'
    obtain ⟨m_r, _, h_reg_eq⟩ := ((IsBlock.memRegion dst len).iff h_reg).mp hp_reg
    have hdisj_new : h_pts.Disjoint h_R' := by
      unfold Heap.Disjoint at hdisj' ⊢
      refine ⟨fun a => ?_,
        fun _ _ => Or.inl (by simp [h_pts, regionHeap]),
        fun _ _ => Or.inl (by simp [h_pts, regionHeap]),
        (fun _ _ _ _ h => by rcases h with ⟨h0, _⟩ | ⟨_, h0⟩ <;> simp [h_pts, regionHeap] at h0),
        fun _ => Or.inl (by simp [h_pts, regionHeap])⟩
      by_cases hin : InRegion dst len a
      · have hr_some : h_reg.phys a = some (.rw (m_r.read8 a)) := by
          rw [h_reg_eq]; simp [regionHeap, hin]
        rcases hdisj'.1 a with h1 | h2 | ⟨_, h3, _⟩
        · rw [hr_some] at h1; cases h1
        · exact Or.inr (Or.inl h2)
        · rw [hr_some] at h3; cases h3
      · exact Or.inl (by dsimp [h_pts]; simp [regionHeap, hin])
    have hm_R'_swx : h_R'.Matches (stripWx (f_ms u).mem) := by
      unfold Heap.Disjoint at hdisj'
      unfold Heap.Matches at hm_R' ⊢
      rcases hs2_u with ⟨hs2_rd, ⟨⟨_, _⟩, ⟨hs2_anon, hs2_pn⟩⟩, hs2_r⟩
      have hperm_swx : ∀ a, (stripWx (f_ms u).mem).perm a = (stripWx u.mem).perm a :=
        fun a => stripWx_perm_congr (hperm_u a)
      refine ⟨fun a c hc => ?_, hm_R'.2.1, fun a hma => ?_⟩
      · have hout : OutsideRegion dst len a := by
          by_cases hin : InRegion dst len a
          · have hr_some : h_reg.phys a = some (.rw (m_r.read8 a)) := by
              rw [h_reg_eq]; simp [regionHeap, hin]
            rcases hdisj'.1 a with h1 | h2 | ⟨_, h3, _⟩
            · rw [hr_some] at h1; cases h1
            · rw [hc] at h2; cases h2
            · rw [hr_some] at h3; cases h3
          · exact (outsideRegion_iff_not_inRegion dst len a).mpr hin
        have hout_l : ∀ r ∈ [(dst, len)], OutsideRegion r.1 r.2 a := by
          intro r hr_m; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr_m
          subst hr_m; exact hout
        have hcell := hm_R'.1 a c hc
        cases c with
        | rw b =>
          have hp_sw : (stripWx u.mem).permNoLazy a = some Perm.rw :=
            Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hcell.2.1, hcell.2.2⟩
          obtain ⟨hpu, hlfu⟩ :=
            Memory.permNoLazy_eq_some_rw_iff.mp ((stripWx_permNoLazy_rw_iff u.mem a).mp hp_sw)
          have hru : (u.mem.perm a).r = true := by rw [hpu]; rfl
          have hrd' : (f_ms u).mem.read8 a = u.mem.read8 a := hs2_rd a hru hlfu hout_l
          have hlf' : (f_ms u).mem.isLazyFree a = false := (hs2_r a hru hlfu).2
          have hpu' : (f_ms u).mem.perm a = some Perm.rw := (hperm_u a).trans hpu
          obtain ⟨hp_f, hlf_f⟩ := Memory.permNoLazy_eq_some_rw_iff.mp
            ((stripWx_permNoLazy_rw_iff (f_ms u).mem a).mpr
              (Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hpu', hlf'⟩))
          exact ⟨(stripWx_read8 _ a).trans (hrd'.trans ((stripWx_read8 u.mem a).symm.trans hcell.1)),
            hp_f, hlf_f⟩
        | ro b =>
          have hmap_sw : ((stripWx u.mem).perm a).mapped = true := by
            cases hpx : (stripWx u.mem).perm a with
            | none => rw [hpx] at hcell; cases hcell.2.1
            | some _ => rfl
          obtain ⟨_, hlf_eq, _⟩ := stripWx_mapped_props hmap_sw
          have hlfu : u.mem.isLazyFree a = false := hlf_eq.symm.trans hcell.2.2
          have hru : (u.mem.perm a).r = true := by
            have h1 := hcell.2.1
            unfold stripWx at h1
            rw [(ProofLib.strip_perm_props keepLs (hideWx u.mem) a).1, hideWx_perm] at h1
            revert h1
            rcases u.mem.perm a with _ | ⟨r, w, x, _, _⟩ <;> intro h1
            · cases h1
            · cases r <;> cases w <;> cases x <;> simp [Perm.protNone, Option.r] at h1 ⊢
          have hrd' : (f_ms u).mem.read8 a = u.mem.read8 a := hs2_rd a hru hlfu hout_l
          have hlf' : (f_ms u).mem.isLazyFree a = false := (hs2_r a hru hlfu).2
          have hmap_sw' : ((stripWx (f_ms u).mem).perm a).mapped = true := by
            rw [hperm_swx a]; exact hmap_sw
          obtain ⟨_, hlf_eq', _⟩ := stripWx_mapped_props hmap_sw'
          exact ⟨(stripWx_read8 _ a).trans (hrd'.trans ((stripWx_read8 u.mem a).symm.trans hcell.1)),
            by rw [hperm_swx a]; exact hcell.2.1, hlf_eq'.trans hlf'⟩
        | protNone b =>
          have hmap_sw : ((stripWx u.mem).perm a).mapped = true := by rw [hcell.2.1]; rfl
          obtain ⟨_, hlf_eq, _⟩ := stripWx_mapped_props hmap_sw
          have hlfu : u.mem.isLazyFree a = false := hlf_eq.symm.trans hcell.2.2
          have hmap_sw' : ((stripWx (f_ms u).mem).perm a).mapped = true := by
            rw [hperm_swx a]; exact hmap_sw
          obtain ⟨_, hlf_eq', _⟩ := stripWx_mapped_props hmap_sw'
          have ⟨hrd', hlf'⟩ :
              (f_ms u).mem.read8 a = u.mem.read8 a ∧ (f_ms u).mem.isLazyFree a = false := by
            have hpn_sw := hcell.2.1
            unfold stripWx at hpn_sw
            rw [ProofLib.strip_perm, hideWx_perm] at hpn_sw
            cases hpu : u.mem.perm a with
            | none => rw [hpu] at hpn_sw; cases hpn_sw
            | some p =>
              have ⟨hlf_p, han_p⟩ : p.lazyFree = false ∧ p.anon = true := by
                have hpu0 := hpu
                dsimp only [Memory.perm, Perm.rwx] at hpu0
                revert hpu0
                rcases u.mem.cells a with _ | ⟨_ | _, _⟩ <;> intro hpu0 <;> simp at hpu0
                subst hpu0; exact ⟨rfl, rfl⟩
              rw [hpu] at hpn_sw
              rcases p with ⟨r, w, x, lf, an⟩
              dsimp only at hlf_p han_p; subst hlf_p han_p
              cases r <;> cases w <;> cases x
              · exact (hs2_pn a hpu hout_l).2 hlfu
              · have hfz_u : u.mem.Frozen a := by unfold Memory.Frozen; rw [hpu]; rfl
                obtain ⟨hrd0, _, hlf0, _⟩ := hkf_u a hfz_u
                exact ⟨hrd0, hlf0.trans hlfu⟩
              · generalize keepLs a = ic at hpn_sw
                cases ic <;> simp [ProofLib.stripPerm, Perm.protNone] at hpn_sw
              · simp at hpn_sw
              · generalize keepLs a = ic at hpn_sw
                cases ic <;> simp [ProofLib.stripPerm, Perm.protNone] at hpn_sw
              · generalize keepLs a = ic at hpn_sw
                cases ic <;> simp [ProofLib.stripPerm, Perm.protNone] at hpn_sw
              · generalize keepLs a = ic at hpn_sw
                cases ic <;> simp [ProofLib.stripPerm, Perm.protNone] at hpn_sw
              · have hru : (u.mem.perm a).r = true := by rw [hpu]
                exact ⟨hs2_rd a hru hlfu hout_l, (hs2_r a hru hlfu).2⟩
          exact ⟨(stripWx_read8 _ a).trans (hrd'.trans ((stripWx_read8 u.mem a).symm.trans hcell.1)),
            (hperm_swx a).trans hcell.2.1, hlf_eq'.trans hlf'⟩
        | lazy => rw [hperm_swx a]; exact hcell
        | protNoneLazy => rw [hperm_swx a]; exact hcell
      · have hm0 := hm_R'.2.2 a hma
        obtain ⟨hmap_u, _, han_eq⟩ := stripWx_mapped_props hm0.1
        have han_u' : (f_ms u).mem.isAnon a = true := (hs2_anon a ⟨hmap_u, han_eq.symm.trans hm0.2⟩).2
        have hmap_swx' : ((stripWx (f_ms u).mem).perm a).mapped = true := by
          rw [hperm_swx a]; exact hm0.1
        obtain ⟨_, _, han_eq'⟩ := stripWx_mapped_props hmap_swx'
        exact ⟨hmap_swx', han_eq'.trans han_u'⟩
    exact ProofLib.Satisfies.sepConj_intro hdisj_new hp_pts hp_R'
      (Heap.Matches.union hm_pts_swx hm_R'_swx)

private theorem hookOk_shadowMemset [LibsignalPlacement] (tr0 : List State)
    {f_ms : State → State} (hf_ms_reg : HookOk f_ms sessionMemsetRegionSpec)
    (hvm_ms : ∀ s, VmPreserved s (f_ms s)) (stk : Nat) :
    HookOk (shadowMemset tr0 f_ms) (sessionMemsetSpec stk) := by
  have hreg := hookOk_shadowMemset_region tr0 hf_ms_reg hvm_ms
  rintro ⟨ptr, c, len⟩ R s0 hrun hpre hsp
  dsimp only [sessionMemsetSpec, libcMemsetSpec] at hpre
  rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2⟩, hmem⟩
  have hlen : len ≤ 2 ^ 64 := hx2 ▸ Nat.le_of_lt (s0.readReg64 .x2).isLt
  have hpre_r : s0.mem ⊨ sessionMemsetRegionSpec.pre (ptr, c, len) s0 ∗ (stackAt s0.sp stk ∗ R) := by
    dsimp only [sessionMemsetRegionSpec, memsetRegionSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2, hlen⟩, by simpa only [sepConj_assoc] using hmem⟩
  rcases hreg (ptr, c, len) (stackAt s0.sp stk ∗ R) s0 hrun hpre_r hsp with
    ⟨hkf, hsym, ⟨hret, hcc, hpost⟩ | ⟨h1, hp⟩ | ⟨h1, h2, he⟩ | ⟨h1, ho⟩⟩
  · refine ⟨hkf, hsym, Or.inl ⟨hret, hcc, ?_⟩⟩
    dsimp only [sessionMemsetRegionSpec] at hpost
    dsimp only [sessionMemsetSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hpost.1, by simpa only [sepConj_assoc] using hpost.2⟩
  · exact False.elim (not_satisfies_false_sepConj hp)
  · exact False.elim (not_satisfies_false_sepConj he)
  · exact False.elim (not_satisfies_false_sepConj ho)

private noncomputable def shadowVsigHooks [LibsignalPlacement] (tr0 : List State)
    (H : LibsignalHooks) (n : String) : Option (State → State) :=
  if n == lsMemcpySym then (H n).map (shadowMemcpy tr0)
  else if n == lsVerifyMemsetSym then (H n).map (shadowMemset tr0)
  else vsigOnlyHooks H n

private theorem shadowVsigHooks_memcpy [LibsignalPlacement] (tr0 : List State)
    (H : LibsignalHooks) :
    shadowVsigHooks tr0 H lsMemcpySym = (H lsMemcpySym).map (shadowMemcpy tr0) := by
  simp [shadowVsigHooks]

private theorem shadowVsigHooks_memset [LibsignalPlacement] (tr0 : List State)
    (H : LibsignalHooks) :
    shadowVsigHooks tr0 H lsVerifyMemsetSym = (H lsVerifyMemsetSym).map (shadowMemset tr0) := by
  have h1 : (lsVerifyMemsetSym == lsMemcpySym) = false := by decide
  simp [shadowVsigHooks, h1]

private theorem shadowVsigHooks_other [LibsignalPlacement] (tr0 : List State)
    (H : LibsignalHooks) {n : String}
    (h1 : (n == lsMemcpySym) = false := by decide)
    (h2 : (n == lsVerifyMemsetSym) = false := by decide) :
    shadowVsigHooks tr0 H n = vsigOnlyHooks H n := by
  simp [shadowVsigHooks, h1, h2]

private theorem w3VerifySigHooks_shadow [LibsignalPlacement] (tr0 : List State)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) (Y : UnreachedPqxdhPrimitives) :
    VerifySignaturePlacedHooks (modelPrims Y ⟨W.C, W.Q⟩)
      (shadowVsigHooks tr0 (cliGhostExterns gh (cliExternsPlaced mmpl W))) := by
  have hv := w3VerifySigHooks_vsigOnly mmpl gh W hG Y
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  refine
    { memcpy := ?_
      memset := ?_
      blackBox := (shadowVsigHooks_other tr0 H).trans hv.blackBox
      montToEd := hookSat_of_eq (shadowVsigHooks_other tr0 H) hv.montToEd
      compress := hookSat_of_eq (shadowVsigHooks_other tr0 H) hv.compress
      edNeg := hookSat_of_eq (shadowVsigHooks_other tr0 H) hv.edNeg
      sha512Compress := hookSat_of_eq (shadowVsigHooks_other tr0 H) hv.sha512Compress
      scalarWide := hookSat_of_eq (shadowVsigHooks_other tr0 H) hv.scalarWide
      scalarMod := hookSat_of_eq (shadowVsigHooks_other tr0 H) hv.scalarMod
      doubleMul := hookSat_of_eq (shadowVsigHooks_other tr0 H) hv.doubleMul }
  · obtain ⟨f, hf, _, _, _, _, _, _, _, _, _⟩ := hG.memcpy
    have hH : H lsMemcpySym = some f := cliGhostExterns_memcpy_some gh (cliExternsPlaced mmpl W) hf
    exact ⟨shadowMemcpy tr0 f, by rw [shadowVsigHooks_memcpy (H := H), hH]; rfl,
      hookOk_shadowMemcpy tr0 (hG.memcpy_exact f hf)⟩
  · obtain ⟨f, hf, _, _, _, hreg, hvm, _, _⟩ := hG.memset
    have hH : H lsVerifyMemsetSym = some f :=
      cliGhostExterns_memset_some gh (cliExternsPlaced mmpl W) hf
    exact ⟨shadowMemset tr0 f, by rw [shadowVsigHooks_memset (H := H), hH]; rfl,
      hookOk_shadowMemset tr0 hreg hvm pqxdhHookStack⟩

/-! ### `isAnon` Preservation & Shadow Lockstep -/

private def AnonMono (m1 m2 : Memory) : Prop :=
  ∀ a, (m1.perm a).mapped = true → m1.isAnon a = true → m2.isAnon a = true

private theorem AnonMono.refl (m : Memory) : AnonMono m m := fun _ _ h => h

private theorem AnonMono.trans {m1 m2 m3 : Memory} (h12 : AnonMono m1 m2) (h23 : AnonMono m2 m3)
    (hp12 : ∀ a, m2.perm a = m1.perm a) : AnonMono m1 m3 :=
  fun a hm ha => h23 a (by rw [hp12 a]; exact hm) (h12 a hm ha)

private theorem write8_isAnon_fn (m : Memory) (a : BitVec 64) (v : BitVec 8) :
    (m.write8 a v).isAnon = m.isAnon := funext (write8_isAnon m a v)
private theorem write16_isAnon_fn (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (m.write16 a v).isAnon = m.isAnon := by simp only [Memory.write16, write8_isAnon_fn]
private theorem write32_isAnon_fn (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (m.write32 a v).isAnon = m.isAnon := by simp only [Memory.write32, write8_isAnon_fn]
private theorem write64_isAnon_fn (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (m.write64 a v).isAnon = m.isAnon := by simp only [Memory.write64, write8_isAnon_fn]
private theorem writeSized_isAnon_fn (m : Memory) (sz : MemWidth) (a : BitVec 64) (v : BitVec 64) :
    (m.writeSized sz a v).isAnon = m.isAnon := by
  cases sz <;> simp only [Memory.writeSized, write8_isAnon_fn, write16_isAnon_fn,
    write32_isAnon_fn, write64_isAnon_fn]
private theorem writeSimdSized_isAnon_fn (m : Memory) (sz : SimdMemSize) (a : BitVec 64)
    (v : BitVec 128) : (m.writeSimdSized sz a v).isAnon = m.isAnon := by
  cases sz <;> simp only [Memory.writeSimdSized, Memory.write128, write8_isAnon_fn,
    write16_isAnon_fn, write32_isAnon_fn, write64_isAnon_fn]
private theorem simdStoreRegs_isAnon_fn (sz : SimdMemSize) (vfn : BitVec 5 → BitVec 128) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (m : Memory),
      (simdStoreRegs sz vfn n vt ea m).isAnon = m.isAnon
  | 0, _, _, _ => rfl
  | n + 1, _, _, m => by
    simp only [simdStoreRegs, simdStoreRegs_isAnon_fn sz vfn n, writeSimdSized_isAnon_fn]

private def ia (s : State) : BitVec 64 → Bool := s.mem.isAnon
private theorem ia_adv (s : State) : ia s.advancePC = ia s := by cases s; rfl
private theorem ia_spc (s : State) (q : BitVec 64) : ia (s.setPC q) = ia s := by cases s; rfl
private theorem ia_w64 (s : State) (r : Reg) (v : BitVec 64) : ia (s.writeReg64 r v) = ia s := by
  cases s; cases r <;> rfl
private theorem ia_w32 (s : State) (r : Reg) (v : BitVec 32) : ia (s.writeReg32 r v) = ia s :=
  ia_w64 s r _
private theorem ia_w (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    ia (s.writeReg w r v) = ia s := ia_w64 s r _
private theorem ia_wv128 (s : State) (r : BitVec 5) (v : BitVec 128) :
    ia (s.writeVReg128 r v) = ia s := by cases s; rfl
private theorem ia_wv64 (s : State) (r : BitVec 5) (v : BitVec 64) :
    ia (s.writeVReg64 r v) = ia s := ia_wv128 s r _
private theorem ia_wv32 (s : State) (r : BitVec 5) (v : BitVec 32) :
    ia (s.writeVReg32 r v) = ia s := ia_wv128 s r _
private theorem ia_sps (s : State) (q : PState) : ia (s.setPState q) = ia s := by cases s; rfl
private theorem ia_sfp (s : State) (f : BitVec 32) : ia (s.setFpsr f) = ia s := by cases s; rfl
private theorem ia_sofp (s : State) (f : BitVec 32) : ia (s.orFpsr f) = ia s := by cases s; rfl
private theorem ia_sst (s : State) (st : ExecStatus) : ia (s.setStatus st) = ia s := by cases s; rfl
private theorem ia_wst (s : State) (st : ExecStatus) : ia { s with status := st } = ia s := by
  cases s; rfl
private theorem ia_stp (s : State) (v : BitVec 64) : ia (setTpidrEl0 s v) = ia s := by cases s; rfl
private theorem ia_sex (s : State) : ia s.stepExclOracle = ia s := by cases s; rfl
private theorem ia_smem (s : State) (m : Memory) : ia (s.setMem m) = m.isAnon := by cases s; rfl
private theorem ia_as (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    ia (applySimdResult s rd r) = ia s := by cases s; cases r <;> rfl
private theorem ia_ass (s : State) (rd : BitVec 5) (r : Except String (BitVec 128))
    (sat : Option (BitVec 32)) : ia (applySimdSatResult s rd r sat) = ia s := by
  cases s; cases r <;> cases sat <;> rfl
private theorem ia_slr (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      ia (simdLoadRegs sz m n vt ea s) = ia s
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => by simp only [simdLoadRegs, ia_slr sz m n, ia_wv128]
private theorem ia_mk {rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma} :
    ia (State.mk rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma) = m.isAnon := rfl
private theorem ia_mem (s : State) : s.mem.isAnon = ia s := rfl

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
private theorem execInst_isAnon_of_not_isSvc0 {inst : Instr} (h : inst.isSvc0 = false)
    (s : State) : (execInst inst s).mem.isAnon = s.mem.isAnon := by
  change ia (execInst inst s) = ia s
  cases inst
  case system isHalt imm =>
    cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc]; simp [himm, ia_sst]
    · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, ia_sst]
  all_goals clear h
  case extr w rd rn rm lsb =>
    cases w <;> dsimp only [execInst, execInstWithSvc] <;> simp only [ia_adv, ia_w]
  case sysReg isRead sr rt =>
    cases isRead
    · by_cases hsr : sr == 0x5e82#15
      · simp only [execInst, execInstWithSvc, sysregTpidrEl0, hsr, Bool.false_eq_true, ↓reduceIte,
          ia_adv, ia_stp, ia_mk, ia_mem]
      · dsimp only [execInst, execInstWithSvc, sysregTpidrEl0]
        simp only [hsr, Bool.false_eq_true, ↓reduceIte, ia_adv, ia_w64, ia_sps, ia_sfp, ia_wst,
          ia_mk, ia_mem, apply_ite ia, ite_self]
    · dsimp only [execInst, execInstWithSvc]
      simp only [↓reduceIte, ia_adv, ia_w64, ia_sps, ia_sfp, ia_wst, ia_mk, ia_mem,
        apply_ite ia, ite_self]
  case simdThreeSame q u size rm opcode rn rd =>
    by_cases hop : opcode == 0b00011#5
    · have hsz : size = 0#2 ∨ size = 1#2 ∨ size = 2#2 ∨ size = 3#2 := by revert size; decide
      rcases hsz with rfl | rfl | rfl | rfl <;> cases u <;>
        (dsimp only [execInst, execInstWithSvc]; simp only [hop, ↓reduceIte];
         split <;> simp only [ia_wv128, ia_adv, ia_ass])
    · dsimp only [execInst, execInstWithSvc]
      simp only [hop, Bool.false_eq_true, ↓reduceIte, ia_adv, ia_wv128, ia_sst, ia_wst, ia_as,
        ia_ass, ia_mk, ia_mem, apply_ite ia, ite_self]
  case ldr _ _ _ _ addr | str _ _ addr | ldp _ _ _ _ addr | stp _ _ _ addr
     | ldpSimd _ _ _ addr | stpSimd _ _ _ addr | ldrSimd _ _ addr | strSimd _ _ addr =>
    dsimp only [execInst, execInstWithSvc, execLdr, execStr, execLdp, execStp]
    rcases hea : evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp only [hea, ia_w64, ia_w, ia_wv128, ia_smem, ia_adv, ia_sst, writeSized_isAnon_fn,
        writeSimdSized_isAnon_fn, ia_mem, apply_ite ia, apply_ite Memory.isAnon, ite_self]
  case addSubImm | logicalImm | moveWide | bitfield | logicalShift | addSubShift
     | addSubExt | addSubCarry | condCompareReg | condCompareImm | condSelect
     | dataProc1 | dataProc2 | dataProc3 =>
    dsimp only [execInst, execInstWithSvc, execAddSubImm, execLogicalImm, execMoveWide,
      execBitfield, execLogicalShift, execAddSubShift, execAddSubExt, execAddSubCarry,
      execCondCompare, execCondSelect, execDataProc1, execDataProc2, execDataProc3]
    simp only [ia_adv, ia_w64, ia_w32, ia_w, ia_sps, ia_sst, ia_wst, ia_mk, ia_mem,
      apply_ite ia, ite_self]
    try ((repeat' split) <;> simp only [ia_adv, ia_w64, ia_w32, ia_w, ia_sps, ia_sst, ia_wst,
      ia_mk, ia_mem, apply_ite ia, ite_self])
  all_goals
    dsimp only [execInst, execInstWithSvc, execLdrLit, execLdp, execStp, evalAddrMode]
    simp only [ia_adv, ia_spc, ia_w64, ia_w32, ia_w, ia_wv128, ia_wv64, ia_wv32, ia_sps, ia_sfp,
      ia_sofp, ia_sst, ia_wst, ia_stp, ia_sex, ia_smem, ia_as, ia_ass, ia_slr, ia_mk, ia_mem,
      write8_isAnon_fn, write16_isAnon_fn, write32_isAnon_fn, write64_isAnon_fn,
      writeSized_isAnon_fn, writeSimdSized_isAnon_fn, simdStoreRegs_isAnon_fn,
      apply_ite ia, apply_ite Prod.fst, apply_ite Memory.isAnon, ite_self]

private theorem hook_writeBytes_reg_stripWx_vm [LibsignalPlacement] (r : Reg) (s : State)
    (bs : List (BitVec 8)) :
    returnToLinkRegister ((stripWxS s).setMem
        ((stripWxS s).mem.writeBytes ((stripWxS s).readReg64 r) bs)) =
      stripWxS (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 r) bs))) ∧
    VmPreserved s (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 r) bs))) ∧
    AnonMono s.mem (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 r) bs))).mem := by
  refine ⟨?_, ?_, fun a _ ha => (writeBytes_isAnon bs s.mem (s.readReg64 r) a).trans ha⟩
  · have hm : (stripWxS s).mem = stripWx s.mem := by cases s; rfl
    have hr : (stripWxS s).readReg64 r = s.readReg64 r := by cases s; rfl
    rw [hm, hr, stripWx_writeBytes]; cases s; rfl
  · unfold returnToLinkRegister
    exact ⟨⟨rfl, rfl, rfl⟩, rfl, writeBytes_perm_eq _ _ _, fun _ _ _ => rfl⟩

private theorem shadowVsigHooks_findSome?_active [LibsignalPlacement] (tr0 : List State)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh) :
    let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
    ∀ (l : List (String × Nat)) {off : Nat} {f' : State → State},
      (l.findSome? fun (n, o) => if o == off then shadowVsigHooks tr0 H n else none) = some f' →
      ∀ s : State,
        findState tr0 (stripWxS s) = some s →
        (f' (stripWxS s)).status = .Running →
        ∃ f : State → State,
          (l.findSome? fun (n, o) => if o == off then vsigOnlyHooks H n else none) = some f ∧
          (l.findSome? fun (n, o) => if o == off then H n else none) = some f ∧
          f' (stripWxS s) = stripWxS (f s) ∧
          VmPreserved s (f s) ∧
          AnonMono s.mem (f s).mem := by
  intro H l
  induction l with
  | nil => intro _ _ h; simp at h
  | cons hd tl ih =>
    rcases hd with ⟨n, o⟩
    intro off f' h
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      by_cases hn : vsigKeepSym n = true
      · intro s hfs hrun
        have hk_v : vsigOnlyHooks H n = H n := by simp [vsigOnlyHooks, hn]
        rw [hk_v]
        unfold vsigKeepSym at hn
        simp only [Bool.or_eq_true, beq_iff_eq] at hn
        rcases hn with ((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
        · -- lsMemcpySym
          obtain ⟨f, hf, _, _, _, _, _, _, _, _, _⟩ := hG.memcpy
          have hH : H lsMemcpySym = some f :=
            cliGhostExterns_memcpy_some gh (cliExternsPlaced mmpl W) hf
          have hsh : shadowVsigHooks tr0 H lsMemcpySym = some (shadowMemcpy tr0 f) := by
            rw [shadowVsigHooks_memcpy, hH]; rfl
          rw [hsh] at h; injection h with hf'; subst hf'
          unfold shadowMemcpy at hrun ⊢
          rw [hfs] at hrun ⊢; dsimp only [] at hrun ⊢
          by_cases hcond : (stripWxS s).status = .Running ∧ (stripWxS s).spAligned = true ∧
              (stripWxS s).mem.RW ((stripWxS s).readReg64 .x0) ((stripWxS s).readReg64 .x2).toNat ∧
              (stripWxS s).mem.Readable ((stripWxS s).readReg64 .x1)
                ((stripWxS s).readReg64 .x2).toNat ∧
              (((stripWxS s).readReg64 .x2).toNat = 0 ∨
                DisjointRegions ((stripWxS s).readReg64 .x0) ((stripWxS s).readReg64 .x2).toNat
                  ((stripWxS s).readReg64 .x1) ((stripWxS s).readReg64 .x2).toNat)
          · simp only [hcond, and_self, ↓reduceIte]
            rcases hcond with ⟨hr_s', hsp_s', hrw_s', hrd_s', hdisj_s'⟩
            have hu_run : s.status = .Running := by cases s; exact hr_s'
            have hu_sp : s.spAligned = true := by cases s; exact hsp_s'
            rw [stripWxS_mem, stripWxS_readReg64, stripWxS_readReg64] at hrw_s'
            rw [stripWxS_mem, stripWxS_readReg64, stripWxS_readReg64] at hrd_s'
            rw [stripWxS_readReg64, stripWxS_readReg64, stripWxS_readReg64] at hdisj_s'
            have hu_rw : s.mem.RW (s.readReg64 .x0) (s.readReg64 .x2).toNat :=
              (stripWx_rw_iff s.mem _ _).mp hrw_s'
            have hu_rd : s.mem.Readable (s.readReg64 .x1) (s.readReg64 .x2).toNat :=
              stripWx_readable_imp hrd_s'
            have hex : HookExactMemcpy f := hG.memcpy_exact f hf
            have hvm : VmPreserved s (f s) :=
              (hookExactMemcpy_vmPreserved hex hu_run hu_sp rfl rfl rfl rfl hu_rw hu_rd hdisj_s').1
            obtain ⟨c, hc⟩ := hex hu_run hu_sp rfl rfl rfl rfl rfl hu_rw hu_rd hdisj_s'
            have han : AnonMono s.mem (f s).mem := by
              rw [hc]; intro a _ ha
              exact (writeBytes_isAnon _ s.mem _ a).trans ha
            rw [hH]; exact ⟨f, rfl, rfl, rfl, hvm, han⟩
          · simp only [hcond, ↓reduceIte, status_setStatus] at hrun; cases hrun
        · -- lsVerifyMemsetSym
          obtain ⟨f, hf, _, _, _, hreg, hvm_ms, _, _⟩ := hG.memset
          have hH : H lsVerifyMemsetSym = some f :=
            cliGhostExterns_memset_some gh (cliExternsPlaced mmpl W) hf
          have hsh : shadowVsigHooks tr0 H lsVerifyMemsetSym = some (shadowMemset tr0 f) := by
            rw [shadowVsigHooks_memset, hH]; rfl
          rw [hsh] at h; injection h with hf'; subst hf'
          unfold shadowMemset at hrun ⊢
          rw [hfs] at hrun ⊢; dsimp only [] at hrun ⊢
          by_cases hcond : (stripWxS s).status = .Running ∧ (stripWxS s).spAligned = true ∧
              (stripWxS s).mem.RW ((stripWxS s).readReg64 .x0) ((stripWxS s).readReg64 .x2).toNat
          · simp only [hcond, and_self, ↓reduceIte]
            rcases hcond with ⟨hr_s', hsp_s', hrw_s'⟩
            have hu_run : s.status = .Running := by cases s; exact hr_s'
            have hu_sp_al : (s.sp &&& 15#64) = 0#64 := by
              have hsp_u : s.spAligned = true := by cases s; exact hsp_s'
              simpa [State.spAligned] using hsp_u
            rw [stripWxS_mem, stripWxS_readReg64, stripWxS_readReg64] at hrw_s'
            have hu_rw : s.mem.RW (s.readReg64 .x0) (s.readReg64 .x2).toNat :=
              (stripWx_rw_iff s.mem _ _).mp hrw_s'
            obtain ⟨_, _, _, _, _, _, _, hs2, _⟩ :=
              hookOk_sessionMemsetRegion_elim hreg hu_run rfl rfl rfl hu_sp_al hu_rw
            rw [hH]
            exact ⟨f, rfl, rfl, rfl, hvm_ms s, fun a hm ha => (hs2.2.1.2.1 a ⟨hm, ha⟩).2⟩
          · simp only [hcond, ↓reduceIte, status_setStatus] at hrun; cases hrun
        · -- lsBlackBoxU8Sym
          have hrow : H lsBlackBoxU8Sym = some blackBoxHook :=
            cliGhost_row mmpl gh W (blackBox_row_placed mmpl W)
          have hsh : shadowVsigHooks tr0 H lsBlackBoxU8Sym = some blackBoxHook :=
            (shadowVsigHooks_other tr0 H).trans (hk_v.trans hrow)
          rw [hsh] at h; injection h with hf'; subst hf'
          rw [hrow]; refine ⟨blackBoxHook, rfl, rfl, by cases s; rfl, ?_, fun _ _ ha => ha⟩
          unfold blackBoxHook
          exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun _ => rfl, fun _ _ _ => rfl⟩
        · -- lsVerifyMontToEdSym
          have hrow : H lsVerifyMontToEdSym = some (toEdwardsHook W.Q.montToEd) :=
            cliGhost_row mmpl gh W (toEdwards_row_placed mmpl W)
          have hsh : shadowVsigHooks tr0 H lsVerifyMontToEdSym =
              some (toEdwardsHook W.Q.montToEd) :=
            (shadowVsigHooks_other tr0 H).trans (hk_v.trans hrow)
          rw [hsh] at h; injection h with hf'; subst hf'
          rw [hrow]; refine ⟨toEdwardsHook W.Q.montToEd, rfl, rfl, ?_⟩
          unfold toEdwardsHook; dsimp only []
          rw [stripWxS_readReg64, stripWxS_readReg64, stripWxS_mem, stripWx_readVecN]
          cases W.Q.montToEd (readVecN s.mem (s.readReg64 .x0) 32)
              ((s.readReg64 .x1).setWidth 8 &&& 1#8) with
          | none =>
            refine ⟨?_, ?_, fun a _ ha => by
              dsimp only [returnToLinkRegister, State.setPC, State.setMem]
              exact congrFun (write64_isAnon_fn s.mem _ _) a |>.trans ha⟩
            · cases s; dsimp only [stripWxS, hideWxS, ProofLib.stripS, returnToLinkRegister,
                State.setMem, State.setPC, State.readReg64]; rw [stripWx_write64]; rfl
            · unfold returnToLinkRegister
              exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun a =>
                congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_write64_norm _ _ _) a,
                fun _ _ _ => rfl⟩
          | some p =>
            refine ⟨?_, ?_, fun a _ ha => by
              dsimp only [returnToLinkRegister, State.setPC, State.setMem]
              exact (writeBytes_isAnon _ _ _ a).trans
                (congrFun (write64_isAnon_fn s.mem _ _) a |>.trans ha)⟩
            · cases s; dsimp only [stripWxS, hideWxS, ProofLib.stripS, returnToLinkRegister,
                State.setMem, State.setPC, State.readReg64]
              rw [stripWx_write64, stripWx_writeBytes]; rfl
            · unfold returnToLinkRegister
              exact ⟨⟨rfl, rfl, rfl⟩, rfl, fun a =>
                (writeBytes_perm_eq _ _ _ a).trans
                  (congrFun (LibsignalBinary.Heap.IfaceBudgetLemmas.perm_write64_norm _ _ _) a),
                fun _ _ _ => rfl⟩
        · -- lsDalekCompressSym
          have hrow : H lsDalekCompressSym = some (compressHook W.Q.compress) :=
            cliGhost_row mmpl gh W (compress_row_placed mmpl W)
          have hsh : shadowVsigHooks tr0 H lsDalekCompressSym =
              some (compressHook W.Q.compress) :=
            (shadowVsigHooks_other tr0 H).trans (hk_v.trans hrow)
          rw [hsh] at h; injection h with hf'; subst hf'
          rw [hrow]; refine ⟨compressHook W.Q.compress, rfl, rfl, ?_⟩
          unfold compressHook
          rw [stripWxS_readReg64, stripWxS_mem, stripWx_readVecN]
          exact hook_writeBytes_reg_stripWx_vm .x8 s _
        · -- lsDalekEdNegSym
          have hrow : H lsDalekEdNegSym = some (edNegHook W.Q.edNeg) :=
            cliGhost_row mmpl gh W (edNeg_row_placed mmpl W)
          have hsh : shadowVsigHooks tr0 H lsDalekEdNegSym = some (edNegHook W.Q.edNeg) :=
            (shadowVsigHooks_other tr0 H).trans (hk_v.trans hrow)
          rw [hsh] at h; injection h with hf'; subst hf'
          rw [hrow]; refine ⟨edNegHook W.Q.edNeg, rfl, rfl, ?_⟩
          unfold edNegHook
          rw [stripWxS_readReg64, stripWxS_mem, stripWx_readVecN]
          exact hook_writeBytes_reg_stripWx_vm .x8 s _
        · -- lsSha512CompressSym
          have hrow : H lsSha512CompressSym = some (compress512Hook W.Q.F512) :=
            cliGhost_row mmpl gh W (compress512_row_placed mmpl W)
          have hsh : shadowVsigHooks tr0 H lsSha512CompressSym =
              some (compress512Hook W.Q.F512) :=
            (shadowVsigHooks_other tr0 H).trans (hk_v.trans hrow)
          rw [hsh] at h; injection h with hf'; subst hf'
          rw [hrow]; refine ⟨compress512Hook W.Q.F512, rfl, rfl, ?_⟩
          unfold compress512Hook; dsimp only []
          rw [stripWxS_readReg64, stripWxS_readReg64, stripWxS_readReg64, stripWxS_mem,
            stripWx_readSha512State, stripWx_readBytes]
          exact hook_writeBytes_reg_stripWx_vm .x0 s _
        · -- lsDalekScalarWideSym
          have hrow : H lsDalekScalarWideSym = some (scalarWideHook W.Q.scalarWide) :=
            cliGhost_row mmpl gh W (scalarWide_row_placed mmpl W)
          have hsh : shadowVsigHooks tr0 H lsDalekScalarWideSym =
              some (scalarWideHook W.Q.scalarWide) :=
            (shadowVsigHooks_other tr0 H).trans (hk_v.trans hrow)
          rw [hsh] at h; injection h with hf'; subst hf'
          rw [hrow]; refine ⟨scalarWideHook W.Q.scalarWide, rfl, rfl, ?_⟩
          unfold scalarWideHook
          rw [stripWxS_readReg64, stripWxS_mem, stripWx_readVecN]
          exact hook_writeBytes_reg_stripWx_vm .x8 s _
        · -- lsDalekScalarModSym
          have hrow : H lsDalekScalarModSym = some (scalarModHook W.Q.scalarMod) :=
            cliGhost_row mmpl gh W (scalarMod_row_placed mmpl W)
          have hsh : shadowVsigHooks tr0 H lsDalekScalarModSym =
              some (scalarModHook W.Q.scalarMod) :=
            (shadowVsigHooks_other tr0 H).trans (hk_v.trans hrow)
          rw [hsh] at h; injection h with hf'; subst hf'
          rw [hrow]; refine ⟨scalarModHook W.Q.scalarMod, rfl, rfl, ?_⟩
          unfold scalarModHook
          rw [stripWxS_readReg64, stripWxS_mem, stripWx_readVecN]
          exact hook_writeBytes_reg_stripWx_vm .x8 s _
        · -- lsDalekDoubleMulSym
          have hrow : H lsDalekDoubleMulSym = some (dsmbHook W.Q.dsmb) :=
            cliGhost_row mmpl gh W (dsmb_row_placed mmpl W)
          have hsh : shadowVsigHooks tr0 H lsDalekDoubleMulSym = some (dsmbHook W.Q.dsmb) :=
            (shadowVsigHooks_other tr0 H).trans (hk_v.trans hrow)
          rw [hsh] at h; injection h with hf'; subst hf'
          rw [hrow]; refine ⟨dsmbHook W.Q.dsmb, rfl, rfl, ?_⟩
          unfold dsmbHook
          rw [stripWxS_readReg64, stripWxS_readReg64, stripWxS_readReg64, stripWxS_mem,
            stripWx_readVecN, stripWx_readVecN, stripWx_readVecN]
          exact hook_writeBytes_reg_stripWx_vm .x8 s _
      · simp only [Bool.not_eq_true] at hn
        have hn_mc : (n == lsMemcpySym) = false := by
          by_cases hc : (n == lsMemcpySym) = true
          · rw [beq_iff_eq] at hc; subst hc; simp [vsigKeepSym] at hn
          · simpa using hc
        have hn_ms : (n == lsVerifyMemsetSym) = false := by
          by_cases hc : (n == lsVerifyMemsetSym) = true
          · rw [beq_iff_eq] at hc; subst hc; simp [vsigKeepSym] at hn
          · simpa using hc
        have hsh_eq : shadowVsigHooks tr0 H n = vsigOnlyHooks H n := by
          simp [shadowVsigHooks, hn_mc, hn_ms]
        rw [hsh_eq] at h
        cases hHn : H n with
        | none =>
          have hk_n : vsigOnlyHooks H n = none := by unfold vsigOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_n] at h ⊢; dsimp only at h ⊢; exact ih h
        | some g =>
          have hk_g : vsigOnlyHooks H n = some (fun s => s.setStatus (.Exception "ext")) := by
            unfold vsigOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_g] at h; dsimp only at h
          injection h with hf'; subst hf'; intro s _ hrun; cases s; cases hrun
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact ih h

private theorem shadowVsigHooks_isSome_eq [LibsignalPlacement] (tr0 : List State)
    (H : LibsignalHooks) (n : String) :
    (shadowVsigHooks tr0 H n).isSome = (vsigOnlyHooks H n).isSome := by
  unfold shadowVsigHooks vsigOnlyHooks vsigKeepSym
  by_cases h1 : (n == lsMemcpySym) = true
  · simp [h1]
  · by_cases h2 : (n == lsVerifyMemsetSym) = true
    · simp [h1, h2]
    · simp [h1, h2]

private theorem shadowVsigHooks_findSome?_isSome [LibsignalPlacement] (tr0 : List State)
    (H : LibsignalHooks) :
    ∀ (l : List (String × Nat)) (off : Nat),
      ((l.findSome? fun x => if x.2 == off then shadowVsigHooks tr0 H x.1 else none)).isSome =
      ((l.findSome? fun x => if x.2 == off then vsigOnlyHooks H x.1 else none)).isSome
  | [], _ => rfl
  | (n, o) :: tl, off => by
    dsimp only [List.findSome?]
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte]
      have his := shadowVsigHooks_isSome_eq tr0 H n
      cases hs1 : shadowVsigHooks tr0 H n <;> cases hs2 : vsigOnlyHooks H n
      · exact shadowVsigHooks_findSome?_isSome tr0 H tl off
      · rw [hs1, hs2] at his; cases his
      · rw [hs1, hs2] at his; cases his
      · rfl
    · simp only [ho, Bool.false_eq_true, ↓reduceIte]
      exact shadowVsigHooks_findSome?_isSome tr0 H tl off

private theorem shadowVsigHooks_externAt?_isSome [LibsignalPlacement] (tr0 : List State)
    (H : LibsignalHooks) (pc : BitVec 64) :
    (((blkPC_203).rebase (blkPl_203).base (shadowVsigHooks tr0 H)).externAt? pc).isSome =
    (((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).externAt? pc).isSome := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase
  dsimp only
  rw [findSome?_syms_none]
  simp only [Option.or_none]
  exact shadowVsigHooks_findSome?_isSome tr0 H (blkPC_203).stubs (pc - (blkPl_203).base).toNat

private theorem vsigOnlyHooks_findSome?_none {H : LibsignalHooks} :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then vsigOnlyHooks H n else none) = none →
      (l.findSome? fun (n, o) => if o == off then H n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      cases hHn : H n with
      | none =>
        have hk : vsigOnlyHooks H n = none := by unfold vsigOnlyHooks; split <;> simp [hHn]
        rw [hk] at h; exact vsigOnlyHooks_findSome?_none tl h
      | some g =>
        have hk : ∃ g', vsigOnlyHooks H n = some g' := by
          by_cases hk0 : vsigKeepSym n = true <;> simp [vsigOnlyHooks, hk0, hHn]
        rcases hk with ⟨g', hg'⟩; rw [hg'] at h; cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact vsigOnlyHooks_findSome?_none tl h

private theorem shadowVsigHooks_externAt?_active [LibsignalPlacement] (tr0 : List State)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh)
    {pc : BitVec 64} {f' : State → State}
    (hext' : ((blkPC_203).rebase (blkPl_203).base
      (shadowVsigHooks tr0 (cliGhostExterns gh (cliExternsPlaced mmpl W)))).externAt? pc = some f')
    {s : State} (hfs : findState tr0 (stripWxS s) = some s)
    (hrun : (f' (stripWxS s)).status = .Running) :
    ∃ f : State → State,
      ((blkPC_203).rebase (blkPl_203).base
        (vsigOnlyHooks (cliGhostExterns gh (cliExternsPlaced mmpl W)))).externAt? pc = some f ∧
      ((blkPC_203).rebase (blkPl_203).base
        (cliGhostExterns gh (cliExternsPlaced mmpl W))).externAt? pc = some f ∧
      f' (stripWxS s) = stripWxS (f s) ∧
      VmPreserved s (f s) ∧
      AnonMono s.mem (f s).mem := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext' ⊢
  dsimp only at hext' ⊢
  rw [findSome?_syms_none] at hext' ⊢
  cases hm : ((blkPC_203).stubs.findSome? fun (n, o) =>
      if o == (pc - (blkPl_203).base).toNat then shadowVsigHooks tr0 H n else none) with
  | none => rw [hm] at hext'; cases hext'
  | some g =>
    rw [hm] at hext'; injection hext' with hgf; subst hgf
    obtain ⟨f, hv, hH, hcomm, hvm, han⟩ :=
      shadowVsigHooks_findSome?_active tr0 mmpl gh W hG (blkPC_203).stubs hm s hfs hrun
    rw [hv, hH]
    exact ⟨f, rfl, rfl, hcomm, hvm, han⟩

private theorem vsigOnlyHooks_externAt?_none [LibsignalPlacement] {H : LibsignalHooks}
    {pc : BitVec 64}
    (hext : ((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).externAt? pc = none) :
    ((blkPC_203).rebase (blkPl_203).base H).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_syms_none] at hext ⊢
  have h1 : ((blkPC_203).stubs.findSome? fun (n, o) =>
      if o == (pc - (blkPl_203).base).toNat then vsigOnlyHooks H n else none) = none := by
    cases hm : ((blkPC_203).stubs.findSome? fun (n, o) =>
        if o == (pc - (blkPl_203).base).toNat then vsigOnlyHooks H n else none) with
    | none => rfl
    | some g => rw [hm] at hext; cases hext
  rw [vsigOnlyHooks_findSome?_none (blkPC_203).stubs h1]; rfl

private theorem steps_vsig_lockstep_vm [LibsignalPlacement]
    (tr0_all : List State)
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim gh)
    {tr0 : List State} {s1 sf0 sf' : State}
    (htr0 : StepsList ((blkPC_203).rebase (blkPl_203).base
      (vsigOnlyHooks (cliGhostExterns gh (cliExternsPlaced mmpl W)))) tr0 s1 sf0)
    (hrun0 : sf0.status = .Running) :
    ∀ (seen0 : List State) {tr' : List State} {s1' : State},
      tr0_all = seen0.reverse ++ tr0 →
      (∀ u ∈ seen0, stripWxS u ∉ tr') →
      s1' = stripWxS s1 →
      StepsList ((blkPC_203).rebase (blkPl_203).base
        (shadowVsigHooks tr0_all (cliGhostExterns gh (cliExternsPlaced mmpl W)))) tr' s1' sf' →
      sf'.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      ∃ sf : State,
        (sf = sf0 ∨ (sf' = stripWxS sf ∧ AnonMono s1.mem sf.mem)) ∧
        Steps ((blkPC_203).rebase (blkPl_203).base
          (cliGhostExterns gh (cliExternsPlaced mmpl W))) s1 sf ∧
        VmPreserved s1 sf := by
  let H := cliGhostExterns gh (cliExternsPlaced mmpl W)
  induction htr0 with
  | refl =>
    intro seen0 _ _ _ _ _ _ _ _
    exact ⟨_, Or.inl rfl, .refl _, VmPreserved.refl _⟩
  | @step s1 s2 sf0 tl0 h1_0 hrest0 _ ih =>
    intro seen0 tr' s1' hdecomp hseen hs1' htr' hrun_f hcl1
    cases htr' with
    | refl =>
      exact ⟨s1, Or.inr ⟨hs1', AnonMono.refl s1.mem⟩, .refl s1, VmPreserved.refl s1⟩
    | @step _ s2' _ tl' h1' hrest' hnot' =>
      subst hs1'
      have hr2_0 : s2.status = .Running := by
        cases hrest0 with
        | refl => exact hrun0
        | step hs _ _ => cases hs <;> assumption
      have hr2' : s2'.status = .Running := by
        cases hrest' with
        | refl => exact hrun_f
        | step hs _ _ => cases hs <;> assumption
      have hfs : findState tr0_all (stripWxS s1) = some s1 := by
        rw [hdecomp]
        exact findState_eq_head fun u hu heq =>
          hseen u hu (List.mem_cons.mpr (Or.inl heq))
      have hdecomp2 : tr0_all = (s1 :: seen0).reverse ++ tl0 := by
        rw [List.reverse_cons, List.append_assoc, List.singleton_append]; exact hdecomp
      have hseen2 : ∀ u ∈ s1 :: seen0, stripWxS u ∉ tl' := by
        intro u hu hmem_tl
        rcases List.mem_cons.mp hu with rfl | hu_s
        · exact hnot' hmem_tl
        · exact hseen u hu_s (List.mem_cons.mpr (Or.inr hmem_tl))
      have hpc_eq : (stripWxS s1).pc = s1.pc := by cases s1; rfl
      cases h1_0 with
      | halt_unmapped _ _ _ => cases s1; cases hr2_0
      | extern_fault _ _ _ => cases s1; cases hr2_0
      | @extern f hr1 hext0 hkf_s1 hsym_s1 =>
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @exec inst' _ hfe' =>
          unfold Program.fetchMem at hfe'
          have his : (((blkPC_203).rebase (blkPl_203).base
              (shadowVsigHooks tr0_all H)).externAt? (stripWxS s1).pc).isSome = true := by
            rw [hpc_eq, shadowVsigHooks_externAt?_isSome, hext0]; rfl
          rw [his] at hfe'; simp at hfe'
        | @extern f' _ hext' _ _ =>
          rw [hpc_eq] at hext'
          obtain ⟨f_v, hext_v, hext_H, hcomm, hvm1, han1⟩ :=
            shadowVsigHooks_externAt?_active tr0_all mmpl gh W hG hext' hfs hr2'
          rw [hext0] at hext_v; injection hext_v with hff; subst hff
          have hstep_H : Step ((blkPC_203).rebase (blkPl_203).base H) s1 (f s1) :=
            Step.extern hr1 hext_H hkf_s1 hsym_s1
          have hcl2 : LibsignalCodeLoaded lsmpl (f s1).mem := hcl1.of_keepsFrozen hkf_s1
          obtain ⟨sf, hsf_eq | ⟨hsf', han2⟩, hsteps_H, hvm_rest⟩ :=
            ih hrun0 (s1 :: seen0) hdecomp2 hseen2 hcomm hrest' hrun_f hcl2
          · exact ⟨sf, Or.inl hsf_eq, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩
          · exact ⟨sf, Or.inr ⟨hsf', han1.trans han2 hvm1.perm_eq⟩, .step hstep_H hsteps_H,
              hvm1.trans hvm_rest⟩
      | @exec inst hr1 hfe0 =>
        let P_H := (blkPC_203).rebase (blkPl_203).base H
        have hext_v :
            ((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).externAt? s1.pc = none := by
          cases he : ((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).externAt? s1.pc with
          | none => rfl
          | some g => unfold Program.fetchMem at hfe0; rw [he] at hfe0; simp at hfe0
        have hext_sh :
            ((blkPC_203).rebase (blkPl_203).base (shadowVsigHooks tr0_all H)).externAt? s1.pc =
              none := by
          cases he : ((blkPC_203).rebase (blkPl_203).base
              (shadowVsigHooks tr0_all H)).externAt? s1.pc with
          | none => rfl
          | some g =>
            have his := shadowVsigHooks_externAt?_isSome tr0_all H s1.pc
            rw [he, hext_v] at his; cases his
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @extern f' _ hext' _ _ =>
          rw [hpc_eq, hext_sh] at hext'; cases hext'
        | @exec inst' _ hfe' =>
          have hmem_eq : (stripWxS s1).mem = stripWx s1.mem := by cases s1; rfl
          rw [hpc_eq, hmem_eq] at hfe'
          have hext_H : P_H.externAt? s1.pc = none := vsigOnlyHooks_externAt?_none hext_v
          have ⟨hal_pc, hce', hdec⟩ : s1.pc.toNat % 4 = 0 ∧
              (stripWx s1.mem).canExec s1.pc 4 = true ∧
              Arm64.decode (s1.mem.read32 s1.pc) = some inst' := by
            unfold Program.fetchMem at hfe'
            rw [hext_sh] at hfe'
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
            by_cases hal : s1.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
              split at hfe'
              · contradiction
              · rename_i hce_neg
                simp only [Bool.not_eq_true', Bool.not_eq_false] at hce_neg
                rw [stripWx_read32] at hfe'; exact ⟨hal, hce_neg, hfe'⟩
            · simp only [hal, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
          have ⟨hce, hkeep_pc⟩ : s1.mem.canExec s1.pc 4 = true ∧ keepLs s1.pc = true := by
            unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢
            refine ⟨fun k hk => ?_, ?_⟩
            · have hxk := hce' k hk; unfold stripWx at hxk
              obtain ⟨hx_hw, hkp⟩ := ProofLib.strip_perm_x_imp hxk
              rw [hideWx_perm] at hx_hw
              revert hx_hw
              rcases s1.mem.perm (s1.pc + BitVec.ofNat 64 k) with _ | ⟨r, w, x, _, _⟩ <;> intro hx_hw
              · simp [Option.x] at hx_hw
              · cases r <;> cases w <;> cases x <;> simp [Perm.protNone, Option.x] at hx_hw ⊢
            · have hx0 := hce' 0 (by decide); unfold stripWx at hx0
              simpa using (ProofLib.strip_perm_x_imp hx0).2
          have hfe0' := hfe0
          unfold Program.fetchMem at hfe0'; rw [hext_v] at hfe0'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
            not_true_eq_false, hce, Bool.not_true] at hfe0'
          have hinst_eq : inst' = inst := Option.some.inj (hdec.symm.trans hfe0')
          subst hinst_eq
          have hfe_H : P_H.fetchMem s1.mem s1.pc = some inst' := by
            unfold Program.fetchMem; rw [hext_H]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
              not_true_eq_false, hce, Bool.not_true]
            exact hdec
          obtain ⟨hnsvc0, hnmsr⟩ := safeVm_of_keepLs hcl1 hkeep_pc hal_pc hdec
          have hev0 : ((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).evalInst inst' s1 =
              execInst inst' s1 :=
            Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
          have hev_sh0 : ((blkPC_203).rebase (blkPl_203).base
              (shadowVsigHooks tr0_all H)).evalInst inst' (stripWxS s1) =
              execInst inst' (stripWxS s1) :=
            Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 (stripWxS s1)
          have hr_exec' : (execInst inst' (stripWxS s1)).status = .Running := by
            rwa [← hev_sh0]
          have hev_v : ((blkPC_203).rebase (blkPl_203).base
              (shadowVsigHooks tr0_all H)).evalInst inst' (stripWxS s1) =
              stripWxS (((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).evalInst inst' s1) := by
            rw [hev_sh0, hev0, execInst_stripWxS hnsvc0 s1 hr_exec']
          have hstep_H : Step P_H s1
              (((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            simpa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] using
              Step.exec (prog := P_H) hr1 hfe_H
          have hvm1 : VmPreserved s1
              (((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            exact VmPreserved.of_vm_tpidr
              (VerifiedLibraries.RustStd.nonSyscallPreserved_toVmFields
                (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1))
              (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
              (LibsignalBinary.Heap.FdsHiFrame.of_fs_eq
                (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1).2.2.2.2.2.2)
          have han1 : AnonMono s1.mem
              (((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).evalInst inst' s1).mem := by
            rw [hev0]; intro a _ ha
            exact congrFun (execInst_isAnon_of_not_isSvc0 hnsvc0 s1) a |>.trans ha
          have hcl2 : LibsignalCodeLoaded lsmpl
              (((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).evalInst inst' s1).mem :=
            hcl1.of_keepsFrozen (Step.keepsFrozen hstep_H)
          obtain ⟨sf, hsf_eq | ⟨hsf', han2⟩, hsteps_H, hvm_rest⟩ :=
            ih hrun0 (s1 :: seen0) hdecomp2 hseen2 hev_v hrest' hrun_f hcl2
          · exact ⟨sf, Or.inl hsf_eq, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩
          · exact ⟨sf, Or.inr ⟨hsf', han1.trans han2 hvm1.perm_eq⟩, .step hstep_H hsteps_H,
              hvm1.trans hvm_rest⟩

/-! ### `RwOnlyHeap` Frame Unstripping & `verifySignature_203_vm_ok` -/

private def RwOnlyHeap (h : Heap) : Prop :=
  (∀ a c, h.phys a = some c → (∃ b, c = .rw b) ∨ c = .lazy) ∧
  (∀ γ k, h.auth γ k = none) ∧
  (∀ γ k, h.frag γ k = none) ∧
  (∀ a, h.mapped a = false)

private theorem rwOnlyHeap_of_isBlock {Q : SepProp} {base : BitVec 64} {len : Nat}
    {Φ : Memory → Prop} (hb : IsBlock Q base len Φ) (h : Heap) (hq : Q h) :
    RwOnlyHeap h := by
  obtain ⟨m1, _, rfl⟩ := (hb.iff h).mp hq
  refine ⟨fun a c hc => ?_, fun _ _ => by simp [regionHeap],
    fun _ _ => by simp [regionHeap], fun _ => by simp [regionHeap]⟩
  by_cases hin : InRegion base len a
  · simp [regionHeap, hin] at hc; exact Or.inl ⟨_, hc.symm⟩
  · simp [regionHeap, hin] at hc

private theorem rwOnlyHeap_sepConj {P Q : SepProp}
    (hp : ∀ h, P h → RwOnlyHeap h) (hq : ∀ h, Q h → RwOnlyHeap h)
    (h : Heap) (hpq : (P ∗ Q) h) : RwOnlyHeap h := by
  rcases Arm64.SepProp.holds_sepConj_elim hpq with ⟨h1, h2, _, rfl, hp1, hq2⟩
  obtain ⟨h1_p, h1_a, h1_f, h1_m⟩ := hp h1 hp1
  obtain ⟨h2_p, h2_a, h2_f, h2_m⟩ := hq h2 hq2
  refine ⟨fun a c hc => ?_, fun γ k => ?_, fun γ k => ?_, fun a => ?_⟩
  · unfold Heap.union at hc; dsimp only at hc
    cases hc1 : h1.phys a with
    | some c1 => rw [hc1] at hc; injection hc with hc'; subst hc'; exact h1_p a c1 hc1
    | none => rw [hc1] at hc; exact h2_p a c hc
  · unfold Heap.union; dsimp only; rw [h1_a γ k, h2_a γ k]
  · unfold Heap.union; dsimp only; rw [h1_f γ k, h2_f γ k]
  · unfold Heap.union; dsimp only; rw [h1_m a, h2_m a]; rfl

private theorem vsigPre_rwOnly (P : SignalPqxdh.Primitives)
    (g' : VerifySignaturePlacedGhost) (s0 : State) (h : Heap)
    (hh : (verifySignatureCallSpec P).pre g' s0 h) : RwOnlyHeap h := by
  dsimp only [verifySignatureCallSpec] at hh
  exact rwOnlyHeap_sepConj (rwOnlyHeap_of_isBlock (IsBlock.pointsToBytes _ _))
    (rwOnlyHeap_sepConj (rwOnlyHeap_of_isBlock (IsBlock.pointsToBytes _ _))
      (rwOnlyHeap_sepConj (rwOnlyHeap_of_isBlock (IsBlock.pointsToBytes _ _))
        (rwOnlyHeap_of_isBlock (IsBlock.memRegion _ _)))) h
    (Arm64.SepProp.holds_pure_sepConj hh).2

private theorem vsigPost_rwOnly (P : SignalPqxdh.Primitives)
    (g' : VerifySignaturePlacedGhost) (s0 sf : State) (h : Heap)
    (hh : (verifySignatureCallSpec P).post g' s0 sf h) : RwOnlyHeap h := by
  dsimp only [verifySignatureCallSpec] at hh
  exact rwOnlyHeap_sepConj (rwOnlyHeap_of_isBlock (IsBlock.pointsToBytes _ _))
    (rwOnlyHeap_sepConj (rwOnlyHeap_of_isBlock (IsBlock.pointsToBytes _ _))
      (rwOnlyHeap_sepConj (rwOnlyHeap_of_isBlock (IsBlock.pointsToBytes _ _))
        (rwOnlyHeap_of_isBlock (IsBlock.memRegion _ _)))) h
    (Arm64.SepProp.holds_pure_sepConj hh).2

private theorem rwOnlyHeap_matches_stripWx_iff [LibsignalPlacement] {h : Heap}
    (hrw : RwOnlyHeap h) (m : Memory) :
    h.Matches (stripWx m) ↔ h.Matches m := by
  unfold Heap.Matches
  refine ⟨fun hm => ⟨fun a c hc => ?_, hm.2.1, fun a hma => by rw [hrw.2.2.2 a] at hma; cases hma⟩,
          fun hm => ⟨fun a c hc => ?_, hm.2.1, fun a hma => by rw [hrw.2.2.2 a] at hma; cases hma⟩⟩
  · have hcell := hm.1 a c hc
    rcases hrw.1 a c hc with ⟨b, rfl⟩ | rfl
    · obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp
        ((stripWx_permNoLazy_rw_iff m a).mp
          (Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hcell.2.1, hcell.2.2⟩))
      exact ⟨(stripWx_read8 m a).symm.trans hcell.1, hp, hlf⟩
    · exact ((ProofLib.strip_perm_props keepLs (hideWx m) a).2.2.2.trans
        (by dsimp only [hideWx, Memory.perm, Perm.rw, Perm.rwx, Perm.protNone];
            rcases m.cells a with _ | ⟨_ | ⟨r, w, x, _, _⟩, _⟩ <;>
              [simp; simp; (cases r <;> cases w <;> cases x <;> simp)])).mp hcell
  · have hcell := hm.1 a c hc
    rcases hrw.1 a c hc with ⟨b, rfl⟩ | rfl
    · obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp
        ((stripWx_permNoLazy_rw_iff m a).mpr
          (Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hcell.2.1, hcell.2.2⟩))
      exact ⟨(stripWx_read8 m a).trans hcell.1, hp, hlf⟩
    · exact ((ProofLib.strip_perm_props keepLs (hideWx m) a).2.2.2.trans
        (by dsimp only [hideWx, Memory.perm, Perm.rw, Perm.rwx, Perm.protNone];
            rcases m.cells a with _ | ⟨_ | ⟨r, w, x, _, _⟩, _⟩ <;>
              [simp; simp; (cases r <;> cases w <;> cases x <;> simp)])).mpr hcell

private theorem unstrip_vsigPost_frame [LibsignalPlacement]
    {m0 mf : Memory} {P_post R : SepProp} {h_P h_R : Heap}
    (hP_rw : RwOnlyHeap h_P) (hQ_rw : ∀ h, P_post h → RwOnlyHeap h)
    (hdisj_PR : h_P.Disjoint h_R) (hp_R : R h_R) (hm_R : h_R.Matches m0)
    (hperm : ∀ a, mf.perm a = m0.perm a) (hanon : AnonMono m0 mf)
    (hpost_swx : stripWx mf ⊨ P_post ∗ ⟨fun h => h = fullComplementHeap h_P (stripWx m0)⟩) :
    mf ⊨ P_post ∗ R := by
  obtain ⟨h_Q, h_c, hdisj_Qc, hp_Q, rfl, hm_Qc⟩ := Satisfies.sepConj_elim hpost_swx
  have hQr : RwOnlyHeap h_Q := hQ_rw h_Q hp_Q
  have hm_Q : h_Q.Matches mf :=
    (rwOnlyHeap_matches_stripWx_iff hQr mf).mp (Heap.Matches.of_union_left hm_Qc)
  have hm_c : (fullComplementHeap h_P (stripWx m0)).Matches (stripWx mf) :=
    Heap.Matches.of_union_right hdisj_Qc hm_Qc
  unfold Heap.Disjoint at hdisj_PR hdisj_Qc
  unfold Heap.Matches at hm_R hm_c
  have hcomp_some : ∀ a c_R, h_R.phys a = some c_R →
      (∃ c', (fullComplementHeap h_P (stripWx m0)).phys a = some c') ∧
      (∀ b, (c_R = .rw b ∨ c_R = .ro b ∨ c_R = .protNone b) →
        mf.read8 a = b ∧ mf.isLazyFree a = false) := by
    intro a c_R hcR
    have hP_none : h_P.phys a = none := by
      cases hp : h_P.phys a with
      | none => rfl
      | some cp =>
        rcases hdisj_PR.1 a with h1 | h2 | ⟨_, h3, _⟩
        · rw [hp] at h1; cases h1
        · rw [hcR] at h2; cases h2
        · rcases hP_rw.1 a cp hp with ⟨_, hcp⟩ | hcp <;> rw [hcp] at hp <;> rw [hp] at h3 <;> cases h3
    have hcell := hm_R.1 a c_R hcR
    cases c_R with
    | lazy =>
      have hp_sw : (stripWx m0).perm a = some Perm.rw := by
        dsimp only at hcell
        unfold stripWx
        rw [(ProofLib.strip_perm_props keepLs (hideWx m0) a).2.2.2]
        dsimp only [hideWx, Memory.perm, Perm.rw, Perm.rwx] at hcell ⊢
        revert hcell
        rcases m0.cells a with _ | ⟨_ | ⟨r, w, x, _, _⟩, _⟩ <;> intro hcell <;>
          [simp at hcell; simp at hcell; (cases r <;> cases w <;> cases x <;> simp at hcell ⊢)]
      refine ⟨?_, fun _ h => by rcases h with h | h | h <;> cases h⟩
      cases hlf : (stripWx m0).isLazyFree a
      · exact ⟨.rw ((stripWx m0).read8 a), by simp [fullComplementHeap, hP_none, hp_sw, hlf]⟩
      · exact ⟨.lazy, by simp [fullComplementHeap, hP_none, hp_sw, hlf]⟩
    | protNoneLazy =>
      have hnwx : ((m0.perm a).w && (m0.perm a).x) = false := by rw [hcell]; rfl
      have hp_sw : (stripWx m0).perm a = some Perm.protNone := by
        unfold stripWx; rw [ProofLib.strip_perm, (hideWx_of_not_wx hnwx).1, hcell]
        unfold ProofLib.stripPerm Perm.protNone; cases keepLs a <;> rfl
      refine ⟨?_, fun _ h => by rcases h with h | h | h <;> cases h⟩
      cases hlf : (stripWx m0).isLazyFree a
      · exact ⟨.protNone ((stripWx m0).read8 a), by
          dsimp only [fullComplementHeap]; rw [hP_none, hp_sw, hlf]; simp [Perm.protNone, Perm.rw]⟩
      · exact ⟨.protNoneLazy, by
          dsimp only [fullComplementHeap]; rw [hP_none, hp_sw, hlf]; simp [Perm.protNone, Perm.rw]⟩
    | rw b =>
      obtain ⟨hp_sw, hlf_sw⟩ := Memory.permNoLazy_eq_some_rw_iff.mp
        ((stripWx_permNoLazy_rw_iff m0 a).mpr
          (Memory.permNoLazy_eq_some_rw_iff.mpr ⟨hcell.2.1, hcell.2.2⟩))
      have hca : (fullComplementHeap h_P (stripWx m0)).phys a =
          some (.rw ((stripWx m0).read8 a)) := by
        simp [fullComplementHeap, hP_none, hp_sw, hlf_sw]
      obtain ⟨hrd', hp_f, hlf_f⟩ := hm_c.1 a _ hca
      have hmap_f : ((stripWx mf).perm a).mapped = true := by rw [hp_f]; rfl
      obtain ⟨_, hlf_eq, _⟩ := stripWx_mapped_props hmap_f
      exact ⟨⟨_, hca⟩, fun b' hb' => by
        have hbb : b = b' := by rcases hb' with h | h | h <;> injection h
        subst hbb
        exact ⟨(stripWx_read8 mf a).symm.trans (hrd'.trans ((stripWx_read8 m0 a).trans hcell.1)),
          hlf_eq.symm.trans hlf_f⟩⟩
    | protNone b =>
      have hnwx : ((m0.perm a).w && (m0.perm a).x) = false := by rw [hcell.2.1]; rfl
      obtain ⟨hp_hw, hlf_hw, _⟩ := hideWx_of_not_wx hnwx
      have hp_sw : (stripWx m0).perm a = some Perm.protNone := by
        unfold stripWx; rw [ProofLib.strip_perm, hp_hw, hcell.2.1]
        unfold ProofLib.stripPerm Perm.protNone; cases keepLs a <;> rfl
      have hlf_sw : (stripWx m0).isLazyFree a = false := by
        unfold stripWx; rw [ProofLib.strip_isLazyFree, hlf_hw]; exact hcell.2.2
      have hca : (fullComplementHeap h_P (stripWx m0)).phys a =
          some (.protNone ((stripWx m0).read8 a)) := by
        dsimp only [fullComplementHeap]; rw [hP_none, hp_sw, hlf_sw]; rfl
      obtain ⟨hrd', hp_f, hlf_f⟩ := hm_c.1 a _ hca
      have hmap_f : ((stripWx mf).perm a).mapped = true := by rw [hp_f]; rfl
      obtain ⟨_, hlf_eq, _⟩ := stripWx_mapped_props hmap_f
      exact ⟨⟨_, hca⟩, fun b' hb' => by
        have hbb : b = b' := by rcases hb' with h | h | h <;> injection h
        subst hbb
        exact ⟨(stripWx_read8 mf a).symm.trans (hrd'.trans ((stripWx_read8 m0 a).trans hcell.1)),
          hlf_eq.symm.trans hlf_f⟩⟩
    | ro b =>
      by_cases hwx : ((m0.perm a).w && (m0.perm a).x) = true
      · have hp_hw : (hideWx m0).perm a = some Perm.protNone := by
          rw [hideWx_perm]
          rcases hp0 : m0.perm a with _ | ⟨r, w, x, lf, an⟩
          · rw [hp0] at hwx; cases hwx
          · have hr0 : r = true := by rw [hp0] at hcell; exact hcell.2.1
            have hwx0 : (w && x) = true := by rw [hp0] at hwx; exact hwx
            subst hr0; simp [hwx0]
        have hp_sw : (stripWx m0).perm a = some Perm.protNone := by
          unfold stripWx; rw [ProofLib.strip_perm, hp_hw]
          unfold ProofLib.stripPerm Perm.protNone; cases keepLs a <;> rfl
        have hlf_sw : (stripWx m0).isLazyFree a = false := by
          unfold stripWx; rw [ProofLib.strip_isLazyFree]
          have hlf0 : m0.isLazyFree a = false := hcell.2.2
          dsimp only [hideWx, Memory.isLazyFree, Memory.perm, Option.w, Option.x, Perm.protNone,
            Perm.rwx] at hwx hlf0 ⊢
          revert hwx hlf0
          rcases m0.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> intro hwx hlf0 <;>
            [simp at hwx; simp at hwx;
             (cases r <;> cases w <;> cases x <;> simp at hwx ⊢; exact hlf0)]
        have hca : (fullComplementHeap h_P (stripWx m0)).phys a =
            some (.protNone ((stripWx m0).read8 a)) := by
          dsimp only [fullComplementHeap]; rw [hP_none, hp_sw, hlf_sw]; rfl
        obtain ⟨hrd', hp_f, hlf_f⟩ := hm_c.1 a _ hca
        have hmap_f : ((stripWx mf).perm a).mapped = true := by rw [hp_f]; rfl
        obtain ⟨_, hlf_eq, _⟩ := stripWx_mapped_props hmap_f
        exact ⟨⟨_, hca⟩, fun b' hb' => by
          have hbb : b = b' := by rcases hb' with h | h | h <;> injection h
          subst hbb
          exact ⟨(stripWx_read8 mf a).symm.trans (hrd'.trans ((stripWx_read8 m0 a).trans hcell.1)),
            hlf_eq.symm.trans hlf_f⟩⟩
      · have hnwx : ((m0.perm a).w && (m0.perm a).x) = false := Bool.eq_false_iff.mpr hwx
        obtain ⟨hp_hw, hlf_hw, _⟩ := hideWx_of_not_wx hnwx
        have hr_sw : ((stripWx m0).perm a).r = true := by
          unfold stripWx
          rw [(ProofLib.strip_perm_props keepLs (hideWx m0) a).1, hp_hw]
          exact hcell.2.1
        have hlf_sw : (stripWx m0).isLazyFree a = false := by
          unfold stripWx; rw [ProofLib.strip_isLazyFree, hlf_hw]; exact hcell.2.2
        by_cases hp_rw : (stripWx m0).perm a = some Perm.rw
        · have hca : (fullComplementHeap h_P (stripWx m0)).phys a =
              some (.rw ((stripWx m0).read8 a)) := by
            simp [fullComplementHeap, hP_none, hp_rw, hlf_sw]
          obtain ⟨hrd', hp_f, hlf_f⟩ := hm_c.1 a _ hca
          have hmap_f : ((stripWx mf).perm a).mapped = true := by rw [hp_f]; rfl
          obtain ⟨_, hlf_eq, _⟩ := stripWx_mapped_props hmap_f
          exact ⟨⟨_, hca⟩, fun b' hb' => by
            have hbb : b = b' := by rcases hb' with h | h | h <;> injection h
            subst hbb
            exact ⟨(stripWx_read8 mf a).symm.trans (hrd'.trans ((stripWx_read8 m0 a).trans hcell.1)),
              hlf_eq.symm.trans hlf_f⟩⟩
        · have hca : (fullComplementHeap h_P (stripWx m0)).phys a =
              some (.ro ((stripWx m0).read8 a)) := by
            simp only [fullComplementHeap, hP_none, hp_rw, hr_sw, hlf_sw, and_self, ↓reduceIte]
          obtain ⟨hrd', hr_f, hlf_f⟩ := hm_c.1 a _ hca
          have hmap_f : ((stripWx mf).perm a).mapped = true := by
            revert hr_f
            rcases (stripWx mf).perm a with _ | _ <;> intro hr_f <;> [cases hr_f; rfl]
          obtain ⟨_, hlf_eq, _⟩ := stripWx_mapped_props hmap_f
          exact ⟨⟨_, hca⟩, fun b' hb' => by
            have hbb : b = b' := by rcases hb' with h | h | h <;> injection h
            subst hbb
            exact ⟨(stripWx_read8 mf a).symm.trans (hrd'.trans ((stripWx_read8 m0 a).trans hcell.1)),
              hlf_eq.symm.trans hlf_f⟩⟩
  have hdisj_QR : h_Q.Disjoint h_R := by
    unfold Heap.Disjoint
    refine ⟨fun a => ?_,
      fun γ k => Or.inl (hQr.2.1 γ k),
      fun γ k => Or.inl (hQr.2.2.1 γ k),
      (fun γ k _ _ h => by
        rcases h with ⟨ha, _⟩ | ⟨_, hf⟩
        · rw [hQr.2.1 γ k] at ha; cases ha
        · rw [hQr.2.2.1 γ k] at hf; cases hf),
      fun a => Or.inl (hQr.2.2.2 a)⟩
    cases hcR : h_R.phys a with
    | none => exact Or.inr (Or.inl rfl)
    | some c_R =>
      obtain ⟨⟨c', hc'⟩, _⟩ := hcomp_some a c_R hcR
      rcases hdisj_Qc.1 a with h1 | h2 | ⟨_, h3, _⟩
      · exact Or.inl h1
      · rw [hc'] at h2; cases h2
      · rcases hQr.1 a _ h3 with ⟨_, h4⟩ | h4 <;> cases h4
  have hm_R_mf : h_R.Matches mf := by
    unfold Heap.Matches
    refine ⟨fun a c_R hcR => ?_, hm_R.2.1, fun a hma => ?_⟩
    · have hcell := hm_R.1 a c_R hcR
      cases c_R with
      | lazy => rw [hperm a]; exact hcell
      | protNoneLazy => rw [hperm a]; exact hcell
      | rw b =>
        obtain ⟨hrd, hlf⟩ := (hcomp_some a (.rw b) hcR).2 b (Or.inl rfl)
        exact ⟨hrd, (hperm a).trans hcell.2.1, hlf⟩
      | ro b =>
        obtain ⟨hrd, hlf⟩ := (hcomp_some a (.ro b) hcR).2 b (Or.inr (Or.inl rfl))
        exact ⟨hrd, by rw [hperm a]; exact hcell.2.1, hlf⟩
      | protNone b =>
        obtain ⟨hrd, hlf⟩ := (hcomp_some a (.protNone b) hcR).2 b (Or.inr (Or.inr rfl))
        exact ⟨hrd, (hperm a).trans hcell.2.1, hlf⟩
    · have hm0_a := hm_R.2.2 a hma
      have hmap0 : (m0.perm a).mapped = true := hm0_a.1
      exact ⟨by rw [hperm a]; exact hmap0, hanon a hmap0 hm0_a.2⟩
  exact ProofLib.Satisfies.sepConj_intro hdisj_QR hp_Q hp_R (Heap.Matches.union hm_Q hm_R_mf)

private theorem verifySignature_203_vm_ok [LibsignalPlacement]
    {mmpl : MultiPlacement} (ghFixed : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim ghFixed)
    (Y : UnreachedPqxdhPrimitives) :
    subroutine_ok
      ((blkPC_203).rebase (blkPl_203).base (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
      (blkPl_203).base
      (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims Y ⟨W.C, W.Q⟩))) := by
  let H := cliGhostExterns ghFixed (cliExternsPlaced mmpl W)
  let P := modelPrims Y ⟨W.C, W.Q⟩
  have hprims := VerifySignaturePrims.of_structuralPrims (structuralPrims_initiatorModelPrims Y ⟨W.C, W.Q⟩)
  have hbase0 := verifySignature_placed_ok (H := vsigOnlyHooks H) hprims
    (w3VerifySigHooks_vsigOnly mmpl ghFixed W hG Y)
  refine subroutine_ok_outcome_intro fun g R s0 hpc hrun hpre_cro hsp => ?_
  obtain ⟨⟨hcl, hro⟩, hpre_vs⟩ := extract_withLsCodeRoLoaded hpre_cro
  dsimp only [verifySignatureInnerSpec, withVmPreserved] at hpre_vs
  let g' : VerifySignaturePlacedGhost :=
    { pkPtr := g.pkPtr, pk := g.pk, msgPtr := g.msgPtr, m := g.m,
      sigPtr := g.sigPtr, sig := g.sig }
  have hpre_call : s0.mem ⊨ (verifySignatureCallSpec P).pre g' s0 ∗ R := hpre_vs
  obtain ⟨h_P, h_R, hdisj_PR, hp_P, hp_R, hm_PR⟩ := Satisfies.sepConj_elim hpre_call
  have hP_rw : RwOnlyHeap h_P := vsigPre_rwOnly P g' s0 h_P hp_P
  have hm_P_swx : h_P.Matches (stripWx s0.mem) :=
    (rwOnlyHeap_matches_stripWx_iff hP_rw s0.mem).mpr (Heap.Matches.of_union_left hm_PR)
  let R_view : SepProp := ⟨fun h => h = fullComplementHeap h_P (stripWx s0.mem)⟩
  have hpre_strip : stripWx s0.mem ⊨ (verifySignatureCallSpec P).pre g' s0 ∗ R_view :=
    ProofLib.Satisfies.sepConj_intro (disjoint_fullComplementHeap h_P (stripWx s0.mem)) hp_P rfl
      (Heap.Matches.union hm_P_swx (matches_fullComplementHeap h_P (stripWx s0.mem)))
  have hs0'_mem : (stripWxS s0).mem = stripWx s0.mem := by cases s0; rfl
  have hpre_s0' : (verifySignatureCallSpec P).pre g' (stripWxS s0) =
      (verifySignatureCallSpec P).pre g' s0 := by cases s0; rfl
  have hpre_P : s0.mem ⊨
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (verifySignatureCallSpec P)).pre g' s0 ∗ R := by
    dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hcl, hro⟩, hpre_call⟩
  have hpre_Q : (stripWxS s0).mem ⊨
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (verifySignatureCallSpec P)).pre g' (stripWxS s0) ∗ R_view := by
    dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
    rw [hpre_s0', hs0'_mem, sepConj_comm _ ⌜_⌝, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨libsignalCodeLoaded_stripWx hcl, libsignalRoLoaded_stripWx hro⟩, hpre_strip⟩
  have heq203 : ∀ X, (blkPC_203).rebase (blkPl_203).base X =
      libsignalSessionLib.blockProgram lsmpl 203 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := (blkPC_203).rebase (blkPl_203).base X)
  have hL0 : ((blkPC_203).rebase (blkPl_203).base (vsigOnlyHooks H)).CodeLoaded s0.mem := by
    rw [heq203]; exact hcl 203 (by decide) (by decide) (vsigOnlyHooks H) (fun _ => none) Syscall.standard
  rcases hbase0.no_fault_before_outcome g' R s0 hpc hrun hpre_P hsp hL0 with
    ⟨sf0, hsteps0, ⟨hret0, hcc0, hpost0⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩, _⟩
  · obtain ⟨tr0, htr0⟩ := steps_to_stepsList hsteps0
    have hbase_sh := verifySignature_placed_ok (H := shadowVsigHooks tr0 H) hprims
      (w3VerifySigHooks_shadow tr0 mmpl ghFixed W hG Y)
    have hLQ : ((blkPC_203).rebase (blkPl_203).base (shadowVsigHooks tr0 H)).CodeLoaded
        (stripWxS s0).mem := by
      rw [hs0'_mem, heq203]
      exact libsignalCodeLoaded_stripWx hcl 203 (by decide) (by decide) (shadowVsigHooks tr0 H)
        (fun _ => none) Syscall.standard
    rcases hbase_sh.no_fault_before_outcome g' R_view (stripWxS s0)
          (by cases s0; exact hpc) (by cases s0; exact hrun) hpre_Q (by cases s0; exact hsp) hLQ with
      ⟨sf', hsteps', ⟨hret', hcc', hpost'⟩ | ⟨_, hp⟩ | ⟨_, _, he⟩ | ⟨_, ho⟩, _⟩
    · obtain ⟨tr', htr'⟩ := steps_to_stepsList hsteps'
      obtain ⟨sf, hsf_eq | ⟨hsf'_eq, hanon⟩, hsteps_H, hvm⟩ :=
        steps_vsig_lockstep_vm tr0 mmpl ghFixed W hG htr0 hret0.2.2 [] rfl
          (by intro _ hu; cases hu) rfl htr' hret'.2.2 hcl
      · subst hsf_eq
        dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost0
        refine reaches_outcome_steps hsteps_H (reaches_outcome.of_outcome (Or.inl ⟨hret0, hcc0, ?_⟩))
        dsimp only [withLsCodeRoLoaded, verifySignatureInnerSpec, withVmPreserved]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        exact ⟨hvm, hpost0⟩
      · subst hsf'_eq
        dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hpost'
        have hpost_eq :
            (verifySignatureCallSpec P).post g' (stripWxS s0) (stripWxS sf) =
            (verifySignatureCallSpec P).post g' s0 sf := by cases s0; cases sf; rfl
        have hsf_mem : (stripWxS sf).mem = stripWx sf.mem := by cases sf; rfl
        have hpost'' : (stripWxS sf).mem ⊨
            (verifySignatureCallSpec P).post g' (stripWxS s0) (stripWxS sf) ∗ R_view := hpost'
        rw [hpost_eq, hsf_mem] at hpost''
        have hret : Returned s0 sf := by
          cases s0; cases sf; exact hret'
        have hcc : CallingConventionPreserved s0 sf := by
          cases s0; cases sf; exact hcc'
        refine reaches_outcome_steps hsteps_H (reaches_outcome.of_outcome (Or.inl ⟨hret, hcc, ?_⟩))
        dsimp only [withLsCodeRoLoaded, verifySignatureInnerSpec, withVmPreserved]
        rw [sepConj_assoc, satisfies_pure_sepConj]
        have hres : sf.mem ⊨ (verifySignatureCallSpec P).post g' s0 sf ∗ R :=
          unstrip_vsigPost_frame hP_rw (vsigPost_rwOnly P g' s0 sf) hdisj_PR hp_R
            (Heap.Matches.of_union_right hdisj_PR hm_PR) hvm.perm_eq hanon hpost''
        exact ⟨hvm, hres⟩
    · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        verifySignatureCallSpec] at hp
      exact False.elim (not_satisfies_false_sepConj hp)
    · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        verifySignatureCallSpec] at he
      exact False.elim (not_satisfies_false_sepConj he)
    · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
        verifySignatureCallSpec] at ho
      exact False.elim (not_satisfies_false_sepConj ho)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      verifySignatureCallSpec] at hp
    exact False.elim (not_satisfies_false_sepConj hp)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      verifySignatureCallSpec] at he
    exact False.elim (not_satisfies_false_sepConj he)
  · dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded,
      verifySignatureCallSpec] at ho
    exact False.elim (not_satisfies_false_sepConj ho)

/-- Block-203 `<PublicKey>::verify_signature` contract with `VmPreserved` on `initProgPlaced mmpl ghFixed W`. -/
theorem w3m_verifySignature_vm_ok [LibsignalFullPlacement]
    {mmpl : MultiPlacement} (ghFixed : CliGhostHooks) (W : CliHooks)
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (hG : CliGhostAllocHooks M A lim ghFixed)
    (Y : UnreachedPqxdhPrimitives) :
    subroutine_ok (initProgPlaced mmpl ghFixed W) (lsmpl.base 203)
      (withLsCodeRoLoaded lsmpl (verifySignatureInnerSpec (modelPrims Y ⟨W.C, W.Q⟩))) :=
  transfer_withLsCodeRoLoaded
    (calleeProg := (blkPC_203).rebase (blkPl_203).base
      (cliGhostExterns ghFixed (cliExternsPlaced mmpl W)))
    (verifySignature_203_vm_ok ghFixed W hG Y)

end LibsignalBinary.Proofs.SpecLemmas.SignalSession.Hole3W3VerifySigAux
