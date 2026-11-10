/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat -- proof-setup: allow-public-import
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Transfer
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedExt

/-!
# `HookSat` Sibling of `CryptoBridgePlacedBudgetAux`, Part A (`CryptoBridgePlacedBudgetAuxASat`)

Proves `RunsToVm`, single-hook steps, and `VmPreserved` + `S2Frame` execution
(`finalize_fixed_placed_runsToVm_sat`) for `finalize_fixed` (Block `123`) under
`[HkdfPlacedHooksBudgetSat C.F H]` (`HookSat H lsMemsetSym sessionMemsetRegionBudgetSpec`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement
   libsignalMutatedBlocks libsignalSessionLib
   ls_externAt?_blockProgram_eq_of_externs_eq
   lsmpl lsρ withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (memcpyHook toLEBytes)
open CryptoVerification.LibsignalHmac (compress256Hook shaStateBytes)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved FinSaved Frame HmacSt
   RW RunsTo RunsToFrom TraceEq agreesOutside_seg2a agreesOutside_seg3a agreesOutside_seg4a
   bit_len_inner_eq blkLib_123 blkLib_eq_123
   blkPC_123 blkPl_123 compress256Hook_eq
   digestBytes digestBytes_eq_append finPlacedFakeB finPlacedFakeB_off_0 finSaved_seg3a finSaved_seg4a
   frame_seg2a frame_seg3a frame_seg4a fsp_aligned
   hmacInnerInit hmacOuterInit hmacWith_short innerLastBlock innerLastBlock_length
   lsCompress256Sym lsMemcpySym lsMemsetSym ls_externAt?_of_mem
   memcpyHook_eq outerBlock outerBlock_digestBytes_length
   read32_words_at_104_of_shaStateBytes read32_words_at_64_of_shaStateBytes
   read64_seg2a_mid read64_seg3a_pad_32 read64_seg3a_pad_40
   readBytes_56_eq_append_8 readBytes_56_of_buf_eq
   readBytes_fsp_64_seg2 readBytes_fsp_64_seg3 readBytes_write32_8_digestBytes
   shaStateBytes_length
   toLEBytes_4_rev32 toLEBytes_8_read64 toLEBytes_8_rev32_append toLEBytes_8_rev64
   ult_7_of_lt_56 xor_63_of_lt_64 zeroExtend64_ofNat8 zeroExtend64_truncate32_ofNat64)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x20
   CallingConventionPreserved.x21 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29 S2Frame)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof (FinPre)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt
  (AgreesOn.finSaved_of AgreesOn.read64_eq AgreesOn.readBytes_eq)
open CryptoVerification.LibsignalTripleRatchet.HkdfExt.FinX (read32_seg4a_mid_x)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (checkBlockNoMsrTpidrEl0 hmacCompressOnlyExcHooks hmacCompressOnlyExcHooks_compress
   hmacNoMemsetExcHooks hmacNoMemsetExcHooks_compress hmacNoMemsetExcHooks_memcpy
   placed_memset_budget_steps_sat runsTo_block_lift_vm_compress_only
   runsTo_block_lift_vm_no_memset)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooksBudgetSat HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (CallingConventionPreserved.x23 CallingConventionPreserved.x24 CallingConventionPreserved.x25
   CallingConventionPreserved.x26 CallingConventionPreserved.x28)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixedSat (FinPostSat)

attribute [local arm64_norm] MemWidth.bytes SimdMemSize.bytes

/-! ## 1. `RunsToVm`, Single-Hook Steps & `memset`-Free Block Lifting -/

/-- `RunsTo` strengthened with `VmPreserved` and split `trace` / `calleeSavedVRegs` preservation. -/
@[expose] public def RunsToVm (P : Program) (s : State) (Q : State → Prop) : Prop :=
  P.CodeLoaded s.mem →
  ∃ sf : State,
    Steps P s sf ∧ VmPreserved s sf ∧ sf.trace = s.trace ∧
    calleeSavedVRegs sf = calleeSavedVRegs s ∧ Q sf ∧ P.CodeLoaded sf.mem

public theorem RunsToVm.refl {P : Program} {s : State} {Q : State → Prop} (hq : Q s) :
    RunsToVm P s Q :=
  fun hL => ⟨s, .refl s, VmPreserved.refl s, rfl, rfl, hq, hL⟩

public theorem RunsToVm.mono {P : Program} {s : State} {Q1 Q2 : State → Prop}
    (h : RunsToVm P s Q1) (himp : ∀ sf, Q1 sf → Q2 sf) :
    RunsToVm P s Q2 :=
  fun hL =>
    let ⟨sf, hst, hvm, htr, hv, hq, hLf⟩ := h hL
    ⟨sf, hst, hvm, htr, hv, himp sf hq, hLf⟩

public theorem RunsToVm.trans_full {P : Program} {s : State} {Q1 Q2 : State → Prop}
    (h1 : RunsToVm P s Q1)
    (h2 : ∀ s1, Q1 s1 → s.mem.KeepsFrozen s1.mem → RunsToVm P s1 Q2) :
    RunsToVm P s Q2 :=
  fun hL =>
    let ⟨s1, hst1, hvm1, htr1, hv1, hq1, hL1⟩ := h1 hL
    let ⟨s2, hst2, hvm2, htr2, hv2, hq2, hL2⟩ := h2 s1 hq1 hst1.keepsFrozen hL1
    ⟨s2, hst1.trans hst2, hvm1.trans hvm2, htr2.trans htr1, hv2.trans hv1, hq2, hL2⟩

/-- Transfer `RunsToVm` from placed block `j` to any caller block `i` sharing `H`. -/
public theorem RunsToVm.of_other_block [LibsignalPlacement] {H : LibsignalHooks}
    {i j : Nat} {Pi Pj : Program}
    [hcaller : IsLsBlockProg Pi i H] [hcallee : IsLsBlockProg Pj j H]
    (hj_lt : j < 624) (hj_unmut : (j ∈ libsignalMutatedBlocks) = false)
    {s : State} {Q : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (h : RunsToVm Pj s Q) :
    RunsToVm Pi s Q := by
  intro hLi
  have hLj : Pj.CodeLoaded s.mem :=
    hcallee.eq_blockProgram ▸ hcl j hj_lt hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hst_j, hvm, htr, hv, hq, _⟩ := h hLj
  have hext : ∀ pc, Pj.externAt? pc = Pi.externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : Pj.svc = Pi.svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_i := Steps.of_sameHooks hext hsvc hst_j
  exact ⟨sf, hst_i, hvm, htr, hv, hq, hst_i.codeLoaded hLi⟩

public theorem blk123_noSvc0 :
    VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib_123.text = true := by decide +kernel
public theorem blk123_noMsr :
    checkBlockNoMsrTpidrEl0 blkLib_123.text = true := by decide +kernel

private theorem runsTo_to_hmac {P : Program} {s : State} {Q : State → Prop} (h : RunsTo P s Q) :
    CryptoVerification.LibsignalSession.CryptoHmacSha256.RunsTo P s Q :=
  fun hL => let ⟨s', hst, ⟨htr, hv⟩, hq, hL'⟩ := h hL; ⟨s', hst, htr, hv, hq, hL'⟩

/-- Lift a `memset`-free `RunsTo` segment on block `j` onto any caller block `Pi` (`[IsLsBlockProg Pi i H]`). -/
public theorem lift_block_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksBudgetSat C.F H]
    {i j : Nat} {blkLib : Obj.PlacedLib} {Pi Pj : Program}
    [hcaller : IsLsBlockProg Pi i H] [hcallee : IsLsBlockProg Pj j H]
    (hlib : blkLib = libsignalSessionLib.blockLib j)
    (hchk_svc : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib.text = true)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true)
    (hj_lt : j < 624) (hj_unmut : (j ∈ libsignalMutatedBlocks) = false)
    {s : State} {PostP PostQ : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hrunsP : RunsTo (libsignalSessionLib.blockProgram lsmpl j H) s PostP)
    (hrunsQ : RunsTo (libsignalSessionLib.blockProgram lsmpl j (hmacNoMemsetExcHooks C.F H))
      (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j (hmacNoMemsetExcHooks C.F H))) s) PostQ)
    (hrunP : ∀ s', PostP s' → s'.status = .Running)
    (hrunQ : ∀ s', PostQ s' → s'.status = .Running)
    (hunstrip : ∀ sf, VmPreserved s sf →
      PostQ (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j (hmacNoMemsetExcHooks C.F H))) sf) → PostP sf) :
    RunsToVm Pi s PostP := by
  intro hLi
  have hLj : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s.mem :=
    hcl j hj_lt hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hst_j, hvm, htr, hvregs, hor⟩ :=
    runsTo_block_lift_vm_no_memset hH.memcpy hH.compress256 hlib hchk_svc hchk_msr
      hLj (runsTo_to_hmac hrunsP) (runsTo_to_hmac hrunsQ) hrunP hrunQ
  have hPost : PostP sf := by
    rcases hor with hq | hp
    · exact hunstrip sf hvm hq
    · exact hp
  have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
      Pi.externAt? pc := fun pc => by
    rw [hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = Pi.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  have hst_i := Steps.of_sameHooks hext hsvc hst_j
  exact ⟨sf, hst_i, hvm, htr, hvregs, hPost, hst_i.codeLoaded hLi⟩

/-- `compress256`-only sibling of `lift_block_vm`: lifts a `memset`- and `memcpy`-free `RunsTo`
segment on block `j` onto any caller block `Pi` under `[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem lift_block_vm_compress_only [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {i j : Nat} {blkLib : Obj.PlacedLib} {Pi Pj : Program}
    [hcaller : IsLsBlockProg Pi i H] [hcallee : IsLsBlockProg Pj j H]
    (hlib : blkLib = libsignalSessionLib.blockLib j)
    (hchk_svc : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib.text = true)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true)
    (hj_lt : j < 624) (hj_unmut : (j ∈ libsignalMutatedBlocks) = false)
    {s : State} {PostP PostQ : State → Prop}
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hrunsP : RunsTo (libsignalSessionLib.blockProgram lsmpl j H) s PostP)
    (hrunsQ : RunsTo (libsignalSessionLib.blockProgram lsmpl j (hmacCompressOnlyExcHooks C.F H))
      (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j (hmacCompressOnlyExcHooks C.F H))) s) PostQ)
    (hrunP : ∀ s', PostP s' → s'.status = .Running)
    (hrunQ : ∀ s', PostQ s' → s'.status = .Running)
    (hunstrip : ∀ sf, VmPreserved s sf →
      PostQ (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl j (hmacCompressOnlyExcHooks C.F H))) sf) → PostP sf) :
    RunsToVm Pi s PostP := by
  intro hLi
  have hLj : (libsignalSessionLib.blockProgram lsmpl j H).CodeLoaded s.mem :=
    hcl j hj_lt hj_unmut H (fun _ => none) Syscall.standard
  obtain ⟨sf, hst_j, hvm, htr, hvregs, hor⟩ :=
    runsTo_block_lift_vm_compress_only hH.compress256 hlib hchk_svc hchk_msr
      hLj (runsTo_to_hmac hrunsP) (runsTo_to_hmac hrunsQ) hrunP hrunQ
  have hPost : PostP sf := by
    rcases hor with hq | hp
    · exact hunstrip sf hvm hq
    · exact hp
  have hext : ∀ pc, (libsignalSessionLib.blockProgram lsmpl j H).externAt? pc =
      Pi.externAt? pc := fun pc => by
    rw [hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : (libsignalSessionLib.blockProgram lsmpl j H).svc = Pi.svc := by
    rw [hcaller.eq_blockProgram]; rfl
  have hst_i := Steps.of_sameHooks hext hsvc hst_j
  exact ⟨sf, hst_i, hvm, htr, hvregs, hPost, hst_i.codeLoaded hLi⟩

/-- Step through 1-block `compress256` from `H lsCompress256Sym = some (compress256Hook F)` alone. -/
public theorem s2_compress256_step_of_eq [LibsignalPlacement] {prog : Program} {i : Nat}
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s : State} {Q : State → Prop}
    {stPtr blkPtr lr : BitVec 64} {st : ShaState} {blk : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsCompress256Sym)
    (hx0 : s.readReg64 .x0 = stPtr)
    (hx1 : s.readReg64 .x1 = blkPtr)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hlr : s.readReg64 .lr = lr)
    (hst : s.mem.readBytes stPtr 32 = shaStateBytes st)
    (hblk : s.mem.readBytes blkPtr 64 = blk)
    (hlen : blk.length = 64)
    (hrw : s.mem.RW stPtr 32)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes stPtr (shaStateBytes (F st blk)))).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hcan : s.mem.canWrite stPtr (shaStateBytes (F st blk)).length = true := by
    rw [shaStateBytes_length]
    exact hrw.canWrite_sub (by simp) (by decide)
  have hhook : prog.externAt? s.pc = some (compress256Hook F) := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, h_c256]
  have hstate := compress256Hook_eq F hx0 hx1 hx2 hlr hst hblk hlen
  have hkeep : s.mem.KeepsFrozen (compress256Hook F s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (compress256Hook F s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

/-- Step through `memcpy` from `H lsMemcpySym = some memcpyHook` alone. -/
public theorem s2_memcpy_step_of_eq [LibsignalPlacement] {prog : Program} {i : Nat}
    {H : LibsignalHooks} [IsLsBlockProg prog i H]
    (h_mc : H lsMemcpySym = some memcpyHook)
    {s₀ s : State} {Q : State → Prop}
    {dst src lr : BitVec 64} {len : Nat} {bs : List (BitVec 8)}
    (hrun : s.status = .Running)
    (hpc : s.pc = lsρ lsMemcpySym)
    (hx0 : s.readReg64 .x0 = dst)
    (hx1 : s.readReg64 .x1 = src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hlr : s.readReg64 .lr = lr)
    (hread : s.mem.readBytes src len = bs)
    (hrw : s.mem.RW dst len)
    (h : RunsToFrom prog s₀
      ((s.setMem (s.mem.writeBytes dst bs)).setPC lr) Q)
    (hi : i < 619 := by decide) (hunmut : (i ∈ libsignalMutatedBlocks) = false := by decide) :
    RunsToFrom prog s₀ s Q := by
  have hlen_bs : bs.length = len := by rw [← hread, Memory.readBytes_length]
  have hlen_le : len ≤ 2 ^ 64 := by rw [← hx2]; have := (s.readReg64 .x2).isLt; omega
  have hcan : s.mem.canWrite dst bs.length = true := by
    rw [hlen_bs]
    exact hrw.canWrite_sub (by simp) hlen_le
  have hhook : prog.externAt? s.pc = some memcpyHook := by
    rw [hpc, ls_externAt?_of_mem (by decide) hi hunmut, h_mc]
  have hstate := memcpyHook_eq hx0 hx1 hx2 hlr hread
  have hkeep : s.mem.KeepsFrozen (memcpyHook s).mem := by
    rw [hstate]; exact Memory.keepsFrozen_writeBytes _ hcan
  have hsym : (memcpyHook s).symtab = s.symtab := by rw [hstate]; rfl
  refine RunsTo.hook hrun hhook hkeep hsym ?_
  rwa [hstate]

public theorem mem_setMem (s : State) (m : Memory) : (s.setMem m).mem = m := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_0_64_zero128 : BitVec.extractLsb' 0 64 0#128 = 0#64 := rfl

@[local simp, local arm64_norm]
private theorem extractLsb'_64_64_zero128 : BitVec.extractLsb' 64 64 0#128 = 0#64 := rfl

public theorem stripS_mem (kp : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS kp s).mem = ProofLib.stripExecOutside kp s.mem := by cases s; rfl

public theorem stripS_read8 (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS kp s).mem.read8 a = s.mem.read8 a := by
  cases s; simp [ProofLib.stripS, ProofLib.strip_read8]

public theorem stripS_read64 (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS kp s).mem.read64 a = s.mem.read64 a := by
  cases s; simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

public theorem stripS_readBytes (kp : BitVec 64 → Bool) (s : State) (a : BitVec 64) (n : Nat) :
    (ProofLib.stripS kp s).mem.readBytes a n = s.mem.readBytes a n := by
  rw [stripS_mem, stripExecOutside_readBytes]

public theorem stripS_hmacSt (kp : BitVec 64 → Bool)
    {F : ShaState → List (BitVec 8) → ShaState} {s : State} {a : BitVec 64}
    {key msg : List (BitVec 8)} :
    HmacSt (ProofLib.stripS kp s).mem a F key msg ↔ HmacSt s.mem a F key msg := by
  unfold HmacSt
  simp only [stripS_read8, stripS_read64, stripS_readBytes]

public theorem stripS_finSaved (kp : BitVec 64 → Bool) (s0 s : State) :
    FinSaved (ProofLib.stripS kp s0) ((ProofLib.stripS kp s0).sp - 144#64)
      (ProofLib.stripS kp s).mem ↔
    FinSaved s0 (s0.sp - 144#64) s.mem := by
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  unfold FinSaved
  simp only [hsp0, hr, stripS_read64]

public structure FinCommon (s0 s : State) : Prop where
  status : s.status = .Running
  sp_eq  : s.sp = s0.sp - 144#64
  x29_eq : s.readReg64 .x29 = s0.sp - 144#64 + 0x40#64
  x26_eq : s.readReg64 .x26 = s0.readReg64 .x26
  x27_eq : s.readReg64 .x27 = s0.readReg64 .x27
  x28_eq : s.readReg64 .x28 = s0.readReg64 .x28
  saved  : FinSaved s0 (s0.sp - 144#64) s.mem
  frame  : Frame s0.mem s.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)]

@[expose] public def FinPost (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s' : State) : Prop :=
  s'.pc = s0.readReg64 .lr ∧
  s'.status = .Running ∧
  CalleeSaved s0 s' ∧
  s'.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg ∧
  Frame s0.mem s'.mem
    [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)]

public theorem rw_of_perm_eq {m m' : Memory} {regs : List (BitVec 64 × ℕ)} {a : BitVec 64} {n : ℕ}
    (hfr : Frame m m' regs)
    (hrw : m.RW a n) : m'.RW a n :=
  (S2Frame.of_frame hfr).rw_of_rw a n hrw

public theorem unstrip_finCommon {kp : BitVec 64 → Bool} {s0 s : State}
    (hc : FinCommon (ProofLib.stripS kp s0) (ProofLib.stripS kp s))
    (hperm : ∀ a, s.mem.perm a = s0.mem.perm a) :
    FinCommon s0 s := by
  rcases hc with ⟨hst, hsp_c, hx29, hx26, hx27, hx28, hsav, hfr⟩
  have hr0 : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  rw [stripS_mem, stripS_mem, hr0, hr0, hsp0] at hfr
  exact ⟨(by cases s; exact hst), (by cases s0; cases s; exact hsp_c),
    (by cases s0; cases s; exact hx29), (by cases s0; cases s; exact hx26),
    (by cases s0; cases s; exact hx27), (by cases s0; cases s; exact hx28),
    (stripS_finSaved kp s0 s).mp hsav, unstrip_frame hfr hperm⟩

/-! ## 2. Block `123` (`finalize_fixed`) `RunsToVm` under `HkdfPlacedHooksBudgetSat` -/

private theorem read64_write64_add_same (m : Memory) (fsp c v : BitVec 64) :
    (m.write64 (fsp + c) v).read64 (fsp + c) = v :=
  Memory.read64_write64_same m (fsp + c) v

private theorem read64_write64_add_ne (m : Memory) (fsp c1 c2 v : BitVec 64)
    (h : decide (8 ≤ (c1 - c2).toNat ∧ 8 ≤ (c2 - c1).toNat) = true) :
    (m.write64 (fsp + c1) v).read64 (fsp + c2) = m.read64 (fsp + c2) := by
  have hc := of_decide_eq_true h
  exact Memory.read64_write64_disjoint m (fsp + c1) (fsp + c2) v (by bv_omega) (by bv_omega)

public theorem finSaved_of_seg1a (s0 : State) (m : Memory) :
    FinSaved s0 (s0.sp - 144#64)
      (((((((((m.write64 (s0.sp - 144#64 + 64#64) (s0.readReg64 .x29)).write64
        (s0.sp - 144#64 + 72#64) (s0.readReg64 .lr)).write64
        (s0.sp - 144#64 + 80#64) (s0.readReg64 .x25)).write64
        (s0.sp - 144#64 + 96#64) (s0.readReg64 .x24)).write64
        (s0.sp - 144#64 + 104#64) (s0.readReg64 .x23)).write64
        (s0.sp - 144#64 + 112#64) (s0.readReg64 .x22)).write64
        (s0.sp - 144#64 + 120#64) (s0.readReg64 .x21)).write64
        (s0.sp - 144#64 + 128#64) (s0.readReg64 .x20)).write64
        (s0.sp - 144#64 + 136#64) (s0.readReg64 .x19)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · iterate 8 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 7 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 6 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 5 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 4 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 3 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · iterate 2 rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · rw [read64_write64_add_ne _ _ _ _ _ (by decide)]
    exact read64_write64_add_same _ _ _ _
  · exact read64_write64_add_same _ _ _ _

local macro "fin_reg_local" : tactic =>
  `(tactic| (
    try rw [State.readReg64_setMem]
    try rw [State.pc_setMem]
    try rw [State.sp_setMem]
    try rw [State.status_setMem]
    simp (config := { decide := true }) only [arm64_norm, *]))

private structure StateF0p [LibsignalPlacement] (b : BitVec 64)
    (F : ShaState → List (BitVec 8) → ShaState) (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 28#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x0
  x1_eq   : s.readReg64 .x1 = s0.readReg64 .x1
  hmac_st : HmacSt s.mem (s0.readReg64 .x1) F key msg

private structure StateF1 [LibsignalPlacement] (b : BitVec 64)
    (F : ShaState → List (BitVec 8) → ShaState) (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 76#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  x23_eq  : s.readReg64 .x23 = BitVec.ofNat 64 msg.length
  x24_eq  : s.readReg64 .x24 = 1#64
  x25_eq  : s.readReg64 .x25 = BitVec.ofNat 64 (63 - msg.length)
  buf_eq  : s.mem.readBytes (s0.readReg64 .x1) 64 =
    msg ++ [0x80#8] ++ List.replicate (63 - msg.length) 0#8
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF2 [LibsignalPlacement] (b : BitVec 64)
    (F : ShaState → List (BitVec 8) → ShaState) (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 176#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x40#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 = innerLastBlock msg
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF3 [LibsignalPlacement] (b : BitVec 64)
    (F : ShaState → List (BitVec 8) → ShaState) (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 180#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq  : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq  : s.readReg64 .x22 = 0x80#64
  ist_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 =
    shaStateBytes (F (hmacInnerInit F key) (innerLastBlock msg))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq  : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure StateF3b [LibsignalPlacement] (b : BitVec 64)
    (F : ShaState → List (BitVec 8) → ShaState) (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 304#64
  common  : FinCommon s0 s
  x0_eq   : s.readReg64 .x0 = s0.readReg64 .x1 + 0x68#64
  x1_eq   : s.readReg64 .x1 = s0.sp - 144#64
  x2_eq   : s.readReg64 .x2 = 1#64
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  blk_eq  : s.mem.readBytes (s0.sp - 144#64) 64 =
    outerBlock (digestBytes (F (hmacInnerInit F key) (innerLastBlock msg)))
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)

private structure StateF4 [LibsignalPlacement] (b : BitVec 64)
    (F : ShaState → List (BitVec 8) → ShaState) (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq   : s.pc = (blkPl_123).base + 308#64
  common  : FinCommon s0 s
  x19_eq  : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq  : s.readReg64 .x20 = s0.readReg64 .x1
  ost_eq  : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 =
    shaStateBytes (F (hmacOuterInit F key)
      (outerBlock (digestBytes (F (hmacInnerInit F key) (innerLastBlock msg)))))

private structure StateF5 [LibsignalPlacement] (b : BitVec 64)
    (F : ShaState → List (BitVec 8) → ShaState) (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = (blkPl_123).base + 420#64
  common : FinCommon s0 s
  out_eq : s.mem.readBytes (s0.readReg64 .x0) 32 = hmacWith F key msg

private structure StateFPreMemset123 [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (key msg : List (BitVec 8)) (s0 s : State) : Prop where
  pc_eq  : s.pc = lsρ lsMemsetSym
  common : FinCommon s0 s
  lr_eq  : s.readReg64 .lr = (blkPl_123).base + 76#64
  x0_eq  : s.readReg64 .x0 = s0.readReg64 .x1 + BitVec.ofNat 64 msg.length + 1#64
  x1_eq  : (s.readReg64 .x1).truncate 8 = 0#8
  x2_eq  : (s.readReg64 .x2).toNat = 63 - msg.length
  x19_eq : s.readReg64 .x19 = s0.readReg64 .x0
  x20_eq : s.readReg64 .x20 = s0.readReg64 .x1
  x21_eq : s.readReg64 .x21 = s0.readReg64 .x1 + 0x40#64
  x22_eq : s.readReg64 .x22 = 0x80#64
  x23_eq : s.readReg64 .x23 = BitVec.ofNat 64 msg.length
  x24_eq : s.readReg64 .x24 = 1#64
  x25_eq : s.readReg64 .x25 = BitVec.ofNat 64 (63 - msg.length)
  pad_eq : s.mem.readBytes (s0.readReg64 .x1) (msg.length + 1) = msg ++ [0x80#8]
  ist_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x40#64) 32 = shaStateBytes (hmacInnerInit F key)
  ost_eq : s.mem.readBytes (s0.readReg64 .x1 + 0x68#64) 32 = shaStateBytes (hmacOuterInit F key)
  obl_eq : s.mem.read64 (s0.readReg64 .x1 + 0x88#64) = 1#64

private structure FinMidPre123 (key msg : List (BitVec 8)) (s0 : State) : Prop where
  key_le      : key.length ≤ 64
  msg_lt      : msg.length < 56
  rw_out      : RW s0.mem (s0.readReg64 .x0) 32
  rw_hm       : RW s0.mem (s0.readReg64 .x1) 0x90
  rw_fsp      : RW s0.mem (s0.sp - 144#64) 144
  disj_out_fsp : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64) 144
  disj_hm_fsp : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64) 144
  sp_aligned  : (s0.sp &&& 0b1111#64) = 0#64

private theorem FinMidPre123.stripS {key msg : List (BitVec 8)} {s0 : State}
    (h : FinMidPre123 key msg s0) (kp : BitVec 64 → Bool) :
    FinMidPre123 key msg (ProofLib.stripS kp s0) := by
  have hr : ∀ r, (ProofLib.stripS kp s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hsp0 : (ProofLib.stripS kp s0).sp = s0.sp := by cases s0; rfl
  exact
    { key_le := h.key_le, msg_lt := h.msg_lt,
      rw_out := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp s0.mem _ _ h.rw_out,
      rw_hm := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp s0.mem _ _ h.rw_hm,
      rw_fsp := by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp s0.mem _ _ h.rw_fsp,
      disj_out_fsp := by rw [hr, hsp0]; exact h.disj_out_fsp,
      disj_hm_fsp := by rw [hr, hsp0]; exact h.disj_hm_fsp,
      sp_aligned := by rw [hsp0]; exact h.sp_aligned }

private theorem seg1a_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s0 (StateF0p finPlacedFakeB C.F key msg s0) := by
  have hpc : s0.pc = (blkPl_123).base := by simpa only [finPlacedFakeB_off_0] using hpre.pc_eq
  have hstat := hpre.status
  have hal0 : (s0.sp &&& 15#64) = 0#64 := hpre.sp_aligned
  have hal_fsp : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hpre.sp_aligned
  have hrw_fsp : s0.mem.RW (s0.sp - 144#64) 144 := hpre.rw_fsp
  iterate 7 s2_step
  refine RunsTo.refl ?_
  have hag : AgreesOutside s0.mem
      (((((((((s0.mem.write64 (s0.sp - 144#64 + 64#64) (s0.readReg64 .x29)).write64
        (s0.sp - 144#64 + 72#64) (s0.readReg64 .lr)).write64
        (s0.sp - 144#64 + 80#64) (s0.readReg64 .x25)).write64
        (s0.sp - 144#64 + 96#64) (s0.readReg64 .x24)).write64
        (s0.sp - 144#64 + 104#64) (s0.readReg64 .x23)).write64
        (s0.sp - 144#64 + 112#64) (s0.readReg64 .x22)).write64
        (s0.sp - 144#64 + 120#64) (s0.readReg64 .x21)).write64
        (s0.sp - 144#64 + 128#64) (s0.readReg64 .x20)).write64
        (s0.sp - 144#64 + 136#64) (s0.readReg64 .x19))
      (s0.sp - 144#64) 144 := by
    agrees_outside_writes
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by rw [mem_setMem]; exact finSaved_of_seg1a s0 s0.mem
          frame := by rw [mem_setMem]; exact Frame.trans_agreesOutside (Frame.refl s0.mem _) (by simp) hag }
      x0_eq := by fin_reg_local
      x1_eq := by fin_reg_local
      hmac_st := by rw [mem_setMem]; exact HmacSt.of_agreesOutside hpre.hmac_st hag hpre.disj_hm_fsp.symm }

private theorem seg1b_pre_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 s : State}
    (hpre : FinPre finPlacedFakeB C.F key msg s0)
    (hs : StateF0p finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateFPreMemset123 C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hhmac⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  rcases hhmac with ⟨hmsg_lt64, hmsg_eq, hpos_eq, hin_eq, hibl_eq, hout_eq, hobl_eq⟩
  have hpc' : s.pc = (blkPl_123).base + 28#64 := hpc
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hpre.rw_hm
  have hcw_pos : s.mem.canWrite (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1 = true :=
    hrw_hm.canWrite_sub (by bv_omega) (by decide)
  have hze32 := zeroExtend64_truncate32_ofNat64 hmsg_lt64
  have hze64 := zeroExtend64_ofNat8 hmsg_lt64
  have hxor63 := xor_63_of_lt_64 hmsg_lt64
  iterate 12 s2_step
  have htoNat_sub : (BitVec.ofNat 64 (63 - msg.length)).toNat = 63 - msg.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  refine RunsTo.refl ?_
  set m_pre := s.mem.write8 (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 128#8
  have hag_pre : AgreesOutside s.mem m_pre (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1 := by
    dsimp only [m_pre]; agrees_outside_writes
  have hd_pre_saved : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1
      (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hpre.disj_hm_fsp.sub_left _ ⟨by decide, by have := hpre.msg_lt; bv_omega⟩).sub_right _
      ⟨by decide, by bv_omega⟩
  have hd_pre_ist : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have := hpre.msg_lt; unfold DisjointRegions; bv_omega
  have hd_pre_ost : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    have := hpre.msg_lt; unfold DisjointRegions; bv_omega
  have hd_pre_obl : DisjointRegions (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1
      (s0.readReg64 .x1 + 0x88#64) 8 := by
    have := hpre.msg_lt; unfold DisjointRegions; bv_omega
  have hpad : m_pre.readBytes (s0.readReg64 .x1) (msg.length + 1) = msg ++ [0x80#8] := by
    rw [readBytes_add m_pre (s0.readReg64 .x1) msg.length 1]
    have hl : m_pre.readBytes (s0.readReg64 .x1) msg.length = msg := by
      by_cases h0 : msg.length = 0
      · cases msg with | nil => rfl | cons _ _ => cases h0
      · refine (hag_pre.readBytes_eq ?_ (by have := hpre.msg_lt; omega)).trans hmsg_eq
        have := hpre.msg_lt; unfold DisjointRegions; bv_omega
    have hr : m_pre.readBytes (s0.readReg64 .x1 + BitVec.ofNat 64 msg.length) 1 = [0x80#8] := by
      dsimp only [m_pre]
      simp [Memory.readBytes, Memory.read8_write8_same]
    rw [hl, hr]
  refine
    { pc_eq := rfl
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by rw [mem_setMem]; exact FinSaved.of_agreesOutside hsaved hag_pre hd_pre_saved
          frame := by
            rw [mem_setMem]
            have := hpre.msg_lt
            exact Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
              (by simp) (by bv_omega) hag_pre }
      lr_eq := by fin_reg_local
      x0_eq := by simp only [arm64_norm]
      x1_eq := by simp (config := { decide := true }) only [arm64_norm]
      x2_eq := by simpa only [arm64_norm] using htoNat_sub
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local, x21_eq := by fin_reg_local,
      x22_eq := by fin_reg_local, x23_eq := by fin_reg_local, x24_eq := by fin_reg_local,
      x25_eq := by fin_reg_local
      pad_eq := by rw [mem_setMem]; exact hpad
      ist_eq := by rw [mem_setMem]; exact (hag_pre.readBytes_eq hd_pre_ist (by decide)).trans hin_eq
      ost_eq := by rw [mem_setMem]; exact (hag_pre.readBytes_eq hd_pre_ost (by decide)).trans hout_eq
      obl_eq := by rw [mem_setMem]; exact (hag_pre.read64_eq hd_pre_obl).trans hobl_eq }

private theorem seg2a_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 s : State}
    (hmid : FinMidPre123 key msg s0)
    (hs : StateF1 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateF2 finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hpc' : s.pc = (blkPl_123).base + 76#64 := hpc
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe hmid.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hmid.sp_aligned
  have hult_7 := ult_7_of_lt_56 hmid.msg_lt
  obtain ⟨hbit_len1, hbit_len2⟩ := bit_len_inner_eq hmid.msg_lt
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  iterate 6 s2_step
  have hread32 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 32#64 (by decide) hd_hm64_fsp64
  have hread40 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 40#64 (by decide) hd_hm64_fsp64
  have hread48 := fun u0 u1 u2 u3 w56 =>
    read64_seg2a_mid s.mem _ _ u0 u1 u2 u3 w56 48#64 (by decide) hd_hm64_fsp64
  iterate 7 s2_step
  clear hread32 hread40 hread48
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3⟩ := agreesOutside_seg2a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ist : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x40#64) 32 :=
    (hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ist : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x40#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_fsp64_obl : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x88#64) 8 :=
    (hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_obl : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact FinSaved.of_agreesOutside
              (FinSaved.of_agreesOutside (FinSaved.of_agreesOutside hsaved hag1 hd_fsp64_saved)
                hag2 hd_hm64_saved) hag3 hd_fsp64_saved
          frame := by rw [mem_setMem]; exact frame_seg2a hframe hag1 hag2 hag3 }
      x0_eq := by fin_reg_local, x1_eq := by fin_reg_local, x2_eq := by fin_reg_local,
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local,
      x21_eq := by fin_reg_local, x22_eq := by fin_reg_local
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg2 _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64,
            toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_read64, toLEBytes_8_rev64,
            readBytes_56_eq_append_8 s.mem (s0.readReg64 .x1),
            readBytes_56_of_buf_eq s.mem (s0.readReg64 .x1) msg hbuf hmid.msg_lt]
        rfl
      ist_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ist (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ist (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ist (by decide)).trans hist))
      ost_eq := by
        rw [mem_setMem]
        exact (hag3.readBytes_eq hd_fsp64_ost (by decide)).trans
          ((hag2.readBytes_eq hd_hm64_ost (by decide)).trans
            ((hag1.readBytes_eq hd_fsp64_ost (by decide)).trans host))
      obl_eq := by
        rw [mem_setMem]
        exact (hag3.read64_eq hd_fsp64_obl).trans
          ((hag2.read64_eq hd_hm64_obl).trans
            ((hag1.read64_eq hd_fsp64_obl).trans hobl)) }

private theorem seg2b_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    (h_c256 : Hk lsCompress256Sym = some (compress256Hook C.F))
    {key msg : List (BitVec 8)} {s0 s : State}
    (hmid : FinMidPre123 key msg s0)
    (hs : StateF2 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateF3 finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hblk, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hpc' : s.pc = (blkPl_123).base + 176#64 := hpc
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_ist : s.mem.RW (s0.readReg64 .x1 + 0x40#64) 32 := hrw_hm.sub (by bv_omega)
  s2_step
  refine s2_compress256_step_of_eq h_c256
    (stPtr := s0.readReg64 .x1 + 0x40#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 180#64) (st := hmacInnerInit C.F key) (blk := innerLastBlock msg)
    hstat rfl
    (by fin_reg_local) (by fin_reg_local) (by fin_reg_local) rfl
    hist hblk (innerLastBlock_length hmid.msg_lt) hrw_ist ?_
  refine RunsTo.refl ?_
  set blk_in := shaStateBytes (C.F (hmacInnerInit C.F key) (innerLastBlock msg))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x40#64) blk_in)
      (s0.readReg64 .x1 + 0x40#64) 32 := by
    have hlen : blk_in.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_in
  have hd_ist_saved : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_ist_ost : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  have hd_ist_obl : DisjointRegions (s0.readReg64 .x1 + 0x40#64) 32 (s0.readReg64 .x1 + 0x88#64) 8 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ist_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local,
      x21_eq := by fin_reg_local, x22_eq := by fin_reg_local
      ist_eq := by
        have hlen : blk_in.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_in (by rw [hlen]; decide)
      ost_eq := (hag_comp.readBytes_eq hd_ist_ost (by decide)).trans host
      obl_eq := (hag_comp.read64_eq hd_ist_obl).trans hobl }

private theorem seg3a_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 s : State}
    (hmid : FinMidPre123 key msg s0)
    (hs : StateF3 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateF3b finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, hx21, hx22, hist, host, hobl⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hpc' : s.pc = (blkPl_123).base + 180#64 := hpc
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe hmid.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hmid.sp_aligned
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_64_of_shaStateBytes s.mem (s0.readReg64 .x1) h_in hist
  have hd_hm64_fsp64 : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64) 64 :=
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hrev768 : rev64 (256#64 ||| 512#64) = 0x0003000000000000#64 := by decide
  have hread32 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_32 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  have hread40 := fun w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 =>
    read64_seg3a_pad_40 s.mem _ _ w0 w1 w2 w3 w4 w5 w6 w7 u0 u1 u2 u3 hd_hm64_fsp64
  iterate 31 s2_step
  clear hread32 hread40
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg3a s.mem (s0.readReg64 .x1) (s0.sp - 144#64)
    _ _ _ _ _ _ _ _ _ _ _ _ 0#64 0x0003000000000000#64 0x80#64 0#64 0#64 0x0003000000000000#64
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_hm64_saved : DisjointRegions (s0.readReg64 .x1) 64 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_ost : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1 + 0x68#64) 32 :=
    (hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  have hd_hm64_ost : DisjointRegions (s0.readReg64 .x1) 64 (s0.readReg64 .x1 + 0x68#64) 32 := by
    unfold DisjointRegions; bv_omega
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg3a hsaved hag1 hag2 hag3 hag4 hd_hm64_saved hd_fsp64_saved
          frame := by rw [mem_setMem]; exact frame_seg3a hframe hag1 hag2 hag3 hag4 }
      x0_eq := by fin_reg_local, x1_eq := by fin_reg_local, x2_eq := by fin_reg_local,
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local
      blk_eq := by
        rw [mem_setMem]
        refine (readBytes_fsp_64_seg3 _ _ _ _ _ _ _ _ _ _ _ _ _ hd_hm64_fsp64).trans ?_
        rw [toLEBytes_8_rev32_append, toLEBytes_8_rev32_append,
            toLEBytes_8_rev32_append, toLEBytes_8_rev32_append]
        have htail : toLEBytes 8 0x80#64 ++ toLEBytes 8 0#64 ++ toLEBytes 8 0#64 ++
            toLEBytes 8 (rev64 768#64) =
            [0x80#8] ++ List.replicate 23 0#8 ++ toBEBytes 8 768#64 := by decide
        unfold outerBlock
        rw [digestBytes_eq_append h_in]
        simp only [List.append_assoc] at htail ⊢
        rw [htail]; rfl
      ost_eq := by
        rw [mem_setMem]
        exact (hag4.readBytes_eq hd_fsp64_ost (by decide)).trans
          ((hag3.readBytes_eq hd_hm64_ost (by decide)).trans
            ((hag2.readBytes_eq hd_fsp64_ost (by decide)).trans
              ((hag1.readBytes_eq hd_hm64_ost (by decide)).trans host))) }

private theorem seg3b_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    (h_c256 : Hk lsCompress256Sym = some (compress256Hook C.F))
    {key msg : List (BitVec 8)} {s0 s : State}
    (hmid : FinMidPre123 key msg s0)
    (hs : StateF3b finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateF4 finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx0, hx1, hx2, hx19, hx20, hblk, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hpc' : s.pc = (blkPl_123).base + 304#64 := hpc
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_ost : s.mem.RW (s0.readReg64 .x1 + 0x68#64) 32 := hrw_hm.sub (by bv_omega)
  set h_in := C.F (hmacInnerInit C.F key) (innerLastBlock msg)
  s2_step
  refine s2_compress256_step_of_eq h_c256
    (stPtr := s0.readReg64 .x1 + 0x68#64) (blkPtr := s0.sp - 144#64)
    (lr := (blkPl_123).base + 308#64) (st := hmacOuterInit C.F key) (blk := outerBlock (digestBytes h_in))
    hstat rfl
    (by fin_reg_local) (by fin_reg_local) (by fin_reg_local) rfl
    host hblk (outerBlock_digestBytes_length h_in) hrw_ost ?_
  refine RunsTo.refl ?_
  set blk_out := shaStateBytes (C.F (hmacOuterInit C.F key) (outerBlock (digestBytes h_in)))
  have hag_comp : AgreesOutside s.mem (s.mem.writeBytes (s0.readReg64 .x1 + 0x68#64) blk_out)
      (s0.readReg64 .x1 + 0x68#64) 32 := by
    have hlen : blk_out.length = 32 := shaStateBytes_length _
    rw [← hlen]
    exact ProofLib.AgreesOutside.writeBytes_self s.mem _ blk_out
  have hd_ost_saved : DisjointRegions (s0.readReg64 .x1 + 0x68#64) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    (hmid.disj_hm_fsp.sub_left _ ⟨by decide, by bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := FinSaved.of_agreesOutside hsaved hag_comp hd_ost_saved
          frame := Frame.trans_agreesOutside_sub hframe (rbase := s0.readReg64 .x1) (rlen := 0x90)
            (by simp) (by bv_omega) hag_comp }
      x19_eq := by fin_reg_local, x20_eq := by fin_reg_local
      ost_eq := by
        have hlen : blk_out.length = 32 := shaStateBytes_length _
        rw [← hlen]
        exact readBytes_writeBytes_same s.mem _ blk_out (by rw [hlen]; decide) }

private theorem seg4a_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 s : State}
    (hmid : FinMidPre123 key msg s0)
    (hs : StateF4 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (StateF5 finPlacedFakeB C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hx19, hx20, host⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hpc' : s.pc = (blkPl_123).base + 308#64 := hpc
  have hrw_hm : s.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hframe hmid.rw_hm
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe hmid.rw_fsp
  have hrw_out : s.mem.RW (s0.readReg64 .x0) 32 := rw_of_perm_eq hframe hmid.rw_out
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hmid.sp_aligned
  set h_out := C.F (hmacOuterInit C.F key)
    (outerBlock (digestBytes (C.F (hmacInnerInit C.F key) (innerLastBlock msg))))
  obtain ⟨hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7⟩ :=
    read32_words_at_104_of_shaStateBytes s.mem (s0.readReg64 .x1) h_out host
  have hzero64 : (0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 ++ 0#8 : BitVec 64) = 0#64 := rfl
  iterate 11 s2_step
  have hd_fsp64_hm : DisjointRegions (s0.sp - 144#64) 64 (s0.readReg64 .x1) 0x90 :=
    hmid.disj_hm_fsp.symm.sub_left _ ⟨by decide, by bv_omega⟩
  have hread128 := read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 128#64 (h_out.get 6)
    (Or.inl rfl) hd_fsp64_hm hw6
  have hread132 := read32_seg4a_mid_x s.mem (s0.readReg64 .x1) (s0.sp - 144#64) 132#64 (h_out.get 7)
    (Or.inr rfl) hd_fsp64_hm hw7
  iterate 2 s2_step
  clear hw0 hw1 hw2 hw3 hw4 hw5 hw6 hw7 hread128 hread132 hd_fsp64_hm host
  iterate 15 s2_step
  refine RunsTo.refl ?_
  obtain ⟨hag1, hag2, hag3, hag4⟩ := agreesOutside_seg4a s.mem
    (s0.readReg64 .x0) (s0.readReg64 .x1) (s0.sp - 144#64) _ _ _ _ _ _ _ _
  have hd_hm_saved : DisjointRegions (s0.readReg64 .x1) 0x90 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    hmid.disj_hm_fsp.sub_right _ ⟨by decide, by bv_omega⟩
  have hd_fsp64_saved : DisjointRegions (s0.sp - 144#64) 64 (s0.sp - 144#64 + 0x40#64) 0x50 := by
    unfold DisjointRegions; bv_omega
  have hd_out_saved : DisjointRegions (s0.readReg64 .x0) 32 (s0.sp - 144#64 + 0x40#64) 0x50 :=
    hmid.disj_out_fsp.sub_right _ ⟨by decide, by bv_omega⟩
  refine
    { pc_eq := by fin_reg_local
      common :=
        { status := by fin_reg_local, sp_eq := by fin_reg_local, x29_eq := by fin_reg_local,
          x26_eq := by fin_reg_local, x27_eq := by fin_reg_local, x28_eq := by fin_reg_local,
          saved := by
            rw [mem_setMem]
            exact finSaved_seg4a hsaved hag1 hag2 hag3 hag4 hd_hm_saved hd_fsp64_saved hd_out_saved
          frame := by rw [mem_setMem]; exact frame_seg4a hframe hag1 hag2 hag3 hag4 }
      out_eq := by
        rw [mem_setMem]
        exact (readBytes_write32_8_digestBytes _ (s0.readReg64 .x0) h_out _ _ _ _ _ _ _ _
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)
          (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _) (toLEBytes_4_rev32 _)).trans
          (hmacWith_short C.F key msg hmid.key_le hmid.msg_lt).symm }

private theorem seg4b_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    {key msg : List (BitVec 8)} {s0 s : State}
    (hmid : FinMidPre123 key msg s0)
    (hs : StateF5 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (FinPost C.F key msg s0) := by
  rcases hs with ⟨hpc, hcom, hout⟩
  rcases hcom with ⟨hstat, hsp, hx29, hx26, hx27, hx28, hsaved, hframe⟩
  have hpc' : s.pc = (blkPl_123).base + 420#64 := hpc
  have hrw_fsp : s.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hframe hmid.rw_fsp
  have hsp_align : ((s0.sp - 144#64) &&& 15#64) = 0#64 := fsp_aligned hmid.sp_aligned
  rcases hsaved with ⟨hs29, hslr, hs25, hs24, hs23, hs22, hs21, hs20, hs19⟩
  have hs29' : s.mem.read64 (s0.sp - 144#64 + 64#64) = s0.readReg64 .x29 := hs29
  have hslr' : s.mem.read64 (s0.sp - 144#64 + 72#64) = s0.readReg64 .lr := hslr
  have hs25' : s.mem.read64 (s0.sp - 144#64 + 80#64) = s0.readReg64 .x25 := hs25
  have hs24' : s.mem.read64 (s0.sp - 144#64 + 96#64) = s0.readReg64 .x24 := hs24
  have hs23' : s.mem.read64 (s0.sp - 144#64 + 104#64) = s0.readReg64 .x23 := hs23
  have hs22' : s.mem.read64 (s0.sp - 144#64 + 112#64) = s0.readReg64 .x22 := hs22
  have hs21' : s.mem.read64 (s0.sp - 144#64 + 120#64) = s0.readReg64 .x21 := hs21
  have hs20' : s.mem.read64 (s0.sp - 144#64 + 128#64) = s0.readReg64 .x20 := hs20
  have hs19' : s.mem.read64 (s0.sp - 144#64 + 136#64) = s0.readReg64 .x19 := hs19
  iterate 7 s2_step
  refine RunsTo.refl ⟨by simp (config := { decide := true }) only [arm64_norm], hstat,
    ⟨by simp (config := { decide := true }) only [arm64_norm], fun r hr => ?_⟩, hout, hframe⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [arm64_norm, hx26, hx27, hx28]

private theorem seg2_to_end_123 [LibsignalPlacement] {C : Crypto} {Hk : LibsignalHooks}
    (h_c256 : Hk lsCompress256Sym = some (compress256Hook C.F))
    {key msg : List (BitVec 8)} {s0 s : State}
    (hmid : FinMidPre123 key msg s0)
    (hs : StateF1 finPlacedFakeB C.F key msg s0 s) :
    RunsTo ((blkPC_123).rebase (blkPl_123).base Hk) s (FinPost C.F key msg s0) :=
  (seg2a_123 hmid hs).trans fun _ hs2 =>
  (seg2b_123 h_c256 hmid hs2).trans fun _ hs3 =>
  (seg3a_123 hmid hs3).trans fun _ hs3b =>
  (seg3b_123 h_c256 hmid hs3b).trans fun _ hs4 =>
  (seg4a_123 hmid hs4).trans fun _ hs5 =>
  seg4b_123 hmid hs5

/-- Full relocatable `RunsToVm` contract of `finalize_fixed` (Block `123`) under
`[HkdfPlacedHooksExactBudgetSat C.F H]` with `FinPostSat` (`S2Frame`). -/
public theorem finalize_fixed_placed_runsToVm_sat [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [hH : HkdfPlacedHooksExactBudgetSat C.F H]
    {key msg : List (BitVec 8)} {s0 : State}
    (hcl : LibsignalCodeLoaded lsmpl s0.mem)
    (hpre : FinPre finPlacedFakeB C.F key msg s0) :
    RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s0 (FinPostSat C.F key msg s0) := by
  have heq123 : ∀ X, (blkPC_123).rebase (blkPl_123).base X =
      libsignalSessionLib.blockProgram lsmpl 123 X :=
    fun X => IsLsBlockProg.eq_blockProgram (prog := (blkPC_123).rebase (blkPl_123).base X)
  let Q123 := libsignalSessionLib.blockProgram lsmpl 123 (hmacCompressOnlyExcHooks C.F H)
  let kp123 := ProofLib.progKeep Q123
  have hpre_strip : FinPre finPlacedFakeB C.F key msg (ProofLib.stripS kp123 s0) := by
    have hr : ∀ r, (ProofLib.stripS kp123 s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
    have hsp0 : (ProofLib.stripS kp123 s0).sp = s0.sp := by cases s0; rfl
    exact
      { pc_eq := (by cases s0; rfl : (ProofLib.stripS kp123 s0).pc = s0.pc).trans hpre.pc_eq,
        status := (by cases s0; rfl : (ProofLib.stripS kp123 s0).status = s0.status).trans hpre.status,
        key_le := hpre.key_le, msg_lt := hpre.msg_lt,
        hmac_st := by rw [hr, stripS_hmacSt]; exact hpre.hmac_st,
        rw_out := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp123 s0.mem _ _ hpre.rw_out,
        rw_hm := by rw [stripS_mem, hr]; exact stripExecOutside_rw kp123 s0.mem _ _ hpre.rw_hm,
        rw_fsp := by rw [stripS_mem, hsp0]; exact stripExecOutside_rw kp123 s0.mem _ _ hpre.rw_fsp,
        disj_out_hm := by rw [hr, hr]; exact hpre.disj_out_hm,
        disj_out_fsp := by rw [hr, hsp0]; exact hpre.disj_out_fsp,
        disj_hm_fsp := by rw [hr, hsp0]; exact hpre.disj_hm_fsp,
        sp_aligned := by rw [hsp0]; exact hpre.sp_aligned }
  -- Piece 1: `+0 -> bl memset` (`s0 -> s1`, 0 `memset` calls)
  have hp1 : RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s0
      (StateFPreMemset123 C.F key msg s0) := by
    refine lift_block_vm_compress_only (Pj := (blkPC_123).rebase (blkPl_123).base H)
      blkLib_eq_123 blk123_noSvc0 blk123_noMsr (by decide) (by decide) hcl
      (heq123 H ▸ (seg1a_123 hpre).trans fun _ hs0 => seg1b_pre_123 hpre hs0)
      (heq123 _ ▸ (seg1a_123 hpre_strip).trans fun _ hs0 => seg1b_pre_123 hpre_strip hs0)
      (fun _ hs => hs.common.status) (fun _ hs => hs.common.status)
      fun s1 hvm1 hs1 => ?_
    rcases hs1 with ⟨hpc, hc, hlr, hx0, hx1, hx2, hx19, hx20, hx21, hx22, hx23, hx24, hx25,
      hpad, hist, host, hobl⟩
    have hr0 : ∀ r, (ProofLib.stripS kp123 s0).readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
    rw [hr0, stripS_readBytes] at hpad hist host
    rw [hr0, stripS_read64] at hobl
    exact ⟨(by cases s1; exact hpc), unstrip_finCommon hc hvm1.perm_eq,
      (by cases s1; exact hlr), (by cases s0; cases s1; exact hx0),
      (by cases s1; exact hx1), (by cases s1; exact hx2),
      (by cases s0; cases s1; exact hx19), (by cases s0; cases s1; exact hx20),
      (by cases s0; cases s1; exact hx21), (by cases s1; exact hx22),
      (by cases s1; exact hx23), (by cases s1; exact hx24), (by cases s1; exact hx25),
      hpad, hist, host, hobl⟩
  refine hp1.trans_full fun s1 hs1 hkf1 => ?_
  -- Piece 2: `bl memset` (`s1 -> s2`)
  have hp2 : RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s1 fun s2 =>
      S2Frame s0.mem s2.mem
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] ∧
      StateF1 finPlacedFakeB C.F key msg (s0.setMem s2.mem) s2 := by
    intro hL1
    rcases hs1 with ⟨hpc1, ⟨hstat1, hsp1, hx29_1, hx26_1, hx27_1, hx28_1, hsaved1, hfr1⟩,
      hlr1, hx0_1, hx1_1, hx2_1, hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
      hpad1, hist1, host1, hobl1⟩
    set dst := s0.readReg64 .x1 + BitVec.ofNat 64 msg.length + 1#64
    set len := 63 - msg.length
    have hrw_hm1 : s1.mem.RW (s0.readReg64 .x1) 0x90 := rw_of_perm_eq hfr1 hpre.rw_hm
    have hrw_fsp1 : s1.mem.RW (s0.sp - 144#64) 144 := rw_of_perm_eq hfr1 hpre.rw_fsp
    have hrw_dst : s1.mem.RW dst len :=
      hrw_hm1.sub (by have := hpre.msg_lt; dsimp only [dst, len]; bv_omega)
    have hsp1_al : (s1.sp &&& 15#64) = 0#64 := by
      rw [hsp1]; exact fsp_aligned hpre.sp_aligned
    obtain ⟨s2, hst2, hvm2, htr2, hv2, hpc2, hstat2, hcc2, _, _, _, hs2_fr, hs2_ag⟩ :=
      placed_memset_budget_steps_sat (prog := (blkPC_123).rebase (blkPl_123).base H) (i := 123)
        hH.memset hstat1 hpc1 hx0_1 hx1_1 hx2_1 hlr1 hsp1_al hrw_dst
    have hfr_0_2 : S2Frame s0.mem s2.mem
        [(s0.readReg64 .x0, 32), (s0.readReg64 .x1, 0x90), (s0.sp - 144#64, 144)] := by
      refine (S2Frame.of_frame hfr1).trans (hs2_fr.mono fun a ha r hr => ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; subst hr
      have ha_hm := ha (s0.readReg64 .x1, 0x90) (by simp)
      have := hpre.msg_lt; dsimp only [dst, len]; unfold OutsideRegion at ha_hm ⊢; bv_omega
    have hP1 : ∀ {a : BitVec 64}, s1.mem.permNoLazy a = some Perm.rw →
        (s1.mem.perm a).r = true ∧ s1.mem.isLazyFree a = false := fun {a} hnl => by
      obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp hnl
      exact ⟨by rw [hp]; rfl, hlf⟩
    have hag_wb : AgreesOutside s1.mem (s1.mem.writeBytes dst (List.replicate len 0#8)) dst len := by
      have hlen_r : (List.replicate len 0#8).length = len := List.length_replicate
      conv_rhs => rw [← hlen_r]
      exact ProofLib.AgreesOutside.writeBytes_self s1.mem dst (List.replicate len 0#8)
    have hd_dst_saved : DisjointRegions dst len (s0.sp - 144#64 + 0x40#64) 0x50 :=
      (hpre.disj_hm_fsp.sub_left dst ⟨by have := hpre.msg_lt; dsimp only [dst, len]; bv_omega,
        by have := hpre.msg_lt; dsimp only [dst, len]; bv_omega⟩).sub_right _ ⟨by decide, by bv_omega⟩
    have hsaved2 : FinSaved (s0.setMem s2.mem) ((s0.setMem s2.mem).sp - 144#64) s2.mem :=
      AgreesOn.finSaved_of hs2_ag (FinSaved.of_agreesOutside hsaved1 hag_wb hd_dst_saved)
        (fun a ha => hP1 (hrw_fsp1 a (by rw [State.sp_setMem] at ha; unfold InRegion at ha ⊢; bv_omega)))
    have hbuf2 : s2.mem.readBytes (s0.readReg64 .x1) 64 =
        msg ++ [0x80#8] ++ List.replicate len 0#8 := by
      rw [AgreesOn.readBytes_eq hs2_ag (s0.readReg64 .x1) 64 (by decide)
        (fun a ha => hP1 (hrw_hm1 a (by unfold InRegion at ha ⊢; bv_omega)))]
      have hsplit : (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes (s0.readReg64 .x1) 64 =
          (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes (s0.readReg64 .x1) (msg.length + 1) ++
          (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes
            (s0.readReg64 .x1 + BitVec.ofNat 64 (msg.length + 1)) len := by
        rw [← ProofLib.readBytes_add]; congr 1; have := hpre.msg_lt; dsimp only [len]; omega
      have hdst_eq : s0.readReg64 .x1 + BitVec.ofNat 64 (msg.length + 1) = dst := by
        dsimp only [dst]; rw [BitVec.ofNat_add]; simp [BitVec.add_assoc]
      rw [hsplit, hdst_eq]
      have hl : (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes
          (s0.readReg64 .x1) (msg.length + 1) = msg ++ [0x80#8] := by
        by_cases h0 : len = 0
        · simp [h0, Memory.writeBytes]; exact hpad1
        · rw [ProofLib.readBytes_writeBytes_disjoint s1.mem (s0.readReg64 .x1) (msg.length + 1)
            dst (List.replicate len 0#8)]
          · exact hpad1
          · rw [List.length_replicate]; have := hpre.msg_lt; dsimp only [dst, len] at h0 ⊢
            unfold DisjointRegions; bv_omega
      have hr : (s1.mem.writeBytes dst (List.replicate len 0#8)).readBytes dst len =
          List.replicate len 0#8 := by
        have hlen_r : (List.replicate len 0#8).length = len := List.length_replicate
        conv => lhs; arg 3; rw [← hlen_r]
        exact ProofLib.readBytes_writeBytes_same s1.mem dst (List.replicate len 0#8)
          (by rw [hlen_r]; dsimp only [len]; omega)
      rw [hl, hr]
    have hd_dst_ist : DisjointRegions dst len (s0.readReg64 .x1 + 0x40#64) 32 := by
      have := hpre.msg_lt; dsimp only [dst, len]; unfold DisjointRegions; bv_omega
    have hd_dst_ost : DisjointRegions dst len (s0.readReg64 .x1 + 0x68#64) 32 := by
      have := hpre.msg_lt; dsimp only [dst, len]; unfold DisjointRegions; bv_omega
    have hd_dst_obl : DisjointRegions dst len (s0.readReg64 .x1 + 0x88#64) 8 := by
      have := hpre.msg_lt; dsimp only [dst, len]; unfold DisjointRegions; bv_omega
    refine ⟨s2, hst2, hvm2, htr2, hv2, ⟨hfr_0_2,
      ⟨hpc2,
        ⟨hstat2, (CallingConventionPreserved.sp_eq hcc2).trans hsp1,
          (CallingConventionPreserved.x29 hcc2).trans hx29_1,
          (CallingConventionPreserved.x26 hcc2).trans hx26_1,
          (CallingConventionPreserved.x27 hcc2).trans hx27_1,
          (CallingConventionPreserved.x28 hcc2).trans hx28_1,
          hsaved2, Frame.refl s2.mem _⟩,
        (CallingConventionPreserved.x19 hcc2).trans hx19_1,
        (CallingConventionPreserved.x20 hcc2).trans hx20_1,
        (CallingConventionPreserved.x21 hcc2).trans hx21_1,
        (CallingConventionPreserved.x22 hcc2).trans hx22_1,
        (CallingConventionPreserved.x23 hcc2).trans hx23_1,
        (CallingConventionPreserved.x24 hcc2).trans hx24_1,
        (CallingConventionPreserved.x25 hcc2).trans hx25_1,
        hbuf2,
        (AgreesOn.readBytes_eq hs2_ag _ 32 (by decide)
          (fun a ha => hP1 (hrw_hm1 a (by rw [State.readReg64_setMem] at ha; unfold InRegion at ha ⊢; bv_omega)))).trans
          ((hag_wb.readBytes_eq hd_dst_ist (by decide)).trans hist1),
        (AgreesOn.readBytes_eq hs2_ag _ 32 (by decide)
          (fun a ha => hP1 (hrw_hm1 a (by rw [State.readReg64_setMem] at ha; unfold InRegion at ha ⊢; bv_omega)))).trans
          ((hag_wb.readBytes_eq hd_dst_ost (by decide)).trans host1),
        (AgreesOn.read64_eq hs2_ag _
          (fun a ha => hP1 (hrw_hm1 a (by rw [State.readReg64_setMem] at ha; unfold InRegion at ha ⊢; bv_omega)))).trans
          ((hag_wb.read64_eq hd_dst_obl).trans hobl1)⟩⟩,
      hst2.codeLoaded hL1⟩
  refine hp2.trans_full fun s2 ⟨hfr_0_2, hs2⟩ hkf2 => ?_
  -- Piece 3: `+76 -> ret` (`s2 -> sf`, 0 `memset` calls, anchored at `s0' := s0.setMem s2.mem`)
  have hcl2 : LibsignalCodeLoaded lsmpl s2.mem :=
    (hcl.of_keepsFrozen hkf1).of_keepsFrozen hkf2
  let s0' := s0.setMem s2.mem
  have hmid : FinMidPre123 key msg s0' :=
    { key_le := hpre.key_le, msg_lt := hpre.msg_lt,
      rw_out := hfr_0_2.rw_of_rw _ _ hpre.rw_out,
      rw_hm := hfr_0_2.rw_of_rw _ _ hpre.rw_hm,
      rw_fsp := hfr_0_2.rw_of_rw _ _ hpre.rw_fsp,
      disj_out_fsp := hpre.disj_out_fsp, disj_hm_fsp := hpre.disj_hm_fsp,
      sp_aligned := hpre.sp_aligned }
  have hs2_strip : StateF1 finPlacedFakeB C.F key msg (ProofLib.stripS kp123 s0')
      (ProofLib.stripS kp123 s2) := by
    rcases hs2 with ⟨hpc, ⟨hst, hsp_c, hx29, hx26, hx27, hx28, hsav, _⟩,
      hx19, hx20, hx21, hx22, hx23, hx24, hx25, hbuf, hist, host, hobl⟩
    have hm_eq : (ProofLib.stripS kp123 s0').mem = (ProofLib.stripS kp123 s2).mem := by
      cases s0; cases s2; rfl
    have hr0 : ∀ r, (ProofLib.stripS kp123 s0').readReg64 r = s0'.readReg64 r := fun _ => by
      cases s0; rfl
    exact ⟨(by cases s2; exact hpc),
      ⟨(by cases s2; exact hst), (by cases s0; cases s2; exact hsp_c),
        (by cases s0; cases s2; exact hx29), (by cases s0; cases s2; exact hx26),
        (by cases s0; cases s2; exact hx27), (by cases s0; cases s2; exact hx28),
        (stripS_finSaved kp123 s0' s2).mpr hsav, hm_eq ▸ Frame.refl _ _⟩,
      (by cases s0; cases s2; exact hx19), (by cases s0; cases s2; exact hx20),
      (by cases s0; cases s2; exact hx21), (by cases s2; exact hx22),
      (by cases s2; exact hx23), (by cases s2; exact hx24), (by cases s2; exact hx25),
      by rw [hr0, stripS_readBytes]; exact hbuf,
      by rw [hr0, stripS_readBytes]; exact hist,
      by rw [hr0, stripS_readBytes]; exact host,
      by rw [hr0, stripS_read64]; exact hobl⟩
  have hp3 : RunsToVm ((blkPC_123).rebase (blkPl_123).base H) s2
      (FinPost C.F key msg s0') := by
    refine lift_block_vm_compress_only (Pj := (blkPC_123).rebase (blkPl_123).base H)
      blkLib_eq_123 blk123_noSvc0 blk123_noMsr (by decide) (by decide) hcl2
      (heq123 H ▸ seg2_to_end_123 hH.compress256 hmid hs2)
      (heq123 _ ▸ seg2_to_end_123 (hmacCompressOnlyExcHooks_compress C.F H) (hmid.stripS kp123) hs2_strip)
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1)
      fun sf hvm3 ⟨hpc_f, hstat_f, hcs_f, hout_f, hfr_f⟩ => ?_
    have hr0 : ∀ r, (ProofLib.stripS kp123 s0').readReg64 r = s0'.readReg64 r := fun _ => by
      cases s0; rfl
    have hsp0 : (ProofLib.stripS kp123 s0').sp = s0'.sp := by cases s0; rfl
    have hm0 : (ProofLib.stripS kp123 s0').mem = ProofLib.stripExecOutside kp123 s2.mem := by
      cases s0; rfl
    rw [hr0, stripS_readBytes] at hout_f
    rw [hm0, stripS_mem, hr0, hr0, hsp0] at hfr_f
    refine ⟨(by cases s0; cases sf; exact hpc_f), (by cases sf; exact hstat_f),
      ⟨(by cases s0; cases sf; exact hcs_f.1), fun r hr => ?_⟩,
      hout_f, unstrip_frame hfr_f hvm3.perm_eq⟩
    have := hcs_f.2 r hr
    cases s0; cases sf; exact this
  exact hp3.mono fun sf ⟨hpc_f, hstat_f, hcs_f, hout_f, hfr_f⟩ =>
    ⟨hpc_f, hstat_f, hcs_f, hout_f, hfr_0_2.trans (S2Frame.of_frame hfr_f)⟩

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat
