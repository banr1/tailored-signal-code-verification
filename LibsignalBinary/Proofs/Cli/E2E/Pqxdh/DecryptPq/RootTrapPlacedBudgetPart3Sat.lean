/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DecryptTailTrap507PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SpqrRecvTrapV1_507PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.VerifyMacTrap507PlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget -- proof-setup: allow-public-import
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import GeneratedLean.LibsignalSession -- shake: keep
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
import LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.CompressAndDigest
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.Defs
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceFirstHalf
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceSecondHalf
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetUuid
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget
import LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
import LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudget
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudget

/-!
# `HookSat` Sibling of `RootTrapPlacedBudgetPart3` (`RootTrapPlacedBudgetPart3Sat`)

Block-`507` CLI seam proofs (`s6_507_cli`, `s9_507_cli`, `s7_507_cli_of_hMs`, `s7_507_cli`),
replacing `HkdfPlacedHooks` (`= some hookMemset`) in `s6_507_cli` with
`(hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec)`
via `HkdfPlacedHooksExactBudgetSat`, and proving `new_from_slice` (`≤ 64`-byte key path) from
`HookSatExactMemcpy` without `memset` or `memcpy` row-equality hypotheses.
-/

public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart3Sat

open Arm64 ProofLib SepProp
open CryptoGames.HMAC (ShaState sha256IV)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
   blkLib_eq_114 blkPC_114 blkPC_252 blkPC_60 blkPC_61 blkPC_69 blkPl_114 blkPl_252 blkPl_60
   blkPl_61 blkPl_69 libsignalSessionLib lsProg_114 ls_subroutine_ok_of_block lsmpl
   subroutine_ok_withLsCodeLoaded_of_plain withLsCodeLoaded)
open CryptoVerification.CliHandshake.TryDecPlaced (blkPC_508 blkPl_508 instIsLsBlockProg_508)
open CryptoVerification.LibsignalAesCbc (returnToLinkRegister)
open CryptoVerification.LibsignalAesCbc.Run.Bytes (readBytes_slice_of_readBytes_eq)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState shaStateBytes)
open CryptoVerification.LibsignalSession.CryptoHmacSha256
  (AgreesOutside.write64_self CalleeSaved CallingConventionPreserved_of_calleeSaved Frame HmacSt
   Layout.readBytes_writeBytes_eq NfsMemInv NfsRegInv RW RunsTo RunsTo.lsProg_svc
   RunsTo.pairStep_114_0x28 TraceEq agreesOutside_nfsPrologueMem agreesOutside_toFrame
   disjointRegions_of_ro_rw keyBlock keyBlock_length lsCompress256Sym lsMemcpySym lsMemsetSym
   lsSha256IVAddr nfsPlacedFakeB nfsPlacedFakeB_add_iv nfsPrologueMem nfsSavedStack_prologue_432
   nfsSp nfs_chunk1_placed nfs_chunk2_placed nfs_chunk3_placed nfs_chunk4_placed
   nfs_second_half_placed nfs_sp_add_464_align nfs_sp_add_544_align nfs_sp_align nfs_sp_eq_add
   nfs_ule_65_false readBytes_writeBytes_16_other readBytes_writeBytes_16_self
   rodata_placed_sha256IV slice16 slice16_length write64_oct_zero_eq_writeBytes_64
   write64_quad_288_eq_writeBytes_slice16 writeBytes_key_over_zero64)
open CryptoVerification.LibsignalTripleRatchet
  (LibsignalCodeRoLoaded SpqrModel keys_ls_hook_ok_of_mem keys_ls_subroutine_ok_of_block_cro
   newFromSliceSpec newFromSliceStack subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
   withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (isBlock_nfsResult)
open CryptoVerification.LibsignalTripleRatchetRepr (uuidTryParse)
open CryptoVerification.SignalSession
  (CliHooks cliExternsPlaced cliHookTablePlaced lsRustAllocSymCli lsRustAllocZeroedSymCli
   lsRustDeallocSymCli lsRustNoAllocShimSymCli lsRustReallocSymCli lsStringCloneSym)
open CryptoVerification.SignalSession.Cli.RunGlue
  (CliGhostHooks cliExternsPlaced_row cliGhostExterns cliGhostExterns_other cliGhostExterns_shim)
open CryptoVerification.SignalSession.Cli.Slots
  (cliGhostExterns_sat_of_cliExternsPlaced compress256_row_placed)
open LibsignalBinary.Heap
  (AllocCostModel AllocEvent BudgetLimits FdsHiFrame PoolPreserved RustCliAllocBudget VmPreserved)
open LibsignalBinary.Heap.MuslMemOpsRunsTo (applyMemcpyClobber)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.DecryptTailTrap507PlacedBudget
  (applyRatchet_507_placed_ok)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.SpqrRecvTrapV1_507PlacedBudget
  (deriveKeys_507_placed_ok)
open LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.VerifyMacTrap507PlacedBudget
  (verifyMac_507_placed_ok)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.DecryptTailTrapPlacedBudget (s9Env)
open LibsignalBinary.Proofs.Cli.SpqrV1.M4.VerifyMacTrapPlacedBudget (s7Env)
open LibsignalBinary.Proofs.Cli.TripleRatchet.Decrypt.DefsPlacedBudget
  (S6SeamPlaced S7SeamPlaced S9SeamPlaced)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAux
  (stripExecOutside_readBytes stripExecOutside_readable stripExecOutside_rw unstrip_frame)
open LibsignalBinary.Proofs.ConsumeMessageKey.AssemblyBudgetAuxSat
  (blockProgram_allInstrs_not_isMsrTpidrEl0 checkBlockNoMsrTpidrEl0)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetSat
  (expand_multi_info_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetSat
  (extract_placed_vm_ok_of_other_block_sat)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore
  (HookSatExactMemcpy placed_memcpy_step_of_exact)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.CliSlotCalleesInstPlacedBudgetUuid
  (uuidTryParse_placed_vm_ok)
open LibsignalBinary.Proofs.SignalSession.Cli.Run.Slots.CliHookSatPlacedBudget
  (CliGhostAllocHooks cliExternsPlaced_alloc_budget_sat cliExternsPlaced_blackBox_budget_sat
   cliExternsPlaced_compress256Multi_budget_sat cliExternsPlaced_dealloc_budget_sat
   cliExternsPlaced_exactMemcpy_sat cliExternsPlaced_framelessMemcpy_budget_sat
   cliExternsPlaced_noAllocShim_budget_sat cliExternsPlaced_sessionMemcpyRegion_budget_sat
   cliExternsPlaced_sessionMemsetRegion_budget_sat cliExternsPlaced_shim_budget_sat)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget (stripS_readReg64 stripS_sp)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.DefsBudget
  (framelessMemcpyBudgetSpec noAllocShim_hookOk)
open LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerializeBudget
  (public_key_serialize_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeysBudget (s6FreeOnlyEnv)
open LibsignalBinary.Proofs.TripleRatchet.Getters.ClearUnacknowledgedPreKeyMessageBudget
  (clear_unacknowledged_pre_key_message_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat (HkdfPlacedHooksExactBudgetSat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonSat
  (HkdfPlacedHooksExactSat hookSat_sessionMemsetRegion_of_budget)
open LibsignalBinary.Proofs.TripleRatchet.Hooks.DefsBudget (sessionMemsetRegionBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.CallsBudget (parse_sid_placed_ok_at_of_code)
open LibsignalBinary.Proofs.TripleRatchet.InImageCallees.DefsBudget
  (parseSidCodeBudgetSpec uuidTryParseCodeBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Keys.GenerateKeysBudget
  (generateKeys_placed_ok_of_contracts)
open LibsignalBinary.Proofs.TripleRatchet.Mac.ComputeBudgetAux (newFromSliceBudgetSpec)
open LibsignalBinary.Proofs.TripleRatchet.Mac.VerifyBudget (verifyMacWithAddresses_placed_cro_ok)
open LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.ApplyBudget (trApply_placed_ok)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open Obj (MultiPlacedLib MultiPlacement PlacedLib)
open VerifiedLibraries.RustStd (blockProgram_rebase_allInstrs_not_isSvc0)

private theorem cliGhost_row (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    {sym : String} {f : State → State} (hrow : (sym, f) ∈ cliHookTablePlaced mmpl W)
    (h1 : sym ≠ lsRustAllocSymCli := by decide) (h2 : sym ≠ lsRustDeallocSymCli := by decide)
    (h3 : sym ≠ lsRustReallocSymCli := by decide) (h4 : sym ≠ lsRustAllocZeroedSymCli := by decide)
    (h5 : sym ≠ lsRustNoAllocShimSymCli := by decide) (h6 : sym ≠ lsStringCloneSym := by decide)
    (h7 : sym ≠ CryptoVerification.SignalSession.lsReadFileSym := by decide)
    (h8 : sym ≠ CryptoVerification.SignalSession.lsReadStdinSym := by decide)
    (h9 : sym ≠ CryptoVerification.SignalSession.lsMemsetSym := by decide)
    (h10 : sym ≠ CryptoVerification.SignalSession.lsMemcpySym := by decide) :
    cliGhostExterns g (cliExternsPlaced mmpl W) sym = some f :=
  (cliGhostExterns_other g _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10).trans (cliExternsPlaced_row mmpl W hrow)

private theorem mkHkdfPlacedHooksExactSat_cli [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    HkdfPlacedHooksExactSat W.C.F (cliGhostExterns g (cliExternsPlaced mmpl W)) :=
  { memset := hookSat_sessionMemsetRegion_of_budget
      (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
    memcpy := cliExternsPlaced_exactMemcpy_sat mmpl g W hG
    compress256 := cliGhost_row mmpl g W (compress256_row_placed mmpl W) }

private theorem framelessMemcpy_budget_sat [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) "memcpy" framelessMemcpyBudgetSpec := by
  obtain ⟨f, hf, hok⟩ := cliExternsPlaced_framelessMemcpy_budget_sat mmpl g W hG
  refine ⟨f, hf, fun x R s0 hrun hpre hsp => ?_⟩
  rcases hok x R s0 hrun hpre hsp with ⟨hkeep, hsym, hout⟩
  refine ⟨hkeep, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | hrest
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rcases x with ⟨dst, src, bs⟩
    dsimp only [withVmPreserved, CryptoVerification.LibsignalTripleRatchet.framelessMemcpySpec,
      framelessMemcpyBudgetSpec] at hpost ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, sepConj_assoc,
      satisfies_pure_sepConj] at hpost
    rw [sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hpost.2.1.1, hpost.2.1.2, hpost.1⟩, hpost.2.2⟩
  · exact Or.inr hrest

private theorem stripS_read64 (p : BitVec 64 → Bool) (s : State) (a : BitVec 64) :
    (ProofLib.stripS p s).mem.read64 a = s.mem.read64 a := by
  cases s; simp [ProofLib.stripS, Memory.read64, ProofLib.strip_read8]

private theorem stripExecOutside_hmacSt {F : ShaState → List (BitVec 8) → ShaState}
    {p : BitVec 64 → Bool} {m : Memory} {a : BitVec 64} {key msg : List (BitVec 8)} :
    HmacSt (ProofLib.stripExecOutside p m) a F key msg ↔ HmacSt m a F key msg := by
  unfold HmacSt; simp only [stripExecOutside_readBytes, Memory.read64, ProofLib.strip_read8]

private theorem stripExecOutside_perm_eq_of_perm_eq (keep : BitVec 64 → Bool)
    {m m' : Memory} (hp : m'.perm = m.perm) :
    (ProofLib.stripExecOutside keep m').perm = (ProofLib.stripExecOutside keep m).perm := by
  funext a; rw [ProofLib.strip_perm, ProofLib.strip_perm, hp]

private theorem stripExecOutside_writeBytes (p : BitVec 64 → Bool) :
    ∀ (m : Memory) (a : BitVec 64) (bs : List (BitVec 8)),
      (ProofLib.stripExecOutside p m).writeBytes a bs =
        ProofLib.stripExecOutside p (m.writeBytes a bs)
  | _, _, [] => rfl
  | m, a, b :: bs => by
    simp only [Memory.writeBytes, ProofLib.strip_write8,
      stripExecOutside_writeBytes p (m.write8 a b) (a + 1#64) bs]

private theorem stripExecOutside_readShaState (p : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    readShaState (ProofLib.stripExecOutside p m) a = readShaState m a := by
  simp [readShaState, Memory.read32, ProofLib.strip_read8]

private theorem stripS_compress256Hook (F : ShaState → List (BitVec 8) → ShaState)
    (p : BitVec 64 → Bool) (s : State) :
    compress256Hook F (ProofLib.stripS p s) = ProofLib.stripS p (compress256Hook F s) := by
  cases s
  dsimp only [ProofLib.stripS, compress256Hook, returnToLinkRegister,
    State.setMem, State.setPC, State.readReg64]
  rw [stripExecOutside_readShaState, stripExecOutside_readBytes, stripExecOutside_writeBytes]

private theorem vmPreserved_compress256Hook (F : ShaState → List (BitVec 8) → ShaState) (s : State) :
    VmPreserved s (compress256Hook F s) := by
  dsimp only [compress256Hook, returnToLinkRegister]
  simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private def hmacCompressOnlyExcHooks (F : ShaState → List (BitVec 8) → ShaState)
    (H : LibsignalHooks) : LibsignalHooks :=
  fun n =>
    if n = lsCompress256Sym then some (compress256Hook F)
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

private theorem hmacCompressOnlyExcHooks_compress (F : ShaState → List (BitVec 8) → ShaState)
    (H : LibsignalHooks) :
    hmacCompressOnlyExcHooks F H lsCompress256Sym = some (compress256Hook F) := by
  simp [hmacCompressOnlyExcHooks]

private theorem strip_codeLoaded_of_keep {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun k hk => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 k - prog.base = BitVec.ofNat 64 k := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 k) = true := by
    unfold ProofLib.progKeep
    rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact decide_eq_true hk
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq k hk, hL.perm_eq k hk, hL.isLazyFree_eq k hk⟩

private theorem strip_execOnlyIn_of_keep (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with | refl => exact hr | step h1 _ => cases h1 <;> assumption

private theorem step_P_extern_eq {P : Program} {s1 s2 : State} {f : State → State}
    (hstep : Step P s1 s2) (hrun2 : s2.status = .Running) (heP : P.externAt? s1.pc = some f) :
    s2 = f s1 ∧ s1.mem.KeepsFrozen (f s1).mem ∧ (f s1).symtab = s1.symtab := by
  cases hstep with
  | @exec inst _ hfe => unfold Program.fetchMem at hfe; rw [heP] at hfe; simp at hfe
  | halt_unmapped _ _ he => rw [heP] at he; cases he
  | extern _ he hkf hsym => rw [heP] at he; injection he with hff; subst hff; exact ⟨rfl, hkf, hsym⟩
  | extern_fault _ _ _ => cases s1; cases hrun2

private theorem step_P_exec_eq {P : Program} {s1 s2 : State} {inst : Instr}
    (hstep : Step P s1 s2) (hfeP : P.fetchMem s1.mem s1.pc = some inst)
    (hnsvc0 : inst.isSvc0 = false) : s2 = execInst inst s1 := by
  have heP_none : P.externAt? s1.pc = none := by
    unfold Program.fetchMem at hfeP
    cases he : P.externAt? s1.pc with | none => rfl | some _ => simp [he] at hfeP
  cases hstep with
  | @exec inst' _ hfe' =>
    rw [hfeP] at hfe'; injection hfe' with hi; subst hi
    exact Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
  | halt_unmapped _ hfe' _ => rw [hfeP] at hfe'; cases hfe'
  | extern _ he _ _ => rw [heP_none] at he; cases he
  | extern_fault _ he _ => rw [heP_none] at he; cases he

private theorem stripExecOutside_frame (keep : BitVec 64 → Bool)
    {m m' : Memory} {rs : List (BitVec 64 × Nat)} (hf : Frame m m' rs) :
    Frame (ProofLib.stripExecOutside keep m) (ProofLib.stripExecOutside keep m') rs :=
  ⟨fun a ha => by rw [ProofLib.strip_read8, ProofLib.strip_read8]; exact hf.1 a ha,
   stripExecOutside_perm_eq_of_perm_eq keep hf.2.1,
   fun a ha => by rw [ProofLib.strip_isLazyFree, ProofLib.strip_isLazyFree]; exact hf.2.2.1 a ha,
   fun a ha => by rw [ProofLib.strip_isLazyFree] at ha ⊢; exact hf.2.2.2.1 a ha,
   fun a ha => by rw [ProofLib.strip_isAnon] at ha ⊢; exact hf.2.2.2.2 a ha⟩

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

private theorem hmacCompressOnlyExcHooks_isSome {F : ShaState → List (BitVec 8) → ShaState}
    {H : LibsignalHooks} (h_c256 : H lsCompress256Sym = some (compress256Hook F)) (n : String) :
    (hmacCompressOnlyExcHooks F H n).isSome = (H n).isSome := by
  unfold hmacCompressOnlyExcHooks
  by_cases h1 : n = lsCompress256Sym
  · subst h1; simp [h_c256]
  · simp [h1]

private theorem blockProgram_hmacCompressOnlyExcHooks_externAt?_isSome
    (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) (pc : BitVec 64) :
    ((lib.blockProgram pl i (hmacCompressOnlyExcHooks F H)).externAt? pc).isSome =
      ((lib.blockProgram pl i H).externAt? pc).isSome := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program
  dsimp only
  rw [option_or_isSome, option_or_isSome]
  rw [findSome?_isSome_congr _
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then
        hmacCompressOnlyExcHooks F H x.1
      else none)
    (fun x : String × Nat =>
      if (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) = true then H x.1 else none)]
  intro x
  cases h : (x.2 == (pc - (lib.blockPlacement pl i).base).toNat) <;>
    simp [hmacCompressOnlyExcHooks_isSome h_c256]

private theorem findSome?_hmacCompressOnlyExcHooks_cases
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_c256 : H lsCompress256Sym = some (compress256Hook F)) :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then hmacCompressOnlyExcHooks F H n else none) =
        some f →
      (∀ s, (f s).status = .Exception "ext") ∨
      (f = compress256Hook F ∧
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f)
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    simp only [List.findSome?_cons] at h ⊢
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact findSome?_hmacCompressOnlyExcHooks_cases h_c256 tl h
    · simp only [ho, ↓reduceIte] at h ⊢
      unfold hmacCompressOnlyExcHooks at h
      by_cases h1 : n = lsCompress256Sym
      · subst h1; simp only [↓reduceIte, Option.some.injEq] at h; subst h
        rw [h_c256]; exact Or.inr ⟨rfl, rfl⟩
      · simp only [h1, ↓reduceIte] at h
        cases hHn : H n with
        | none =>
          rw [hHn] at h
          dsimp only [Option.map] at h ⊢
          exact findSome?_hmacCompressOnlyExcHooks_cases h_c256 tl h
        | some g =>
          rw [hHn] at h; simp only [Option.map, Option.some.injEq] at h; subst h
          exact Or.inl fun s => by cases s; rfl

private theorem blockProgram_hmacCompressOnlyExcHooks_externAt?_cases
    {lib : MultiPlacedLib} {pl : MultiPlacement} {i : Nat}
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    {pc : BitVec 64} {f : State → State}
    (h : (lib.blockProgram pl i (hmacCompressOnlyExcHooks F H)).externAt? pc = some f) :
    (∀ s, (f s).status = .Exception "ext") ∨
    (f = compress256Hook F ∧ (lib.blockProgram pl i H).externAt? pc = some f) := by
  unfold Program.externAt? Program.hookAtOff? MultiPlacedLib.blockProgram PlacedLib.program at h ⊢
  dsimp only at h ⊢
  have hnone : ∀ (l : List (String × Nat)),
      (l.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none := by
    intro l; induction l with | nil => rfl | cons _ _ ih => exact ih
  simp only [ite_self, hnone, Option.or_none] at h ⊢
  exact findSome?_hmacCompressOnlyExcHooks_cases h_c256 _ h

private theorem steps_hmacCompressOnlyExc_lift_strip
    (lib : MultiPlacedLib) (pl : MultiPlacement) (i : Nat)
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (hall_svc : (lib.blockProgram pl i (hmacCompressOnlyExcHooks F H)).allInstrs
      (fun ins => !ins.isSvc0) = true)
    (hall_msr : (lib.blockProgram pl i (hmacCompressOnlyExcHooks F H)).allInstrs
      (fun ins => !ins.isMsrTpidrEl0) = true)
    {s1' sf' : State}
    (hsteps : Steps (lib.blockProgram pl i (hmacCompressOnlyExcHooks F H)) s1' sf')
    (hrun_f : sf'.status = .Running) :
    let Q := lib.blockProgram pl i (hmacCompressOnlyExcHooks F H)
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
        rcases blockProgram_hmacCompressOnlyExcHooks_externAt?_cases h_c256 he with
          htrap | ⟨rfl, heP⟩
        · rw [htrap] at hrb'; cases hrb'
        · obtain ⟨hs2P, hkf1, hsym1⟩ := step_P_extern_eq h1_P hr2P heP
          rw [hs2P] at hrest_P
          have hstepP := Step.extern hr1 heP hkf1 hsym1
          obtain ⟨sf, hsteps_rest, hvm_rest, hor⟩ :=
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
            blockProgram_hmacCompressOnlyExcHooks_externAt?_isSome lib pl i h_c256 s1.pc
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

private theorem runsTo_block_lift_vm_compress_only_local [LibsignalPlacement] {blkLib : PlacedLib}
    {i : Nat} {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_c256 : H lsCompress256Sym = some (compress256Hook F))
    (hlib : blkLib = libsignalSessionLib.blockLib i)
    (hchk_svc : VerifiedLibraries.RustStd.checkBlockNoSvc0 blkLib.text = true := by rfl)
    (hchk_msr : checkBlockNoMsrTpidrEl0 blkLib.text = true := by rfl)
    {s : State} {PostP PostQ : State → Prop}
    (hL : (libsignalSessionLib.blockProgram lsmpl i H).CodeLoaded s.mem)
    (hrunsP : RunsTo (libsignalSessionLib.blockProgram lsmpl i H) s PostP)
    (hrunsQ : RunsTo (libsignalSessionLib.blockProgram lsmpl i (hmacCompressOnlyExcHooks F H))
      (ProofLib.stripS (ProofLib.progKeep
        (libsignalSessionLib.blockProgram lsmpl i (hmacCompressOnlyExcHooks F H))) s) PostQ)
    (hPostP_run : ∀ s', PostP s' → s'.status = .Running)
    (hPostQ_run : ∀ s', PostQ s' → s'.status = .Running) :
    let Q := libsignalSessionLib.blockProgram lsmpl i (hmacCompressOnlyExcHooks F H)
    ∃ sf : State,
      Steps (libsignalSessionLib.blockProgram lsmpl i H) s sf ∧
      VmPreserved s sf ∧
      sf.trace = s.trace ∧
      calleeSavedVRegs sf = calleeSavedVRegs s ∧
      (PostQ (ProofLib.stripS (ProofLib.progKeep Q) sf) ∨ PostP sf) := by
  subst hlib
  intro Q
  have hall_svc : Q.allInstrs (fun ins => !ins.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 libsignalSessionLib lsmpl i hchk_svc
  have hall_msr : Q.allInstrs (fun ins => !ins.isMsrTpidrEl0) = true :=
    blockProgram_allInstrs_not_isMsrTpidrEl0 libsignalSessionLib lsmpl i
      (hmacCompressOnlyExcHooks F H) hchk_msr
  have hLQ : Q.CodeLoaded s.mem := hL.of_base_code rfl rfl
  have hLQ_strip : Q.CodeLoaded (ProofLib.stripS (ProofLib.progKeep Q) s).mem := by
    have hm : (ProofLib.stripS (ProofLib.progKeep Q) s).mem =
        ProofLib.stripExecOutside (ProofLib.progKeep Q) s.mem := by cases s; rfl
    rw [hm]; exact strip_codeLoaded_of_keep hLQ
  obtain ⟨sfP, hstepsP, htrP, hvregsP, hPostP, _⟩ := hrunsP hL
  obtain ⟨sf', hstepsQ, htr', hvregs', hPost', _⟩ := hrunsQ hLQ_strip
  obtain ⟨sf, hsteps_out, hvm, hsf_eq | rfl⟩ :=
    steps_hmacCompressOnlyExc_lift_strip libsignalSessionLib lsmpl i h_c256 hall_svc hall_msr
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

section NfsSeg0Vm

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
private theorem bv_add_sub_lit (x : BitVec 64) (a b : Nat) (h : b ≤ a := by decide)
    (ha : a < 2 ^ 64 := by decide) :
    x + BitVec.ofNat 64 a - BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have : b % 2 ^ 64 = b := Nat.mod_eq_of_lt (by omega)
  have : a % 2 ^ 64 = a := Nat.mod_eq_of_lt ha
  have : (a - b) % 2 ^ 64 = a - b := Nat.mod_eq_of_lt (by omega)
  simp only [*]
  omega

attribute [local arm64_norm]
  BitVec.neg_neg bv_add_sub_lit BitVec.add_zero
  MemWidth.bytes SimdMemSize.bytes
  Memory.read8_write8_base_off_disjoint
  Memory.read8_write8_base_zero_off
  Memory.read8_write8_base_off_zero
  Memory.read8_write64_base_off_disjoint
  Memory.read8_write64_base_zero_off
  Memory.read8_write64_base_off_zero
  Memory.read8_write64_base_off_inbounds

private def NonMemVmEq (s₀ s : State) : Prop :=
  PoolPreserved s₀ s ∧ s.physMemAvail = s₀.physMemAvail ∧ s.fs = s₀.fs

private theorem NonMemVmEq.refl (s : State) : NonMemVmEq s s := ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩
private theorem NonMemVmEq.advancePC {s₀ s : State} (h : NonMemVmEq s₀ s) : NonMemVmEq s₀ s.advancePC := h
private theorem NonMemVmEq.setMem {s₀ s : State} {m : Memory} (h : NonMemVmEq s₀ s) : NonMemVmEq s₀ (s.setMem m) := h
private theorem NonMemVmEq.setPC {s₀ s : State} {pc : BitVec 64} (h : NonMemVmEq s₀ s) : NonMemVmEq s₀ (s.setPC pc) := h
private theorem NonMemVmEq.setPState {s₀ s : State} {f : PState} (h : NonMemVmEq s₀ s) : NonMemVmEq s₀ (s.setPState f) := h
private theorem NonMemVmEq.writeReg64 {s₀ s : State} {r : Reg} {v : BitVec 64} (h : NonMemVmEq s₀ s) : NonMemVmEq s₀ (s.writeReg64 r v) := h
private theorem NonMemVmEq.writeReg32 {s₀ s : State} {r : Reg} {v : BitVec 32} (h : NonMemVmEq s₀ s) : NonMemVmEq s₀ (s.writeReg32 r v) := h
private theorem NonMemVmEq.writeVReg128 {s₀ s : State} {k : BitVec 5} {v : BitVec 128} (h : NonMemVmEq s₀ s) : NonMemVmEq s₀ (s.writeVReg128 k v) := h

set_option maxHeartbeats 3200000 in
private theorem nfs_seg0_placed_exact_vm [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h_memcpy : HookSatExactMemcpy H lsMemcpySym)
    {s₀ : State}
    (hpc : s₀.pc = (blkPl_114).base)
    (hstat : s₀.status = .Running)
    (hlen : (s₀.readReg64 .x2).toNat ≤ 64)
    (hiv : s₀.mem.readBytes lsSha256IVAddr 32 = shaStateBytes sha256IV)
    (hread_iv : s₀.mem.Readable lsSha256IVAddr 32)
    (hdisj_iv_stack : DisjointRegions lsSha256IVAddr 32 (s₀.sp - 544#64) 544)
    (hrw_out : RW s₀.mem (s₀.readReg64 .x0) 0x98)
    (hrw_stack : RW s₀.mem (s₀.sp - 544#64) 544)
    (hdisj_out_stack : DisjointRegions (s₀.readReg64 .x0) 0x98 (s₀.sp - 544#64) 544)
    (hread_key_s0 : s₀.mem.Readable (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat)
    (hdisj_key_stack : (s₀.readReg64 .x2).toNat = 0 ∨
      DisjointRegions (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat (s₀.sp - 544#64) 544)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64) :
    let key := s₀.mem.readBytes (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat
    RunsTo (lsProg_114 H) s₀ (fun s' =>
      VmPreserved s₀ s' ∧
      s'.pc = (blkPl_114).base + 476#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x8 = 0x36#64 ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.readVReg128 2#5 = s'.mem.read64 (nfsSp s₀ + 152#64) ++ s'.mem.read64 (nfsSp s₀ + 144#64) ∧
      s'.readVReg128 0#5 = s'.mem.read64 (nfsSp s₀ + 168#64) ++ s'.mem.read64 (nfsSp s₀ + 160#64) ∧
      s'.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0 ∧
      s'.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) := by
  intro key
  generalize hPost : (fun s' : State => _) = Post
  have hkey_len : key.length ≤ 64 := by
    dsimp only [key]; rw [Memory.readBytes_length]; exact hlen
  have hkb_len : (keyBlock key).length = 64 := keyBlock_length hkey_len
  have hsp₀ : s₀.sp = nfsSp s₀ + 544#64 := nfs_sp_eq_add s₀
  have hal_nfs : (nfsSp s₀ &&& 0b1111#64) = 0#64 := nfs_sp_align hal
  have hal_464 : ((nfsSp s₀ + 464#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_464_align hal
  have hal_544 : ((nfsSp s₀ + 544#64) &&& 0b1111#64) = 0#64 := nfs_sp_add_544_align hal
  have hRW_stack : s₀.mem.RW (nfsSp s₀) 544 := hrw_stack
  have hcond : BitVec.ule 0x41#64 (s₀.readReg64 .x2) = false := nfs_ule_65_false hlen
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  refine RunsTo.pairStep_114_0x28 (by simp only [arm64_norm, hpc]) (by simp only [arm64_norm, hstat]) ?_
  sess_step; sess_step; sess_step; sess_step; sess_step
  have hA_pro : AgreesOutside s₀.mem (nfsPrologueMem s₀) (nfsSp s₀ + 464#64) 80 :=
    agreesOutside_nfsPrologueMem s₀
  have hA_zero : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8))
      (nfsSp s₀ + 112#64) 64 := by
    simpa using AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (List.replicate 64 0#8)
  have hread_key : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).readBytes
      (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat = key := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · simp only [key, h0, Memory.readBytes]
    have hdisj_key_pro : DisjointRegions (nfsSp s₀ + 464#64) 80 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    have hdisj_key_112 : DisjointRegions (nfsSp s₀ + 112#64) 64 (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
      clear * - hdisj_key_stack
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
    rw [(agreesOutside_toFrame hA_zero).readBytes_eq (by simp [hdisj_key_112]) (by omega),
        (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdisj_key_pro]) (by omega)]
  have hrw_memcpy : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW
      (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat := by
    have hrw0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).RW (nfsSp s₀) 544 :=
      (Frame.rw_iff (agreesOutside_toFrame hA_zero) _ _).mpr
        ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
    exact hrw0.sub (by clear * - hlen; bv_omega)
  have hreadable_memcpy :
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (List.replicate 64 0#8)).Readable
        (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat :=
    (Frame.readable_iff (agreesOutside_toFrame hA_zero) _ _).mpr
      ((Frame.readable_iff (agreesOutside_toFrame hA_pro) _ _).mpr hread_key_s0)
  have hdisj_memcpy :
      (s₀.readReg64 .x2).toNat = 0 ∨
        DisjointRegions (nfsSp s₀ + 112#64) (s₀.readReg64 .x2).toNat
          (s₀.readReg64 .x1) (s₀.readReg64 .x2).toNat := by
    rcases hdisj_key_stack with h0 | hdisj_key_stack
    · exact Or.inl h0
    · refine Or.inr ?_
      clear * - hdisj_key_stack hlen
      simp only [DisjointRegions, nfsSp] at hdisj_key_stack ⊢
      bv_omega
  refine placed_memcpy_step_of_exact h_memcpy
    (hrun := by simp only [arm64_norm, hstat])
    (hsp := by simp only [State.spAligned, arm64_norm, hal_nfs])
    (hpc := by simp only [arm64_norm, lsMemcpySym])
    (hx0 := by simp only [arm64_norm])
    (hx1 := by simp only [arm64_norm])
    (hx2 := by simp only [arm64_norm])
    (hlr := by simp only [arm64_norm]; rfl)
    (hmem := write64_oct_zero_eq_writeBytes_64 (nfsPrologueMem s₀) (nfsSp s₀))
    (hread := hread_key)
    (hrw := hrw_memcpy)
    (hreadable := hreadable_memcpy)
    (hdisj := hdisj_memcpy)
    fun c => ?_
  dsimp only [applyMemcpyClobber]
  rw [writeBytes_key_over_zero64]
  have hA_k0 : AgreesOutside (nfsPrologueMem s₀)
      ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)) (nfsSp s₀ + 112#64) 64 := by
    have h := AgreesOutside.writeBytes_self (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key)
    rwa [hkb_len] at h
  have hRW_k0 : ((nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)).RW (nfsSp s₀) 544 :=
    (Frame.rw_iff (agreesOutside_toFrame hA_k0) _ _).mpr
      ((Frame.rw_iff (agreesOutside_toFrame hA_pro) _ _).mpr hrw_stack)
  sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step; sess_step
  subst hPost
  refine RunsTo.refl ?_
  set m_k0 := (nfsPrologueMem s₀).writeBytes (nfsSp s₀ + 112#64) (keyBlock key)
  have hk0_64 : m_k0.readBytes (nfsSp s₀ + 112#64) 64 = keyBlock key :=
    Layout.readBytes_writeBytes_eq (nfsPrologueMem s₀) (nfsSp s₀ + 112#64) (keyBlock key) 64 hkb_len (by decide)
  have hk0_take32 : m_k0.readBytes (nfsSp s₀ + 112#64) 32 = (keyBlock key).take 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 0 32 (by omega)
    simpa using h
  have hk0_drop32 : m_k0.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32 := by
    have h := readBytes_slice_of_readBytes_eq m_k0 (nfsSp s₀ + 112#64) (keyBlock key)
      (by rw [hkb_len]; exact hk0_64) 32 32 (by omega)
    have hadd : (nfsSp s₀ + 112#64) + BitVec.ofNat 64 32 = nfsSp s₀ + 144#64 := by clear * -; bv_omega
    rw [hadd, List.take_of_length_le (by simp [hkb_len])] at h
    exact h
  have hA_432 : AgreesOutside m_k0 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) (nfsSp s₀ + 432#64) 8 :=
    AgreesOutside.write64_self m_k0 (nfsSp s₀ + 432#64) 1#64
  have hf_k0 : Frame s₀.mem (m_k0.write64 (nfsSp s₀ + 432#64) 1#64)
      [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := by
    have hf0 : Frame s₀.mem s₀.mem [(s₀.readReg64 .x0, 0x98), (nfsSp s₀, 544)] := Frame.refl _ _
    have hf1 := Frame.of_agreesOutside_stack hf0 hA_pro (by decide)
    have hf2 := Frame.of_agreesOutside_stack hf1 hA_k0 (by decide)
    exact Frame.of_agreesOutside_stack hf2 hA_432 (by decide)
  have hM_432 : NfsMemInv nfsPlacedFakeB s₀ (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) := {
    rw_stack := (Frame.rw_iff hf_k0 _ _).mpr hrw_stack
    rw_out := (Frame.rw_iff hf_k0 _ _).mpr hrw_out
    readable_iv := by
      rw [nfsPlacedFakeB_add_iv]
      exact (Frame.readable_iff hf_k0 _ _).mpr hread_iv
    iv_bytes := by
      rw [nfsPlacedFakeB_add_iv]
      have hd432 : DisjointRegions (nfsSp s₀ + 432#64) 8 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdk0 : DisjointRegions (nfsSp s₀ + 112#64) 64 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      have hdpro : DisjointRegions (nfsSp s₀ + 464#64) 80 lsSha256IVAddr 32 := by
        clear * - hdisj_iv_stack; simp only [DisjointRegions, nfsSp] at hdisj_iv_stack ⊢; bv_omega
      rw [(agreesOutside_toFrame hA_432).readBytes_eq (by simp [hd432]) (by decide),
          (agreesOutside_toFrame hA_k0).readBytes_eq (by simp [hdk0]) (by decide),
          (agreesOutside_toFrame hA_pro).readBytes_eq (by simp [hdpro]) (by decide), hiv]
    disj_iv_stack := by rw [nfsPlacedFakeB_add_iv]; exact hdisj_iv_stack
    disj_out_stack := hdisj_out_stack
    saved := nfsSavedStack_prologue_432 s₀ m_k0 hA_k0
    frame := hf_k0
  }
  have hM_final : NfsMemInv nfsPlacedFakeB s₀
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)) :=
    (hM_432.writeBytes_low 288#64 _ (by simp [slice16_length])).writeBytes_low
      304#64 _ (by simp [slice16_length])
  have h144_eq :
      (((m_k0.write64 (nfsSp s₀ + 432#64) 1#64).writeBytes
        (nfsSp s₀ + 288#64) (slice16 (keyBlock key) 0)).writeBytes
        (nfsSp s₀ + 304#64) (slice16 (keyBlock key) 16)).readBytes (nfsSp s₀ + 144#64) 32 =
      (keyBlock key).drop 32 := by
    rw [readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _),
        (agreesOutside_toFrame hA_432).readBytes_eq
          (by clear * -; simp only [List.mem_singleton, forall_eq, DisjointRegions]; bv_omega) (by decide),
        hk0_drop32]
  have vm_of_nm : ∀ {s' : State}, NonMemVmEq s₀ s' → (∀ a, s'.mem.perm a = s₀.mem.perm a) →
      VmPreserved s₀ s' :=
    fun hnm hp => ⟨hnm.1, hnm.2.1, hp, FdsHiFrame.of_fs_eq hnm.2.2⟩
  refine ⟨vm_of_nm (by
    repeat' (first
      | with_reducible apply NonMemVmEq.advancePC
      | with_reducible apply NonMemVmEq.setMem
      | with_reducible apply NonMemVmEq.setPC
      | with_reducible apply NonMemVmEq.setPState
      | with_reducible apply NonMemVmEq.writeReg64
      | with_reducible apply NonMemVmEq.writeReg32
      | with_reducible apply NonMemVmEq.writeVReg128
      | with_reducible exact NonMemVmEq.refl _)) (fun a => ?_),
    by simp only [arm64_norm], by simp only [arm64_norm, hstat],
    ⟨by simp only [arm64_norm], hal_nfs, by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm],
     by simp only [arm64_norm], by simp only [arm64_norm]⟩,
    ?_,
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp only [arm64_norm], by simp only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    by simp (config := { decide := true }) only [arm64_norm],
    ?_, ?_, ?_⟩
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact congrFun hM_final.frame.2.1 a
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact hM_final
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact h144_eq
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact (readBytes_writeBytes_16_other _ _ _ _ _ _ (slice16_length _ _)).trans
      (readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _))
  · dsimp only [State.setMem, State.setPC, State.setPState, State.writeReg64, State.writeVReg128, State.advancePC]
    rw [write64_quad_288_eq_writeBytes_slice16 (m_k0.write64 (nfsSp s₀ + 432#64) 1#64) m_k0
      (nfsSp s₀) (keyBlock key) hkb_len hk0_take32]
    exact readBytes_writeBytes_16_self _ _ _ _ (slice16_length _ _)

private theorem nfs_tail_from_476 [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState} {H : LibsignalHooks}
    (h_compress : H lsCompress256Sym = some (compress256Hook F))
    {s₀ s₁ : State} {key : List (BitVec 8)}
    (hkey_len : key.length ≤ 64)
    (hal : (s₀.sp &&& 0b1111#64) = 0#64)
    (hpc1 : s₁.pc = (blkPl_114).base + 476#64)
    (hstat1 : s₁.status = .Running)
    (hR1 : NfsRegInv nfsPlacedFakeB s₀ s₁)
    (hM1 : NfsMemInv nfsPlacedFakeB s₀ s₁.mem)
    (hx8_1 : s₁.readReg64 .x8 = 0x36#64)
    (hx0_1 : s₁.readReg64 .x0 = nfsSp s₀ + 400#64)
    (hx1_1 : s₁.readReg64 .x1 = nfsSp s₀ + 288#64)
    (hx2_1 : s₁.readReg64 .x2 = 1#64)
    (hq2_1 : s₁.readVReg128 2#5 = s₁.mem.read64 (nfsSp s₀ + 152#64) ++ s₁.mem.read64 (nfsSp s₀ + 144#64))
    (hq0_1 : s₁.readVReg128 0#5 = s₁.mem.read64 (nfsSp s₀ + 168#64) ++ s₁.mem.read64 (nfsSp s₀ + 160#64))
    (hk0_1 : s₁.mem.readBytes (nfsSp s₀ + 144#64) 32 = (keyBlock key).drop 32)
    (hs0_1 : s₁.mem.readBytes (nfsSp s₀ + 288#64) 16 = slice16 (keyBlock key) 0)
    (hs16_1 : s₁.mem.readBytes (nfsSp s₀ + 304#64) 16 = slice16 (keyBlock key) 16) :
    RunsTo (lsProg_114 H) s₁ (fun s' =>
      s'.pc = s₀.readReg64 .lr ∧ s'.status = .Running ∧ CalleeSaved s₀ s' ∧
      s'.mem.read64 (s₀.readReg64 .x0) = 0#64 ∧ HmacSt s'.mem (s₀.readReg64 .x0 + 8#64) F key [] ∧
      Frame s₀.mem s'.mem [(s₀.readReg64 .x0, 0x98), (s₀.sp - 544#64, 544)]) := by
  have hfirst_tail : RunsTo (lsProg_114 H) s₁ (fun s' =>
      s'.pc = (blkPl_114).base + 1260#64 ∧
      s'.status = .Running ∧
      NfsRegInv nfsPlacedFakeB s₀ s' ∧
      NfsMemInv nfsPlacedFakeB s₀ s'.mem ∧
      s'.readReg64 .x0 = nfsSp s₀ + 400#64 ∧
      s'.readReg64 .x1 = nfsSp s₀ + 288#64 ∧
      s'.readReg64 .x2 = 1#64 ∧
      s'.mem.readBytes (nfsSp s₀ + 400#64) 32 = shaStateBytes sha256IV ∧
      s'.mem.readBytes (nfsSp s₀ + 288#64) 64 = (keyBlock key).map (· ^^^ 0x36#8) ∧
      s'.mem.readBytes (nfsSp s₀) 32 =
        (shaStateBytes sha256IV).drop 16 ++ (shaStateBytes sha256IV).take 16) := by
    refine (nfs_chunk1_placed hkey_len hpc1 hstat1 hR1 hM1 hx8_1 hx0_1 hx1_1 hx2_1 hs0_1 hs16_1).trans fun s2 h2 => ?_
    rcases h2 with ⟨hpc2, hstat2, hR2, hM2, hx8_2, hx0_2, hx1_2, hx2_2, hx10_2, hx11_2, hq2_2, hq0_2, hs0_2, hs16_2⟩
    refine (nfs_chunk2_placed hkey_len hal hpc2 hstat2 hR2 hM2 hx8_2 hx0_2 hx1_2 hx2_2 hx10_2 hx11_2
      (hq2_2.trans hq2_1) (hq0_2.trans hq0_1) hk0_1 hs0_2 hs16_2).trans fun s3 h3 => ?_
    rcases h3 with ⟨hpc3, hstat3, hR3, hM3, hx8_3, hx0_3, hx1_3, hx2_3, hx11_3, hx9_3, hs0_3, hs16_3, hs32_3, hs48_3⟩
    refine (nfs_chunk3_placed hkey_len hpc3 hstat3 hR3 hM3 hx8_3 hx0_3 hx1_3 hx2_3 hx11_3 hx9_3
      hs0_3 hs16_3 hs32_3 hs48_3).trans fun s4 h4 => ?_
    rcases h4 with ⟨hpc4, hstat4, hR4, hM4, hx8_4, hx0_4, hx1_4, hx2_4, hx9_4, hx10_4, hs0_4, hs16_4, hs32_4, hs48_4⟩
    exact nfs_chunk4_placed hkey_len hal hpc4 hstat4 hR4 hM4 hx8_4 hx0_4 hx1_4 hx2_4 hx9_4 hx10_4
      hs0_4 hs16_4 hs32_4 hs48_4
  refine hfirst_tail.trans fun s5 h5 => ?_
  rcases h5 with ⟨hpc5, hstat5, hR5, hM5, hx0_5, hx1_5, hx2_5, hist5, hblk5, hivsw5⟩
  exact nfs_second_half_placed h_compress hkey_len hal hpc5 hstat5 hR5 hM5 hx0_5 hx1_5 hx2_5
    hist5 hblk5 hivsw5

end NfsSeg0Vm

private theorem stripS_mem (p : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS p s).mem = ProofLib.stripExecOutside p s.mem := by cases s; rfl
private theorem stripS_pc (p : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS p s).pc = s.pc := by cases s; rfl
private theorem stripS_status (p : BitVec 64 → Bool) (s : State) :
    (ProofLib.stripS p s).status = s.status := by cases s; rfl
private theorem stripS_readVReg128 (p : BitVec 64 → Bool) (s : State) (i : BitVec 5) :
    (ProofLib.stripS p s).readVReg128 i = s.readVReg128 i := by cases s; rfl
private theorem stripS_nfsSp (p : BitVec 64 → Bool) (s : State) :
    nfsSp (ProofLib.stripS p s) = nfsSp s := by simp [nfsSp, stripS_sp]
private theorem nfsRegInv_stripS (p : BitVec 64 → Bool) {b : BitVec 64} {s₀ s₁ : State}
    (h : NfsRegInv b s₀ s₁) : NfsRegInv b (ProofLib.stripS p s₀) (ProofLib.stripS p s₁) :=
  ⟨by rw [stripS_sp, stripS_nfsSp]; exact h.sp_eq, by rw [stripS_nfsSp]; exact h.sp_align,
   by rw [stripS_readReg64, stripS_nfsSp]; exact h.x29_eq,
   by rw [stripS_readReg64, stripS_readReg64]; exact h.x19_eq,
   by rw [stripS_readReg64]; exact h.x20_eq, by rw [stripS_readReg64]; exact h.x22_eq,
   by rw [stripS_readReg64, stripS_readReg64]; exact h.x25_eq,
   by rw [stripS_readReg64, stripS_readReg64]; exact h.x26_eq,
   by rw [stripS_readReg64, stripS_readReg64]; exact h.x27_eq⟩
private theorem calleeSaved_of_stripS (p : BitVec 64 → Bool) {s₀ sf : State}
    (h : CalleeSaved (ProofLib.stripS p s₀) (ProofLib.stripS p sf)) : CalleeSaved s₀ sf :=
  ⟨by simpa only [stripS_sp] using h.1, fun r hr => by simpa only [stripS_readReg64] using h.2 r hr⟩

private theorem new_from_slice_114_ro_vm_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok ((blkPC_114).rebase (blkPl_114).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_114).base
      { newFromSliceBudgetSpec W.C.F with
        pre := fun x s0 => (newFromSliceBudgetSpec W.C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝ } := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  apply subroutine_ok_intro; intro ⟨ret, keyA, key⟩ R s0 hpc hrun hpre hsp hL
  dsimp only [newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec] at hpre
  rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hro, ⟨hx0, hx1, hx2_nat, hkey_len⟩, hsep⟩
  have hb_out := IsBlock.memRegion ret 0x98; have hb_key := IsBlock.pointsToBytes (a := keyA) key
  have hb_stk := IsBlock.memRegion (s0.sp - 544#64) 544
  have hsep_out : s0.mem ⊨ memRegion ret 0x98 ∗ (memRegion (s0.sp - 544#64) 544 ∗ ((keyA ↦ₛ key) ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep; ac_nf at hsep ⊢
  have hsep_key : s0.mem ⊨ (keyA ↦ₛ key) ∗ (memRegion (s0.sp - 544#64) 544 ∗ (memRegion ret 0x98 ∗ R)) := by
    simp only [newFromSliceStack, stackAt] at hsep; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 544#64) 544 ∗ (memRegion ret 0x98 ∗ (keyA ↦ₛ key) ∗ R) := by
    simp only [newFromSliceStack, stackAt] at hsep; ac_nf at hsep ⊢
  have hkey_eq : s0.mem.readBytes keyA key.length = key := (hb_key.read hsep_key).2
  have hread_key : s0.mem.Readable keyA key.length := by
    intro a ha
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp (hb_key.permNoLazy_rw hsep_key ha)
    exact ⟨by rw [hp]; rfl, hlf⟩
  obtain ⟨hro_iv, hiv_eq⟩ := rodata_placed_sha256IV hro
  have hrw_out : s0.mem.RW ret 0x98 := fun a ha => hb_out.permNoLazy_rw hsep_out ha
  have hrw_stk : s0.mem.RW (s0.sp - 544#64) 544 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hread_iv : s0.mem.Readable lsSha256IVAddr 32 := fun a ha => ⟨by rw [(hro_iv a ha).1]; rfl, (hro_iv a ha).2⟩
  have hdisj_iv := disjointRegions_of_ro_rw (by decide) (by decide) hro_iv hrw_stk
  have hdisj_out := hb_out.disjoint hb_stk (by decide) (by decide) hsep_out
  have hdisj_key : key.length = 0 ∨ DisjointRegions keyA key.length (s0.sp - 544#64) 544 := by
    cases key with
    | nil => exact Or.inl rfl
    | cons _ _ => exact Or.inr (hb_key.disjoint hb_stk (by simp) (by decide) hsep_key)
  have hmc : HookSatExactMemcpy H lsMemcpySym := cliExternsPlaced_exactMemcpy_sat mmpl g W hG
  have hc256 : H lsCompress256Sym = some (compress256Hook W.C.F) :=
    cliGhost_row mmpl g W (compress256_row_placed mmpl W)
  have heq114 : ∀ X, lsProg_114 X = libsignalSessionLib.blockProgram lsmpl 114 X := fun X =>
    IsLsBlockProg.eq_blockProgram (prog := lsProg_114 X)
  have heq114' : (blkPC_114).rebase (blkPl_114).base H = libsignalSessionLib.blockProgram lsmpl 114 H :=
    IsLsBlockProg.eq_blockProgram
  have hal : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hL_ls : (lsProg_114 H).CodeLoaded s0.mem := by rw [heq114 H, ← heq114']; exact hL
  obtain ⟨s1, hsteps1_ls, htr1, hvregs1, hPost1, hL1_ls⟩ :=
    nfs_seg0_placed_exact_vm hmc hpc hrun (by rw [hx2_nat]; exact hkey_len)
      hiv_eq hread_iv hdisj_iv (by rw [hx0]; exact hrw_out) hrw_stk (by rw [hx0]; exact hdisj_out)
      (by rw [hx1, hx2_nat]; exact hread_key) (by rw [hx1, hx2_nat]; exact hdisj_key) hal hL_ls
  rw [hx1, hx2_nat, hkey_eq] at hPost1
  rcases hPost1 with ⟨hvm1, hpc1, hstat1, hR1, hM1, hx8_1, hx0_1, hx1_1, hx2_1,
    hq2_1, hq0_1, hk0_1, hs0_1, hs16_1⟩
  let kp := ProofLib.progKeep
    (libsignalSessionLib.blockProgram lsmpl 114 (hmacCompressOnlyExcHooks W.C.F H))
  have hm_s0 := stripS_mem kp s0
  have hm_s1 := stripS_mem kp s1
  have hsp_strip := stripS_nfsSp kp s0
  have hM1_strip : NfsMemInv nfsPlacedFakeB (ProofLib.stripS kp s0) (ProofLib.stripS kp s1).mem := {
    rw_stack := by rw [hm_s1, hsp_strip]; exact stripExecOutside_rw kp s1.mem _ _ hM1.rw_stack
    rw_out := by rw [hm_s1, stripS_readReg64]; exact stripExecOutside_rw kp s1.mem _ _ hM1.rw_out
    readable_iv := by rw [hm_s1]; exact stripExecOutside_readable kp s1.mem _ _ hM1.readable_iv
    iv_bytes := by rw [hm_s1, stripExecOutside_readBytes]; exact hM1.iv_bytes
    disj_iv_stack := by rw [hsp_strip]; exact hM1.disj_iv_stack
    disj_out_stack := by rw [stripS_readReg64, hsp_strip]; exact hM1.disj_out_stack
    saved := by
      cases hM1.saved with | mk m432 m464 m472 m480 m496 m504 m512 m520 m528 m536 =>
      exact ⟨by rw [stripS_read64, hsp_strip]; exact m432,
             by rw [stripS_read64, hsp_strip, stripS_readReg64]; exact m464,
             by rw [stripS_read64, hsp_strip, stripS_readReg64]; exact m472,
             by rw [stripS_read64, hsp_strip, stripS_readReg64]; exact m480,
             by rw [stripS_read64, hsp_strip, stripS_readReg64]; exact m496,
             by rw [stripS_read64, hsp_strip, stripS_readReg64]; exact m504,
             by rw [stripS_read64, hsp_strip, stripS_readReg64]; exact m512,
             by rw [stripS_read64, hsp_strip, stripS_readReg64]; exact m520,
             by rw [stripS_read64, hsp_strip, stripS_readReg64]; exact m528,
             by rw [stripS_read64, hsp_strip, stripS_readReg64]; exact m536⟩
    frame := by rw [hm_s0, hm_s1, stripS_readReg64, hsp_strip]; exact stripExecOutside_frame kp hM1.frame
  }
  have hrunsP_tail := nfs_tail_from_476 hc256 hkey_len hal hpc1 hstat1 hR1 hM1
    hx8_1 hx0_1 hx1_1 hx2_1 hq2_1 hq0_1 hk0_1 hs0_1 hs16_1
  have hrunsQ_tail := nfs_tail_from_476 (s₀ := ProofLib.stripS kp s0) (s₁ := ProofLib.stripS kp s1)
    (hmacCompressOnlyExcHooks_compress W.C.F H) hkey_len
    (by simpa only [stripS_sp] using hal)
    (by rw [stripS_pc]; exact hpc1)
    (by rw [stripS_status]; exact hstat1)
    (nfsRegInv_stripS kp hR1)
    hM1_strip
    (by rw [stripS_readReg64]; exact hx8_1)
    (by rw [stripS_readReg64, hsp_strip]; exact hx0_1)
    (by rw [stripS_readReg64, hsp_strip]; exact hx1_1)
    (by rw [stripS_readReg64]; exact hx2_1)
    (by rw [stripS_readVReg128, stripS_read64, stripS_read64, hsp_strip]; exact hq2_1)
    (by rw [stripS_readVReg128, stripS_read64, stripS_read64, hsp_strip]; exact hq0_1)
    (by rw [hm_s1, hsp_strip, stripExecOutside_readBytes]; exact hk0_1)
    (by rw [hm_s1, hsp_strip, stripExecOutside_readBytes]; exact hs0_1)
    (by rw [hm_s1, hsp_strip, stripExecOutside_readBytes]; exact hs16_1)
  have hL1_bp : (libsignalSessionLib.blockProgram lsmpl 114 H).CodeLoaded s1.mem :=
    heq114 H ▸ hL1_ls
  obtain ⟨sf, hsteps2_bp, hvm2, htr2, hvregs2, hsf_or⟩ :=
    runsTo_block_lift_vm_compress_only_local hc256 blkLib_eq_114 rfl rfl hL1_bp
      (heq114 _ ▸ hrunsP_tail) (heq114 _ ▸ hrunsQ_tail)
      (fun _ hs => hs.2.1) (fun _ hs => hs.2.1)
  have hvm : VmPreserved s0 sf := hvm1.trans hvm2
  have htr : sf.trace = s0.trace := htr2.trans htr1
  have hvregs : calleeSavedVRegs sf = calleeSavedVRegs s0 := hvregs2.trans hvregs1
  have hsteps_bp : Steps (libsignalSessionLib.blockProgram lsmpl 114 H) s0 sf :=
    (heq114 H ▸ hsteps1_ls).trans hsteps2_bp
  have hraw : sf.pc = s0.readReg64 .x30 ∧ sf.status = .Running ∧
      CalleeSaved s0 sf ∧
      sf.mem.read64 ret = 0#64 ∧ HmacSt sf.mem (ret + 8#64) W.C.F key [] ∧
      Frame s0.mem sf.mem [(ret, 0x98), (s0.sp - 544#64, 544)] := by
    rcases hsf_or with ⟨hpc_f, hst_f, hcs_f, hr_f, hh_f, hfr_f⟩ | ⟨hpc_f, hst_f, hcs_f, hr_f, hh_f, hfr_f⟩
    · have hm_sf := stripS_mem kp sf
      rw [stripS_readReg64, hx0, stripS_read64] at hr_f
      rw [hm_s0, hm_sf, stripS_readReg64, stripS_sp, hx0] at hfr_f
      rw [hm_sf, stripS_readReg64, hx0, stripExecOutside_hmacSt] at hh_f
      exact ⟨by simpa only [stripS_pc, stripS_readReg64] using hpc_f,
             by simpa only [stripS_status] using hst_f,
             calleeSaved_of_stripS kp hcs_f, hr_f, hh_f, unstrip_frame hfr_f hvm.perm_eq⟩
    · rw [hx0] at hr_f hh_f hfr_f
      exact ⟨hpc_f, hst_f, hcs_f, hr_f, hh_f, hfr_f⟩
  rcases hraw with ⟨hpc_sf, hstat_sf, hcallee, hret_sf, hst_sf, hframe_sf⟩
  refine ⟨sf, heq114' ▸ hsteps_bp,
    Or.inl ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee hvregs⟩⟩
  dsimp only [newFromSliceBudgetSpec, withVmPreserved, newFromSliceSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, htr, ?_⟩
  have hpost := Frame.update_two_blocks hb_out (isBlock_nfsResult W.C.F ret key) hb_stk hb_stk
    hsep_out hframe_sf ⟨hret_sf, hst_sf⟩ trivial
  simp only [newFromSliceStack, stackAt]; ac_nf at hpost ⊢

private theorem new_from_slice_60_cro_ok [LibsignalPlacement]
    {M : AllocCostModel} {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) :
    subroutine_ok ((blkPC_60).rebase (blkPl_60).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (lsmpl.base 114) (withLsCodeRoLoaded lsmpl (newFromSliceBudgetSpec W.C.F)) := by
  have hblk := ls_subroutine_ok_of_block
    (callerProg := (blkPC_60).rebase (blkPl_60).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
    (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl) (new_from_slice_114_ro_vm_ok mmpl g W hG))
  refine subroutine_ok_mono hblk (fun x R s0 hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [withLsCodeRoLoaded, withLsCodeLoaded] at hp ⊢
  have h1 : ((newFromSliceBudgetSpec W.C.F).pre x s0 ∗ ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeRoLoaded lsmpl s0.mem⌝ ∗ ((newFromSliceBudgetSpec W.C.F).pre x s0 ∗ R) := by
    sep_ac_rfl
  have h2 : (((newFromSliceBudgetSpec W.C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded lsmpl s0.mem⌝ ∗ (⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗
        ((newFromSliceBudgetSpec W.C.F).pre x s0 ∗ R)) := by
    sep_ac_rfl
  rw [h1, satisfies_pure_sepConj] at hp
  rw [h2, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

private theorem parseSid_61_ok [LibsignalPlacement] (H : LibsignalHooks) :
    subroutine_ok ((blkPC_61).rebase (blkPl_61).base H) (lsmpl.base 206)
      (withLsCodeLoaded lsmpl (parseSidCodeBudgetSpec uuidTryParse)) := by
  have huuid :
      subroutine_ok ((blkPC_252).rebase (blkPl_252).base H) (blkPl_252).base
        (withLsCodeLoaded lsmpl (uuidTryParseCodeBudgetSpec uuidTryParse)) := by
    refine subroutine_ok_mono (uuidTryParse_placed_vm_ok H)
      (fun _ _ _ hp => hp) (fun _ _ _ _ hq => ?_)
    dsimp only [withLsCodeLoaded, uuidTryParseCodeBudgetSpec, withVmPreserved, Spec.keepsFs] at hq ⊢
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rcases hq with ⟨hvm, hq⟩
    rw [sepConj_assoc, satisfies_pure_sepConj] at hq
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hvm, hq.2⟩
  exact parse_sid_placed_ok_at_of_code (prog := (blkPC_61).rebase (blkPl_61).base H) huuid

/-- `S6SeamPlaced` on Block `507` at `cliGhostExterns g (cliExternsPlaced mmpl W)` under
`HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym sessionMemsetRegionBudgetSpec`. -/
theorem s6_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (ctl : BitVec 64) :
    S6SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl s6FreeOnlyEnv := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  have _ : HkdfPlacedHooksExactSat W.C.F H := mkHkdfPlacedHooksExactSat_cli mmpl g W hG
  have _ : HkdfPlacedHooksExactBudgetSat W.C.F H := HkdfPlacedHooksExactBudgetSat.of_exactSat hMs
  have hext69 := extract_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_69).rebase (blkPl_69).base H) H
  have hexp69 := expand_multi_info_placed_vm_ok_of_other_block_sat W.C
    (callerProg := (blkPC_69).rebase (blkPl_69).base H) H
  have hgen69 := generateKeys_placed_ok_of_contracts hext69 hexp69
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
  exact deriveKeys_507_placed_ok W.C A lim ctl H
    (keys_ls_subroutine_ok_of_block_cro (callerProg := (blkPC_508).rebase (blkPl_508).base H) hgen69)

/-- `S9SeamPlaced` on Block `507` at `cliGhostExterns g (cliExternsPlaced mmpl W)`. -/
theorem s9_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g) (ctl : BitVec 64) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    S9SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S tdEnv s9Env := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  have hTrApply58 := trApply_placed_ok
    ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (framelessMemcpy_budget_sat mmpl g W hG)
  have hClearUpk35 := subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
    (clear_unacknowledged_pre_key_message_placed_ok
      (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))
  exact applyRatchet_507_placed_ok W.C A lim ctl S tdEnv H
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H) hTrApply58))
    (subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (ls_subroutine_ok_of_block (callerProg := (blkPC_508).rebase (blkPl_508).base H) hClearUpk35))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

/-- `HookSat`-parameterized `S7SeamPlaced` on Block `507` at
`cliGhostExterns g (cliExternsPlaced mmpl W)` under `hMs`. -/
theorem s7_507_cli_of_hMs [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (hMs : HookSat (cliGhostExterns g (cliExternsPlaced mmpl W)) lsMemsetSym
      sessionMemsetRegionBudgetSpec)
    (ctl : BitVec 64) (S : SpqrModel) :
    S7SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S (s7Env W.C.F uuidTryParse) := by
  let H := cliGhostExterns g (cliExternsPlaced mmpl W)
  have _ := instIsLsBlockProg_508 H
  have hpk60 := subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := (blkPC_60).rebase (blkPl_60).base H)
      (subroutine_ok_withLsCodeLoaded_of_plain (pl := lsmpl)
        (public_key_serialize_placed_ok
          ⟨hookNoop, (cliGhostExterns_shim g _).trans (congrArg some hG.shim_eq), noAllocShim_hookOk⟩
          (cliExternsPlaced_alloc_budget_sat mmpl g W hG))))
  have hvmac62 := verifyMacWithAddresses_placed_cro_ok W.C M A lim uuidTryParse H
    (parseSid_61_ok H) (new_from_slice_60_cro_ok mmpl g W hG) hpk60
    (keys_ls_hook_ok_of_mem
      (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
        (cliExternsPlaced_blackBox_budget_sat mmpl W)))
    (cliExternsPlaced_noAllocShim_budget_sat mmpl g W hG.shim_eq)
    (cliExternsPlaced_alloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_dealloc_budget_sat mmpl g W hG)
    (cliExternsPlaced_sessionMemcpyRegion_budget_sat mmpl g W hG)
    (cliGhostExterns_sat_of_cliExternsPlaced mmpl g W
      (cliExternsPlaced_compress256Multi_budget_sat mmpl W))
    hMs
  exact verifyMac_507_placed_ok W.C A lim ctl S H
    (keys_ls_subroutine_ok_of_block_cro (callerProg := (blkPC_508).rebase (blkPl_508).base H) hvmac62)
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_shim_budget_sat mmpl g W hG.shim_eq))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_alloc_budget_sat mmpl g W hG))
    (keys_ls_hook_ok_of_mem (cliExternsPlaced_dealloc_budget_sat mmpl g W hG))

/-- `S7SeamPlaced` on Block `507` at `cliGhostExterns g (cliExternsPlaced mmpl W)` from
`CliGhostAllocHooks M A lim g`. -/
theorem s7_507_cli [LibsignalPlacement] {M : AllocCostModel}
    {A : RustCliAllocBudget M} {lim : BudgetLimits}
    (mmpl : Obj.MultiPlacement) (g : CliGhostHooks) (W : CliHooks)
    (hG : CliGhostAllocHooks M A lim g)
    (ctl : BitVec 64) (S : SpqrModel) :
    S7SeamPlaced
      ((blkPC_508).rebase (blkPl_508).base (cliGhostExterns g (cliExternsPlaced mmpl W)))
      (blkPl_508).base W.C A lim ctl uuidTryParse S (s7Env W.C.F uuidTryParse) :=
  s7_507_cli_of_hMs mmpl g W hG
    (cliExternsPlaced_sessionMemsetRegion_budget_sat mmpl g W hG)
    ctl S

end LibsignalBinary.Proofs.Cli.E2E.Pqxdh.DecryptPq.RootTrapPlacedBudgetPart3Sat
