/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCallees
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget
import LibsignalBinary.Proofs.AesCbc.Bytes
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedA
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlaced
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfLongPlacedA
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExpandCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.FinalizeFixed
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.OpcodeExclusion
import ProofLib.SepLogic.WP.Apply

/-!
# `VmPreserved` Lockstep Bridges for Block `53` (`96` B) and Block `54` (`GenericHkdf::extract`)

Proves `expand_multi_info_96_46_placed_vm_ok` (Block `53`), `extract_placed_vm_ok_cro` (Block `54`,
`ikm.length = 32`), and `pqxdhHkdfExtractNone_placed_ok_block54` (Block `54`,
`ikm.length ∈ {160, 192, 224}`) with `VmPreserved` under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAux

open Arm64 ProofLib SepProp BitVec
open CryptoGames.HMAC (hmacWith)
open CryptoGames.HKDF (hkdfExpand hkdfExtract)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
   blkLib_114 blkLib_eq_114 blkPC_114 blkPl_114
   libsignalRoLoaded_of_keepsFrozen libsignalSessionLib
   ls_externAt?_blockProgram_eq_of_externs_eq lsmpl prog_eq_blockProgram withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (memcpyHook memsetHook returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState)
open CryptoVerification.LibsignalTripleRatchet
  (CalleeSaved CallingConventionPreserved_of_calleeSaved ExtractGhost Frame HkdfPlacedHooks
   HmacSt LibsignalCodeRoLoaded RunsTo TraceEq
   blkLib_123 blkLib_53 blkLib_54 blkLib_eq_123 blkLib_eq_53 blkLib_eq_54
   blkPC_123 blkPC_53 blkPC_54 blkPl_123 blkPl_53 blkPl_54
   effectiveSalt expPlacedFakeB expPlacedFakeB_off_0 expandMultiInfoStack
   extPlacedFakeB extPlacedFakeB_off_380 extractSpec extractStack extract_withLsCodeRoLoaded
   finPlacedFakeB finPlacedFakeB_off_0 finalizeFixedStack
   hmacCoreAt isBlock_hmacCoreAt length_hmacWith lsCompress256Sym lsMemcpySym lsMemsetSym
   newFromSliceSpec newFromSliceStack optSaltAt ro_outside_rw_shared_lb withLsCodeRoLoaded)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (new_from_slice_placed_ro_ok)
open CryptoVerification.LibsignalTripleRatchet.Expand
  (ExpandCommon ExpandFrame ExpandPost StateLoop StateLoopFin StateX2Placed StateX2r
   esp esp_aligned t1 t1_length t2 t2_length t3 t3_length)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (EPost ERetFin ExtFrame ExtSaved RunsToE S2Frame
   disj_sp0_off disj_sp0_sub_off disj_stk_sub_right
   effectiveSalt_length
   fin_placed_runsTo nfs1_placed_runsTo nfs2_placed_runsTo
   rw_stk_sub saltPtrOf
   seg0_placed_runsTo seg1a_placed_runsTo seg1b_placed_runsTo seg1c_placed_runsTo
   seg2_placed_runsTo seg3_placed_runsTo sp0_aligned sp0_aligned_0b1111)
open CryptoVerification.LibsignalTripleRatchet.FinalizeFixedProof
  (FinPre finalize_fixed_placed_runsTo)
open CryptoVerification.LibsignalTripleRatchet.Keys (stackAt_alloc_extract)
open CryptoVerification.E2E.Pqxdh.Initiator
  (Bytes Primitives bytesToBv8 hkdfExtractRef hkdfExtractRef_length)
open CryptoVerification.E2E.Pqxdh.ResponderCore
  (EFinLongPlaced ExpandPre96_46 FinGenPre PrimitivesMatchCrypto
   StateLoopC_96Placed
   bytesToBv8_hkdfExtractRef_none bytesToBv8_length
   epilogue_96_placed_runsTo expandMultiInfo96_46Spec
   finalize_fixed_gen_placed_runsTo hkdfExpand_96_eq
   iter_a1_96_placed_runsTo iter_a2_96_placed_runsTo
   iter_b1_96_placed_runsTo iter_b2_96_placed_runsTo iter_b3_96_placed_runsTo
   iter_c_96_placed_runsTo iter_d_continue_96_placed_runsTo iter_d_done_96_placed_runsTo
   nfs1_long_placed_runsTo pqxdhHmacStateAt_eq
   seg0_96_placed_runsTo seg0_long_placed_runsTo seg1_96_placed_runsTo
   seg1a_long_placed_runsTo seg1b1_long_placed_runsTo seg1b2_long_placed_runsTo
   seg1c_long_placed_runsTo seg2a_96_placed_runsTo seg2b_96_placed_runsTo seg3_96_placed_runsTo)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDeriveBudget
  (pqxdhHkdfExtractNonePlacedSpec)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (checkBlockSafeVm placedLib_rebase_allInstrs_safeVm stripS_calleeSavedVRegs
   stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace vmTrapHooks)
open LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget (extractBudgetSpec)

/-! ## 1. Shared KDF `VmPreserved` & `stripExecOutside` Lockstep Infrastructure -/

private def VmNoTpidr (s₁ s₂ : State) : Prop :=
  (s₂.brkStart = s₁.brkStart ∧ s₂.brk = s₁.brk) ∧
  s₂.physMemAvail = s₁.physMemAvail ∧
  (∀ a, s₂.mem.perm a = s₁.mem.perm a) ∧
  LibsignalBinary.Heap.FdsHiFrame s₁ s₂

private theorem VmNoTpidr.toVmPreserved {s₁ s₂ : State}
    (h : VmNoTpidr s₁ s₂) (htp : s₂.tpidrEl0 = s₁.tpidrEl0) : VmPreserved s₁ s₂ :=
  ⟨⟨h.1.1, h.1.2, htp⟩, h.2.1, h.2.2.1, h.2.2.2⟩

private theorem vmNoTpidr_execInst {inst : Instr} (hnsvc0 : inst.isSvc0 = false) (s : State) :
    VmNoTpidr s (execInst inst s) := by
  have h := ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s
  exact ⟨⟨h.2.2.2.1, h.2.2.1⟩, h.2.2.2.2.1, fun a => congrFun h.2.1 a,
    LibsignalBinary.Heap.FdsHiFrame.of_fs_eq h.2.2.2.2.2.2⟩

private theorem findSome?_symbols_none {α : Type} :
    ∀ (syms : List (String × Nat)) {off : Nat},
      (syms.findSome? fun x => if x.2 == off then (none : Option α) else none) = none
  | [], _ => rfl
  | _ :: rest, _ => by
    rw [List.findSome?_cons, ite_self]
    exact findSome?_symbols_none rest

private def kdfOnlyHooks (H : LibsignalHooks) : LibsignalHooks :=
  fun n =>
    if n == lsMemsetSym || n == lsMemcpySym || n == lsCompress256Sym then H n
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

private instance instHkdfPlacedHooks_kdfOnly (C : Crypto) {H : LibsignalHooks}
    [hH : HkdfPlacedHooks C.F H] : HkdfPlacedHooks C.F (kdfOnlyHooks H) where
  memset := by simp [kdfOnlyHooks, hH.memset]
  memcpy := by simp [kdfOnlyHooks, hH.memcpy]
  compress256 := by simp [kdfOnlyHooks, hH.compress256]

private theorem strip_codeLoaded_of_keep_sub {R : Program} {keep : BitVec 64 → Bool} {m : Memory}
    (hsub : ∀ a, ProofLib.progKeep R a = true → keep a = true)
    (hL : R.CodeLoaded m) : R.CodeLoaded (ProofLib.stripExecOutside keep m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub_add : R.base + BitVec.ofNat 64 i - R.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : keep (R.base + BitVec.ofNat 64 i) = true := by
    apply hsub
    unfold ProofLib.progKeep
    rw [hsub_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ∀ n, (ProofLib.stripExecOutside keep m).readBytes a n = m.readBytes a n
  | 0 => rfl
  | n + 1 => by
    simp [Memory.readBytes, ProofLib.strip_read8, strip_readBytes keep m (a + 1#64) n]

private theorem strip_read32 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (ProofLib.stripExecOutside keep m).read32 a = m.read32 a := by
  simp [Memory.read32, ProofLib.strip_read8]

private theorem strip_read64 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (ProofLib.stripExecOutside keep m).read64 a = m.read64 a := by
  simp [Memory.read64, ProofLib.strip_read8]

private theorem strip_readShaState (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    readShaState (ProofLib.stripExecOutside keep m) a = readShaState m a := by
  unfold readShaState
  congr 1; funext i
  exact strip_read32 keep m _

private theorem strip_writeBytes_comm (keep : BitVec 64 → Bool) :
    ∀ (bs : List (BitVec 8)) (m : Memory) (a : BitVec 64),
      (ProofLib.stripExecOutside keep m).writeBytes a bs =
        ProofLib.stripExecOutside keep (m.writeBytes a bs)
  | [], _, _ => rfl
  | b :: bs, m, a => by
    simp only [Memory.writeBytes]
    rw [ProofLib.strip_write8, strip_writeBytes_comm keep bs (m.write8 a b) (a + 1#64)]

private theorem strip_permNoLazy_rw {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (h : m.permNoLazy a = some Perm.rw) :
    (ProofLib.stripExecOutside keep m).permNoLazy a = some Perm.rw := by
  dsimp only [ProofLib.stripExecOutside, Memory.permNoLazy] at h ⊢
  rcases hc : m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> simp [hc, Perm.rw] at h ⊢
  rcases h with ⟨rfl, rfl, rfl, rfl⟩; cases keep a <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem strip_perm_ro {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (h : m.perm a = some Perm.ro) :
    (ProofLib.stripExecOutside keep m).perm a = some Perm.ro := by
  dsimp only [ProofLib.stripExecOutside, ProofLib.stripPerm, Memory.perm, Perm.rwx, Perm.ro] at h ⊢
  rcases hc : m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> simp [hc] at h ⊢
  rcases h with ⟨rfl, rfl, rfl⟩; cases keep a <;> simp

private theorem strip_perm_r (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ((ProofLib.stripExecOutside keep m).perm a).r = (m.perm a).r := by
  dsimp only [ProofLib.stripExecOutside, ProofLib.stripPerm, Memory.perm, Perm.rwx, Option.r]
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩
  · rfl
  · rfl
  · cases keep a <;> cases x <;> rfl

private theorem strip_perm_mapped (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ((ProofLib.stripExecOutside keep m).perm a).mapped = (m.perm a).mapped := by
  dsimp only [ProofLib.stripExecOutside, ProofLib.stripPerm, Memory.perm, Perm.rwx, Option.mapped]
  rcases m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> cases keep a <;> rfl

private theorem strip_perm_of_protNone {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (h : m.perm a = some Perm.protNone) :
    (ProofLib.stripExecOutside keep m).perm a = some Perm.protNone := by
  dsimp only [ProofLib.stripExecOutside, ProofLib.stripPerm, Memory.perm, Perm.rwx, Perm.protNone] at h ⊢
  rcases hc : m.cells a with _ | ⟨_ | ⟨r, w, x, lf, an⟩, _⟩ <;> simp [hc] at h ⊢
  rcases h with ⟨rfl, rfl, rfl⟩
  cases keep a <;> simp

private theorem holdsBytes_ro_strip {keep : BitVec 64 → Bool} {m : Memory}
    {addr : BitVec 64} {bytes : List (BitVec 8)}
    (h : Obj.HoldsBytes m addr bytes (fun _ => Perm.ro)) :
    Obj.HoldsBytes (ProofLib.stripExecOutside keep m) addr bytes (fun _ => Perm.ro) := by
  intro i hi
  obtain ⟨hb, hp, hlf⟩ := h i hi
  rw [ProofLib.strip_read8, strip_perm_ro hp, ProofLib.strip_isLazyFree]
  exact ⟨hb, rfl, hlf⟩

private theorem libsignalRoLoaded_strip {keep : BitVec 64 → Bool} {pl : Obj.MultiPlacement}
    {m : Memory} (hro : LibsignalRoLoaded pl m) :
    LibsignalRoLoaded pl (ProofLib.stripExecOutside keep m) :=
  fun d hd hrd => holdsBytes_ro_strip (hro d hd hrd)

private theorem hook_writeBytes_strip_vm (keep : BitVec 64 → Bool) (s : State)
    (bs : List (BitVec 8)) :
    returnToLinkRegister ((ProofLib.stripS keep s).setMem
        ((ProofLib.stripS keep s).mem.writeBytes ((ProofLib.stripS keep s).readReg64 .x0) bs)) =
      ProofLib.stripS keep
        (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) bs))) ∧
    VmPreserved s (returnToLinkRegister (s.setMem (s.mem.writeBytes (s.readReg64 .x0) bs))) := by
  refine ⟨?_, ?_⟩
  · cases s
    dsimp only [ProofLib.stripS, returnToLinkRegister, State.setMem, State.setPC, State.readReg64]
    rw [strip_writeBytes_comm]
  · unfold returnToLinkRegister
    simp only [vmPreserved_setPC, vmPreserved_setMem_writeBytes, vmPreserved_refl_iff]

private theorem kdfOnlyHooks_findSome?_active (keep : BitVec 64 → Bool)
    {C : Crypto} {H : LibsignalHooks} [hH : HkdfPlacedHooks C.F H] :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then kdfOnlyHooks H n else none) = some f →
      ∀ s : State,
        (f (ProofLib.stripS keep s)).status = .Running →
        (l.findSome? fun (n, o) => if o == off then H n else none) = some f ∧
        f (ProofLib.stripS keep s) = ProofLib.stripS keep (f s) ∧
        VmPreserved s (f s)
  | [], _, _, h => by simp at h
  | (n, o) :: tl, off, f, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      by_cases hn : (n == lsMemsetSym || n == lsMemcpySym || n == lsCompress256Sym) = true
      · have hk_eq : kdfOnlyHooks H n = H n := by simp [kdfOnlyHooks, hn]
        rw [hk_eq] at h
        intro s _hrun
        simp only [Bool.or_eq_true, beq_iff_eq] at hn
        rcases hn with (rfl | rfl) | rfl
        · rw [hH.memset] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold memsetHook
          simp only [stripS_readReg64]
          exact hook_writeBytes_strip_vm keep s _
        · rw [hH.memcpy] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold memcpyHook
          simp only [stripS_readReg64]
          have hrd : (ProofLib.stripS keep s).mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat =
              s.mem.readBytes (s.readReg64 .x1) (s.readReg64 .x2).toNat := by
            cases s; exact strip_readBytes keep _ _ _
          rw [hrd]
          exact hook_writeBytes_strip_vm keep s _
        · rw [hH.compress256] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
          refine ⟨rfl, ?_⟩
          unfold compress256Hook
          dsimp only []
          simp only [stripS_readReg64]
          have hst : readShaState (ProofLib.stripS keep s).mem (s.readReg64 .x0) =
              readShaState s.mem (s.readReg64 .x0) := by
            cases s; exact strip_readShaState keep _ _
          have hbs : (ProofLib.stripS keep s).mem.readBytes (s.readReg64 .x1)
                (64 * (s.readReg64 .x2).toNat) =
              s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat) := by
            cases s; exact strip_readBytes keep _ _ _
          rw [hst, hbs]
          exact hook_writeBytes_strip_vm keep s _
      · simp only [Bool.not_eq_true] at hn
        cases hHn : H n with
        | none =>
          have hk_n : kdfOnlyHooks H n = none := by unfold kdfOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_n] at h; dsimp only at h ⊢
          exact kdfOnlyHooks_findSome?_active keep (C := C) tl h
        | some g =>
          have hk_g : kdfOnlyHooks H n = some (fun s => s.setStatus (.Exception "ext")) := by
            unfold kdfOnlyHooks; rw [hn]; simp [hHn]
          rw [hk_g] at h; dsimp only at h
          injection h with hf; subst hf; intro s hrun; cases s; cases hrun
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact kdfOnlyHooks_findSome?_active keep (C := C) tl h

private theorem kdfOnlyHooks_findSome?_none {H : LibsignalHooks} :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then kdfOnlyHooks H n else none) = none →
      (l.findSome? fun (n, o) => if o == off then H n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      cases hHn : H n with
      | none =>
        have hk : kdfOnlyHooks H n = none := by
          unfold kdfOnlyHooks; split <;> simp [hHn]
        rw [hk] at h
        exact kdfOnlyHooks_findSome?_none tl h
      | some g =>
        have hk : ∃ g', kdfOnlyHooks H n = some g' := by
          unfold kdfOnlyHooks
          split
          · exact ⟨g, hHn⟩
          · exact ⟨_, by rw [hHn]; rfl⟩
        rcases hk with ⟨g', hg'⟩
        rw [hg'] at h
        cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact kdfOnlyHooks_findSome?_none tl h

private theorem kdfOnlyHooks_externAt?_active {blkPC : Program} {b : BitVec 64}
    (keep : BitVec 64 → Bool)
    {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H] {pc : BitVec 64} {f : State → State}
    (hext : (blkPC.rebase b (kdfOnlyHooks H)).externAt? pc = some f)
    {s : State} (hrun : (f (ProofLib.stripS keep s)).status = .Running) :
    (blkPC.rebase b H).externAt? pc = some f ∧
    f (ProofLib.stripS keep s) = ProofLib.stripS keep (f s) ∧
    VmPreserved s (f s) := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none] at hext ⊢
  cases hm : (blkPC.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then kdfOnlyHooks H n else none) with
  | none => rw [hm] at hext; cases hext
  | some g =>
    rw [hm] at hext; injection hext with hgf; subst hgf
    obtain ⟨hhk, hcomm, hvm⟩ :=
      kdfOnlyHooks_findSome?_active keep (C := C) blkPC.stubs hm s hrun
    rw [hhk]
    exact ⟨rfl, hcomm, hvm⟩

private theorem kdfOnlyHooks_externAt?_none {blkPC : Program} {b : BitVec 64}
    {H : LibsignalHooks} {pc : BitVec 64}
    (hext : (blkPC.rebase b (kdfOnlyHooks H)).externAt? pc = none) :
    (blkPC.rebase b H).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢
  rw [findSome?_symbols_none] at hext ⊢
  have h1 : (blkPC.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then kdfOnlyHooks H n else none) = none := by
    cases hm : (blkPC.stubs.findSome? fun (n, o) =>
        if o == (pc - b).toNat then kdfOnlyHooks H n else none) with
    | none => rfl
    | some g => rw [hm] at hext; cases hext
  rw [kdfOnlyHooks_findSome?_none blkPC.stubs h1]
  rfl

private theorem safeVm_of_block_progKeep
    (lib : Obj.PlacedLib) (pl : Obj.Placement)
    (hchk : checkBlockSafeVm lib.text = true)
    {m : Memory} {pc : BitVec 64} {inst : Instr}
    (hL : ((lib.program pl).rebase pl.base vmTrapHooks).CodeLoaded m)
    (hkeep : ProofLib.progKeep ((lib.program pl).rebase pl.base vmTrapHooks) pc = true)
    (hal_pc : pc.toNat % 4 = 0)
    (hdec : Arm64.decode (m.read32 pc) = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  let Q := (lib.program pl).rebase pl.base (fun _ => none)
  have hall : Q.allInstrs (fun i => !(i.isSvc0 || i.isMsrTpidrEl0)) = true :=
    placedLib_rebase_allInstrs_safeVm lib pl (fun _ => none) hchk
  have hLQ : Q.CodeLoaded m := hL.of_base_code rfl rfl
  have hlen_mod4 : Q.code.length % 4 = 0 := by
    have hcode : Q.code = lib.text.patched pl := rfl
    rw [hcode, Obj.CodeBlock.length_patched]
    omega
  have hoff_lt : (pc - Q.base).toNat < Q.code.length := by
    unfold ProofLib.progKeep at hkeep
    exact of_decide_eq_true hkeep
  have hbase_al : Q.base.toNat % 4 = 0 := hLQ.aligned
  have hno_wrap : Q.base.toNat + Q.code.length ≤ 2 ^ 64 := hLQ.no_wrap
  have hpc_eq : pc = Q.base + BitVec.ofNat 64 (pc - Q.base).toNat := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm Q.base, BitVec.sub_add_cancel]
  have hpc_nat : pc.toNat = Q.base.toNat + (pc - Q.base).toNat := by
    conv_lhs => rw [hpc_eq]
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := (pc - Q.base).toNat) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hin : (pc - Q.base).toNat + 4 ≤ Q.code.length := by omega
  have hfe_Q : Q.fetchMem m pc = some inst := by
    have hext_Q : Q.externAt? pc = none := by
      unfold Q Program.externAt? Program.hookAtOff? Program.rebase
      dsimp only
      rw [findSome?_symbols_none, findSome?_symbols_none]
      rfl
    have hce_Q : m.canExec pc 4 = true := by
      unfold Memory.canExec; rw [Memory.allPerm_iff]; intro k hk
      have hk_lt : (pc - Q.base).toNat + k < Q.code.length := by omega
      have heq_addr : pc + BitVec.ofNat 64 k =
          Q.base + BitVec.ofNat 64 ((pc - Q.base).toNat + k) := by
        conv_lhs => rw [hpc_eq]
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      rw [heq_addr, hLQ.perm_eq _ hk_lt]
      rfl
    unfold Program.fetchMem
    rw [hext_Q]
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
      not_true_eq_false, hce_Q, Bool.not_true]
    exact hdec
  have hboth := Program.fetchMem_of_allInstrs_holdsBytes_in_code hall hbase_al hno_wrap
    (fun k hk => ⟨hLQ.byte_eq k hk, hLQ.perm_eq k hk, hLQ.isLazyFree_eq k hk⟩) hin hfe_Q
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff] at hboth
  exact hboth

private theorem cl_of_keepsFrozen {pl : Obj.MultiPlacement} {m m' : Memory}
    (hcl : LibsignalCodeLoaded pl m) (hkf : m.KeepsFrozen m') :
    LibsignalCodeLoaded pl m' :=
  fun j hj hunmut ext panics svc => (hcl j hj hunmut ext panics svc).of_keepsFrozen hkf

private theorem steps_kdf_lockstep_vm [LibsignalPlacement]
    {blkPC : Program} {b : BitVec 64} {keep : BitVec 64 → Bool}
    (hsafe : ∀ {m : Memory} {pc : BitVec 64} {inst : Instr},
      LibsignalCodeLoaded lsmpl m → keep pc = true → pc.toNat % 4 = 0 →
      Arm64.decode (m.read32 pc) = some inst →
      inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false)
    {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H] {s1 sf0 sf' : State}
    (hsteps0 : Steps (blkPC.rebase b (kdfOnlyHooks H)) s1 sf0)
    (hrun0 : sf0.status = .Running) :
    ∀ {s1' : State},
      s1' = ProofLib.stripS keep s1 →
      Steps (blkPC.rebase b (kdfOnlyHooks H)) s1' sf' →
      sf'.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      ∃ sf : State,
        (sf = sf0 ∨ sf' = ProofLib.stripS keep sf) ∧
        Steps (blkPC.rebase b H) s1 sf ∧
        VmPreserved s1 sf := by
  induction hsteps0 with
  | refl =>
    intro s1' _ _ _ _
    exact ⟨_, Or.inl rfl, .refl _, VmPreserved.refl _⟩
  | @step s1 s2 sf0 h1_0 hrest0 ih =>
    intro s1' hs1' hsteps' hrun_f hcl1
    cases hsteps' with
    | refl =>
      exact ⟨s1, Or.inr hs1', .refl s1, VmPreserved.refl s1⟩
    | @step _ s2' _ h1' hrest' =>
      subst hs1'
      have hr2_0 : s2.status = .Running := by
        cases hrest0 with
        | refl => exact hrun0
        | step hs _ => cases hs <;> assumption
      have hr2' : s2'.status = .Running := by
        cases hrest' with
        | refl => exact hrun_f
        | step hs _ => cases hs <;> assumption
      cases h1_0 with
      | halt_unmapped _ _ _ => cases s1; cases hr2_0
      | extern_fault _ _ _ => cases s1; cases hr2_0
      | @extern f hr1 hext0 hkf_s1 hsym_s1 =>
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @exec inst' _ hfe' =>
          have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
          unfold Program.fetchMem at hfe'
          rw [hpc_eq, hext0] at hfe'
          simp at hfe'
        | @extern f' _ hext' _ _ =>
          have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
          rw [hpc_eq, hext0] at hext'
          injection hext' with hff'
          subst hff'
          obtain ⟨hext_H, hcomm, hvm1⟩ :=
            kdfOnlyHooks_externAt?_active keep (C := C) hext0 hr2'
          have hstep_H : Step (blkPC.rebase b H) s1 (f s1) :=
            Step.extern hr1 hext_H hkf_s1 hsym_s1
          have hcl2 : LibsignalCodeLoaded lsmpl (f s1).mem := cl_of_keepsFrozen hcl1 hkf_s1
          obtain ⟨sf, hor, hsteps_H, hvm_rest⟩ := ih hrun0 hcomm hrest' hrun_f hcl2
          exact ⟨sf, hor, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩
      | @exec inst hr1 hfe0 =>
        let P_H := blkPC.rebase b H
        have hext_kdf : (blkPC.rebase b (kdfOnlyHooks H)).externAt? s1.pc = none := by
          cases he : (blkPC.rebase b (kdfOnlyHooks H)).externAt? s1.pc with
          | none => rfl
          | some g => unfold Program.fetchMem at hfe0; rw [he] at hfe0; simp at hfe0
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @extern f' _ hext' _ _ =>
          have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
          rw [hpc_eq, hext_kdf] at hext'; cases hext'
        | @exec inst' _ hfe' =>
          have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
          have hmem_eq : (ProofLib.stripS keep s1).mem =
              ProofLib.stripExecOutside keep s1.mem := by cases s1; rfl
          rw [hpc_eq, hmem_eq] at hfe'
          have hext_H : P_H.externAt? s1.pc = none := kdfOnlyHooks_externAt?_none hext_kdf
          have ⟨hal_pc, hce', hdec⟩ : s1.pc.toNat % 4 = 0 ∧
              (ProofLib.stripExecOutside keep s1.mem).canExec s1.pc 4 = true ∧
              Arm64.decode (s1.mem.read32 s1.pc) = some inst' := by
            unfold Program.fetchMem at hfe'
            rw [hext_kdf] at hfe'
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
            by_cases hal : s1.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
              split at hfe'
              · contradiction
              · rename_i hce_neg
                simp only [Bool.not_eq_true', Bool.not_eq_false] at hce_neg
                rw [strip_read32] at hfe'; exact ⟨hal, hce_neg, hfe'⟩
            · simp only [hal, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
          have hce : s1.mem.canExec s1.pc 4 = true := by
            unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢; intro k hk
            have hxk := hce' k hk
            rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
          have hfe0' := hfe0
          unfold Program.fetchMem at hfe0'
          rw [hext_kdf] at hfe0'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
            not_true_eq_false, hce, Bool.not_true] at hfe0'
          have hinst_eq : inst' = inst := Option.some.inj (hdec.symm.trans hfe0')
          subst hinst_eq
          have hfe_H : P_H.fetchMem s1.mem s1.pc = some inst' := by
            unfold Program.fetchMem
            rw [hext_H]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
              not_true_eq_false, hce, Bool.not_true]
            exact hdec
          have hkeep_pc : keep s1.pc = true := by
            unfold Memory.canExec at hce'; rw [Memory.allPerm_iff] at hce'
            have hx0 := hce' 0 (by omega)
            simpa using (ProofLib.strip_perm_x_imp hx0).2
          have ⟨hnsvc0, hnmsr⟩ := hsafe hcl1 hkeep_pc hal_pc hdec
          have hev0 : (blkPC.rebase b (kdfOnlyHooks H)).evalInst inst' s1 =
              execInst inst' s1 :=
            Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
          have hev_kdf : (blkPC.rebase b (kdfOnlyHooks H)).evalInst inst'
              (ProofLib.stripS keep s1) =
              ProofLib.stripS keep ((blkPC.rebase b (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0, Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
          have hstep_H : Step P_H s1 ((blkPC.rebase b (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            have := Step.exec (prog := P_H) hr1 hfe_H
            rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
          have hcl2 : LibsignalCodeLoaded lsmpl
              ((blkPC.rebase b (kdfOnlyHooks H)).evalInst inst' s1).mem :=
            cl_of_keepsFrozen hcl1 hstep_H.keepsFrozen
          have hvm1 : VmPreserved s1 ((blkPC.rebase b (kdfOnlyHooks H)).evalInst inst' s1) := by
            rw [hev0]
            exact (vmNoTpidr_execInst hnsvc0 s1).toVmPreserved
              (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
          obtain ⟨sf, hor, hsteps_H, hvm_rest⟩ := ih hrun0 hev_kdf hrest' hrun_f hcl2
          exact ⟨sf, hor, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩

private theorem extract_withLsCodeLoaded {α : Type} {pl : Obj.MultiPlacement}
    {spec : Spec α} {x : α} {s0 : State} {R : SepProp}
    (hpre : s0.mem ⊨ (withLsCodeLoaded pl spec).pre x s0 ∗ R) :
    LibsignalCodeLoaded pl s0.mem ∧ (s0.mem ⊨ spec.pre x s0 ∗ R) := by
  dsimp only [withLsCodeLoaded] at hpre
  have hcomm : (spec.pre x s0 ∗ ⌜LibsignalCodeLoaded pl s0.mem⌝) ∗ R =
      ⌜LibsignalCodeLoaded pl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by sep_ac_rfl
  rwa [hcomm, satisfies_pure_sepConj] at hpre

/-! ## 2. Block `53` `expand_multi_info` (`96` B, `info.length = 46`) with `VmPreserved` -/

private theorem blk53_safeVm : checkBlockSafeVm blkLib_53.text = true := by decide +kernel
private theorem blk123_safeVm : checkBlockSafeVm blkLib_123.text = true := by decide +kernel

private noncomputable def keepExp [LibsignalPlacement] (a : BitVec 64) : Bool :=
  ProofLib.progKeep ((blkPC_53).rebase (blkPl_53).base vmTrapHooks) a ||
  ProofLib.progKeep ((blkPC_123).rebase (blkPl_123).base vmTrapHooks) a

private def ExpCodeLoaded [LibsignalPlacement] (m : Memory) : Prop :=
  ∀ (H : LibsignalHooks),
    ((blkPC_53).rebase (blkPl_53).base H).CodeLoaded m ∧
    ((blkPC_123).rebase (blkPl_123).base H).CodeLoaded m

private theorem ExpCodeLoaded.of_keepsFrozen [LibsignalPlacement] {m m' : Memory}
    (hcl : ExpCodeLoaded m) (hk : m.KeepsFrozen m') : ExpCodeLoaded m' :=
  fun H =>
    let ⟨h1, h2⟩ := hcl H
    ⟨h1.of_keepsFrozen hk, h2.of_keepsFrozen hk⟩

private theorem expCodeLoaded_of_ls [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) : ExpCodeLoaded m := by
  intro H
  have hI53 : IsLsBlockProg ((blkPC_53).rebase (blkPl_53).base H) 53 H := inferInstance
  have hI123 : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base H) 123 H := inferInstance
  exact ⟨hI53.eq_blockProgram ▸ hcl 53 (by decide) (by decide) H (fun _ => none) Syscall.standard,
    hI123.eq_blockProgram ▸ hcl 123 (by decide) (by decide) H (fun _ => none) Syscall.standard⟩

private theorem expCodeLoaded_strip [LibsignalPlacement] {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m) :
    ExpCodeLoaded (ProofLib.stripExecOutside keepExp m) := by
  intro H
  have ⟨hL53, hL123⟩ := expCodeLoaded_of_ls hcl H
  refine ⟨strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL53,
    strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL123⟩
  · have ha' : ProofLib.progKeep ((blkPC_53).rebase (blkPl_53).base vmTrapHooks) a = true := ha
    simp [keepExp, ha']
  · have ha' : ProofLib.progKeep ((blkPC_123).rebase (blkPl_123).base vmTrapHooks) a = true := ha
    simp [keepExp, ha']

private theorem safeVm_keepExp [LibsignalPlacement] {m : Memory} {pc : BitVec 64} {inst : Instr}
    (hcl : LibsignalCodeLoaded lsmpl m) (hkeep : keepExp pc = true)
    (hal_pc : pc.toNat % 4 = 0) (hdec : Arm64.decode (m.read32 pc) = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  unfold keepExp at hkeep
  simp only [Bool.or_eq_true] at hkeep
  rcases hkeep with hk53 | hk123
  · have hI : IsLsBlockProg ((blkPC_53).rebase (blkPl_53).base vmTrapHooks) 53 vmTrapHooks :=
      inferInstance
    have hL : ((blkPC_53).rebase (blkPl_53).base vmTrapHooks).CodeLoaded m :=
      hI.eq_blockProgram ▸ hcl 53 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
    have hEq : (blkPC_53).rebase (blkPl_53).base vmTrapHooks =
        (blkLib_53.program blkPl_53).rebase (blkPl_53).base vmTrapHooks :=
      hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_53).symm
    exact safeVm_of_block_progKeep blkLib_53 blkPl_53 blk53_safeVm
      (hEq ▸ hL) (hEq ▸ hk53) hal_pc hdec
  · have hI : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base vmTrapHooks) 123 vmTrapHooks :=
      inferInstance
    have hL : ((blkPC_123).rebase (blkPl_123).base vmTrapHooks).CodeLoaded m :=
      hI.eq_blockProgram ▸ hcl 123 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
    have hEq : (blkPC_123).rebase (blkPl_123).base vmTrapHooks =
        (blkLib_123.program blkPl_123).rebase (blkPl_123).base vmTrapHooks :=
      hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_123).symm
    exact safeVm_of_block_progKeep blkLib_123 blkPl_123 blk123_safeVm
      (hEq ▸ hL) (hEq ▸ hk123) hal_pc hdec

private theorem runsTo_of_exp_123 [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {P_post : State → Prop}
    (hcl : ExpCodeLoaded s.mem)
    (h : RunsTo ((blkPC_123).rebase (blkPl_123).base H) s P_post) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s P_post := by
  intro hL_caller
  have hcaller : IsLsBlockProg ((blkPC_53).rebase (blkPl_53).base H) 53 H := inferInstance
  have hcallee : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base H) 123 H := inferInstance
  obtain ⟨s', hst_callee, htr, hP, _⟩ := h (hcl H).2
  have hext : ∀ pc, ((blkPC_123).rebase (blkPl_123).base H).externAt? pc =
      ((blkPC_53).rebase (blkPl_53).base H).externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : ((blkPC_123).rebase (blkPl_123).base H).svc =
      ((blkPC_53).rebase (blkPl_53).base H).svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_caller := Steps.of_sameHooks hext hsvc hst_callee
  exact ⟨s', hst_caller, htr, hP, hst_caller.codeLoaded hL_caller⟩

private theorem fin1_96_exp_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ s : State}
    (hcl : ExpCodeLoaded s.mem)
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (hx : StateX2Placed C.F prk info 96 s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateX2r expPlacedFakeB C.F prk info 96 s₀) := by
  rcases hpre.fin_side_conditions hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinPre finPlacedFakeB C.F prk (info ++ [1#8]) s :=
    { pc_eq := by rw [hx.pc_eq]; simp only [arm64_norm]
      status := hx.common.status
      key_le := hpre.prk_le
      msg_lt := by simp [hpre.info_len_eq]
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (runsTo_of_exp_123 hcl (finalize_fixed_placed_runsTo (C := C) (H := H) hfin_pre)).mono
    fun s' ⟨hpc', hrun', hcs, ht1, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq] at ht1
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  exact ⟨by simp only [arm64_norm, hpc'],
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans hx.x23_eq,
    (CalleeSaved.x26 hcs).trans hx.x26_eq,
    ht1⟩

private theorem iter_fin_96_exp_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {prk info tPrev okmSoFar : List (BitVec 8)} {infoPtr : BitVec 64}
    {i rem dstOff : ℕ} {s₀ s : State}
    (hcl : ExpCodeLoaded s.mem)
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (_ht_len : tPrev.length = 32)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 i rem dstOff s₀) := by
  have hmin : min rem 32 = 32 := by rcases hrem with rfl | rfl <;> rfl
  rcases hpre.fin_side_conditions hx.common.frame with
    ⟨hrw_x0, hrw_x1, hrw_sp, hd_x0_x1, hd_x0_sp, hd_x1_sp⟩
  have hfin_pre : FinGenPre finPlacedFakeB C.F prk (tPrev ++ info.take 32)
      (info.drop 32 ++ [BitVec.ofNat 8 (i + 1)]) s :=
    { pc_eq := by rw [hx.pc_eq]; simp only [arm64_norm]
      status := hx.common.status
      key_le := hpre.prk_le
      rem_lt := by simp [hpre.info_len_eq]
      hmac_st := by rw [hx.x1_eq]; exact hx.hmac_240
      rw_out := by rw [hx.x0_eq]; exact hrw_x0
      rw_hm := by rw [hx.x1_eq]; exact hrw_x1
      rw_fsp := by rw [hx.common.sp_eq]; exact hrw_sp
      disj_out_hm := by rw [hx.x0_eq, hx.x1_eq]; exact hd_x0_x1
      disj_out_fsp := by rw [hx.x0_eq, hx.common.sp_eq]; exact hd_x0_sp
      disj_hm_fsp := by rw [hx.x1_eq, hx.common.sp_eq]; exact hd_x1_sp
      sp_aligned := by rw [hx.common.sp_eq]; exact esp_aligned hpre.sp_aligned }
  refine (runsTo_of_exp_123 hcl (finalize_fixed_gen_placed_runsTo (C := C) (H := H) hfin_pre)).mono
    fun s' ⟨hpc', hrun', hcs, ht, hfr⟩ => ?_
  rw [hx.lr_eq] at hpc'
  rw [hx.x0_eq, List.append_assoc, ← List.append_assoc (info.take 32),
      List.take_append_drop, ← List.append_assoc] at ht
  rw [hx.x0_eq, hx.x1_eq, hx.common.sp_eq] at hfr
  have hokm' : s'.mem.readBytes (s₀.readReg64 .x2) dstOff = okmSoFar := by
    by_cases h0 : dstOff = 0
    · subst h0; exact hx.okm_pre
    · refine (Frame.readBytes_eq hfr (fun r hr => ?_) (by omega)).trans hx.okm_pre
      have hd_stk : DisjointRegions (s₀.sp - 640#64) 640 (s₀.readReg64 .x2) dstOff :=
        hpre.disj_x2_stack.symm.sub_right (s₀.readReg64 .x2) ⟨by omega, by bv_omega⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl <;>
        exact hd_stk.sub_left _ ⟨by simp, by unfold esp; bv_omega⟩
  exact ⟨by simp only [arm64_norm, hpc'],
    ExpandCommon.of_fin_frame hx.common hrun' hcs hfr,
    (CalleeSaved.x19 hcs).trans hx.x19_eq,
    (CalleeSaved.x21 hcs).trans (by rw [hmin]; exact hx.x21_eq),
    (CalleeSaved.x22 hcs).trans hx.x22_eq,
    (CalleeSaved.x23 hcs).trans (by rw [hmin]; exact hx.x23_eq),
    (CalleeSaved.x24 hcs).trans hx.x24_eq,
    (CalleeSaved.x26 hcs).trans (by rw [hmin]; exact hx.x26_eq),
    (CalleeSaved.x28 hcs).trans hx.x28_eq,
    ht, hokm'⟩

private theorem iter_to_fin_96_exp_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {prk info tPrev okmSoFar : List (BitVec 8)}
    {infoPtr : BitVec 64} {i rem dstOff : ℕ} {s₀ s : State}
    (hcl : ExpCodeLoaded s.mem)
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀)
    (ht_len : tPrev.length = 32)
    (hi : i = 1 ∨ i = 2)
    (hrem : rem = 64 ∨ rem = 32)
    (hdst : dstOff ≤ 96)
    (hx : StateLoop expPlacedFakeB 96 tPrev okmSoFar i rem dstOff s₀ s) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopFin expPlacedFakeB C.F prk info tPrev okmSoFar 96 i rem dstOff s₀) := by
  have h16 : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s
      (StateLoopC_96Placed C.F prk info tPrev okmSoFar i rem dstOff s₀) :=
    (iter_a1_96_placed_runsTo hpre hrem hdst hx).trans fun _ hs1 =>
    (iter_a2_96_placed_runsTo hpre ht_len hrem hdst hs1).trans fun _ hs2 =>
    (iter_b1_96_placed_runsTo hpre ht_len hdst hs2).trans fun _ hs3 =>
    (iter_b2_96_placed_runsTo hpre ht_len hdst hs3).trans fun _ hs4 =>
    (iter_b3_96_placed_runsTo hpre ht_len hi hdst hs4).trans fun _ hs5 =>
    iter_c_96_placed_runsTo hpre hrem hdst hs5
  refine h16.trans_keepsFrozen fun s6 hs6 hkf => ?_
  exact iter_fin_96_exp_runsTo (hcl.of_keepsFrozen hkf) hpre ht_len hrem hdst hs6

private theorem expand_multi_info_96_46_exp_runsTo [LibsignalPlacement]
    {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    {prk info : List (BitVec 8)} {infoPtr : BitVec 64} {s₀ : State}
    (hcl : ExpCodeLoaded s₀.mem)
    (hpre : ExpandPre96_46 expPlacedFakeB C.F prk info infoPtr s₀) :
    RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀ (ExpandPost C.F prk info 96 s₀) := by
  have h04 : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateX2Placed C.F prk info 96 s₀) :=
    (seg0_96_placed_runsTo hpre).trans fun _ hs1 =>
    (seg1_96_placed_runsTo hpre hs1).trans fun _ hs2 =>
    (seg2a_96_placed_runsTo hpre hs2).trans fun _ hs3 =>
    seg2b_96_placed_runsTo hpre hs3
  have h06 : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateLoop expPlacedFakeB 96 (t1 C.F prk info) (t1 C.F prk info) 1 64 32 s₀) :=
    h04.trans_keepsFrozen fun s4 hs4 hkf =>
      (fin1_96_exp_runsTo (hcl.of_keepsFrozen hkf) hpre hs4).trans fun _ hs5 =>
      seg3_96_placed_runsTo hpre hs5
  have h08 : RunsTo ((blkPC_53).rebase (blkPl_53).base H) s₀
      (StateLoop expPlacedFakeB 96 (t2 C.F prk info)
        (t1 C.F prk info ++ t2 C.F prk info) 2 32 64 s₀) :=
    h06.trans_keepsFrozen fun s6 hs6 hkf =>
      (iter_to_fin_96_exp_runsTo (hcl.of_keepsFrozen hkf) hpre (t1_length C.F prk info)
        (Or.inl rfl) (Or.inl rfl) (by decide) hs6).trans fun _ hs7 =>
      iter_d_continue_96_placed_runsTo hpre (tNext := t2 C.F prk info) rfl hs7
  refine h08.trans_keepsFrozen fun s8 hs8 hkf => ?_
  refine (iter_to_fin_96_exp_runsTo (hcl.of_keepsFrozen hkf) hpre (t2_length C.F prk info)
    (Or.inr rfl) (Or.inr rfl) (by decide) hs8).trans fun s9 hs9 => ?_
  have hokm96 : (t1 C.F prk info ++ t2 C.F prk info) ++
      hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) =
      hkdfExpand C.F prk info 96 := by
    rw [show hmacWith C.F prk (t2 C.F prk info ++ info ++ [3#8]) = t3 C.F prk info from rfl,
        hkdfExpand_96_eq]
  refine (iter_d_done_96_placed_runsTo hpre hokm96 hs9).trans fun s10 hs10 => ?_
  exact epilogue_96_placed_runsTo hpre hs10

/-- Relocatable `subroutine_ok` with `VmPreserved` for `expand_multi_info` (Block `53`) when
`okmLen = 96` and `info.length = 46`. -/
theorem expand_multi_info_96_46_placed_vm_ok [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_53).rebase (blkPl_53).base H) (blkPl_53).base
      (withLsCodeLoaded lsmpl (withVmPreserved (expandMultiInfo96_46Spec C.F))) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cl hsp => ?_
  obtain ⟨hcl, hpre⟩ := extract_withLsCodeLoaded hpre_cl
  dsimp only [withVmPreserved, expandMultiInfo96_46Spec, stackAt, expandMultiInfoStack,
    finalizeFixedStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, hprk_le, hinfo_len, hokm_len⟩, hsep⟩
  change s0.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
      (x.infoA ↦ᵣ x.info) ∗ memRegion x.okmA 96 ∗
      memRegion (s0.sp - 640#64) 640) ∗ R at hsep
  have hb_hm := isBlock_hmacCoreAt C.F x.hkdfA x.prk [] (by decide)
  have hb_hdr0 := IsBlock.pointsTo64 x.infoHdrA x.infoA
  have hb_hdr8 := IsBlock.pointsTo64 (x.infoHdrA + 8#64) 46#64
  have hb_hdr : IsBlock ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64))
      x.infoHdrA 16
      (fun m => m.read64 x.infoHdrA = x.infoA ∧
        m.read64 (x.infoHdrA + 8#64) = 46#64) :=
    hb_hdr0.sepConj hb_hdr8 rfl (by decide)
  have hro_info := IsBlockRO.pointsToBytesRO x.infoA x.info (by omega)
  have hb_okm := IsBlock.memRegion x.okmA 96
  have hb_stk := IsBlock.memRegion (s0.sp - 640#64) 640
  let R_inv : SepProp :=
    hmacCoreAt C.F x.hkdfA x.prk [] ∗
      ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (x.infoA ↦ᵣ x.info) ∗ R
  have hsep_okm_stk : s0.mem ⊨ memRegion x.okmA 96 ∗ (memRegion (s0.sp - 640#64) 640 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (s0.sp - 640#64) 640 ∗ (memRegion x.okmA 96 ∗ R_inv) := by
    dsimp only [R_inv]; ac_nf at hsep ⊢
  have hsep_hm_stk : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hm_okm : s0.mem ⊨ hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (memRegion x.okmA 96 ∗
        (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_stk : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗ ((x.infoA ↦ᵣ x.info) ∗ (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_hdr_okm : s0.mem ⊨ ((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
      (memRegion x.okmA 96 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          ((x.infoA ↦ᵣ x.info) ∗ (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_stk : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion (s0.sp - 640#64) 640 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
            (memRegion x.okmA 96 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hsep_info_okm : s0.mem ⊨ (x.infoA ↦ᵣ x.info) ∗
      (memRegion x.okmA 96 ∗
        (hmacCoreAt C.F x.hkdfA x.prk [] ∗
          (((x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64)) ∗
            (memRegion (s0.sp - 640#64) 640 ∗ R)))) := by
    ac_nf at hsep ⊢
  have hrw_hm : s0.mem.RW x.hkdfA 0x90 := fun a ha => hb_hm.permNoLazy_rw hsep_hm_stk ha
  have hrw_hdr : s0.mem.RW x.infoHdrA 16 := fun a ha => hb_hdr.permNoLazy_rw hsep_hdr_stk ha
  have hrw_okm : s0.mem.RW x.okmA 96 := fun a ha => hb_okm.permNoLazy_rw hsep_okm_stk ha
  have hrw_stk : s0.mem.RW (s0.sp - 640#64) 640 := fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  let s0' := ProofLib.stripS keepExp s0
  have hs0'_mem : s0'.mem = ProofLib.stripExecOutside keepExp s0.mem := by cases s0; rfl
  have hrw_strip : ∀ {base : BitVec 64} {len : Nat}, s0.mem.RW base len → s0'.mem.RW base len := by
    intro base len hrw a ha
    rw [hs0'_mem]
    exact strip_permNoLazy_rw (hrw a ha)
  have h_exp_pre0 : ExpandPre96_46 expPlacedFakeB C.F x.prk x.info x.infoA s0 :=
    { pc_eq := by rw [expPlacedFakeB_off_0]; exact hpc
      status := hrun
      x3_eq := hx3
      prk_le := hprk_le
      info_len_eq := hinfo_len
      hmac_st := by rw [hx0]; exact hb_hm.read hsep_hm_stk
      info_ptr := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by rw [hx1]; exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := by rw [← hinfo_len]; exact hro_info.read hsep_info_stk
      read_x0 := by rw [hx0]; exact Memory.RW.readable hrw_hm
      read_x1 := by rw [hx1]; exact Memory.RW.readable hrw_hdr
      rw_x2 := by rw [hx2]; exact hrw_okm
      rw_stack := hrw_stk
      disj_x2_stack := by rw [hx2]; exact hb_okm.disjoint hb_stk (by decide) (by decide) hsep_okm_stk
      disj_x0_stack := by rw [hx0]; exact hb_hm.disjoint hb_stk (by decide) (by decide) hsep_hm_stk
      disj_x0_x2 := by rw [hx0, hx2]; exact hb_hm.disjoint hb_okm (by decide) (by decide) hsep_hm_okm
      disj_x1_stack := by rw [hx1]; exact hb_hdr.disjoint hb_stk (by decide) (by decide) hsep_hdr_stk
      disj_x1_x2 := by rw [hx1, hx2]; exact hb_hdr.disjoint hb_okm (by decide) (by decide) hsep_hdr_okm
      out_info_stk := by rw [← hinfo_len]; exact ro_outside_rw_shared_lb hro_info hb_stk hsep_info_stk
      out_info_x2 := by
        rw [hx2, ← hinfo_len]; exact ro_outside_rw_shared_lb hro_info hb_okm hsep_info_okm
      sp_aligned := by simpa [State.spAligned] using hsp }
  have h_exp_pre' : ExpandPre96_46 expPlacedFakeB C.F x.prk x.info x.infoA s0' :=
    { pc_eq := by rw [expPlacedFakeB_off_0]; simpa [s0', stripS_pc] using hpc
      status := by simpa [s0', stripS_status] using hrun
      x3_eq := by simpa [s0', stripS_readReg64] using hx3
      prk_le := hprk_le
      info_len_eq := hinfo_len
      hmac_st := by
        rcases h_exp_pre0.hmac_st with ⟨h1, h2, h3, h4a, h4b, h4c, h4d⟩
        simp only [s0', stripS_readReg64, hs0'_mem]
        exact ⟨h1, by rwa [strip_readBytes], by rwa [ProofLib.strip_read8],
          by rwa [strip_readBytes], by rwa [strip_read64],
          by rwa [strip_readBytes], by rwa [strip_read64]⟩
      info_ptr := by
        simp only [s0', stripS_readReg64, hs0'_mem, strip_read64, hx1]
        exact (hb_hdr.read hsep_hdr_stk).1
      info_len := by
        simp only [s0', stripS_readReg64, hs0'_mem, strip_read64, hx1]
        exact (hb_hdr.read hsep_hdr_stk).2
      info_bytes := by
        rw [hs0'_mem, strip_readBytes, ← hinfo_len]
        exact hro_info.read hsep_info_stk
      read_x0 := by
        simp only [s0', stripS_readReg64, hx0]
        exact Memory.RW.readable (hrw_strip hrw_hm)
      read_x1 := by
        simp only [s0', stripS_readReg64, hx1]
        exact Memory.RW.readable (hrw_strip hrw_hdr)
      rw_x2 := by simp only [s0', stripS_readReg64, hx2]; exact hrw_strip hrw_okm
      rw_stack := by simp only [s0', stripS_sp]; exact hrw_strip hrw_stk
      disj_x2_stack := by simp only [s0', stripS_readReg64, stripS_sp]; exact h_exp_pre0.disj_x2_stack
      disj_x0_stack := by simp only [s0', stripS_readReg64, stripS_sp]; exact h_exp_pre0.disj_x0_stack
      disj_x0_x2 := by simp only [s0', stripS_readReg64]; exact h_exp_pre0.disj_x0_x2
      disj_x1_stack := by simp only [s0', stripS_readReg64, stripS_sp]; exact h_exp_pre0.disj_x1_stack
      disj_x1_x2 := by simp only [s0', stripS_readReg64]; exact h_exp_pre0.disj_x1_x2
      out_info_stk := by simp only [s0', stripS_sp]; exact h_exp_pre0.out_info_stk
      out_info_x2 := by simp only [s0', stripS_readReg64]; exact h_exp_pre0.out_info_x2
      sp_aligned := by simpa [State.spAligned, s0', stripS_sp] using hsp }
  let H' := kdfOnlyHooks H
  have hRuns0 := expand_multi_info_96_46_exp_runsTo (C := C) (H := H')
    (expCodeLoaded_of_ls hcl) h_exp_pre0
  have hRuns' := expand_multi_info_96_46_exp_runsTo (C := C) (H := H')
    (hs0'_mem ▸ expCodeLoaded_strip hcl) h_exp_pre'
  intro hL0
  have hL0_exp : ((blkPC_53).rebase (blkPl_53).base H').CodeLoaded s0.mem :=
    (expCodeLoaded_of_ls hcl) H' |>.1
  have hL0' : ((blkPC_53).rebase (blkPl_53).base H').CodeLoaded s0'.mem :=
    (hs0'_mem ▸ expCodeLoaded_strip hcl) H' |>.1
  obtain ⟨sf0, hsteps0, htr0, hpost0, _⟩ := hRuns0 hL0_exp
  obtain ⟨sf', hsteps', htr', hpost', _⟩ := hRuns' hL0'
  obtain ⟨sf, hor, hsteps_H, hvm⟩ :=
    steps_kdf_lockstep_vm safeVm_keepExp (C := C) (H := H)
      hsteps0 hpost0.2.1 rfl hsteps' hpost'.2.1 hcl
  have ⟨htr, hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩ :
      TraceEq s0 sf ∧ ExpandPost C.F x.prk x.info 96 s0 sf := by
    rcases hor with rfl | hsf_eq
    · exact ⟨htr0, hpost0⟩
    · subst hsf_eq
      rcases hpost' with ⟨hpc_sf', hstat_sf', hcallee', hokm_sf', hframe_sf'⟩
      have hpc_sf : sf.pc = s0.readReg64 .x30 := by
        simpa [s0', stripS_pc, stripS_readReg64] using hpc_sf'
      have hstat_sf : sf.status = .Running := by
        simpa [stripS_status] using hstat_sf'
      have hcallee : CalleeSaved s0 sf := by
        refine ⟨by simpa [s0', stripS_sp] using hcallee'.1, fun r hr => ?_⟩
        simpa [s0', stripS_readReg64] using hcallee'.2 r hr
      have htr : TraceEq s0 sf :=
        ⟨by simpa [s0', stripS_trace] using htr'.1,
         by simpa [s0', stripS_calleeSavedVRegs] using htr'.2⟩
      have hsf_mem : (ProofLib.stripS keepExp sf).mem =
          ProofLib.stripExecOutside keepExp sf.mem := by
        cases sf; rfl
      have hx2_s0' : s0'.readReg64 .x2 = s0.readReg64 .x2 :=
        stripS_readReg64 keepExp s0 .x2
      have hsp_s0' : s0'.sp = s0.sp := stripS_sp keepExp s0
      have hokm_sf : sf.mem.readBytes (s0.readReg64 .x2) 96 =
          hkdfExpand C.F x.prk x.info 96 := by
        rw [← hx2_s0']
        rwa [hsf_mem, strip_readBytes] at hokm_sf'
      have hframe_sf : ExpandFrame 96 s0 sf.mem := by
        unfold ExpandFrame Frame at hframe_sf' ⊢
        rcases hframe_sf' with ⟨hfr1, _hfr2, hfr3, hfr4, hfr5⟩
        refine ⟨?_, funext hvm.perm_eq, ?_, ?_, ?_⟩
        · intro a hout
          have h1 := hfr1 a (by rwa [hx2_s0', hsp_s0'])
          rwa [hsf_mem, hs0'_mem, ProofLib.strip_read8, ProofLib.strip_read8] at h1
        · intro a hout
          have h3 := hfr3 a (by rwa [hx2_s0', hsp_s0'])
          rwa [hsf_mem, hs0'_mem, ProofLib.strip_isLazyFree, ProofLib.strip_isLazyFree] at h3
        · intro a hlf
          have h4 := hfr4 a (by rwa [hs0'_mem, ProofLib.strip_isLazyFree])
          rwa [hsf_mem, ProofLib.strip_isLazyFree] at h4
        · intro a han
          have h5 := hfr5 a (by rwa [hs0'_mem, ProofLib.strip_isAnon])
          rwa [hsf_mem, ProofLib.strip_isAnon] at h5
      exact ⟨htr, hpc_sf, hstat_sf, hcallee, hokm_sf, hframe_sf⟩
  refine ⟨sf, hsteps_H,
    Or.inl ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩⟩
  dsimp only [withLsCodeLoaded, withVmPreserved, expandMultiInfo96_46Spec, stackAt,
    expandMultiInfoStack, finalizeFixedStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExpandFrame at hframe_sf
  rw [hx2] at hokm_sf hframe_sf
  have h_exp_len : (hkdfExpand C.F x.prk x.info 96).length = 96 := by
    rw [hkdfExpand_96_eq]
    simp [t1_length, t2_length, t3_length]
  have hb_okm' := IsBlock.pointsToBytes_len (a := x.okmA) h_exp_len
  have hpost_sep : sf.mem ⊨ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info 96) ∗
      (memRegion (s0.sp - 640#64) 640 ∗ R_inv) :=
    Frame.update_two_blocks hb_okm hb_okm' hb_stk hb_stk hsep_okm_stk hframe_sf
      ⟨by rw [h_exp_len]; decide, by rwa [h_exp_len]⟩ trivial
  change sf.mem ⊨
    (hmacCoreAt C.F x.hkdfA x.prk [] ∗
      (x.infoHdrA ↦₆₄ x.infoA) ∗ ((x.infoHdrA + 8#64) ↦₆₄ 46#64) ∗
      (x.infoA ↦ᵣ x.info) ∗ (x.okmA ↦ₛ hkdfExpand C.F x.prk x.info 96) ∗
      memRegion (s0.sp - 640#64) 640) ∗ R
  dsimp only [R_inv] at hpost_sep
  ac_nf at hpost_sep ⊢

/-! ## 3. Block `54` `GenericHkdf::extract` (`32` B & `160/192/224` B) with `VmPreserved` -/

private theorem blk54_safeVm : checkBlockSafeVm blkLib_54.text = true := by decide +kernel
private theorem blk114_safeVm : checkBlockSafeVm blkLib_114.text = true := by decide +kernel

private noncomputable def keepExt [LibsignalPlacement] (a : BitVec 64) : Bool :=
  ProofLib.progKeep ((blkPC_54).rebase (blkPl_54).base vmTrapHooks) a ||
  ProofLib.progKeep ((blkPC_114).rebase (blkPl_114).base vmTrapHooks) a ||
  ProofLib.progKeep ((blkPC_123).rebase (blkPl_123).base vmTrapHooks) a

private def ExtCodeRoLoaded [LibsignalPlacement] (m : Memory) : Prop :=
  (∀ (H : LibsignalHooks),
    ((blkPC_54).rebase (blkPl_54).base H).CodeLoaded m ∧
    ((blkPC_114).rebase (blkPl_114).base H).CodeLoaded m ∧
    ((blkPC_123).rebase (blkPl_123).base H).CodeLoaded m) ∧
  LibsignalRoLoaded lsmpl m

private theorem ExtCodeRoLoaded.of_keepsFrozen [LibsignalPlacement] {m m' : Memory}
    (h : ExtCodeRoLoaded m) (hk : m.KeepsFrozen m') : ExtCodeRoLoaded m' :=
  ⟨fun H =>
    let ⟨h54, h114, h123⟩ := h.1 H
    ⟨h54.of_keepsFrozen hk, h114.of_keepsFrozen hk, h123.of_keepsFrozen hk⟩,
   libsignalRoLoaded_of_keepsFrozen h.2 hk⟩

private theorem extCodeRoLoaded_of_cro [LibsignalPlacement] {m : Memory}
    (hcro : LibsignalCodeRoLoaded lsmpl m) : ExtCodeRoLoaded m := by
  refine ⟨fun H => ?_, hcro.2⟩
  have hI54 : IsLsBlockProg ((blkPC_54).rebase (blkPl_54).base H) 54 H := inferInstance
  have hI114 : IsLsBlockProg ((blkPC_114).rebase (blkPl_114).base H) 114 H := inferInstance
  have hI123 : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base H) 123 H := inferInstance
  exact ⟨hI54.eq_blockProgram ▸ hcro.1 54 (by decide) (by decide) H (fun _ => none) Syscall.standard,
    hI114.eq_blockProgram ▸ hcro.1 114 (by decide) (by decide) H (fun _ => none) Syscall.standard,
    hI123.eq_blockProgram ▸ hcro.1 123 (by decide) (by decide) H (fun _ => none) Syscall.standard⟩

private theorem extCodeRoLoaded_strip [LibsignalPlacement] {m : Memory}
    (hcro : LibsignalCodeRoLoaded lsmpl m) :
    ExtCodeRoLoaded (ProofLib.stripExecOutside keepExt m) := by
  refine ⟨fun H => ?_, libsignalRoLoaded_strip hcro.2⟩
  have ⟨hL54, hL114, hL123⟩ := (extCodeRoLoaded_of_cro hcro).1 H
  refine ⟨strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL54,
    strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL114,
    strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL123⟩
  · have ha' : ProofLib.progKeep ((blkPC_54).rebase (blkPl_54).base vmTrapHooks) a = true := ha
    simp [keepExt, ha']
  · have ha' : ProofLib.progKeep ((blkPC_114).rebase (blkPl_114).base vmTrapHooks) a = true := ha
    simp [keepExt, ha']
  · have ha' : ProofLib.progKeep ((blkPC_123).rebase (blkPl_123).base vmTrapHooks) a = true := ha
    simp [keepExt, ha']

private theorem safeVm_keepExt [LibsignalPlacement] {m : Memory} {pc : BitVec 64} {inst : Instr}
    (hcl : LibsignalCodeLoaded lsmpl m) (hkeep : keepExt pc = true)
    (hal_pc : pc.toNat % 4 = 0) (hdec : Arm64.decode (m.read32 pc) = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  unfold keepExt at hkeep
  simp only [Bool.or_eq_true] at hkeep
  rcases hkeep with (hk54 | hk114) | hk123
  · have hI : IsLsBlockProg ((blkPC_54).rebase (blkPl_54).base vmTrapHooks) 54 vmTrapHooks :=
      inferInstance
    have hL : ((blkPC_54).rebase (blkPl_54).base vmTrapHooks).CodeLoaded m :=
      hI.eq_blockProgram ▸ hcl 54 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
    have hEq : (blkPC_54).rebase (blkPl_54).base vmTrapHooks =
        (blkLib_54.program blkPl_54).rebase (blkPl_54).base vmTrapHooks :=
      hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_54).symm
    exact safeVm_of_block_progKeep blkLib_54 blkPl_54 blk54_safeVm
      (hEq ▸ hL) (hEq ▸ hk54) hal_pc hdec
  · have hI : IsLsBlockProg ((blkPC_114).rebase (blkPl_114).base vmTrapHooks) 114 vmTrapHooks :=
      inferInstance
    have hL : ((blkPC_114).rebase (blkPl_114).base vmTrapHooks).CodeLoaded m :=
      hI.eq_blockProgram ▸ hcl 114 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
    have hEq : (blkPC_114).rebase (blkPl_114).base vmTrapHooks =
        (blkLib_114.program blkPl_114).rebase (blkPl_114).base vmTrapHooks :=
      hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_114).symm
    exact safeVm_of_block_progKeep blkLib_114 blkPl_114 blk114_safeVm
      (hEq ▸ hL) (hEq ▸ hk114) hal_pc hdec
  · have hI : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base vmTrapHooks) 123 vmTrapHooks :=
      inferInstance
    have hL : ((blkPC_123).rebase (blkPl_123).base vmTrapHooks).CodeLoaded m :=
      hI.eq_blockProgram ▸ hcl 123 (by decide) (by decide) vmTrapHooks (fun _ => none) Syscall.standard
    have hEq : (blkPC_123).rebase (blkPl_123).base vmTrapHooks =
        (blkLib_123.program blkPl_123).rebase (blkPl_123).base vmTrapHooks :=
      hI.eq_blockProgram.trans (prog_eq_blockProgram blkLib_eq_123).symm
    exact safeVm_of_block_progKeep blkLib_123 blkPl_123 blk123_safeVm
      (hEq ▸ hL) (hEq ▸ hk123) hal_pc hdec

private theorem runsTo_of_ext_123 [LibsignalPlacement] {H : LibsignalHooks}
    {s : State} {P_post : State → Prop}
    (hcl : ExtCodeRoLoaded s.mem)
    (h : RunsTo ((blkPC_123).rebase (blkPl_123).base H) s P_post) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s P_post := by
  intro hL_caller
  have hcaller : IsLsBlockProg ((blkPC_54).rebase (blkPl_54).base H) 54 H := inferInstance
  have hcallee : IsLsBlockProg ((blkPC_123).rebase (blkPl_123).base H) 123 H := inferInstance
  obtain ⟨s', hst_callee, htr, hP, _⟩ := h (hcl.1 H).2.2
  have hext : ∀ pc, ((blkPC_123).rebase (blkPl_123).base H).externAt? pc =
      ((blkPC_54).rebase (blkPl_54).base H).externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc : ((blkPC_123).rebase (blkPl_123).base H).svc =
      ((blkPC_54).rebase (blkPl_54).base H).svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  have hst_caller := Steps.of_sameHooks hext hsvc hst_callee
  exact ⟨s', hst_caller, htr, hP, hst_caller.codeLoaded hL_caller⟩

private theorem new_from_slice_ext_ok [LibsignalPlacement]
    (C : Crypto) (H : LibsignalHooks) [hH : HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with
        pre := fun x s0 =>
          (newFromSliceSpec C.F).pre x s0 ∗ ⌜ExtCodeRoLoaded s0.mem⌝ } := by
  have h114 := new_from_slice_placed_ro_ok C.F hH.memcpy hH.compress256
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hcomm : ((newFromSliceSpec C.F).pre x s0 ∗ ⌜ExtCodeRoLoaded s0.mem⌝) ∗ R =
      ⌜ExtCodeRoLoaded s0.mem⌝ ∗ ((newFromSliceSpec C.F).pre x s0 ∗ R) := by sep_ac_rfl
  rw [hcomm, satisfies_pure_sepConj] at hpre
  obtain ⟨hext_cro, hpre_nfs⟩ := hpre
  have hpre_ro : s0.mem ⊨
      ((newFromSliceSpec C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗ R := by
    have hc : ((newFromSliceSpec C.F).pre x s0 ∗ ⌜LibsignalRoLoaded lsmpl s0.mem⌝) ∗ R =
        ⌜LibsignalRoLoaded lsmpl s0.mem⌝ ∗ ((newFromSliceSpec C.F).pre x s0 ∗ R) := by sep_ac_rfl
    rw [hc, satisfies_pure_sepConj]
    exact ⟨hext_cro.2, hpre_nfs⟩
  have hcaller : IsLsBlockProg ((blkPC_54).rebase (blkPl_54).base H) 54 H := inferInstance
  have hcallee : IsLsBlockProg ((blkPC_114).rebase (blkPl_114).base H) 114 H := inferInstance
  have hQL : ((blkPC_114).rebase (blkPl_114).base H).CodeLoaded s0.mem := (hext_cro.1 H).2.1
  obtain ⟨sf, hstepsQ, hout, _⟩ := h114.no_fault_before_outcome x R s0 hpc hrun hpre_ro hsp hQL
  have hext_eq : ∀ pc, ((blkPC_114).rebase (blkPl_114).base H).externAt? pc =
      ((blkPC_54).rebase (blkPl_54).base H).externAt? pc := fun pc => by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram,
      ls_externAt?_blockProgram_eq_of_externs_eq libsignalSessionLib lsmpl H Syscall.standard
        (hcallee.externs_eq.trans hcaller.externs_eq.symm)]
  have hsvc_eq : ((blkPC_114).rebase (blkPl_114).base H).svc =
      ((blkPC_54).rebase (blkPl_54).base H).svc := by
    rw [hcallee.eq_blockProgram, hcaller.eq_blockProgram]; rfl
  exact reaches_outcome_steps (Steps.of_sameHooks hext_eq hsvc_eq hstepsQ)
    (reaches_outcome.of_outcome hout)

private theorem s2Frame_of_strip_vm {keep : BitVec 64 → Bool} {m₁ m₂ : Memory}
    {regs : List (BitVec 64 × ℕ)}
    (hf' : S2Frame (ProofLib.stripExecOutside keep m₁) (ProofLib.stripExecOutside keep m₂) regs)
    (hperm : ∀ a, m₂.perm a = m₁.perm a) :
    S2Frame m₁ m₂ regs := by
  refine ⟨?_, ⟨⟨?_, fun a ha => (hperm a).trans ha⟩, ⟨?_, ?_⟩⟩, ?_⟩
  · intro a hr hlf hout
    have h1 := hf'.1 a (by rwa [strip_perm_r]) (by rwa [ProofLib.strip_isLazyFree]) hout
    rwa [ProofLib.strip_read8, ProofLib.strip_read8] at h1
  · intro a ha
    obtain ⟨hp, hlf⟩ := Memory.permNoLazy_eq_some_rw_iff.mp ha
    have hr1 : (m₁.perm a).r = true := by rw [hp]; rfl
    have hlf2' := (hf'.2.2 a (by rwa [strip_perm_r]) (by rwa [ProofLib.strip_isLazyFree])).2
    rw [ProofLib.strip_isLazyFree] at hlf2'
    exact Memory.permNoLazy_eq_some_rw_iff.mpr ⟨(hperm a).trans hp, hlf2'⟩
  · intro a ⟨hm, han⟩
    have h2 := (hf'.2.1.2.1 a ⟨by rwa [strip_perm_mapped], by rwa [ProofLib.strip_isAnon]⟩).2
    rw [ProofLib.strip_isAnon] at h2
    exact ⟨by rwa [hperm a], h2⟩
  · intro a hp hout
    have h2 := hf'.2.1.2.2 a (strip_perm_of_protNone hp) hout
    refine ⟨(hperm a).trans hp, fun hlf => ?_⟩
    obtain ⟨hrd, hlf2⟩ := h2.2 (by rwa [ProofLib.strip_isLazyFree])
    rw [ProofLib.strip_read8, ProofLib.strip_read8] at hrd
    rw [ProofLib.strip_isLazyFree] at hlf2
    exact ⟨hrd, hlf2⟩
  · intro a hr hlf
    have hlf2 := (hf'.2.2 a (by rwa [strip_perm_r]) (by rwa [ProofLib.strip_isLazyFree])).2
    rw [ProofLib.strip_isLazyFree] at hlf2
    exact ⟨by rwa [hperm a], hlf2⟩

private theorem epost_lockstep_ext [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hcro : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hRuns0 : RunsToE ((blkPC_54).rebase (blkPl_54).base (kdfOnlyHooks H)) s0
      (EPost C.F x s0 sp0))
    (hRuns' : RunsToE ((blkPC_54).rebase (blkPl_54).base (kdfOnlyHooks H))
      (ProofLib.stripS keepExt s0) (EPost C.F x (ProofLib.stripS keepExt s0) sp0)) :
    ∀ {Q oom : State → Prop},
      (∀ sf, VmPreserved s0 sf → TraceEq s0 sf → EPost C.F x s0 sp0 sf →
        sf.pc = s0.readReg64 .x30 ∧ sf.status = .Running ∧ Q sf) →
      reaches_pc ((blkPC_54).rebase (blkPl_54).base H) (s0.readReg64 .x30) s0 Q oom := by
  intro Q oom hK hL0
  let H' := kdfOnlyHooks H
  let s0' := ProofLib.stripS keepExt s0
  have hs0'_mem : s0'.mem = ProofLib.stripExecOutside keepExt s0.mem := by cases s0; rfl
  have hL0_ext : ((blkPC_54).rebase (blkPl_54).base H').CodeLoaded s0.mem :=
    (extCodeRoLoaded_of_cro hcro).1 H' |>.1
  have hL0' : ((blkPC_54).rebase (blkPl_54).base H').CodeLoaded s0'.mem :=
    (hs0'_mem ▸ extCodeRoLoaded_strip hcro).1 H' |>.1
  obtain ⟨sf0, hsteps0, htr0, hpost0, _⟩ := hRuns0 hL0_ext
  obtain ⟨sf', hsteps', htr', hpost', _⟩ := hRuns' hL0'
  obtain ⟨sf, hor, hsteps_H, hvm⟩ :=
    steps_kdf_lockstep_vm safeVm_keepExt (C := C) (H := H)
      hsteps0 hpost0.2.1 rfl hsteps' hpost'.2.1 hcro.1
  have ⟨htr, hpost⟩ : TraceEq s0 sf ∧ EPost C.F x s0 sp0 sf := by
    rcases hor with rfl | hsf_eq
    · exact ⟨htr0, hpost0⟩
    · subst hsf_eq
      rcases hpost' with ⟨hpc_sf', hstat_sf', hcallee', hprk_sf', hhm_sf', hframe_sf'⟩
      have hpc_sf : sf.pc = s0.readReg64 .x30 := by
        simpa [s0', stripS_pc, stripS_readReg64] using hpc_sf'
      have hstat_sf : sf.status = .Running := by
        simpa [stripS_status] using hstat_sf'
      have hcallee : CalleeSaved s0 sf := by
        refine ⟨by simpa [s0', stripS_sp] using hcallee'.1, fun r hr => ?_⟩
        simpa [s0', stripS_readReg64] using hcallee'.2 r hr
      have htr : TraceEq s0 sf :=
        ⟨by simpa [s0', stripS_trace] using htr'.1,
         by simpa [s0', stripS_calleeSavedVRegs] using htr'.2⟩
      have hsf_mem : (ProofLib.stripS keepExt sf).mem =
          ProofLib.stripExecOutside keepExt sf.mem := by
        cases sf; rfl
      have hx0_s0' : s0'.readReg64 .x0 = s0.readReg64 .x0 :=
        stripS_readReg64 keepExt s0 .x0
      have hprk_sf : sf.mem.readBytes (s0.readReg64 .x0) 32 = x.prk C.F := by
        rw [← hx0_s0']
        rwa [hsf_mem, strip_readBytes] at hprk_sf'
      have hhm_sf : HmacSt sf.mem (s0.readReg64 .x0 + 0x20#64) C.F (x.prk C.F) [] := by
        rw [← hx0_s0']
        rcases hhm_sf' with ⟨h1, h2, h3, h4a, h4b, h4c, h4d⟩
        rw [hsf_mem] at h2 h3 h4a h4b h4c h4d
        exact ⟨h1, by rwa [strip_readBytes] at h2, by rwa [ProofLib.strip_read8] at h3,
          by rwa [strip_readBytes] at h4a, by rwa [strip_read64] at h4b,
          by rwa [strip_readBytes] at h4c, by rwa [strip_read64] at h4d⟩
      have hframe_sf : ExtFrame s0 sp0 sf.mem := by
        unfold ExtFrame at hframe_sf' ⊢
        rw [hs0'_mem, hsf_mem, hx0_s0'] at hframe_sf'
        exact s2Frame_of_strip_vm hframe_sf' hvm.perm_eq
      exact ⟨htr, hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  exact ⟨sf, hsteps_H, Or.inl (hK sf hvm htr hpost)⟩

private theorem extract_salt_props_976 {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    {R : SepProp}
    (hb_stk : IsBlock (memRegion (sp0 - 544#64) 976) (sp0 - 544#64) 976 (fun _ => True))
    (hsep : s0.mem ⊨
      (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
        memRegion (sp0 - 544#64) 976) ∗ R) :
    ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      Memory.RW s0.mem x.saltA 32 ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976 := by
  intro sv hsalt
  have hsep_salt : s0.mem ⊨ (⌜x.saltA ≠ 0#64⌝ ∗ (x.saltA ↦ₛ sv.toList)) ∗
      (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ (memRegion (sp0 - 544#64) 976 ∗ R))) := by
    have hsep' := hsep
    rw [hsalt] at hsep'
    dsimp only [optSaltAt] at hsep'
    ac_nf at hsep' ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hsep_salt
  rcases hsep_salt with ⟨hne, hsep_sv⟩
  have hb_sv := IsBlock.pointsToBytes_len (a := x.saltA) sv.2
  have hsep_sv_stk : s0.mem ⊨ (x.saltA ↦ₛ sv.toList) ∗
      (memRegion (sp0 - 544#64) 976 ∗ (memRegion x.ret 0xb0 ∗ ((x.ikmA ↦ₛ x.ikm) ∗ R))) := by
    ac_nf at hsep_sv ⊢
  have hsv_mem : s0.mem.readBytes x.saltA 32 = sv.toList := by
    have h := (hb_sv.read hsep_sv).2
    rwa [sv.2] at h
  have hrw_sv : Memory.RW s0.mem x.saltA 32 :=
    fun a ha => hb_sv.permNoLazy_rw hsep_sv ha
  have hd_sv_stk : DisjointRegions x.saltA 32 (sp0 - 544#64) 976 :=
    hb_sv.disjoint hb_stk (by decide) (by decide) hsep_sv_stk
  exact ⟨hne, hsv_mem, hrw_sv, hd_sv_stk⟩

private theorem extract_ext_runsToE [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hcl0 : ExtCodeRoLoaded s0.mem)
    (hpc : s0.pc = (blkPl_54).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx2 : x.salt.isSome → s0.readReg64 .x2 = 32#64)
    (hsalt_none : x.salt = none → x.saltA = 0#64 ∨ s0.readReg64 .x2 = 0#64)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = 32#64)
    (hikm_len : x.ikm.length = 32)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hRW_out : Memory.RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : Memory.RW s0.mem x.ikmA 32)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm)
    (hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0)
    (hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976)
    (hsalt_props : ∀ sv, x.salt = some sv →
      x.saltA ≠ 0#64 ∧ s0.mem.readBytes x.saltA 32 = sv.toList ∧
      Memory.RW s0.mem x.saltA 32 ∧
      DisjointRegions x.saltA 32 (sp0 - 544#64) 976) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s0 (EPost C.F x s0 sp0) := by
  have hNfs := new_from_slice_ext_ok C H
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stk_sub hRW_stk sp0 432 hsub_432
  have hsub_144 : ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : 0 < 544 ∧ ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x98 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hRW_salt : Memory.RW s0.mem (saltPtrOf sp0 x) 32 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact rw_stk_sub hRW_stk (sp0 + 144#64) 32 hsub_144
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact (hsalt_props sv hsalt).2.2.1
  have hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 - 544#64) 544 hsub_544
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    cases hsalt : x.salt with
    | none =>
      rw [saltPtrOf, hsalt]
      exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
    | some sv =>
      rw [saltPtrOf, hsalt]
      exact disj_stk_sub_right (hsalt_props sv hsalt).2.2.2 (sp0 + 176#64) 0x98 hsub_176
  have h0 := CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg0_placed_runsTo (H := H)
    hpc hrun hsp0 hx1 hx2 hx3 hx4 hsp_al hrw_sp0 hsalt_none
    (fun sv hsv => ⟨(hsalt_props sv hsv).1, (hsalt_props sv hsv).2.1, (hsalt_props sv hsv).2.2.2⟩))
  have h1 := RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_placed_runsTo hNfs (hcl0.of_keepsFrozen hkf) hRW_stk hRW_salt hd_salt_544 hd_salt_176 hsp_al hs
  have h2 := h1.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg1a_placed_runsTo hRW_stk hsp_al hs)
  have h3 := h2.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg1b_placed_runsTo hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h4 := h3.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg1c_placed_runsTo hRW_stk hsp_al hs)
  have h5 := RunsToE.trans_full h4 fun s hs hkf _ =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (fin_placed_runsTo
      (fun hpre => runsTo_of_ext_123 (hcl0.of_keepsFrozen hkf)
        (finalize_fixed_placed_runsTo (C := C) (H := H) hpre))
      hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg2_placed_runsTo hsp_al hs)
  have h7 := RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_placed_runsTo hNfs (hcl0.of_keepsFrozen hkf) hRW_stk hsp_al hs
  exact h7.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg3_placed_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)

/-- Relocatable `subroutine_ok` with `VmPreserved` for
`GenericHkdf<Hmac<Sha256>>::extract` (Block `54`, `32`-B `ikm`) under `withLsCodeRoLoaded lsmpl`. -/
theorem extract_placed_vm_ok_cro [LibsignalPlacement] (C : Crypto)
    (H : LibsignalHooks) [HkdfPlacedHooks C.F H] :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (blkPl_54).base
      (withLsCodeRoLoaded lsmpl (extractBudgetSpec C.F)) := by
  refine subroutine_ok_intro fun x R s0 hpc hrun hpre_cro hsp => ?_
  obtain ⟨hcro, hpre⟩ := extract_withLsCodeRoLoaded hpre_cro
  dsimp only [extractBudgetSpec, withVmPreserved, extractSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hsalt_none, hx3, hx4, hikm_len⟩, hsep⟩
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let R_rest : SepProp := optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗ R
  change s0.mem ⊨
    (memRegion x.ret 0xb0 ∗ optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 976#64) 976) ∗ R at hsep
  rw [hsp_m976] at hsep
  have hb_ret := IsBlock.memRegion x.ret 0xb0
  have hb_ikm := IsBlock.pointsToBytes_len (a := x.ikmA) hikm_len
  have hb_stk := IsBlock.memRegion (sp0 - 544#64) 976
  have hsep_ret_stk : s0.mem ⊨ memRegion x.ret 0xb0 ∗ (memRegion (sp0 - 544#64) 976 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 544#64) 976 ∗
      (memRegion x.ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ (memRegion (sp0 - 544#64) 976 ∗ R))) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (x.ikmA ↦ₛ x.ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗ (memRegion x.ret 0xb0 ∗ (optSaltAt x.saltA x.salt ∗ R))) := by
    ac_nf at hsep ⊢
  have hRW_out : Memory.RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : Memory.RW s0.mem x.ikmA 32 :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA 32 = x.ikm := by
    have h := (hb_ikm.read hsep_ikm_ret).2
    rwa [hikm_len] at h
  have hd_ikm_out : DisjointRegions x.ikmA 32 (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret (by decide) (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA 32 (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk (by decide) (by decide) hsep_ikm_stk
  have hsalt_props := extract_salt_props_976 hb_stk hsep
  let H' := kdfOnlyHooks H
  let s0' := ProofLib.stripS keepExt s0
  have hs0'_mem : s0'.mem = ProofLib.stripExecOutside keepExt s0.mem := by cases s0; rfl
  have hrw_strip : ∀ {base : BitVec 64} {len : Nat}, s0.mem.RW base len → s0'.mem.RW base len := by
    intro base len hrw a ha; rw [hs0'_mem]; exact strip_permNoLazy_rw (hrw a ha)
  have hRuns0 := extract_ext_runsToE (C := C) (H := H') (extCodeRoLoaded_of_cro hcro)
    hpc hrun hsp0 hx1 hx2 hsalt_none hx3 hx4 hikm_len hsp_al
    hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk hsalt_props
  have hRuns' := extract_ext_runsToE (C := C) (H := H') (hs0'_mem ▸ extCodeRoLoaded_strip hcro)
    (by simpa [s0', stripS_pc] using hpc)
    (by simpa [s0', stripS_status] using hrun)
    (by simpa [s0', stripS_sp] using hsp0)
    (by simpa [s0', stripS_readReg64] using hx1)
    (fun hs => by simpa [s0', stripS_readReg64] using hx2 hs)
    (fun hs => (hsalt_none hs).imp id (fun hx2_0 => by simpa [s0', stripS_readReg64] using hx2_0))
    (by simpa [s0', stripS_readReg64] using hx3)
    (by simpa [s0', stripS_readReg64] using hx4)
    hikm_len hsp_al
    (by simpa [s0', stripS_readReg64] using hrw_strip hRW_out)
    (hrw_strip hRW_stk)
    (hrw_strip hRW_ikm)
    (by simpa [s0', stripS_readReg64] using hd_out_stk)
    (by rw [hs0'_mem, strip_readBytes]; exact hikm_mem0)
    (by simpa [s0', stripS_readReg64] using hd_ikm_out)
    hd_ikm_stk
    (fun sv hsv =>
      let ⟨hne, hmem, hrw, hdisj⟩ := hsalt_props sv hsv
      ⟨hne, by rw [hs0'_mem, strip_readBytes]; exact hmem, hrw_strip hrw, hdisj⟩)
  refine epost_lockstep_ext (C := C) (H := H) hcro hRuns0 hRuns' fun sf hvm htr hpost => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [withLsCodeRoLoaded, extractBudgetSpec, withVmPreserved, extractSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]
    exact length_hmacWith C.F _ _
  have hb_prk := IsBlock.pointsToBytes_len (a := x.ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [])
      x.ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes x.ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (x.ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep : sf.mem ⊨ ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) []) ∗
      (memRegion (sp0 - 544#64) 976 ∗ R_rest) :=
    S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  change sf.mem ⊨
    ((x.ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (x.ret + 0x20#64) (x.prk C.F) [] ∗
      optSaltAt x.saltA x.salt ∗ (x.ikmA ↦ₛ x.ikm) ∗
      memRegion (s0.sp - 976#64) 976) ∗ R
  rw [hsp_m976]
  dsimp only [R_rest] at hpost_sep
  ac_nf at hpost_sep ⊢

private theorem fin_long_ext_runsTo [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hcl : ExtCodeRoLoaded s.mem)
    (hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : EFinLongPlaced C.F x s0 sp0 s) :
    RunsTo ((blkPC_54).rebase (blkPl_54).base H) s
      (ERetFin extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx22, hhm⟩
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_176 : 0 < 0x90 ∧ ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x90 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_m144 : 0 < 144 ∧ ((sp0 - 144#64) - (sp0 - 544#64)).toNat + 144 ≤ 976 := by
    have heq : (sp0 - 144#64) - (sp0 - 544#64) = 400#64 := by bv_lin
    rw [heq]; decide
  have hpre : FinGenPre finPlacedFakeB C.F (effectiveSalt x.salt)
      (x.ikm.take (64 * (x.ikm.length / 64))) (x.ikm.drop (64 * (x.ikm.length / 64))) s :=
    { pc_eq := by rw [finPlacedFakeB_off_0]; exact hpc
      status := hstat
      key_le := by rw [effectiveSalt_length]; decide
      rem_lt := by simp; omega
      hmac_st := by rw [hx1]; exact hhm
      rw_out := by rw [hx0]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_144.2)
      rw_hm := by rw [hx1]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_176.2)
      rw_fsp := by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_m144.2)
      disj_out_hm := by
        rw [hx0, hx1]; exact disj_sp0_off sp0 144#64 32 176#64 0x90 (by decide)
      disj_out_fsp := by
        rw [hx0, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 144#64 32 (by decide)).symm
      disj_hm_fsp := by
        rw [hx1, hsp]; exact (disj_sp0_sub_off sp0 144#64 144 176#64 0x90 (by decide)).symm
      sp_aligned := by rw [hsp]; exact sp0_aligned_0b1111 hsp_al }
  refine (runsTo_of_ext_123 hcl (finalize_fixed_gen_placed_runsTo (C := C) (H := H) hpre)).mono
    fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hout, hfr'⟩
  rw [hx0, hx1, hsp] at hfr'
  rw [hx0, List.take_append_drop] at hout
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_frame hfr' ?_
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact disj_sp0_off sp0 144#64 32 336#64 96 (by decide)
    · exact disj_sp0_off sp0 176#64 0x90 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 144#64 144 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem :=
    hframe.trans_triple hfr' hsub_144.2 hsub_176.2 hsub_m144.2
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 380) := by
    rw [hlr, extPlacedFakeB_off_380]
  exact ⟨⟨hstat', hcs.sp_eq.trans hsp, (CalleeSaved.x19 hcs).trans hx19,
    (CalleeSaved.x27 hcs).trans hx27,
    (CalleeSaved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CalleeSaved.x22 hcs).trans hx22, hout⟩

private theorem extract_none_long_ext_runsToE [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooks C.F H] {x : ExtractGhost} {s0 : State} {sp0 : BitVec 64}
    (hcl0 : ExtCodeRoLoaded s0.mem)
    (hpc : s0.pc = (blkPl_54).base)
    (hrun : s0.status = .Running)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hx1 : s0.readReg64 .x1 = x.saltA)
    (hx3 : s0.readReg64 .x3 = x.ikmA)
    (hx4 : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length)
    (hsalt : x.salt = none)
    (hsaltA : x.saltA = 0#64)
    (hikm_len : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hRW_out : Memory.RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976)
    (hRW_ikm : Memory.RW s0.mem x.ikmA x.ikm.length)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm)
    (hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0)
    (hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976) :
    RunsToE ((blkPC_54).rebase (blkPl_54).base H) s0 (EPost C.F x s0 sp0) := by
  have hNfs := new_from_slice_ext_ok C H
  have hsub_432 : (sp0 - (sp0 - 544#64)).toNat + 432 ≤ 976 := by
    have heq : sp0 - (sp0 - 544#64) = 544#64 := by bv_lin
    rw [heq]; decide
  have hsub_144 : 0 < 32 ∧ ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hrw_sp0 : s0.mem.RW sp0 432 := rw_stk_sub hRW_stk sp0 432 hsub_432
  have hRW_salt : Memory.RW s0.mem (saltPtrOf sp0 x) 32 := by
    rw [saltPtrOf, hsalt]
    exact rw_stk_sub hRW_stk _ _ hsub_144.2
  have hd_salt_544 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 - 544#64) 544 := by
    rw [saltPtrOf, hsalt]
    exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm
  have hd_salt_176 : DisjointRegions (saltPtrOf sp0 x) 32 (sp0 + 176#64) 0x98 := by
    rw [saltPtrOf, hsalt]
    exact disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)
  have h0 := CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg0_long_placed_runsTo (H := H)
    hpc hrun hsp0 hx1 hx3 hx4 hsp_al hrw_sp0 hsalt hsaltA)
  have h1 := RunsToE.trans_full h0 fun s hs hkf _ =>
    nfs1_long_placed_runsTo hNfs (hcl0.of_keepsFrozen hkf) hRW_stk hRW_salt hd_salt_544 hd_salt_176 hsp_al hs
  have h2 := h1.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg1a_long_placed_runsTo hRW_stk hikm_len hsp_al hs)
  have h3a := h2.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
      (seg1b1_long_placed_runsTo hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hsp_al hs)
  have h3 := h3a.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
      (seg1b2_long_placed_runsTo hRW_stk hRW_ikm hikm_len hikm_mem0 hd_ikm_stk hd_ikm_out hs)
  have h4 := h3.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg1c_long_placed_runsTo hRW_stk hsp_al hs)
  have h5 := RunsToE.trans_full h4 fun s hs hkf _ =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (fin_long_ext_runsTo (hcl0.of_keepsFrozen hkf) hRW_stk hikm_len hsp_al hs)
  have h6 := h5.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg2_placed_runsTo hsp_al hs)
  have h7 := RunsToE.trans_full h6 fun s hs hkf _ =>
    nfs2_placed_runsTo hNfs (hcl0.of_keepsFrozen hkf) hRW_stk hsp_al hs
  exact h7.trans fun s hs =>
    CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE (seg3_placed_runsTo hsp0 hRW_out hRW_stk hd_out_stk hsp_al hs)

/-- `subroutine_ok` for `HandshakeDeriveBudget.pqxdhHkdfExtractNonePlacedSpec` on Block `54`
(`salt = None`, `160` / `192` / `224`-B `ikm`, carrying `VmPreserved` in `post`). -/
theorem pqxdhHkdfExtractNone_placed_ok_block54 [LibsignalPlacement]
    {P : Primitives} {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooks C.F H]
    (hP : PrimitivesMatchCrypto P C) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 54)
      (pqxdhHkdfExtractNonePlacedSpec P lsmpl) := by
  refine subroutine_ok_intro fun ⟨ret, ikmA, ikm, sp⟩ R s0 hpc hrun hpre hsp => ?_
  dsimp only [pqxdhHkdfExtractNonePlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractNonePlacedSpec] at hpre
  rw [stackAt_alloc_extract sp] at hpre
  dsimp only [stackAt, extractStack, newFromSliceStack] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF0, hx0, hx1, hx3, hx4, hsp_eq, hikm_len⟩, hsep⟩
  subst hsp_eq
  have hcro : LibsignalCodeRoLoaded lsmpl s0.mem := ⟨hF0.code, hF0.ro⟩
  let sp0 := s0.sp - 432#64
  have hsp0 : s0.sp = sp0 + 432#64 := by dsimp [sp0]; bv_lin
  have hsp_m976 : s0.sp - 976#64 = sp0 - 544#64 := by dsimp [sp0]; bv_lin
  have hsp_al_0 : (s0.sp &&& 0b1111#64) = 0#64 := by simpa [State.spAligned] using hsp
  have hsp_al : (sp0 &&& 15#64) = 0#64 := sp0_aligned hsp0 hsp_al_0
  let x : ExtractGhost := ⟨ret, 0#64, none, ikmA, bytesToBv8 ikm⟩
  have hikm_bv_len : x.ikm.length = ikm.length := by dsimp [x]; exact bytesToBv8_length ikm
  have hikm_cases : x.ikm.length = 160 ∨ x.ikm.length = 192 ∨ x.ikm.length = 224 := by
    rwa [hikm_bv_len]
  have hikm_pos : 0 < x.ikm.length := by omega
  have hx4' : s0.readReg64 .x4 = BitVec.ofNat 64 x.ikm.length := by
    rw [hikm_bv_len]; exact hx4
  let R_rest : SepProp :=
    (ikmA ↦ₛ bytesToBv8 ikm) ∗
    memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
    memRegion (s0.sp - 4096#64) 3120 ∗ R
  rw [hsp_m976] at hsep
  have hb_ret := IsBlock.memRegion ret 0xb0
  have hb_ikm := IsBlock.pointsToBytes_len (a := ikmA) (rfl : x.ikm.length = x.ikm.length)
  have hb_stk := IsBlock.memRegion (sp0 - 544#64) 976
  have hsep_ret_stk : s0.mem ⊨ memRegion ret 0xb0 ∗ (memRegion (sp0 - 544#64) 976 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_stk : s0.mem ⊨ memRegion (sp0 - 544#64) 976 ∗ (memRegion ret 0xb0 ∗ R_rest) := by
    dsimp only [R_rest]; ac_nf at hsep ⊢
  have hsep_ikm_ret : s0.mem ⊨ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      (memRegion ret 0xb0 ∗
        (memRegion (s0.sp - 8192#64) 3936 ∗ memRegion (s0.sp - 4256#64) 160 ∗
          memRegion (s0.sp - 4096#64) 3120 ∗ memRegion (sp0 - 544#64) 976 ∗ R)) := by
    ac_nf at hsep ⊢
  have hsep_ikm_stk : s0.mem ⊨ (ikmA ↦ₛ bytesToBv8 ikm) ∗
      (memRegion (sp0 - 544#64) 976 ∗
        (memRegion ret 0xb0 ∗ memRegion (s0.sp - 8192#64) 3936 ∗
          memRegion (s0.sp - 4256#64) 160 ∗ memRegion (s0.sp - 4096#64) 3120 ∗ R)) := by
    ac_nf at hsep ⊢
  have hRW_out : Memory.RW s0.mem (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact fun a ha => hb_ret.permNoLazy_rw hsep_ret_stk ha
  have hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976 :=
    fun a ha => hb_stk.permNoLazy_rw hsep_stk ha
  have hRW_ikm : Memory.RW s0.mem x.ikmA x.ikm.length :=
    fun a ha => hb_ikm.permNoLazy_rw hsep_ikm_ret ha
  have hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976 := by
    rw [hx0]; exact hb_ret.disjoint hb_stk (by decide) (by decide) hsep_ret_stk
  have hikm_mem0 : s0.mem.readBytes x.ikmA x.ikm.length = x.ikm :=
    (hb_ikm.read hsep_ikm_ret).2
  have hd_ikm_out : DisjointRegions x.ikmA x.ikm.length (s0.readReg64 .x0) 0xb0 := by
    rw [hx0]; exact hb_ikm.disjoint hb_ret hikm_pos (by decide) hsep_ikm_ret
  have hd_ikm_stk : DisjointRegions x.ikmA x.ikm.length (sp0 - 544#64) 976 :=
    hb_ikm.disjoint hb_stk hikm_pos (by decide) hsep_ikm_stk
  let H' := kdfOnlyHooks H
  let s0' := ProofLib.stripS keepExt s0
  have hs0'_mem : s0'.mem = ProofLib.stripExecOutside keepExt s0.mem := by cases s0; rfl
  have hrw_strip : ∀ {base : BitVec 64} {len : Nat}, s0.mem.RW base len → s0'.mem.RW base len := by
    intro base len hrw a ha; rw [hs0'_mem]; exact strip_permNoLazy_rw (hrw a ha)
  have hRuns0 := extract_none_long_ext_runsToE (C := C) (H := H') (extCodeRoLoaded_of_cro hcro)
    hpc hrun hsp0 hx1 hx3 hx4' rfl rfl hikm_cases hsp_al
    hRW_out hRW_stk hRW_ikm hd_out_stk hikm_mem0 hd_ikm_out hd_ikm_stk
  have hRuns' := extract_none_long_ext_runsToE (C := C) (H := H')
    (hs0'_mem ▸ extCodeRoLoaded_strip hcro)
    ((stripS_pc keepExt s0).trans hpc)
    (by simpa [s0', stripS_status] using hrun)
    (by simpa [s0', stripS_sp] using hsp0)
    (by simpa [s0', stripS_readReg64] using hx1)
    (by simpa [s0', stripS_readReg64] using hx3)
    (by simpa [s0', stripS_readReg64] using hx4')
    rfl rfl hikm_cases hsp_al
    (by simpa [s0', stripS_readReg64] using hrw_strip hRW_out)
    (hrw_strip hRW_stk)
    (hrw_strip hRW_ikm)
    (by simpa [s0', stripS_readReg64] using hd_out_stk)
    (by rw [hs0'_mem, strip_readBytes]; exact hikm_mem0)
    (by simpa [s0', stripS_readReg64] using hd_ikm_out)
    hd_ikm_stk
  refine epost_lockstep_ext (C := C) (H := H) hcro hRuns0 hRuns' fun sf hvm htr hpost => ?_
  rcases hpost with ⟨hpc_sf, hstat_sf, hcallee, hprk_sf, hhm_sf, hframe_sf⟩
  refine ⟨hpc_sf, hstat_sf, ?_, CallingConventionPreserved_of_calleeSaved hcallee⟩
  dsimp only [pqxdhHkdfExtractNonePlacedSpec, withVmPreserved,
    CryptoVerification.E2E.Pqxdh.Initiator.pqxdhHkdfExtractNonePlacedSpec]
  rw [stackAt_alloc_extract s0.sp]
  dsimp only [stackAt, extractStack, newFromSliceStack]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨hvm, ?_⟩
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨htr.1, ?_⟩
  unfold ExtFrame at hframe_sf
  rw [hx0] at hprk_sf hhm_sf hframe_sf
  have hprk_eq : x.prk C.F = bytesToBv8 (hkdfExtractRef P none ikm) := by
    dsimp [x, ExtractGhost.prk]
    exact (bytesToBv8_hkdfExtractRef_none hP ikm).symm
  have hprk_ref_len : (hkdfExtractRef P none ikm).length = 32 :=
    hkdfExtractRef_length P none ikm
  have hprk_len : (x.prk C.F).length = 32 := by
    rw [hprk_eq, bytesToBv8_length, hprk_ref_len]
  have hb_prk := IsBlock.pointsToBytes_len (a := ret) hprk_len
  have hb_hm := isBlock_hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [] (by decide)
  have hb_ret' : IsBlock ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) [])
      ret 0xb0
      (fun m => ((x.prk C.F).length ≤ 2 ^ 64 ∧ m.readBytes ret (x.prk C.F).length = x.prk C.F) ∧
        HmacSt m (ret + 0x20#64) C.F (x.prk C.F) []) :=
    hb_prk.sepConj hb_hm rfl (by decide)
  have hpost_sep : sf.mem ⊨ ((ret ↦ₛ x.prk C.F) ∗ hmacCoreAt C.F (ret + 0x20#64) (x.prk C.F) []) ∗
      (memRegion (sp0 - 544#64) 976 ∗ R_rest) :=
    S2Frame.update_two_blocks hb_ret hb_ret' hb_stk hb_stk hsep_ret_stk hframe_sf
      ⟨⟨by rw [hprk_len]; decide, by rwa [hprk_len]⟩, hhm_sf⟩ trivial
  rw [hprk_eq, ← pqxdhHmacStateAt_eq hP (ret + 0x20#64) (by omega)] at hpost_sep
  rw [hsp_m976]
  dsimp only [R_rest] at hpost_sep
  ac_nf at hpost_sep ⊢

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAux
