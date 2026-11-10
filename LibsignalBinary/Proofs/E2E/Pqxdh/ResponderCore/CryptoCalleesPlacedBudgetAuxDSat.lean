/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxASat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.HkdfGenFinPlacedSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSlice -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSliceSat -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChainBudget -- proof-setup: allow-public-import
import LibsignalBinary.Heap.SpecBudget
import LibsignalBinary.Proofs.Common.SharedHelpers
meta import LibsignalBinary.Proofs.Common.SharedHelpers -- shake: keep
import LibsignalBinary.Proofs.Placed.BudgetVmSteps
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractSegs
import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
import ProofLib.SepLogic.HeapIntro

/-!
# `HookSat` Sibling of `CryptoCalleesPlacedBudgetAux`, Part D (`CryptoCalleesPlacedBudgetAuxDSat`)

`memset`-free `VmPreserved` & `stripExecOutside` lockstep infrastructure on Blocks `54` + `114`,
unstripping lemmas for `EFinPlaced` / `EFinLongPlaced` / `EPost`, and the shared re-anchored
post-`finalize_fixed` tail `post_fin_vm_runsTo_sat`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

namespace LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxDSat

open Arm64 ProofLib SepProp BitVec
open CryptoGames.HKDF (hkdfExtract)
open CryptoGames.LibsignalSession (Crypto)
open CryptoVerification
  (IsLsBlockProg LibsignalCodeLoaded LibsignalHooks LibsignalPlacement LibsignalRoLoaded
   blkLib_114 blkLib_eq_114 blkPC_114 blkPl_114
   libsignalRoLoaded_of_keepsFrozen libsignalSessionLib
   ls_externAt?_blockProgram_eq_of_externs_eq lsmpl prog_eq_blockProgram withLsCodeLoaded)
open CryptoVerification.LibsignalAesCbc (memcpyHook returnToLinkRegister)
open CryptoVerification.LibsignalHmac (compress256Hook readShaState)
open CryptoVerification.LibsignalTripleRatchet
  (ExtractGhost HmacSt LibsignalCodeRoLoaded NewFromSliceGhost
   blkLib_54 blkLib_eq_54 blkPC_54 blkPl_54 extPlacedFakeB extPlacedFakeB_off_396
   hmacCoreAt isBlock_hmacCoreAt length_hmacWith lsCompress256Sym lsMemcpySym
   newFromSliceSpec newFromSliceStack)
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer (new_from_slice_placed_ro_ok)
open CryptoVerification.LibsignalTripleRatchet.Extract
  (CallingConventionPreserved.x19 CallingConventionPreserved.x22
   CallingConventionPreserved.x27 CallingConventionPreserved.x29
   EFinPlaced ENfs2Placed EPost ERet2 ERetFin ExtCommon ExtFrame ExtSaved RunsToE S2Frame
   disj_sp0_off disj_sp0_sub_off disjoint_fullComplementHeap fullComplementHeap
   isBlock_three_s2frame matches_fullComplementHeap nfs2_placed_runsTo rw_stk_sub
   satisfies_three_blocks seg2_placed_runsTo seg3_placed_runsTo)
open CryptoVerification.E2E.Pqxdh.ResponderCore (EFinLongPlaced)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoBridgePlacedBudgetAuxASat
  (RunsToVm stripS_hmacSt)
open LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxASat
  (stripS_hmacStGen)
open LibsignalBinary.Proofs.Placed.BudgetVmSteps
  (vmPreserved_refl_iff vmPreserved_setMem_writeBytes vmPreserved_setPC)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyExactCore (HookSatExactMemcpy)
open LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.DefsBudget
  (checkBlockSafeVm placedLib_rebase_allInstrs_safeVm stripS_calleeSavedVRegs
   stripS_pc stripS_readReg64 stripS_sp stripS_status stripS_trace vmTrapHooks)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.InstancesBudgetSat
  (new_from_slice_placed_ro_vm_ok_at_block_sat)
open LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.NewFromSliceSat
  (new_from_slice_placed_ro_ok_sat)
open LibsignalBinary.Proofs.TripleRatchet.Hkdf.CommonBudgetSat
  (HkdfPlacedHooksBudgetSat HkdfPlacedHooksExactBudgetSat)

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

@[expose] public def noMemsetKdfHooks (H : LibsignalHooks) : LibsignalHooks :=
  fun n =>
    if n == lsMemcpySym || n == lsCompress256Sym then H n
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

public theorem noMemsetKdfHooks_memcpy {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksBudgetSat C.F H] :
    noMemsetKdfHooks H lsMemcpySym = some memcpyHook := by
  unfold noMemsetKdfHooks
  simp [hH.memcpy]

public theorem noMemsetKdfHooks_compress256 {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksBudgetSat C.F H] :
    noMemsetKdfHooks H lsCompress256Sym = some (compress256Hook C.F) := by
  unfold noMemsetKdfHooks
  simp [hH.compress256]

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

public theorem strip_readBytes (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
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

public theorem strip_permNoLazy_rw {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
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

private theorem noMemsetKdfHooks_findSome?_active (keep : BitVec 64 → Bool)
    {C : Crypto} {H : LibsignalHooks} [hH : HkdfPlacedHooksBudgetSat C.F H] :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then noMemsetKdfHooks H n else none) = some f →
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
      by_cases hn : (n == lsMemcpySym || n == lsCompress256Sym) = true
      · have hk_eq : noMemsetKdfHooks H n = H n := by simp [noMemsetKdfHooks, hn]
        rw [hk_eq] at h
        intro s _hrun
        simp only [Bool.or_eq_true, beq_iff_eq] at hn
        rcases hn with rfl | rfl
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
          have hk_n : noMemsetKdfHooks H n = none := by unfold noMemsetKdfHooks; rw [hn]; simp [hHn]
          rw [hk_n] at h; dsimp only at h ⊢
          exact noMemsetKdfHooks_findSome?_active keep (C := C) tl h
        | some g =>
          have hk_g : noMemsetKdfHooks H n = some (fun s => s.setStatus (.Exception "ext")) := by
            unfold noMemsetKdfHooks; rw [hn]; simp [hHn]
          rw [hk_g] at h; dsimp only at h
          injection h with hf; subst hf; intro s hrun; cases s; cases hrun
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact noMemsetKdfHooks_findSome?_active keep (C := C) tl h

private theorem maskedHooks_findSome?_none {M H : LibsignalHooks}
    (hnone : ∀ n, M n = none → H n = none) :
    ∀ (l : List (String × Nat)) {off : Nat},
      (l.findSome? fun (n, o) => if o == off then M n else none) = none →
      (l.findSome? fun (n, o) => if o == off then H n else none) = none
  | [], _, _ => rfl
  | (n, o) :: tl, off, h => by
    dsimp only [List.findSome?] at h ⊢
    by_cases ho : (o == off) = true
    · simp only [ho, ↓reduceIte] at h ⊢
      cases hMn : M n with
      | none =>
        rw [hMn] at h; rw [hnone n hMn]
        simpa using maskedHooks_findSome?_none hnone tl (by simpa using h)
      | some g => rw [hMn] at h; cases h
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact maskedHooks_findSome?_none hnone tl h

private theorem maskedHooks_externAt?_none {blkPC : Program} {b : BitVec 64}
    {M H : LibsignalHooks} (hnone : ∀ n, M n = none → H n = none) {pc : BitVec 64}
    (hext : (blkPC.rebase b M).externAt? pc = none) :
    (blkPC.rebase b H).externAt? pc = none := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢; rw [findSome?_symbols_none] at hext ⊢
  have h1 : (blkPC.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then M n else none) = none := by
    cases hm : (blkPC.stubs.findSome? fun (n, o) =>
        if o == (pc - b).toNat then M n else none) with
    | none => rfl | some g => rw [hm] at hext; cases hext
  rw [maskedHooks_findSome?_none hnone blkPC.stubs h1]; rfl

private theorem noMemsetKdfHooks_externAt?_active {blkPC : Program} {b : BitVec 64}
    (keep : BitVec 64 → Bool) {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksBudgetSat C.F H]
    {pc : BitVec 64} {f : State → State}
    (hext : (blkPC.rebase b (noMemsetKdfHooks H)).externAt? pc = some f)
    {s : State} (hrun : (f (ProofLib.stripS keep s)).status = .Running) :
    (blkPC.rebase b H).externAt? pc = some f ∧
    f (ProofLib.stripS keep s) = ProofLib.stripS keep (f s) ∧ VmPreserved s (f s) := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢; rw [findSome?_symbols_none] at hext ⊢
  cases hm : (blkPC.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then noMemsetKdfHooks H n else none) with
  | none => rw [hm] at hext; cases hext
  | some g =>
    rw [hm] at hext; injection hext with hgf; subst hgf
    obtain ⟨hhk, hcomm, hvm⟩ :=
      noMemsetKdfHooks_findSome?_active keep (C := C) blkPC.stubs hm s hrun
    rw [hhk]; exact ⟨rfl, hcomm, hvm⟩

private theorem noMemsetKdfHooks_externAt?_none {blkPC : Program} {b : BitVec 64}
    {H : LibsignalHooks} {pc : BitVec 64}
    (hext : (blkPC.rebase b (noMemsetKdfHooks H)).externAt? pc = none) :
    (blkPC.rebase b H).externAt? pc = none :=
  maskedHooks_externAt?_none
    (fun n hn => by unfold noMemsetKdfHooks at hn; split at hn <;> simpa using hn) hext

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

public theorem cl_of_keepsFrozen {pl : Obj.MultiPlacement} {m m' : Memory}
    (hcl : LibsignalCodeLoaded pl m) (hkf : m.KeepsFrozen m') :
    LibsignalCodeLoaded pl m' :=
  fun j hj hunmut ext panics svc => (hcl j hj hunmut ext panics svc).of_keepsFrozen hkf

private theorem steps_maskedKdf_lockstep_vm [LibsignalPlacement]
    {blkPC : Program} {b : BitVec 64} {keep : BitVec 64 → Bool}
    (hsafe : ∀ {m : Memory} {pc : BitVec 64} {inst : Instr},
      LibsignalCodeLoaded lsmpl m → keep pc = true → pc.toNat % 4 = 0 →
      Arm64.decode (m.read32 pc) = some inst →
      inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false)
    {M H : LibsignalHooks}
    (hact : ∀ {pc : BitVec 64} {f : State → State} {s : State},
      (blkPC.rebase b M).externAt? pc = some f →
      (f (ProofLib.stripS keep s)).status = .Running →
      (blkPC.rebase b H).externAt? pc = some f ∧
      f (ProofLib.stripS keep s) = ProofLib.stripS keep (f s) ∧ VmPreserved s (f s))
    (hnone : ∀ {pc : BitVec 64},
      (blkPC.rebase b M).externAt? pc = none → (blkPC.rebase b H).externAt? pc = none)
    {s1 sf0 sf' : State}
    (hsteps0 : Steps (blkPC.rebase b M) s1 sf0) (hrun0 : sf0.status = .Running) :
    ∀ {s1' : State}, s1' = ProofLib.stripS keep s1 →
      Steps (blkPC.rebase b M) s1' sf' → sf'.status = .Running →
      LibsignalCodeLoaded lsmpl s1.mem →
      ∃ sf : State, (sf = sf0 ∨ sf' = ProofLib.stripS keep sf) ∧
        Steps (blkPC.rebase b H) s1 sf ∧ VmPreserved s1 sf := by
  induction hsteps0 with
  | refl => intro s1' _ _ _ _; exact ⟨_, Or.inl rfl, .refl _, VmPreserved.refl _⟩
  | @step s1 s2 sf0 h1_0 hrest0 ih =>
    intro s1' hs1' hsteps' hrun_f hcl1
    cases hsteps' with
    | refl => exact ⟨s1, Or.inr hs1', .refl s1, VmPreserved.refl s1⟩
    | @step _ s2' _ h1' hrest' =>
      subst hs1'
      have hr2_0 : s2.status = .Running := by
        cases hrest0 with | refl => exact hrun0 | step hs _ => cases hs <;> assumption
      have hr2' : s2'.status = .Running := by
        cases hrest' with | refl => exact hrun_f | step hs _ => cases hs <;> assumption
      cases h1_0 with
      | halt_unmapped _ _ _ => cases s1; cases hr2_0
      | extern_fault _ _ _ => cases s1; cases hr2_0
      | @extern f hr1 hext0 hkf_s1 hsym_s1 =>
        cases h1' with
        | halt_unmapped _ _ _ => cases s1; cases hr2'
        | extern_fault _ _ _ => cases s1; cases hr2'
        | @exec inst' _ hfe' =>
          have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
          unfold Program.fetchMem at hfe'; rw [hpc_eq, hext0] at hfe'; simp at hfe'
        | @extern f' _ hext' _ _ =>
          have hpc_eq : (ProofLib.stripS keep s1).pc = s1.pc := by cases s1; rfl
          rw [hpc_eq, hext0] at hext'; injection hext' with hff'; subst hff'
          obtain ⟨hext_H, hcomm, hvm1⟩ := hact hext0 hr2'
          have hstep_H : Step (blkPC.rebase b H) s1 (f s1) :=
            Step.extern hr1 hext_H hkf_s1 hsym_s1
          obtain ⟨sf, hor, hsteps_H, hvm_rest⟩ :=
            ih hrun0 hcomm hrest' hrun_f (cl_of_keepsFrozen hcl1 hkf_s1)
          exact ⟨sf, hor, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩
      | @exec inst hr1 hfe0 =>
        let P_H := blkPC.rebase b H
        have hext_kdf : (blkPC.rebase b M).externAt? s1.pc = none := by
          cases he : (blkPC.rebase b M).externAt? s1.pc with
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
          have hext_H : P_H.externAt? s1.pc = none := hnone hext_kdf
          have ⟨hal_pc, hce', hdec⟩ : s1.pc.toNat % 4 = 0 ∧
              (ProofLib.stripExecOutside keep s1.mem).canExec s1.pc 4 = true ∧
              Arm64.decode (s1.mem.read32 s1.pc) = some inst' := by
            unfold Program.fetchMem at hfe'; rw [hext_kdf] at hfe'
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe'
            by_cases hal : s1.pc.toNat % 4 = 0
            · simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hfe'
              split at hfe'
              · contradiction
              · rename_i hce_neg; simp only [Bool.not_eq_true', Bool.not_eq_false] at hce_neg
                rw [strip_read32] at hfe'; exact ⟨hal, hce_neg, hfe'⟩
            · simp only [hal, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
          have hce : s1.mem.canExec s1.pc 4 = true := by
            unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢; intro k hk
            have hxk := hce' k hk
            rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
          have hfe0' := hfe0; unfold Program.fetchMem at hfe0'; rw [hext_kdf] at hfe0'
          simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
            not_true_eq_false, hce, Bool.not_true] at hfe0'
          have hinst_eq : inst' = inst := Option.some.inj (hdec.symm.trans hfe0')
          subst hinst_eq
          have hfe_H : P_H.fetchMem s1.mem s1.pc = some inst' := by
            unfold Program.fetchMem; rw [hext_H]
            simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hal_pc, ne_eq,
              not_true_eq_false, hce, Bool.not_true]; exact hdec
          have hkeep_pc : keep s1.pc = true := by
            unfold Memory.canExec at hce'; rw [Memory.allPerm_iff] at hce'
            simpa using (ProofLib.strip_perm_x_imp (hce' 0 (by omega))).2
          have ⟨hnsvc0, hnmsr⟩ := hsafe hcl1 hkeep_pc hal_pc hdec
          have hev0 : (blkPC.rebase b M).evalInst inst' s1 = execInst inst' s1 :=
            Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0 s1
          have hev_kdf : (blkPC.rebase b M).evalInst inst' (ProofLib.stripS keep s1) =
              ProofLib.stripS keep ((blkPC.rebase b M).evalInst inst' s1) := by
            rw [hev0, Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
          have hstep_H : Step P_H s1 ((blkPC.rebase b M).evalInst inst' s1) := by
            rw [hev0]; have := Step.exec (prog := P_H) hr1 hfe_H
            rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
          have hvm1 : VmPreserved s1 ((blkPC.rebase b M).evalInst inst' s1) := by
            rw [hev0]
            exact (vmNoTpidr_execInst hnsvc0 s1).toVmPreserved
              (Arm64.execInst_tpidrEl0_of_not_isMsrTpidrEl0 hnmsr s1)
          obtain ⟨sf, hor, hsteps_H, hvm_rest⟩ :=
            ih hrun0 hev_kdf hrest' hrun_f (cl_of_keepsFrozen hcl1 hstep_H.keepsFrozen)
          exact ⟨sf, hor, .step hstep_H hsteps_H, hvm1.trans hvm_rest⟩

private theorem steps_noMemsetKdf_lockstep_vm [LibsignalPlacement]
    {blkPC : Program} {b : BitVec 64} {keep : BitVec 64 → Bool}
    (hsafe : ∀ {m : Memory} {pc : BitVec 64} {inst : Instr},
      LibsignalCodeLoaded lsmpl m → keep pc = true → pc.toNat % 4 = 0 →
      Arm64.decode (m.read32 pc) = some inst →
      inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false)
    {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksBudgetSat C.F H] {s1 sf0 sf' : State}
    (hsteps0 : Steps (blkPC.rebase b (noMemsetKdfHooks H)) s1 sf0) (hrun0 : sf0.status = .Running)
    {s1' : State} (hs1' : s1' = ProofLib.stripS keep s1)
    (hsteps' : Steps (blkPC.rebase b (noMemsetKdfHooks H)) s1' sf')
    (hrun_f : sf'.status = .Running) (hcl1 : LibsignalCodeLoaded lsmpl s1.mem) :
    ∃ sf : State, (sf = sf0 ∨ sf' = ProofLib.stripS keep sf) ∧
      Steps (blkPC.rebase b H) s1 sf ∧ VmPreserved s1 sf :=
  steps_maskedKdf_lockstep_vm hsafe
    (fun hext hrun => noMemsetKdfHooks_externAt?_active keep (C := C) hext hrun)
    noMemsetKdfHooks_externAt?_none hsteps0 hrun0 hs1' hsteps' hrun_f hcl1

private theorem blk54_safeVm : checkBlockSafeVm blkLib_54.text = true := by decide +kernel
private theorem blk114_safeVm : checkBlockSafeVm blkLib_114.text = true := by decide +kernel

@[expose] public noncomputable def keepExt54_114 [LibsignalPlacement] (a : BitVec 64) : Bool :=
  ProofLib.progKeep ((blkPC_54).rebase (blkPl_54).base vmTrapHooks) a ||
  ProofLib.progKeep ((blkPC_114).rebase (blkPl_114).base vmTrapHooks) a

@[expose] public def Ext54_114CodeRoLoaded [LibsignalPlacement] (m : Memory) : Prop :=
  (∀ (H : LibsignalHooks),
    ((blkPC_54).rebase (blkPl_54).base H).CodeLoaded m ∧
    ((blkPC_114).rebase (blkPl_114).base H).CodeLoaded m) ∧
  LibsignalRoLoaded lsmpl m

public theorem Ext54_114CodeRoLoaded.of_keepsFrozen [LibsignalPlacement] {m m' : Memory}
    (h : Ext54_114CodeRoLoaded m) (hk : m.KeepsFrozen m') : Ext54_114CodeRoLoaded m' :=
  ⟨fun H =>
    let ⟨h54, h114⟩ := h.1 H
    ⟨h54.of_keepsFrozen hk, h114.of_keepsFrozen hk⟩,
   libsignalRoLoaded_of_keepsFrozen h.2 hk⟩

public theorem ext54_114CodeRoLoaded_of_cro [LibsignalPlacement] {m : Memory}
    (hcro : LibsignalCodeRoLoaded lsmpl m) : Ext54_114CodeRoLoaded m := by
  refine ⟨fun H => ?_, hcro.2⟩
  have hI54 : IsLsBlockProg ((blkPC_54).rebase (blkPl_54).base H) 54 H := inferInstance
  have hI114 : IsLsBlockProg ((blkPC_114).rebase (blkPl_114).base H) 114 H := inferInstance
  exact ⟨hI54.eq_blockProgram ▸ hcro.1 54 (by decide) (by decide) H (fun _ => none) Syscall.standard,
    hI114.eq_blockProgram ▸ hcro.1 114 (by decide) (by decide) H (fun _ => none) Syscall.standard⟩

public theorem ext54_114CodeRoLoaded_strip [LibsignalPlacement] {m : Memory}
    (hcro : LibsignalCodeRoLoaded lsmpl m) :
    Ext54_114CodeRoLoaded (ProofLib.stripExecOutside keepExt54_114 m) := by
  refine ⟨fun H => ?_, libsignalRoLoaded_strip hcro.2⟩
  have ⟨hL54, hL114⟩ := (ext54_114CodeRoLoaded_of_cro hcro).1 H
  refine ⟨strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL54,
    strip_codeLoaded_of_keep_sub (fun a ha => ?_) hL114⟩
  · have ha' : ProofLib.progKeep ((blkPC_54).rebase (blkPl_54).base vmTrapHooks) a = true := ha
    simp [keepExt54_114, ha']
  · have ha' : ProofLib.progKeep ((blkPC_114).rebase (blkPl_114).base vmTrapHooks) a = true := ha
    simp [keepExt54_114, ha']

private theorem safeVm_keepExt54_114 [LibsignalPlacement] {m : Memory} {pc : BitVec 64}
    {inst : Instr} (hcl : LibsignalCodeLoaded lsmpl m) (hkeep : keepExt54_114 pc = true)
    (hal_pc : pc.toNat % 4 = 0) (hdec : Arm64.decode (m.read32 pc) = some inst) :
    inst.isSvc0 = false ∧ inst.isMsrTpidrEl0 = false := by
  unfold keepExt54_114 at hkeep
  simp only [Bool.or_eq_true] at hkeep
  rcases hkeep with hk54 | hk114
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

public theorem new_from_slice_ext54_114_ok [LibsignalPlacement]
    (C : Crypto) (H : LibsignalHooks)
    (hmc : HookSatExactMemcpy H lsMemcpySym)
    (hc256 : H lsCompress256Sym = some (compress256Hook C.F)) :
    subroutine_ok ((blkPC_54).rebase (blkPl_54).base H) (lsmpl.base 114)
      { newFromSliceSpec C.F with
        pre := fun x s0 =>
          (newFromSliceSpec C.F).pre x s0 ∗ ⌜Ext54_114CodeRoLoaded s0.mem⌝ } := by
  have h114 := new_from_slice_placed_ro_ok_sat C.F hmc hc256
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  have hcomm : ((newFromSliceSpec C.F).pre x s0 ∗ ⌜Ext54_114CodeRoLoaded s0.mem⌝) ∗ R =
      ⌜Ext54_114CodeRoLoaded s0.mem⌝ ∗ ((newFromSliceSpec C.F).pre x s0 ∗ R) := by sep_ac_rfl
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
  have hQL : ((blkPC_114).rebase (blkPl_114).base H).CodeLoaded s0.mem := (hext_cro.1 H).2
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

public theorem lift_runsToE_ext54_114_vm [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooksBudgetSat C.F H] {s1 : State} {Q0 Q' : State → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hRuns0 : RunsToE ((blkPC_54).rebase (blkPl_54).base (noMemsetKdfHooks H)) s1 Q0)
    (hRuns' : RunsToE ((blkPC_54).rebase (blkPl_54).base (noMemsetKdfHooks H))
      (ProofLib.stripS keepExt54_114 s1) Q')
    (hrun0 : ∀ sf, Q0 sf → sf.status = .Running)
    (hrun' : ∀ sf', Q' sf' → sf'.status = .Running)
    (hunstrip : ∀ sf, VmPreserved s1 sf → Q' (ProofLib.stripS keepExt54_114 sf) → Q0 sf) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s1 Q0 := by
  intro hL1
  let H' := noMemsetKdfHooks H
  let s1' := ProofLib.stripS keepExt54_114 s1
  have hs1'_mem : s1'.mem = ProofLib.stripExecOutside keepExt54_114 s1.mem := by cases s1; rfl
  have hL1_ext : ((blkPC_54).rebase (blkPl_54).base H').CodeLoaded s1.mem :=
    (ext54_114CodeRoLoaded_of_cro hcro).1 H' |>.1
  have hL1' : ((blkPC_54).rebase (blkPl_54).base H').CodeLoaded s1'.mem :=
    (hs1'_mem ▸ ext54_114CodeRoLoaded_strip hcro).1 H' |>.1
  obtain ⟨sf0, hsteps0, htr0, hpost0, _⟩ := hRuns0 hL1_ext
  obtain ⟨sf', hsteps', htr', hpost', _⟩ := hRuns' hL1'
  obtain ⟨sf, hor, hsteps_H, hvm⟩ :=
    steps_noMemsetKdf_lockstep_vm safeVm_keepExt54_114 (C := C) (H := H)
      hsteps0 (hrun0 sf0 hpost0) rfl hsteps' (hrun' sf' hpost') hcro.1
  rcases hor with rfl | hsf_eq
  · exact ⟨sf, hsteps_H, hvm, htr0.1, htr0.2, hpost0, hsteps_H.codeLoaded hL1⟩
  · subst hsf_eq
    have htr_eq : sf.trace = s1.trace := by simpa [s1', stripS_trace] using htr'.1
    have hv_eq : calleeSavedVRegs sf = calleeSavedVRegs s1 := by
      simpa [s1', stripS_calleeSavedVRegs] using htr'.2
    exact ⟨sf, hsteps_H, hvm, htr_eq, hv_eq, hunstrip sf hvm hpost', hsteps_H.codeLoaded hL1⟩

private theorem extSaved_setMem {s0 : State} {m m' : Memory} {sp0 : BitVec 64}
    (hs : ExtSaved s0 sp0 m) : ExtSaved (s0.setMem m') sp0 m := by
  rcases hs with ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩; cases s0
  exact ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩

private theorem extSaved_of_setMem {s0 : State} {m m' : Memory} {sp0 : BitVec 64}
    (hs : ExtSaved (s0.setMem m') sp0 m) : ExtSaved s0 sp0 m := by
  rcases hs with ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩; cases s0
  exact ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩

private theorem unstrip_extSaved {keep : BitVec 64 → Bool} {s0 sf : State} {sp0 : BitVec 64}
    (hs' : ExtSaved (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf).mem) :
    ExtSaved s0 sp0 sf.mem := by
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  rcases hs' with ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩
  rw [hsf_mem] at h29 hlr h28 h26 h25 h24 h23 h22 h21 h20 h19
  simp only [strip_read64, stripS_readReg64] at h29 hlr h28 h26 h25 h24 h23 h22 h21 h20 h19
  exact ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩

private theorem strip_extSaved (keep : BitVec 64 → Bool) {s0 sf : State} {sp0 : BitVec 64}
    (hs : ExtSaved s0 sp0 sf.mem) :
    ExtSaved (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf).mem := by
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  rcases hs with ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩
  rw [← strip_read64 keep sf.mem, ← hsf_mem, ← stripS_readReg64 keep s0]
    at h29 hlr h28 h26 h25 h24 h23 h22 h21 h20 h19
  exact ⟨h29, hlr, h28, h26, h25, h24, h23, h22, h21, h20, h19⟩

private theorem unstrip_extCommon {keep : BitVec 64 → Bool} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hc' : ExtCommon (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    ExtCommon s0 sp0 sf := by
  rcases hc' with ⟨hstat', hsp', hx19', hx27', hx29', hsaved', hframe'⟩
  have hs0_mem : (ProofLib.stripS keep s0).mem = ProofLib.stripExecOutside keep s0.mem := by
    cases s0; rfl
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  refine ⟨by simpa [stripS_status] using hstat',
    by simpa [stripS_sp] using hsp',
    by simpa [stripS_readReg64] using hx19',
    by simpa [stripS_readReg64] using hx27',
    by simpa [stripS_readReg64] using hx29',
    unstrip_extSaved hsaved', ?_⟩
  unfold ExtFrame at hframe' ⊢
  rw [hs0_mem, hsf_mem, stripS_readReg64] at hframe'
  exact s2Frame_of_strip_vm hframe' hperm

public theorem unstrip_efinPlaced [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {C : Crypto} {x : ExtractGhost} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hs' : EFinPlaced C.F x (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    EFinPlaced C.F x s0 sp0 sf := by
  rcases hs' with ⟨hc', hpc', hlr', hx0', hx1', hx22', hhm'⟩
  rw [stripS_hmacSt] at hhm'
  exact ⟨unstrip_extCommon hperm hc',
    by simpa [stripS_pc] using hpc',
    by simpa [stripS_readReg64] using hlr',
    by simpa [stripS_readReg64] using hx0',
    by simpa [stripS_readReg64] using hx1',
    by simpa [stripS_readReg64] using hx22',
    hhm'⟩

public theorem unstrip_efinLongPlaced [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {C : Crypto} {x : ExtractGhost} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hs' : EFinLongPlaced C.F x (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    EFinLongPlaced C.F x s0 sp0 sf := by
  rcases hs' with ⟨hc', hpc', hlr', hx0', hx1', hx22', hhm'⟩
  rw [stripS_hmacStGen] at hhm'
  exact ⟨unstrip_extCommon hperm hc',
    by simpa [stripS_pc] using hpc',
    by simpa [stripS_readReg64] using hlr',
    by simpa [stripS_readReg64] using hx0',
    by simpa [stripS_readReg64] using hx1',
    by simpa [stripS_readReg64] using hx22',
    hhm'⟩

private theorem unstrip_epost {keep : BitVec 64 → Bool}
    {C : Crypto} {x : ExtractGhost} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hpost' : EPost C.F x (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    EPost C.F x s0 sp0 sf := by
  rcases hpost' with ⟨hpc_sf', hstat_sf', hcallee', hprk_sf', hhm_sf', hframe_sf'⟩
  have hs0_mem : (ProofLib.stripS keep s0).mem = ProofLib.stripExecOutside keep s0.mem := by
    cases s0; rfl
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  have hx0_s0' : (ProofLib.stripS keep s0).readReg64 .x0 = s0.readReg64 .x0 :=
    stripS_readReg64 keep s0 .x0
  rw [hx0_s0'] at hprk_sf' hhm_sf'
  rw [hsf_mem, strip_readBytes] at hprk_sf'
  rw [stripS_hmacSt] at hhm_sf'
  unfold ExtFrame at hframe_sf'
  rw [hs0_mem, hsf_mem, hx0_s0'] at hframe_sf'
  exact ⟨by simpa [stripS_pc, stripS_readReg64] using hpc_sf',
    by simpa [stripS_status] using hstat_sf',
    ⟨by simpa [stripS_sp] using hcallee'.1,
      fun r hr => by simpa [stripS_readReg64] using hcallee'.2 r hr⟩,
    hprk_sf', hhm_sf', s2Frame_of_strip_vm hframe_sf' hperm⟩

@[expose] public def noMemsetMemcpyKdfHooks (H : LibsignalHooks) : LibsignalHooks :=
  fun n =>
    if n == lsCompress256Sym then H n
    else (H n).map (fun _ s => s.setStatus (.Exception "ext"))

public theorem noMemsetMemcpyKdfHooks_compress256 {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H] :
    noMemsetMemcpyKdfHooks H lsCompress256Sym = some (compress256Hook C.F) := by
  unfold noMemsetMemcpyKdfHooks
  simp [hH.compress256]

private theorem noMemsetMemcpyKdfHooks_findSome?_active (keep : BitVec 64 → Bool)
    {C : Crypto} {H : LibsignalHooks} [hH : HkdfPlacedHooksExactBudgetSat C.F H] :
    ∀ (l : List (String × Nat)) {off : Nat} {f : State → State},
      (l.findSome? fun (n, o) => if o == off then noMemsetMemcpyKdfHooks H n else none) = some f →
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
      by_cases hn : (n == lsCompress256Sym) = true
      · have hk_eq : noMemsetMemcpyKdfHooks H n = H n := by simp [noMemsetMemcpyKdfHooks, hn]
        rw [hk_eq] at h; intro s _hrun
        simp only [beq_iff_eq] at hn; subst hn
        rw [hH.compress256] at h ⊢; dsimp only at h ⊢; injection h with hf; subst hf
        refine ⟨rfl, ?_⟩
        unfold compress256Hook; dsimp only []; simp only [stripS_readReg64]
        have hst : readShaState (ProofLib.stripS keep s).mem (s.readReg64 .x0) =
            readShaState s.mem (s.readReg64 .x0) := by cases s; exact strip_readShaState keep _ _
        have hbs : (ProofLib.stripS keep s).mem.readBytes (s.readReg64 .x1)
              (64 * (s.readReg64 .x2).toNat) =
            s.mem.readBytes (s.readReg64 .x1) (64 * (s.readReg64 .x2).toNat) := by
          cases s; exact strip_readBytes keep _ _ _
        rw [hst, hbs]; exact hook_writeBytes_strip_vm keep s _
      · simp only [Bool.not_eq_true] at hn
        cases hHn : H n with
        | none =>
          have hk_n : noMemsetMemcpyKdfHooks H n = none := by
            unfold noMemsetMemcpyKdfHooks; rw [hn]; simp [hHn]
          rw [hk_n] at h; dsimp only at h ⊢
          exact noMemsetMemcpyKdfHooks_findSome?_active keep (C := C) tl h
        | some g =>
          have hk_g : noMemsetMemcpyKdfHooks H n = some (fun s => s.setStatus (.Exception "ext")) := by
            unfold noMemsetMemcpyKdfHooks; rw [hn]; simp [hHn]
          rw [hk_g] at h; dsimp only at h
          injection h with hf; subst hf; intro s hrun; cases s; cases hrun
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact noMemsetMemcpyKdfHooks_findSome?_active keep (C := C) tl h

private theorem noMemsetMemcpyKdfHooks_externAt?_active {blkPC : Program} {b : BitVec 64}
    (keep : BitVec 64 → Bool) {C : Crypto} {H : LibsignalHooks} [HkdfPlacedHooksExactBudgetSat C.F H]
    {pc : BitVec 64} {f : State → State}
    (hext : (blkPC.rebase b (noMemsetMemcpyKdfHooks H)).externAt? pc = some f)
    {s : State} (hrun : (f (ProofLib.stripS keep s)).status = .Running) :
    (blkPC.rebase b H).externAt? pc = some f ∧
    f (ProofLib.stripS keep s) = ProofLib.stripS keep (f s) ∧ VmPreserved s (f s) := by
  unfold Program.externAt? Program.hookAtOff? Program.rebase at hext ⊢
  dsimp only at hext ⊢; rw [findSome?_symbols_none] at hext ⊢
  cases hm : (blkPC.stubs.findSome? fun (n, o) =>
      if o == (pc - b).toNat then noMemsetMemcpyKdfHooks H n else none) with
  | none => rw [hm] at hext; cases hext
  | some g =>
    rw [hm] at hext; injection hext with hgf; subst hgf
    obtain ⟨hhk, hcomm, hvm⟩ :=
      noMemsetMemcpyKdfHooks_findSome?_active keep (C := C) blkPC.stubs hm s hrun
    rw [hhk]; exact ⟨rfl, hcomm, hvm⟩

private theorem noMemsetMemcpyKdfHooks_externAt?_none {blkPC : Program} {b : BitVec 64}
    {H : LibsignalHooks} {pc : BitVec 64}
    (hext : (blkPC.rebase b (noMemsetMemcpyKdfHooks H)).externAt? pc = none) :
    (blkPC.rebase b H).externAt? pc = none :=
  maskedHooks_externAt?_none
    (fun n hn => by unfold noMemsetMemcpyKdfHooks at hn; split at hn <;> simpa using hn) hext

/-- `compress256`-only lockstep sibling of `lift_runsToE_ext54_114_vm`: lifts `memset`- and
`memcpy`-free `RunsToE` segments on Blocks `54` + `114` to `RunsToVm` under
`[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem lift_runsToE_ext54_114_vm_compress_only [LibsignalPlacement] {C : Crypto}
    {H : LibsignalHooks} [HkdfPlacedHooksExactBudgetSat C.F H] {s1 : State} {Q0 Q' : State → Prop}
    (hcro : LibsignalCodeRoLoaded lsmpl s1.mem)
    (hRuns0 : RunsToE ((blkPC_54).rebase (blkPl_54).base (noMemsetMemcpyKdfHooks H)) s1 Q0)
    (hRuns' : RunsToE ((blkPC_54).rebase (blkPl_54).base (noMemsetMemcpyKdfHooks H))
      (ProofLib.stripS keepExt54_114 s1) Q')
    (hrun0 : ∀ sf, Q0 sf → sf.status = .Running)
    (hrun' : ∀ sf', Q' sf' → sf'.status = .Running)
    (hunstrip : ∀ sf, VmPreserved s1 sf → Q' (ProofLib.stripS keepExt54_114 sf) → Q0 sf) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s1 Q0 := by
  intro hL1
  let H' := noMemsetMemcpyKdfHooks H
  let s1' := ProofLib.stripS keepExt54_114 s1
  have hs1'_mem : s1'.mem = ProofLib.stripExecOutside keepExt54_114 s1.mem := by cases s1; rfl
  have hL1_ext : ((blkPC_54).rebase (blkPl_54).base H').CodeLoaded s1.mem :=
    (ext54_114CodeRoLoaded_of_cro hcro).1 H' |>.1
  have hL1' : ((blkPC_54).rebase (blkPl_54).base H').CodeLoaded s1'.mem :=
    (hs1'_mem ▸ ext54_114CodeRoLoaded_strip hcro).1 H' |>.1
  obtain ⟨sf0, hsteps0, htr0, hpost0, _⟩ := hRuns0 hL1_ext
  obtain ⟨sf', hsteps', htr', hpost', _⟩ := hRuns' hL1'
  obtain ⟨sf, hor, hsteps_H, hvm⟩ :=
    steps_maskedKdf_lockstep_vm safeVm_keepExt54_114
      (fun hext hrun => noMemsetMemcpyKdfHooks_externAt?_active keepExt54_114 (C := C) hext hrun)
      noMemsetMemcpyKdfHooks_externAt?_none
      hsteps0 (hrun0 sf0 hpost0) rfl hsteps' (hrun' sf' hpost') hcro.1
  rcases hor with rfl | hsf_eq
  · exact ⟨sf, hsteps_H, hvm, htr0.1, htr0.2, hpost0, hsteps_H.codeLoaded hL1⟩
  · subst hsf_eq
    have htr_eq : sf.trace = s1.trace := by simpa [s1', stripS_trace] using htr'.1
    have hv_eq : calleeSavedVRegs sf = calleeSavedVRegs s1 := by
      simpa [s1', stripS_calleeSavedVRegs] using htr'.2
    exact ⟨sf, hsteps_H, hvm, htr_eq, hv_eq, hunstrip sf hvm hpost', hsteps_H.codeLoaded hL1⟩

private theorem unstrip_enfs2Placed [LibsignalPlacement] {keep : BitVec 64 → Bool}
    {C : Crypto} {x : ExtractGhost} {s0 sf : State} {sp0 : BitVec 64}
    (hperm : ∀ a, sf.mem.perm a = s0.mem.perm a)
    (hs' : ENfs2Placed C.F x (ProofLib.stripS keep s0) sp0 (ProofLib.stripS keep sf)) :
    ENfs2Placed C.F x s0 sp0 sf := by
  rcases hs' with ⟨hc', hpc', hlr', hx0', hx1', hx2', hx22', hprk'⟩
  have hsf_mem : (ProofLib.stripS keep sf).mem = ProofLib.stripExecOutside keep sf.mem := by
    cases sf; rfl
  rw [hsf_mem, strip_readBytes] at hprk'
  exact ⟨unstrip_extCommon hperm hc',
    by simpa [stripS_pc] using hpc', by simpa [stripS_readReg64] using hlr',
    by simpa [stripS_readReg64] using hx0', by simpa [stripS_readReg64] using hx1',
    by simpa [stripS_readReg64] using hx2', by simpa [stripS_readReg64] using hx22', hprk'⟩

private theorem nfs32_vm_runsTo_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [hH : HkdfPlacedHooksExactBudgetSat C.F H] {s : State} {ret keyA : BitVec 64}
    {key : List (BitVec 8)}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = lsmpl.base 114) (hstat : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ret) (hx1 : s.readReg64 .x1 = keyA) (hx2 : s.readReg64 .x2 = 32#64)
    (hkey_len : key.length = 32) (hkey_mem : s.mem.readBytes keyA 32 = key)
    (hrw_ret : Memory.RW s.mem ret 0x98) (hrw_key : Memory.RW s.mem keyA 32)
    (hrw_stk : Memory.RW s.mem (s.sp - 544#64) 544)
    (hd_ret_key : DisjointRegions ret 0x98 keyA 32)
    (hd_ret_stk : DisjointRegions ret 0x98 (s.sp - 544#64) 544)
    (hd_key_stk : DisjointRegions keyA 32 (s.sp - 544#64) 544)
    (hsp_al : (s.sp &&& 15#64) = 0#64) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (fun s' =>
      s'.pc = s.readReg64 .lr ∧ s'.status = .Running ∧ CallingConventionPreserved s s' ∧
      s'.mem.read64 ret = 0#64 ∧ HmacSt s'.mem (ret + 8#64) C.F key [] ∧
      S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)]) := by
  intro hL
  have hNfs := new_from_slice_placed_ro_vm_ok_at_block_sat
    (callerProg := (blkPC_54).rebase (blkPl_54).base H) (i := 54) C.F hH.memcpy hH.compress256
  let xg : NewFromSliceGhost := { ret := ret, keyA := keyA, key := key }
  let P1 : SepProp := memRegion ret 0x98
  let P2 : SepProp := (keyA ↦ₛ key)
  let P3 : SepProp := stackAt s.sp newFromSliceStack
  let P : SepProp := P1 ∗ P2 ∗ P3
  have hb1 := IsBlock.memRegion ret 0x98
  have hb2 := IsBlock.pointsToBytes keyA key
  have hb3 := IsBlock.memRegion (s.sp - 544#64) 544
  have hkey_le64 : key.length ≤ 64 := by omega
  have hkey_le264 : key.length ≤ 2 ^ 64 := by omega
  have hrw_key' : Memory.RW s.mem keyA key.length := by rwa [hkey_len]
  have hd_ret_key' : DisjointRegions ret 0x98 keyA key.length := by rwa [hkey_len]
  have hd_key_stk' : DisjointRegions keyA key.length (s.sp - 544#64) 544 := by rwa [hkey_len]
  have hsatP : s.mem ⊨ P :=
    satisfies_three_blocks hb1 hb2 hb3 trivial ⟨hkey_le264, by rwa [hkey_len]⟩ trivial
      hrw_ret hrw_key' hrw_stk hd_ret_key' hd_ret_stk hd_key_stk' hkey_le264 (by decide)
  obtain ⟨hP, hpP, hmP⟩ := Satisfies.elim hsatP
  let hc : Heap := fullComplementHeap hP s.mem
  let R : SepProp := ⟨fun h => h = hc⟩
  have hsatPR : s.mem ⊨ P ∗ R :=
    Satisfies.sepConj_intro (disjoint_fullComplementHeap hP s.mem) hpP rfl
      (Heap.Matches.union hmP (matches_fullComplementHeap hP s.mem))
  have hx2_nat : (s.readReg64 .x2).toNat = key.length := by rw [hx2, hkey_len]; rfl
  have hpre_sat : s.mem ⊨
      (withLsCodeLoaded lsmpl
        { withVmPreserved (newFromSliceSpec C.F) with
          pre := fun g s0 =>
            (withVmPreserved (newFromSliceSpec C.F)).pre g s0 ∗
              ⌜LibsignalRoLoaded lsmpl s0.mem⌝ }).pre xg s ∗ R := by
    dsimp only [withLsCodeLoaded, withVmPreserved]
    rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
    refine ⟨hcro.1, ?_⟩
    rw [sepConj_assoc, sepConj_left_comm ((newFromSliceSpec C.F).pre xg s), satisfies_pure_sepConj]
    refine ⟨hcro.2, ?_⟩
    rw [newFromSliceSpec]; dsimp only [xg]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2_nat, hkey_le64⟩, by simpa [P, P1, P2, P3, sepConj_assoc] using hsatPR⟩
  have hcall := subroutine_ok_apply_full hNfs xg R hpc hstat hpre_sat
    (by simpa [State.spAligned] using hsp_al)
    (by intro _ _ hp; dsimp only [withLsCodeLoaded, withVmPreserved, newFromSliceSpec] at hp
        rw [satisfies_pure_sepConj] at hp; exact hp.1)
    (by intro _ _ _ he; dsimp only [withLsCodeLoaded, withVmPreserved, newFromSliceSpec] at he
        rw [satisfies_pure_sepConj] at he; exact he.1)
    (by intro _ _ ho; dsimp only [withLsCodeLoaded, withVmPreserved, newFromSliceSpec] at ho
        rw [satisfies_pure_sepConj] at ho; exact ho.1) hL
  rcases hcall with ⟨s', hsteps, ⟨hpc', hstat', hpost_sat, hcc⟩ | ⟨_, ⟨⟩⟩⟩
  dsimp only [withLsCodeLoaded, withVmPreserved, newFromSliceSpec, xg] at hpost_sat
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨hvm, hpost_sat⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpost_sat
  rcases hpost_sat with ⟨htr, hpost_sep⟩
  let P1' : SepProp := (ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key []
  have hb1' : IsBlock P1' ret 0x98
      (fun m => m.read64 ret = 0#64 ∧ HmacSt m (ret + 8#64) C.F key []) :=
    (IsBlock.pointsTo64 ret 0#64).sepConj (isBlock_hmacCoreAt C.F (ret + 8#64) key [] (by decide))
      rfl (by decide)
  change s'.mem ⊨ ((ret ↦₆₄ 0#64) ∗ hmacCoreAt C.F (ret + 8#64) key [] ∗ P2 ∗ P3) ∗ R at hpost_sep
  have hpost_1 : s'.mem ⊨ P1' ∗ (P2 ∗ (P3 ∗ R)) := by dsimp only [P1']; ac_nf at hpost_sep ⊢
  have hpost_2 : s'.mem ⊨ P2 ∗ (P1' ∗ (P3 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_3 : s'.mem ⊨ P3 ∗ (P1' ∗ (P2 ∗ R)) := by ac_nf at hpost_1 ⊢
  have hpost_R : s'.mem ⊨ R ∗ (P1' ∗ (P2 ∗ P3)) := by ac_nf at hpost_1 ⊢
  obtain ⟨hok, hhm⟩ := hb1'.read hpost_1
  have hkey_s' : s'.mem.readBytes keyA key.length = key := (hb2.read hpost_2).2
  have hmc : hc.Matches s'.mem := by
    obtain ⟨hc', _, _, hR_hc', _, hmatch⟩ := Satisfies.sepConj_elim hpost_R
    cases hR_hc'; exact Heap.Matches.of_union_left hmatch
  unfold Heap.Matches at hmc
  have hframe : S2Frame s.mem s'.mem [(ret, 0x98), (s.sp - 544#64, 544)] :=
    isBlock_three_s2frame hb1 hb1' hb2 hb3 hpP hmP hpost_1 hpost_2 hpost_3
      hkey_le264 (hkey_s'.trans (by rwa [hkey_len] : s.mem.readBytes keyA key.length = key).symm)
      hmc.1 hmc.2.2
  exact ⟨s', hsteps, hvm, htr, CallingConventionPreserved.vregs hcc,
    ⟨hpc', hstat', hcc, hok, hhm, hframe⟩, hsteps.codeLoaded hL⟩

private theorem nfs2_vm_runsTo_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooksExactBudgetSat C.F H] {x : ExtractGhost} {s0 s : State} {sp0 : BitVec 64}
    (hcro : LibsignalCodeRoLoaded lsmpl s.mem)
    (hRW_stk : Memory.RW s0.mem (sp0 - 544#64) 976) (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs : ENfs2Placed C.F x s0 sp0 s) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s (ERet2 extPlacedFakeB C.F x s0 sp0) := by
  rcases hs with ⟨⟨hstat, hsp, hx19, hx27, hx29, hsaved, hframe⟩,
    hpc, hlr, hx0, hx1, hx2, hx22, hprk⟩
  have hsub_144 : ((sp0 + 144#64) - (sp0 - 544#64)).toNat + 32 ≤ 976 := by
    have heq : (sp0 + 144#64) - (sp0 - 544#64) = 688#64 := by bv_lin
    rw [heq]; decide
  have hsub_x0 : ((sp0 + 176#64) - (sp0 - 544#64)).toNat + 0x98 ≤ 976 := by
    have heq : (sp0 + 176#64) - (sp0 - 544#64) = 720#64 := by bv_lin
    rw [heq]; decide
  have hsub_544 : ((sp0 - 544#64) - (sp0 - 544#64)).toNat + 544 ≤ 976 := by
    have heq : (sp0 - 544#64) - (sp0 - 544#64) = 0#64 := by bv_lin
    rw [heq]; decide
  have hsub_336 : ((sp0 + 336#64) - (sp0 - 544#64)).toNat + 96 ≤ 976 := by
    have heq : (sp0 + 336#64) - (sp0 - 544#64) = 880#64 := by bv_lin
    rw [heq]; decide
  have hprk_len : (x.prk C.F).length = 32 := by
    dsimp [ExtractGhost.prk, hkdfExtract]; exact length_hmacWith C.F _ _
  have hrw_144_s : s.mem.RW (sp0 + 144#64) 32 :=
    hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_144)
  have hrun := nfs32_vm_runsTo_sat (C := C) (H := H) hcro hpc hstat hx0 hx1 hx2 hprk_len hprk
    (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_x0)) hrw_144_s
    (by rw [hsp]; exact hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_544))
    (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 176#64 0x98 (by decide)).symm)
    (by rw [hsp]; exact (disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)).symm)
    (by rw [hsp]; exact hsp_al)
  refine hrun.mono fun s' hs' => ?_
  rcases hs' with ⟨hpc', hstat', hcs, hok, hhm, hfr'⟩
  rw [hsp] at hfr'
  have hx0_8 : sp0 + 176#64 + 8#64 = sp0 + 184#64 := by bv_lin
  rw [hx0_8] at hhm
  have hprk' : s'.mem.readBytes (sp0 + 144#64) 32 = x.prk C.F := by
    rw [hfr'.readBytes_eq hrw_144_s ?_ (by decide)]; · exact hprk
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact (disj_sp0_off sp0 144#64 32 176#64 0x98 (by decide)).symm
    · exact disj_sp0_sub_off sp0 544#64 544 144#64 32 (by decide)
  have hsaved' : ExtSaved s0 sp0 s'.mem := by
    refine hsaved.of_s2frame hfr' (hframe.rw_of_rw _ _ (rw_stk_sub hRW_stk _ _ hsub_336)) ?_
    intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact disj_sp0_off sp0 176#64 0x98 336#64 96 (by decide)
    · exact disj_sp0_sub_off sp0 544#64 544 336#64 96 (by decide)
  have hframe' : ExtFrame s0 sp0 s'.mem := hframe.trans_pair hfr' hsub_x0 hsub_544
  have hlr' : s.readReg64 .lr =
      extPlacedFakeB + bv% (ls_off% "<hkdf::GenericHkdf<hmac::Hmac<sha2::Sha256>>>::extract" + 396) := by
    rw [hlr, extPlacedFakeB_off_396]
  exact ⟨⟨hstat', (CallingConventionPreserved.sp_eq hcs).trans hsp,
    (CallingConventionPreserved.x19 hcs).trans hx19,
    (CallingConventionPreserved.x27 hcs).trans hx27,
    (CallingConventionPreserved.x29 hcs).trans hx29, hsaved', hframe'⟩,
    hpc'.trans hlr', (CallingConventionPreserved.x22 hcs).trans hx22, hok, hprk', hhm⟩

/-- Piece C (shared post-`finalize_fixed` tail on Blocks `54` + `114`, `0` `memset` calls),
re-anchored at `s0_re := s0.setMem s2.mem`, under `[HkdfPlacedHooksExactBudgetSat C.F H]`. -/
public theorem post_fin_vm_runsTo_sat [LibsignalPlacement] {C : Crypto} {H : LibsignalHooks}
    [HkdfPlacedHooksExactBudgetSat C.F H] {x : ExtractGhost} {s0 s2 : State} {sp0 : BitVec 64}
    (hcro2 : LibsignalCodeRoLoaded lsmpl s2.mem)
    (hsp0 : s0.sp = sp0 + 432#64)
    (hRW_out0 : Memory.RW s0.mem (s0.readReg64 .x0) 0xb0)
    (hRW_stk0 : Memory.RW s0.mem (sp0 - 544#64) 976)
    (hd_out_stk : DisjointRegions (s0.readReg64 .x0) 0xb0 (sp0 - 544#64) 976)
    (hsp_al : (sp0 &&& 15#64) = 0#64)
    (hs2 : ERetFin extPlacedFakeB C.F x s0 sp0 s2) :
    RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s2 (EPost C.F x s0 sp0) := by
  let H' := noMemsetMemcpyKdfHooks H
  rcases hs2 with ⟨⟨hstat2, hsp2, hx19_2, hx27_2, hx29_2, hsaved2, hframe2⟩, hpc2, hx22_2, hout2⟩
  let s0_re : State := s0.setMem s2.mem
  have hs0_re_reg : ∀ r, s0_re.readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  let s2' := ProofLib.stripS keepExt54_114 s2
  let s0_re' := ProofLib.stripS keepExt54_114 s0_re
  have hs2'_mem : s2'.mem = ProofLib.stripExecOutside keepExt54_114 s2.mem := by cases s2; rfl
  have hs0_re'_mem : s0_re'.mem = ProofLib.stripExecOutside keepExt54_114 s2.mem := by
    cases s0; rfl
  have hsaved_re : ExtSaved s0_re sp0 s2.mem := extSaved_setMem hsaved2
  have hs2_re : ERetFin extPlacedFakeB C.F x s0_re sp0 s2 :=
    ⟨⟨hstat2, hsp2, by rw [hs0_re_reg]; exact hx19_2, by rw [hs0_re_reg]; exact hx27_2, hx29_2,
      hsaved_re, S2Frame.refl s2.mem _⟩, hpc2, hx22_2, hout2⟩
  have hs2'_re : ERetFin extPlacedFakeB C.F x s0_re' sp0 s2' :=
    ⟨⟨by simpa [s2', stripS_status] using hstat2, by simpa [s2', stripS_sp] using hsp2,
      by simpa [s2', s0_re', stripS_readReg64, hs0_re_reg] using hx19_2,
      by simpa [s2', s0_re', stripS_readReg64, hs0_re_reg] using hx27_2,
      by simpa [s2', stripS_readReg64] using hx29_2,
      strip_extSaved keepExt54_114 hsaved_re,
      by unfold ExtFrame; rw [hs0_re'_mem, hs2'_mem]; exact S2Frame.refl _ _⟩,
     by simpa [s2', stripS_pc] using hpc2, by simpa [s2', stripS_readReg64] using hx22_2,
     by rw [hs2'_mem, strip_readBytes]; exact hout2⟩
  have hSeg2_re : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s2 (ENfs2Placed C.F x s0_re sp0) :=
    lift_runsToE_ext54_114_vm_compress_only (C := C) (H := H) hcro2
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg2_placed_runsTo (H := H') hsp_al hs2_re))
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg2_placed_runsTo (H := H') hsp_al hs2'_re))
      (fun _ hs => hs.1.1) (fun _ hs => hs.1.1)
      (fun sf hvm hs' => unstrip_enfs2Placed (by simpa [s0_re] using hvm.perm_eq) hs')
  have hSeg2 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s2 (ENfs2Placed C.F x s0 sp0) := by
    refine hSeg2_re.mono fun s3 hs3 => ?_
    rcases hs3 with ⟨⟨hstat3, hsp3, hx19_3, hx27_3, hx29_3, hsaved3, hframe3_re⟩, rest3⟩
    rw [hs0_re_reg] at hx19_3 hx27_3
    unfold ExtFrame at hframe2 hframe3_re
    rw [show s0_re.mem = s2.mem from by cases s0; rfl, hs0_re_reg] at hframe3_re
    exact ⟨⟨hstat3, hsp3, hx19_3, hx27_3, hx29_3, extSaved_of_setMem hsaved3,
      hframe2.trans hframe3_re⟩, rest3⟩
  have hNfs2 : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s2
      (ERet2 extPlacedFakeB C.F x s0 sp0) :=
    hSeg2.trans_full fun s3 hs3 hkf3 =>
      nfs2_vm_runsTo_sat ⟨cl_of_keepsFrozen hcro2.1 hkf3, libsignalRoLoaded_of_keepsFrozen hcro2.2 hkf3⟩
        hRW_stk0 hsp_al hs3
  refine hNfs2.trans_full fun s4 hs4 hkf4 => ?_
  have hcro4 : LibsignalCodeRoLoaded lsmpl s4.mem :=
    ⟨cl_of_keepsFrozen hcro2.1 hkf4, libsignalRoLoaded_of_keepsFrozen hcro2.2 hkf4⟩
  rcases hs4 with ⟨⟨hstat4, hsp4, hx19_4, hx27_4, hx29_4, hsaved4, hframe4⟩,
    hpc4, hx22_4, hok4, hprk4, hhm4⟩
  let s0_4 : State := s0.setMem s4.mem
  have hs0_4_reg : ∀ r, s0_4.readReg64 r = s0.readReg64 r := fun _ => by cases s0; rfl
  have hs0_4_sp : s0_4.sp = sp0 + 432#64 := (show s0_4.sp = s0.sp from by cases s0; rfl).trans hsp0
  have hRW_out4 : Memory.RW s0_4.mem (s0_4.readReg64 .x0) 0xb0 := by
    rw [hs0_4_reg]; exact hframe4.rw_of_rw (s0.readReg64 .x0) 0xb0 hRW_out0
  have hRW_stk4 : Memory.RW s0_4.mem (sp0 - 544#64) 976 :=
    hframe4.rw_of_rw (sp0 - 544#64) 976 hRW_stk0
  have hd_out_stk4 : DisjointRegions (s0_4.readReg64 .x0) 0xb0 (sp0 - 544#64) 976 := by
    rwa [hs0_4_reg]
  have hsaved_4 : ExtSaved s0_4 sp0 s4.mem := extSaved_setMem hsaved4
  have hs4_re : ERet2 extPlacedFakeB C.F x s0_4 sp0 s4 :=
    ⟨⟨hstat4, hsp4, by rw [hs0_4_reg]; exact hx19_4, by rw [hs0_4_reg]; exact hx27_4, hx29_4,
      hsaved_4, S2Frame.refl s4.mem _⟩, hpc4, hx22_4, hok4, hprk4, hhm4⟩
  let s4' := ProofLib.stripS keepExt54_114 s4
  let s0_4' := ProofLib.stripS keepExt54_114 s0_4
  have hs4'_mem : s4'.mem = ProofLib.stripExecOutside keepExt54_114 s4.mem := by cases s4; rfl
  have hs0_4'_mem : s0_4'.mem = ProofLib.stripExecOutside keepExt54_114 s4.mem := by cases s0; rfl
  have hrw_strip4 : ∀ {base : BitVec 64} {len : Nat}, s4.mem.RW base len → s0_4'.mem.RW base len := by
    intro base len hrw a ha; rw [hs0_4'_mem]; exact strip_permNoLazy_rw (hrw a ha)
  have hs4'_re : ERet2 extPlacedFakeB C.F x s0_4' sp0 s4' :=
    ⟨⟨by simpa [s4', stripS_status] using hstat4, by simpa [s4', stripS_sp] using hsp4,
      by simpa [s4', s0_4', stripS_readReg64, hs0_4_reg] using hx19_4,
      by simpa [s4', s0_4', stripS_readReg64, hs0_4_reg] using hx27_4,
      by simpa [s4', stripS_readReg64] using hx29_4,
      strip_extSaved keepExt54_114 hsaved_4,
      by unfold ExtFrame; rw [hs0_4'_mem, hs4'_mem]; exact S2Frame.refl _ _⟩,
     by simpa [s4', stripS_pc] using hpc4, by simpa [s4', stripS_readReg64] using hx22_4,
     by rw [hs4'_mem, strip_read64]; exact hok4,
     by rw [hs4'_mem, strip_readBytes]; exact hprk4,
     by rw [← stripS_hmacSt keepExt54_114] at hhm4; exact hhm4⟩
  have hSeg3_re : RunsToVm ((blkPC_54).rebase (blkPl_54).base H) s4 (EPost C.F x s0_4 sp0) :=
    lift_runsToE_ext54_114_vm_compress_only (C := C) (H := H) hcro4
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg3_placed_runsTo (H := H') hs0_4_sp hRW_out4 hRW_stk4 hd_out_stk4 hsp_al hs4_re))
      (CryptoVerification.LibsignalTripleRatchet.Extract.RunsTo.toE
        (seg3_placed_runsTo (H := H')
          (by simpa [s0_4', stripS_sp] using hs0_4_sp)
          (by simpa [s0_4', stripS_readReg64] using hrw_strip4 hRW_out4)
          (hrw_strip4 hRW_stk4)
          (by simpa [s0_4', stripS_readReg64] using hd_out_stk4) hsp_al hs4'_re))
      (fun _ hp => hp.2.1) (fun _ hp => hp.2.1)
      (fun sf hvm hp' => unstrip_epost (by simpa [s0_4] using hvm.perm_eq) hp')
  refine hSeg3_re.mono fun sf hpost_re => ?_
  rcases hpost_re with ⟨hpc_sf, hstat_sf, hcallee_re, hprk_sf, hhm_sf, hframe_re⟩
  rw [hs0_4_reg] at hpc_sf hprk_sf hhm_sf
  unfold ExtFrame at hframe4 hframe_re
  rw [show s0_4.mem = s4.mem from by cases s0; rfl, hs0_4_reg] at hframe_re
  exact ⟨hpc_sf, hstat_sf,
    ⟨(show s0_4.sp = s0.sp from by cases s0; rfl) ▸ hcallee_re.1,
      fun r hr => (hs0_4_reg r) ▸ hcallee_re.2 r hr⟩,
    hprk_sf, hhm_sf, hframe4.trans hframe_re⟩

end LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.CryptoCalleesPlacedBudgetAuxDSat
