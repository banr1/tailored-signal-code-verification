/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib
public import ProofLib.StdStartup.MemOps
public import VerifiedLibraries.Musl.Proofs.MemcpySym
public import VerifiedLibraries.RustStd.Spec.CoreMemrchr
public import LibsignalBinary.Heap.SpecBudget
public import LibsignalBinary.Heap.IfaceSimp
public import LibsignalBinary.Proofs.HookDischarge.Libc.Common -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO -- proof-setup: allow-public-import
public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Pure -- proof-setup: allow-public-import
import VerifiedLibraries.RustStd.Proofs.Wave1.CoreMemrchrLemmas
import LibsignalBinary.Heap.Fine.SpecBudgetHelpersFine
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget

/-!
# Region-Local `core::slice::memchr::memrchr` Code Verification & Master Spec (`HooksDehook.MemrchrCode`)

Card `R2-a1` (non-leaf `β′` route) for de-hooking `core::slice::memchr::memrchr`:

1. **Unified `(ro : Bool)` master specification (`masterMemrchrSpec`, THE master spec for the ghost)
   and process specification (`stdMemrchrSpec`, F1):**
   - `masterMemrchrSpec` is indexed by `(ro, c, p, bs) : Bool × BitVec 8 × BitVec 64 × List (BitVec 8)`
     over `VerifiedLibraries.Musl.memcpySrc ro p bs ∗ stackFrameAt s0.sp 16`, unifying disjoint
     read-write (`p ↦ₛ bs`, `ro = false`, `masterMemrchrSpecRW`) and read-only (`p ↦ᵣ bs`,
     `ro = true`, `masterMemrchrSpecRO`) callers in a single ghost hook. Its spatial frame contains
     no `lr` (`x30`) constraint, so card `b` can freely conjoin `⌜LsRetAddr624 (s0.readReg64 .lr)⌝`
     (`withLsRet`), and `SpecStripSInvariant keep masterMemrchrSpec` is proved below.
   - `stdMemrchrSpec` (plus `stdMemrchrSpecRW` and `stdMemrchrSpecRO`) strengthens the postcondition
     to full `StdStatePreserved s0 sf` (`ProcessFieldsPreserved`, including `sigActions` and
     `∀ a, sf.mem.perm a = s0.mem.perm a`) via `ProofLib.subroutine_ok_lift_pureWords_process`, so
     card `b` can establish pointwise `VmPreserved` through `activeRealRun_stdStatePreserved`.
2. **Contiguous 65-word (`260` B) `pureWordsProg` hull & `slice_index_fail` reachability (F2):**
   - `P_sub := pureWordsProg base coreMemrchrWords` (`65` relocation-free words = `260` B,
     `[base, base + 0x104)`) has `externAt? pc = none` (`MemsetCode.pureWordsProg_externAt_none`),
     requiring zero stub externs and no K4 relaxation.
   - `keepR ⊇ [base, base + 260)` is sufficient and the 2 panic blocks at `+0x104` / `+0x118`
     (`bl slice_index_fail` in the 74-word / 296 B `coreMultiLib` block `2`) can stay outside
     `keepR` (or inside a larger `.text.lib2` `keepR`), because under `masterMemrchrSpec.pre`
     (`bs.length < 2 ^ 64`) both bounds-check branches into `+0x104` / `+0x118` are untaken and
     those panic blocks are never fetched.
3. **W-free fallback soundness (`hookMemrchr_masterMemrchr_ok`, F3) and consumer `HookOk` lifts:**
   - `memrchrHook` has no `W : CliHooks` parameter and satisfies `masterMemrchrSpec` unconditionally.
   - Consumer `HookOk` lifts cover `MainHops.memrchrSpec stk`, `Memrchr.cliMemrchrSpec stk`,
     `CliExt.memrchrSpec`, `CalleesRO.memrchrSpecRO stk`, and their `keepsFs` / `withVmPreserved` /
     `memrchrSpecK` wrappers for `16 ≤ stk ∧ stk ≤ 2 ^ 64` only. Callers with `stk < 16` do **not**
     lift (the ghost returns `.Exception` when the 16 B stack precondition fails; those callers are
     narrowed to `16 ≤ stk` in `*Sat` siblings).
4. **Scope & trust boundary (F4):**
   - There is no trusted placed-lib entry in C2; matching `coreMemrchrWords` against the C2 stock
     ELF image belongs to untrusted card `a2` (inside C2) together with `K3`.
-/

set_option autoImplicit false

public section

namespace LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode

open Arm64 ProofLib SepProp
open Arm64.Process (pureWordsProg pureWordsProg_hasWords)
open ProofLib.StdStartup (StdStatePreserved)
open VerifiedLibraries.Musl (memcpySrc)
open VerifiedLibraries.RustStd (
  lastIndexOf NoMatchFrom noMatchFrom_self noMatchFrom_step_one noMatchFrom_step_one_sub
  noMatchFrom_step_chunk16 memrchrLastIdx_eq_none memrchrLastIdx_eq_some_of_hit
  memrchrRepeatByte64 lowByte_mov_and_ff memrchrSwarBics_eq_zero_iff
  memrchrHeadBV memrchrHeadBV_lt8 memrchrHeadBV_eq_ofNat
  sub32_zext64_and15_eq ofNat_sub_and15_eq_mod16 memrchr_split_of_ge
  memrchr_prefix_check_false memrchr_loop1_ptr_eq memrchr_loop1_hit_idx
  memrchr_loop2_ptr_eq memrchr_loop3_ptr_eq pointsToBytes_focus16_words
)
open CryptoVerification.LibsignalTripleRatchet (extHookStack)
open CryptoVerification.SignalSession (memrchrHook)
open CryptoVerification.SignalSession.Cli.MainHops (MemrchrCall memrchrIdx)
open LibsignalBinary.Heap (VmPreserved)
open LibsignalBinary.Heap.SpecBudget (withVmPreserved)
open LibsignalBinary.Proofs.HookDischarge.Libc.Common (keepsFs)
open LibsignalBinary.Proofs.HookDischarge.RustStd.Memrchr (cliMemrchrSpec cliMemrchrSpec_extHookStack)
open LibsignalBinary.Proofs.HookDischarge.RustStd.MemrchrRO (
  coreMemrchrWords lastIndexOf_eq_memrchrIdx coreMemrchr_memrchrSpecRO_ok
)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer (SpecStripSInvariant)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemsetCode (
  MemsetStatePreserved memsetSpecK pureWordsProg_externAt_none
  hookOk_memsetSpecK_of_plain memsetSpecK_keepsFs memsetSpecK_withVmPreserved
  memsetSpecK_withOomPoolPreserved
)
open LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemcpyCode (
  hookOk_map_frame_pureAbort hookOk_memcpySpecK_map_frame_pureAbort
)
open LibsignalBinary.Proofs.SignalSession.Cli.M24.CalleesRO (memrchrSpecRO)
open LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFsBudget (hookOk_withVmPreserved)

/-! ## 1. Master & Process `memrchr` Specifications (`F1`, `F4`) -/

/-- Non-memory process/VM state fields preserved across real `memrchr` and `memrchrHook`
    (reusing `MemsetCode.MemsetStatePreserved` per `F5`). -/
abbrev MemrchrStatePreserved : State → State → Prop := MemsetStatePreserved

theorem MemrchrStatePreserved.refl (s : State) : MemrchrStatePreserved s s :=
  MemsetStatePreserved.refl s

theorem MemrchrStatePreserved.of_stdStatePreserved {s0 sf : State}
    (h : StdStatePreserved s0 sf) : MemrchrStatePreserved s0 sf :=
  MemsetStatePreserved.of_stdStatePreserved h

/-- Unified `(ro : Bool)`-indexed master separation-logic contract for
    `core::slice::memchr::memrchr(c, p, len)` (THE master spec used by the ghost hook):
    owns `memcpySrc ro p bs` (`p ↦ₛ bs` when `ro = false`, `p ↦ᵣ bs` when `ro = true`) and a 16 B
    stack frame `stackFrameAt s0.sp 16`, returns `Option<usize>` via `RustAbi.optionU64` matching
    `(lastIndexOf c bs).map (BitVec.ofNat 64)`, preserves `MemrchrStatePreserved`, and has
    unreachable panic/exit/OOM branches (`⌜False⌝`). -/
@[expose] def masterMemrchrSpec :
    Spec (Bool × BitVec 8 × BitVec 64 × List (BitVec 8)) where
  pre := fun (ro, c, p, bs) s0 =>
    ⌜(s0.readReg64 .x0).setWidth 8 = c ∧
      s0.readReg64 .x1 = p ∧
      s0.readReg64 .x2 = BitVec.ofNat 64 bs.length ∧
      bs.length < 2 ^ 64⌝ ∗
      memcpySrc ro p bs ∗
      stackFrameAt s0.sp 16
  post := fun (ro, c, p, bs) s0 sf =>
    ⌜RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64)) ∧
      MemrchrStatePreserved s0 sf⌝ ∗
      memcpySrc ro p bs ∗
      stackFrameAt s0.sp 16
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Read-write (`ro = false`, `p ↦ₛ bs`) projection of `masterMemrchrSpec` matching the engine
    `CoreMemrchr` spatial frame (`p ↦ₛ bs ∗ stackFrameAt s0.sp 16`). -/
@[expose] def masterMemrchrSpecRW :
    Spec (BitVec 8 × BitVec 64 × List (BitVec 8)) where
  pre := fun (c, p, bs) s0 => masterMemrchrSpec.pre (false, c, p, bs) s0
  post := fun (c, p, bs) s0 sf => masterMemrchrSpec.post (false, c, p, bs) s0 sf
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Read-only (`ro = true`, `p ↦ᵣ bs`) projection of `masterMemrchrSpec`. -/
@[expose] def masterMemrchrSpecRO :
    Spec (BitVec 8 × BitVec 64 × List (BitVec 8)) where
  pre := fun (c, p, bs) s0 => masterMemrchrSpec.pre (true, c, p, bs) s0
  post := fun (c, p, bs) s0 sf => masterMemrchrSpec.post (true, c, p, bs) s0 sf
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Process-level `(ro : Bool)` specification for `memrchr` (`F1`), carrying full
    `StdStatePreserved s0 sf` (`ProcessFieldsPreserved`, including `sigActions` and
    `∀ a, sf.mem.perm a = s0.mem.perm a`) with the exact same precondition as `masterMemrchrSpec`. -/
@[expose] def stdMemrchrSpec :
    Spec (Bool × BitVec 8 × BitVec 64 × List (BitVec 8)) where
  pre := masterMemrchrSpec.pre
  post := fun (ro, c, p, bs) s0 sf =>
    ⌜RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64)) ∧
      StdStatePreserved s0 sf⌝ ∗
      memcpySrc ro p bs ∗
      stackFrameAt s0.sp 16
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Read-write (`ro = false`) projection of `stdMemrchrSpec`. -/
@[expose] def stdMemrchrSpecRW :
    Spec (BitVec 8 × BitVec 64 × List (BitVec 8)) where
  pre := fun (c, p, bs) s0 => stdMemrchrSpec.pre (false, c, p, bs) s0
  post := fun (c, p, bs) s0 sf => stdMemrchrSpec.post (false, c, p, bs) s0 sf
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- Read-only (`ro = true`) projection of `stdMemrchrSpec`. -/
@[expose] def stdMemrchrSpecRO :
    Spec (BitVec 8 × BitVec 64 × List (BitVec 8)) where
  pre := fun (c, p, bs) s0 => stdMemrchrSpec.pre (true, c, p, bs) s0
  post := fun (c, p, bs) s0 sf => stdMemrchrSpec.post (true, c, p, bs) s0 sf
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

/-- `K`-route precondition narrowing (`⌜keep (s.readReg64 .lr) = false⌝ ∗ spec.pre x s`), reusing
    `MemsetCode.memsetSpecK` (`F5`). -/
abbrev memrchrSpecK : (BitVec 64 → Bool) → {α : Type} → Spec α → Spec α := @memsetSpecK

/-- `stdMemrchrSpec.pre` is definitionally `masterMemrchrSpec.pre`. -/
theorem stdMemrchr_pre_eq_masterMemrchr_pre :
    stdMemrchrSpec.pre = masterMemrchrSpec.pre := rfl

/-- Equivalence helper converting `masterMemrchrSpec.pre` to `stdMemrchrSpec.pre` on any frame `R`. -/
theorem stdMemrchr_pre_of_masterMemrchr_pre
    {x : Bool × BitVec 8 × BitVec 64 × List (BitVec 8)} {R : SepProp} {s0 : State}
    (hp : s0.mem ⊨ masterMemrchrSpec.pre x s0 ∗ R) :
    s0.mem ⊨ stdMemrchrSpec.pre x s0 ∗ R := hp

/-- `masterMemrchrSpec` is `stripS`-invariant for arbitrary `keep` (`F4`). -/
theorem specStripSInvariant_masterMemrchr (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep masterMemrchrSpec where
  pre_eq := fun ⟨_, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

/-- `memrchrSpecK keep masterMemrchrSpec` is `stripS`-invariant for arbitrary `keep` (`F4`). -/
theorem specStripSInvariant_masterMemrchrK (keep : BitVec 64 → Bool) :
    SpecStripSInvariant keep (memrchrSpecK keep masterMemrchrSpec) where
  pre_eq := fun ⟨_, _, _, _⟩ s => by cases s; rfl
  post_eq := fun ⟨_, _, _, _⟩ s0 sf => by cases s0; cases sf; rfl
  onPanic_eq := fun _ _ _ => rfl
  onExit_eq := fun _ _ _ _ => rfl
  onOom_eq := fun _ _ _ => rfl

/-! ## 2. `pureWordsProg` (`260` B Hull) & Region-Local `subroutine_ok` (`F1`, `F2`) -/

/-- `coreMemrchrWords` has `65` instruction words (`260` B). -/
theorem coreMemrchrWords_length : coreMemrchrWords.length = 65 := rfl

private theorem ofWords_memrchr_readWordOff_all :
    ((List.range coreMemrchrWords.length).all fun i =>
      (Program.ofWords 0#64 coreMemrchrWords).readWordOff (4 * i) == coreMemrchrWords[i]?) = true := by
  decide +kernel

private theorem readWordOff_eq_of_code_eq {P Q : Program} (h : P.code = Q.code) (off : Nat) :
    P.readWordOff off = Q.readWordOff off := by
  unfold Program.readWordOff
  rw [h]

/-- Concrete `hasWords` instance (`F2`): `pureWordsProg base coreMemrchrWords` holds the 65-word
    (`260` B) relocation-free `memrchr` hull at `base` for every `base : BitVec 64`. -/
theorem pureWordsProg_memrchr_hasWords (base : BitVec 64) :
    (pureWordsProg base coreMemrchrWords).hasWords base coreMemrchrWords := by
  refine pureWordsProg_hasWords (by decide) ?_
  have hcode : (pureWordsProg base coreMemrchrWords).code =
      (Program.ofWords 0#64 coreMemrchrWords).code := rfl
  simp only [readWordOff_eq_of_code_eq hcode]
  exact ofWords_memrchr_readWordOff_all

/-- None of the 65 words in `coreMemrchrWords` is `SVC` or `MSR TPIDR_EL0`. -/
theorem pureWordsProg_memrchr_allInstrs_noSvc_noTpidr (base : BitVec 64) :
    (pureWordsProg base coreMemrchrWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) = true := by
  have h : (pureWordsProg base coreMemrchrWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) =
      (pureWordsProg 0#64 coreMemrchrWords).allInstrs (fun i => !i.isSvc && !i.isMsrTpidrEl0) := by
    unfold Program.allInstrs pureWordsProg Program.ofWords Program.allWords
    rfl
  rw [h]
  decide +kernel

/-- Auxiliary base spec on `pureWordsProg` before `subroutine_ok_lift_pureWords_process` attaches
    full `ProcessFieldsPreserved`. -/
private def memrchrBaseSpec :
    Spec (Bool × BitVec 8 × BitVec 64 × List (BitVec 8)) where
  pre := masterMemrchrSpec.pre
  post := fun (ro, c, p, bs) s0 sf =>
    ⌜RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64))⌝ ∗
      memcpySrc ro p bs ∗
      stackFrameAt s0.sp 16
  onPanic := fun _ _ _ => ⌜False⌝
  onExit := fun _ _ _ _ => ⌜False⌝
  onOom := fun _ _ _ => ⌜False⌝

private theorem memrchrMatch_to_optionU64 {c : BitVec 8} {bs : List (BitVec 8)} {sf : State}
    (hm : match memrchrIdx c bs with
      | some i => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 i
      | none => sf.readReg64 .x0 = 0#64) :
    RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64)) := by
  rw [lastIndexOf_eq_memrchrIdx]
  cases hidx : memrchrIdx c bs with
  | none => simpa [hidx, RustAbi.optionU64] using hm
  | some i => simpa [hidx, RustAbi.optionU64] using hm

section
arm64_proof_prelude

private def CmSavedGprs (s0 s1 : State) : Prop :=
  s1.readReg64 .x19 = s0.readReg64 .x19 ∧ s1.readReg64 .x20 = s0.readReg64 .x20 ∧
  s1.readReg64 .x21 = s0.readReg64 .x21 ∧ s1.readReg64 .x22 = s0.readReg64 .x22 ∧
  s1.readReg64 .x23 = s0.readReg64 .x23 ∧ s1.readReg64 .x24 = s0.readReg64 .x24 ∧
  s1.readReg64 .x25 = s0.readReg64 .x25 ∧ s1.readReg64 .x26 = s0.readReg64 .x26 ∧
  s1.readReg64 .x27 = s0.readReg64 .x27 ∧ s1.readReg64 .x28 = s0.readReg64 .x28

private theorem CmSavedGprs.trans {s0 s1 s2 : State}
    (a : CmSavedGprs s0 s1) (b : CmSavedGprs s1 s2) : CmSavedGprs s0 s2 :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.1.trans a.2.2.2.1,
   b.2.2.2.2.1.trans a.2.2.2.2.1, b.2.2.2.2.2.1.trans a.2.2.2.2.2.1,
   b.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.1,
   b.2.2.2.2.2.2.2.2.1.trans a.2.2.2.2.2.2.2.2.1, b.2.2.2.2.2.2.2.2.2.trans a.2.2.2.2.2.2.2.2.2⟩

private structure CmBodyPreserved (s_entry s : State) (sp0 : BitVec 64) : Prop where
  running : s.status = .Running
  sp_eq : s.sp = sp0 - 16#64
  sp_al : s.spAligned = true
  gprs : CmSavedGprs s_entry s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s_entry

private structure CmExitState (s_entry sf : State) (sp0 fp0 lr0 : BitVec 64)
    (c : BitVec 8) (bs : List (BitVec 8)) : Prop where
  pc_eq : sf.pc = lr0
  running : sf.status = .Running
  sp_eq : sf.sp = sp0
  fp_eq : sf.readReg64 .fp = fp0
  lr_eq : sf.readReg64 .lr = lr0
  gprs : CmSavedGprs s_entry sf
  vregs : calleeSavedVRegs sf = calleeSavedVRegs s_entry
  ret_ok : RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64))

private abbrev cmFrameRW (p sp0 fp0 lr0 : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  (p ↦ₛ bs) ∗ ((sp0 - 16#64) ↦₆₄ fp0) ∗ ((sp0 - 8#64) ↦₆₄ lr0)

private theorem stackFrameAt16_eq_pair (sp0 : BitVec 64) :
    stackFrameAt sp0 16 =
      ∃∗ st0, ∃∗ st1, ((sp0 - 16#64) ↦₆₄ st0) ∗ ((sp0 - 8#64) ↦₆₄ st1) := by
  rw [← stackAt_eq_stackFrameAt sp0 16, stackAt_eq_cells sp0 2]
  dsimp only [cells]
  simp only [Nat.reduceMul, sepConj_emp, sepExists_sepConj_right, bv_lin_norm]

private theorem byte_cmp32_of_eq {x y : BitVec 8} (h : x = y) :
    (BitVec.setWidth 32 x == BitVec.setWidth 32 y) = true ∧
    (BitVec.setWidth 32 x != BitVec.setWidth 32 y) = false := by
  subst h; simp

private theorem byte_cmp32_of_ne {x y : BitVec 8} (h : x ≠ y) :
    (BitVec.setWidth 32 x == BitVec.setWidth 32 y) = false ∧
    (BitVec.setWidth 32 x != BitVec.setWidth 32 y) = true := by
  have hne32 : BitVec.setWidth 32 x ≠ BitVec.setWidth 32 y := fun heq =>
    h (by simpa using congrArg (BitVec.setWidth 8) heq)
  exact ⟨beq_false_of_ne hne32, bne_iff_ne.mpr hne32⟩

private theorem cmLoop3RW {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords) {s_entry : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)}
    {post : State → SepProp → Prop} (hn : bs.length < 2 ^ 64)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRW p sp0 fp0 lr0 bs)) :
    ∀ (cur : Nat) (s : State), cur ≤ bs.length → s.pc = fnBase + 216#64 →
      CmBodyPreserved s_entry s sp0 →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 cur →
      s.readReg64 (.gpr 10#5) = p - 1#64 → s.readReg64 .x0 = 1#64 →
      s.readReg64 (.gpr 9#5) = c.zeroExtend 64 → NoMatchFrom c bs cur →
      SepWP prog lr0 s (cmFrameRW p sp0 fp0 lr0 bs) post
  | 0, s, _hcur, hpc, hpres, hx8, _hx10, _hx0, _hx9, hnomatch => by
    have hnone : lastIndexOf c bs = none := memrchrLastIdx_eq_none hnomatch
    have hrun := hpres.running; have hsp := hpres.sp_eq; have hsp_al := hpres.sp_al
    have hsp0_al : (sp0 &&& 15#64 == 0#64) = true :=
      beq_iff_eq.mpr (by simpa [arm64_norm] using (show (sp0 - 16#64) &&& 15#64 = 0#64 by
        simpa [State.spAligned, hsp] using hsp_al))
    wp_conv_pre => rw [cmFrameRW]
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact hpost _ ⟨rfl, by simpa [arm64_norm] using hrun, by simp [arm64_norm],
      by simp [arm64_norm], by simp [arm64_norm],
      CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
      (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
      by simp [hnone, RustAbi.optionU64, arm64_norm]⟩
  | idx + 1, s, hcur, hpc, hpres, hx8, hx10, hx0, hx9, hnomatch => by
    have hidx : idx < bs.length := by omega
    have hbeq0 : (BitVec.ofNat 64 (idx + 1) == 0#64) = false := beq_false_of_ne (by bv_omega)
    obtain ⟨hptr, hsub1⟩ := memrchr_loop3_ptr_eq p idx
    have hrun := hpres.running; have hsp := hpres.sp_eq; have hsp_al := hpres.sp_al
    by_cases hbc : bs.getD idx 0#8 = c
    · have hsome : lastIndexOf c bs = some idx := memrchrLastIdx_eq_some_of_hit hidx hbc hnomatch
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_eq hbc
      have hsp0_al : (sp0 &&& 15#64 == 0#64) = true :=
        beq_iff_eq.mpr (by simpa [arm64_norm] using (show (sp0 - 16#64) &&& 15#64 = 0#64 by
          simpa [State.spAligned, hsp] using hsp_al))
      wp_conv_pre => rw [cmFrameRW, pointsToBytes_focus8 p bs idx hidx, ← hptr, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      conv => arg 2; rw [hptr, ← sepConj_assoc, ← pointsToBytes_focus8 p bs idx hidx]
      exact hpost _ ⟨rfl, by simpa [arm64_norm] using hrun, by simp [arm64_norm],
        by simp [arm64_norm], by simp [arm64_norm],
        CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
        (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
        by simp [hsome, RustAbi.optionU64, arm64_norm, hx0]⟩
    · have hnomatch' : NoMatchFrom c bs idx := noMatchFrom_step_one hidx hbc hnomatch
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_ne hbc
      apply SepWP.cut (mid := fnBase + 216#64)
      wp_conv_pre => rw [cmFrameRW, pointsToBytes_focus8 p bs idx hidx, ← hptr, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [hptr, ← sepConj_assoc, ← pointsToBytes_focus8 p bs idx hidx]
      exact cmLoop3RW hc hn hpost idx _ (by omega) rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
        (by simp [arm64_norm]) (by simp [arm64_norm, hx10]) (by simp [arm64_norm, hx0])
        (by simp [arm64_norm, hx9]) hnomatch'

private theorem cmAfterLoop2RW {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords) {s_entry s : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)} {cur : Nat}
    {post : State → SepProp → Prop} (hn : bs.length < 2 ^ 64)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRW p sp0 fp0 lr0 bs))
    (hcur : cur ≤ bs.length) (hpc : s.pc = fnBase + 200#64)
    (hpres : CmBodyPreserved s_entry s sp0)
    (hx8 : s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 cur) (hx1 : s.readReg64 .x1 = p)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hx9 : s.readReg64 (.gpr 9#5) = c.zeroExtend 64) (hnomatch : NoMatchFrom c bs cur) :
    SepWP prog lr0 s (cmFrameRW p sp0 fp0 lr0 bs) post := by
  obtain ⟨hhi_false, hule_true⟩ := memrchr_prefix_check_false hcur hn
  have hrun := hpres.running; have hsp := hpres.sp_eq; have hsp_al := hpres.sp_al
  apply SepWP.cut (mid := fnBase + 216#64)
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  exact cmLoop3RW hc hn hpost cur _ hcur rfl
    ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
     by simpa [arm64_norm] using hsp_al,
     CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
     (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
    (by simp [arm64_norm, hx8]) (by simp [arm64_norm]) (by simp [arm64_norm])
    (by simp [arm64_norm, hx9]) hnomatch

private theorem cmLoop2RW {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords) {s_entry : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)} {lo : Nat}
    {post : State → SepProp → Prop} (hn : bs.length < 2 ^ 64)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRW p sp0 fp0 lr0 bs)) :
    ∀ (q : Nat) (s : State), lo + 16 * q ≤ bs.length → s.pc = fnBase + 140#64 →
      CmBodyPreserved s_entry s sp0 →
      s.readReg64 .x0 = BitVec.ofNat 64 (lo + 16 * q) →
      s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 lo →
      s.readReg64 .x1 = p → s.readReg64 .x2 = BitVec.ofNat 64 bs.length →
      s.readReg64 (.gpr 9#5) = c.zeroExtend 64 →
      s.readReg64 (.gpr 11#5) = memrchrRepeatByte64 c →
      s.readReg64 (.gpr 12#5) = 72340172838076672#64 →
      s.readReg64 (.gpr 13#5) = 9259542123273814144#64 →
      NoMatchFrom c bs (lo + 16 * q) →
      SepWP prog lr0 s (cmFrameRW p sp0 fp0 lr0 bs) post
  | 0, s, hcur, hpc, hpres, hx0, hx10, hx1, hx2, hx9, _hx11, _hx12, _hx13, hnomatch => by
    simp only [Nat.mul_zero, Nat.add_zero] at hcur hx0 hnomatch
    have hrun := hpres.running; have hsp := hpres.sp_eq; have hsp_al := hpres.sp_al
    apply SepWP.cut (mid := fnBase + 200#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact cmAfterLoop2RW hc hn hpost hcur rfl
      ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
       by simpa [arm64_norm] using hsp_al,
       CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
       (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
      (by simp [arm64_norm]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hx2])
      (by simp [arm64_norm, hx9]) hnomatch
  | q' + 1, s, hcur, hpc, hpres, hx0, hx10, hx1, hx2, hx9, hx11, hx12, hx13, hnomatch => by
    let cur := lo + 16 * (q' + 1)
    have h16 : 16 ≤ cur := by dsimp [cur]; omega
    have hcur_lt : cur < 2 ^ 64 := by dsimp [cur] at *; omega
    have hcur_sub16 : cur - 16 = lo + 16 * q' := by dsimp [cur]; omega
    have hls_false : (BitVec.ofNat 64 cur).ule (BitVec.ofNat 64 lo) = false := by
      simp [BitVec.ule, BitVec.toNat_ofNat]; dsimp [cur]; omega
    have hgt_true : (BitVec.ofNat 64 lo).ult (BitVec.ofNat 64 cur) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; dsimp [cur]; omega
    obtain ⟨hptr16, hsub16⟩ := memrchr_loop2_ptr_eq p h16 hcur_lt
    obtain ⟨w0, w1, hchunk, hfocus⟩ := pointsToBytes_focus16_words p bs h16 hcur
    have hrun := hpres.running; have hsp := hpres.sp_eq; have hsp_al := hpres.sp_al
    let rep := memrchrRepeatByte64 c
    let u0 := w0 ^^^ rep; let u1 := w1 ^^^ rep
    let swarFlags :=
      9259542123273814144#64 &&&
        ~~~(((72340172838076672#64 - u0) ||| u0) &&& ((72340172838076672#64 - u1) ||| u1))
    by_cases hswar : swarFlags = 0#64
    · have hswar_beq : (swarFlags == 0#64) = true := beq_iff_eq.mpr hswar
      obtain ⟨hw0, hw1⟩ := (memrchrSwarBics_eq_zero_iff w0 w1 c).mp hswar
      have hnomatch' : NoMatchFrom c bs (lo + 16 * q') := by
        rw [← hcur_sub16]
        exact noMatchFrom_step_chunk16 h16 hcur hchunk hw0 hw1 hnomatch
      apply SepWP.cut (mid := fnBase + 140#64)
      wp_conv_pre => rw [cmFrameRW, hfocus, ← hptr16, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← sepConj_assoc, hptr16, ← hfocus]
      exact cmLoop2RW hc hn hpost q' _ (by omega) rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
        (by simp [arm64_norm, hsub16, hcur_sub16, cur]) (by simp [arm64_norm, hx10])
        (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hx2]) (by simp [arm64_norm, hx9])
        (by simp [arm64_norm, hx11]) (by simp [arm64_norm, hx12]) (by simp [arm64_norm, hx13])
        hnomatch'
    · have hswar_beq : (swarFlags == 0#64) = false := beq_false_of_ne hswar
      apply SepWP.cut (mid := fnBase + 200#64)
      wp_conv_pre => rw [cmFrameRW, hfocus, ← hptr16, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← sepConj_assoc, hptr16, ← hfocus]
      exact cmAfterLoop2RW hc hn hpost hcur rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
        (by simp [arm64_norm]) (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hx2])
        (by simp [arm64_norm, hx9]) hnomatch

private theorem cmLoop1RW {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords) {s_entry : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)} {lo mid q : Nat}
    {post : State → SepProp → Prop} (hn : bs.length < 2 ^ 64)
    (hmid_eq : mid = lo + 16 * q) (hmid_le : mid ≤ bs.length)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRW p sp0 fp0 lr0 bs)) :
    ∀ (rem k : Nat) (s : State), rem + k = bs.length - mid → s.pc = fnBase + 80#64 →
      CmBodyPreserved s_entry s sp0 →
      s.readReg64 (.gpr 8#5) = BitVec.ofNat 64 (bs.length - mid) →
      s.readReg64 (.gpr 11#5) = BitVec.ofNat 64 k →
      s.readReg64 (.gpr 12#5) = (p + BitVec.ofNat 64 bs.length - 1#64) - BitVec.ofNat 64 k →
      s.readReg64 (.gpr 9#5) = c.zeroExtend 64 → s.readReg64 .x0 = BitVec.ofNat 64 mid →
      s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 lo → s.readReg64 .x1 = p →
      s.readReg64 .x2 = BitVec.ofNat 64 bs.length → NoMatchFrom c bs (bs.length - k) →
      SepWP prog lr0 s (cmFrameRW p sp0 fp0 lr0 bs) post
  | 0, k, s, hrem, hpc, hpres, hx8, hx11, _hx12, hx9, hx0, hx10, hx1, hx2, hnomatch => by
    have hk_eq : k = bs.length - mid := by omega
    subst hk_eq
    have hsub_mid : bs.length - (bs.length - mid) = mid := by omega
    rw [hsub_mid] at hnomatch
    have hrun := hpres.running; have hsp := hpres.sp_eq; have hsp_al := hpres.sp_al
    apply SepWP.cut (mid := fnBase + 140#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
    exact cmLoop2RW hc hn hpost q _ (hmid_eq ▸ hmid_le) rfl
      ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
       by simpa [arm64_norm] using hsp_al,
       CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
       (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
      (by simp [arm64_norm, hx0, hmid_eq]) (by simp [arm64_norm, hx10]) (by simp [arm64_norm, hx1])
      (by simp [arm64_norm, hx2]) (by simp [arm64_norm, hx9])
      (by simp [arm64_norm, memrchrRepeatByte64]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (hmid_eq ▸ hnomatch)
  | rem' + 1, k, s, hrem, hpc, hpres, hx8, hx11, hx12, hx9, hx0, hx10, hx1, hx2, hnomatch => by
    have hk_lt_sub : k < bs.length - mid := by omega
    have hk_lt_n : k < bs.length := by omega
    let idx := bs.length - 1 - k
    have hidx : idx < bs.length := by dsimp [idx]; omega
    have hbeq_k : (BitVec.ofNat 64 (bs.length - mid) == BitVec.ofNat 64 k) = false :=
      beq_false_of_ne (by bv_omega)
    have hptr := memrchr_loop1_ptr_eq p hk_lt_n hn
    have hhit_idx := memrchr_loop1_hit_idx hk_lt_n hn
    rw [BitVec.ofNat_add] at hhit_idx
    have hrun := hpres.running; have hsp := hpres.sp_eq; have hsp_al := hpres.sp_al
    by_cases hbc : bs.getD idx 0#8 = c
    · have habove_idx : NoMatchFrom c bs (idx + 1) :=
        (show idx + 1 = bs.length - k by dsimp [idx]; omega) ▸ hnomatch
      have hsome : lastIndexOf c bs = some idx := memrchrLastIdx_eq_some_of_hit hidx hbc habove_idx
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_eq hbc
      rw [hptr] at hx12
      wp_conv_pre => rw [cmFrameRW, pointsToBytes_focus8 p bs idx hidx, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      conv => arg 2; rw [← sepConj_assoc, ← pointsToBytes_focus8 p bs idx hidx]
      exact hpost _ ⟨rfl, by simpa [arm64_norm] using hrun, by simp [arm64_norm],
        by simp [arm64_norm], by simp [arm64_norm],
        CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
        (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs,
        by simp [hsome, RustAbi.optionU64, arm64_norm, idx]⟩
    · have hnomatch' : NoMatchFrom c bs (bs.length - (k + 1)) :=
        noMatchFrom_step_one_sub hk_lt_n hbc hnomatch
      obtain ⟨hcmp_eq, hcmp_ne⟩ := byte_cmp32_of_ne hbc
      rw [hptr] at hx12
      apply SepWP.cut (mid := fnBase + 80#64)
      wp_conv_pre => rw [cmFrameRW, pointsToBytes_focus8 p bs idx hidx, sepConj_assoc]
      wp_sym_steps
      refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
      wp_conv_pre => rw [← sepConj_assoc, ← pointsToBytes_focus8 p bs idx hidx]
      exact cmLoop1RW hc hn hmid_eq hmid_le hpost rem' (k + 1) _ (by omega) rfl
        ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
         by simpa [arm64_norm] using hsp_al,
         CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
         (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
        (by simp [arm64_norm, hx8]) (by simp [arm64_norm, BitVec.ofNat_add])
        (by simp only [arm64_norm]; rw [← hptr, BitVec.ofNat_add]; bv_lin)
        (by simp [arm64_norm, hx9]) (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx10])
        (by simp [arm64_norm, hx1]) (by simp [arm64_norm, hx2]) hnomatch'

private theorem cmFromJoin3cRW {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords) {s_entry s : State}
    {sp0 fp0 lr0 p : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)} {lo mid q : Nat}
    {post : State → SepProp → Prop} (hn : bs.length < 2 ^ 64)
    (hmid_eq : mid = lo + 16 * q) (hmid_le : mid ≤ bs.length)
    (hpost : ∀ sf : State, CmExitState s_entry sf sp0 fp0 lr0 c bs →
      post sf (cmFrameRW p sp0 fp0 lr0 bs))
    (hpc : s.pc = fnBase + 60#64) (hpres : CmBodyPreserved s_entry s sp0)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 mid) (hx10 : s.readReg64 (.gpr 10#5) = BitVec.ofNat 64 lo)
    (hx1 : s.readReg64 .x1 = p) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hx8_low : BitVec.zeroExtend 64 (BitVec.setWidth 32 (s.readReg64 (.gpr 8#5)) &&& 255#32) = c.zeroExtend 64) :
    SepWP prog lr0 s (cmFrameRW p sp0 fp0 lr0 bs) post := by
  have hsub_n_mid : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 mid =
      BitVec.ofNat 64 (bs.length - mid) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  have hadd_p : BitVec.ofNat 64 bs.length + p - 1#64 =
      (p + BitVec.ofNat 64 bs.length - 1#64) - BitVec.ofNat 64 0 := by bv_lin
  have hrun := hpres.running; have hsp := hpres.sp_eq; have hsp_al := hpres.sp_al
  apply SepWP.cut (mid := fnBase + 80#64)
  wp_sym_steps
  refine SepWP.done rfl (by simpa [arm64_norm] using hrun) ?_
  exact cmLoop1RW hc hn hmid_eq hmid_le hpost (bs.length - mid) 0 _ (by omega) rfl
    ⟨by simpa [arm64_norm] using hrun, by simpa [arm64_norm] using hsp,
     by simpa [arm64_norm] using hsp_al,
     CmSavedGprs.trans hpres.gprs (by simp [CmSavedGprs, arm64_norm]),
     (by simp [calleeSavedVRegs, arm64_norm] : calleeSavedVRegs _ = calleeSavedVRegs s).trans hpres.vregs⟩
    (by simp only [arm64_norm]; rw [← hmid_eq]; exact hsub_n_mid)
    (by simp [arm64_norm]) (by simp [arm64_norm, hadd_p]) (by simp [arm64_norm, hx8_low])
    (by simp [arm64_norm, hx0]) (by simp [arm64_norm, hx10]) (by simp [arm64_norm, hx1])
    (by simp [arm64_norm, hx2]) (by simpa using noMatchFrom_self c bs)

private theorem coreMemrchrRW_sepWP {prog : Program} {fnBase : BitVec 64}
    (hc : prog.hasCode fnBase coreMemrchrWords)
    {s1 : State} {p st0 st1 : BitVec 64} {c : BitVec 8} {bs : List (BitVec 8)}
    {post : State → SepProp → Prop} (hn : bs.length < 2 ^ 64)
    (hpc1 : s1.pc = fnBase) (hrun1 : s1.status = .Running) (hsp1 : s1.spAligned = true)
    (hc_low : (s1.readReg64 .x0).setWidth 8 = c) (hx1_1 : s1.readReg64 .x1 = p)
    (hx2_1 : s1.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hpost : ∀ sf : State,
      CmExitState s1 sf s1.sp (s1.readReg64 .fp) (s1.readReg64 .lr) c bs →
      post sf (cmFrameRW p s1.sp (s1.readReg64 .fp) (s1.readReg64 .lr) bs)) :
    SepWP prog (s1.readReg64 .lr) s1
      ((p ↦ₛ bs) ∗ ((s1.sp - 16#64) ↦₆₄ st0) ∗ ((s1.sp - 8#64) ↦₆₄ st1)) post := by
  let head := (memrchrHeadBV p).toNat
  have hhead_lt8 : head < 8 := memrchrHeadBV_lt8 p
  have hhead_bv : memrchrHeadBV p = BitVec.ofNat 64 head := memrchrHeadBV_eq_ofNat p
  by_cases hlt : bs.length < head
  · have hult_true : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 head) = true := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    apply SepWP.cut (mid := fnBase + 60#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun1) ?_
    exact cmFromJoin3cRW hc (s_entry := s1) (lo := bs.length) (mid := bs.length) (q := 0)
      hn (by omega) (by omega) hpost rfl
      ⟨by simpa [arm64_norm] using hrun1, by simp [arm64_norm], by simpa [arm64_norm] using hsp1,
       by simp [CmSavedGprs, arm64_norm], by simp [calleeSavedVRegs, arm64_norm]⟩
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm, hx1_1])
      (by simp [arm64_norm, hx2_1])
      (by simpa [arm64_norm, hc_low] using lowByte_mov_and_ff (s1.readReg64 .x0))
  · have hge : head ≤ bs.length := by omega
    have hult_false : (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 head) = false := by
      simp [BitVec.ult, BitVec.toNat_ofNat]; omega
    have hand15 :
        BitVec.zeroExtend 64 ((BitVec.ofNat 64 bs.length).setWidth 32 - (BitVec.ofNat 64 head).setWidth 32) &&& 15#64 =
          BitVec.ofNat 64 ((bs.length - head) % 16) := by
      rw [sub32_zext64_and15_eq, ofNat_sub_and15_eq_mod16 hge hn]
    obtain ⟨_htl_le, htl_ult_false, hmid_bv, hmid_eq, hmid_le⟩ := memrchr_split_of_ge hge hn
    apply SepWP.cut (mid := fnBase + 60#64)
    wp_sym_steps
    refine SepWP.done rfl (by simpa [arm64_norm] using hrun1) ?_
    exact cmFromJoin3cRW hc (s_entry := s1) (lo := head) (mid := bs.length - (bs.length - head) % 16)
      (q := (bs.length - head) / 16) hn hmid_eq hmid_le hpost rfl
      ⟨by simpa [arm64_norm] using hrun1, by simp [arm64_norm], by simpa [arm64_norm] using hsp1,
       by simp [CmSavedGprs, arm64_norm], by simp [calleeSavedVRegs, arm64_norm]⟩
      (by simp [arm64_norm, ← hmid_eq]) (by simp [arm64_norm]) (by simp [arm64_norm, hx1_1])
      (by simp [arm64_norm, hx2_1])
      (by simpa [arm64_norm, hc_low] using lowByte_mov_and_ff (s1.readReg64 .x0))

private theorem coreMemrchrRW_base_ok {prog : Program} {entry : BitVec 64}
    (hc : prog.hasWords entry coreMemrchrWords) :
    subroutine_ok prog entry
      { pre := fun (c, p, bs) s => masterMemrchrSpec.pre (false, c, p, bs) s
        post := fun (c, p, bs) s0 sf => memrchrBaseSpec.post (false, c, p, bs) s0 sf
        onPanic := fun _ _ _ => ⌜False⌝
        onExit := fun _ _ _ _ => ⌜False⌝
        onOom := fun _ _ _ => ⌜False⌝ } := by
  apply subroutine_ok_of_sepWP_init
  rintro ⟨c, p, bs⟩ R s0 hpc hrun hpre hsp
  dsimp only [masterMemrchrSpec, memrchrBaseSpec, memcpySrc, cond] at hpre ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨⟨hx0, hx1, hx2, hn⟩, hpre⟩ := hpre
  rw [stackFrameAt16_eq_pair s0.sp] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨st0, st1, hpre⟩
  refine ⟨_, hpre, ?_⟩
  refine coreMemrchrRW_sepWP hc hn hpc hrun hsp hx0 hx1 hx2 ?_
  intro sf hexit
  have hcs : CalleeSavedPreserved s0 sf := by
    rw [CalleeSavedPreserved.iff_regs]
    exact ⟨hexit.gprs.1, hexit.gprs.2.1, hexit.gprs.2.2.1, hexit.gprs.2.2.2.1,
      hexit.gprs.2.2.2.2.1, hexit.gprs.2.2.2.2.2.1, hexit.gprs.2.2.2.2.2.2.1,
      hexit.gprs.2.2.2.2.2.2.2.1, hexit.gprs.2.2.2.2.2.2.2.2.1,
      hexit.gprs.2.2.2.2.2.2.2.2.2, hexit.fp_eq, hexit.vregs⟩
  refine ⟨fun hm_f => ?_, hexit.sp_eq, hcs⟩
  refine Satisfies.mono ?_ hm_f
  apply sepConj_mono_left
  dsimp only [cmFrameRW]
  rw [stackFrameAt16_eq_pair s0.sp]
  simp only [sepExists_sepConj_right]
  refine Entails.sepExists_right (s0.readReg64 .fp) <|
    Entails.sepExists_right (s0.readReg64 .lr) ?_
  rw [pure_sepConj_of_true hexit.ret_ok]
  sep_entail

end

/-- Base `subroutine_ok` for `memrchrBaseSpec` on any `prog` holding `coreMemrchrWords` at `entry`. -/
private theorem subroutine_ok_memrchrBase_of_hasWords {prog : Program} {entry : BitVec 64}
    (hc : prog.hasWords entry coreMemrchrWords) :
    subroutine_ok prog entry memrchrBaseSpec := by
  refine subroutine_ok_outcome_intro fun ⟨ro, c, p, bs⟩ R s0 hpc hrun hpre hsp => ?_
  cases ro
  · exact (coreMemrchrRW_base_ok hc).mono_outcome (c, p, bs) R s0 hpc hrun hpre hsp (fun _ h => h)
  · dsimp only [memrchrBaseSpec, masterMemrchrSpec] at hpre
    rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
    obtain ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩ := hpre
    have hstk_eq : stackFrameAt s0.sp 16 = stackAt s0.sp 16 :=
      (stackAt_eq_stackFrameAt s0.sp 16 (by decide)).symm
    dsimp only [memcpySrc, cond] at hmem
    rw [hstk_eq] at hmem
    have hpre_ro : s0.mem ⊨ (memrchrSpecRO 16).pre ⟨c, p, bs⟩ s0 ∗ R := by
      dsimp only [memrchrSpecRO]
      rw [sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
    refine (coreMemrchr_memrchrSpecRO_ok (stk := 16) (by decide) hc).mono_outcome
      ⟨c, p, bs⟩ R s0 hpc hrun hpre_ro hsp ?_
    rintro sf (⟨hret, hcc, hq⟩ | hpan | hex)
    · refine Or.inl ⟨hret, hcc, ?_⟩
      dsimp only [memrchrSpecRO] at hq
      rw [sepConj_assoc, satisfies_pure_sepConj] at hq
      obtain ⟨⟨_, _, hmatch⟩, hq_mem⟩ := hq
      dsimp only [memrchrBaseSpec, memcpySrc, cond]
      rw [hstk_eq, sepConj_assoc, satisfies_pure_sepConj]
      exact ⟨memrchrMatch_to_optionU64 hmatch, hq_mem⟩
    · exact Or.inr (Or.inl hpan)
    · exact Or.inr (Or.inr hex)

/-- Region-local `subroutine_ok` for `stdMemrchrSpec` (`F1`, full `StdStatePreserved` including
    `sigActions` and `mem.perm`) on any hook-free `P_sub` holding `coreMemrchrWords` at `entry`. -/
theorem subroutine_ok_stdMemrchr_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    subroutine_ok P_sub entry stdMemrchrSpec := by
  have hproc := ProofLib.subroutine_ok_lift_pureWords_process
    (subroutine_ok_memrchrBase_of_hasWords (pureWordsProg_memrchr_hasWords entry))
    (pureWordsProg_memrchr_allInstrs_noSvc_noTpidr entry)
    hwords hsub_no
    (h_pre_mem := fun ⟨_, _, _, _⟩ s _ => by cases s; rfl)
    (h_post_mem := fun ⟨_, _, _, _⟩ s0 sf _ _ => by cases s0; cases sf; rfl)
  refine subroutine_ok_mono hproc (fun _ _ _ hp => hp) (fun ⟨ro, c, p, bs⟩ R s0 sf hq => ?_)
  dsimp only [memrchrBaseSpec, stdMemrchrSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq
  obtain ⟨hstd, hq⟩ := hq
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1, hstd⟩, hq.2⟩

/-- Read-write (`ro = false`) region-local `subroutine_ok` for `stdMemrchrSpecRW`. -/
theorem subroutine_ok_stdMemrchrRW_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    subroutine_ok P_sub entry stdMemrchrSpecRW := by
  refine subroutine_ok_outcome_intro fun ⟨c, p, bs⟩ R s0 hpc hrun hpre hsp => ?_
  exact (subroutine_ok_stdMemrchr_of_hasWords hsub_no hwords).mono_outcome
    (false, c, p, bs) R s0 hpc hrun hpre hsp (fun _ h => h)

/-- Read-only (`ro = true`) region-local `subroutine_ok` for `stdMemrchrSpecRO`. -/
theorem subroutine_ok_stdMemrchrRO_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    subroutine_ok P_sub entry stdMemrchrSpecRO := by
  refine subroutine_ok_outcome_intro fun ⟨c, p, bs⟩ R s0 hpc hrun hpre hsp => ?_
  exact (subroutine_ok_stdMemrchr_of_hasWords hsub_no hwords).mono_outcome
    (true, c, p, bs) R s0 hpc hrun hpre hsp (fun _ h => h)

/-- Region-local `subroutine_ok` for `masterMemrchrSpec` on any hook-free `P_sub` holding
    `coreMemrchrWords` at `entry`. -/
theorem subroutine_ok_masterMemrchr_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    subroutine_ok P_sub entry masterMemrchrSpec := by
  refine subroutine_ok_mono (subroutine_ok_stdMemrchr_of_hasWords hsub_no hwords)
    (fun _ _ _ hp => hp)
    (fun ⟨_, _, _, _⟩ _ _ _ hq => ?_)
  dsimp only [stdMemrchrSpec, masterMemrchrSpec] at hq ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at hq ⊢
  exact ⟨⟨hq.1.1, MemrchrStatePreserved.of_stdStatePreserved hq.1.2⟩, hq.2⟩

/-- Read-write (`ro = false`) region-local `subroutine_ok` for `masterMemrchrSpecRW`. -/
theorem subroutine_ok_masterMemrchrRW_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    subroutine_ok P_sub entry masterMemrchrSpecRW := by
  refine subroutine_ok_outcome_intro fun ⟨c, p, bs⟩ R s0 hpc hrun hpre hsp => ?_
  exact (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords).mono_outcome
    (false, c, p, bs) R s0 hpc hrun hpre hsp (fun _ h => h)

/-- Read-only (`ro = true`) region-local `subroutine_ok` for `masterMemrchrSpecRO`. -/
theorem subroutine_ok_masterMemrchrRO_of_hasWords {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    subroutine_ok P_sub entry masterMemrchrSpecRO := by
  refine subroutine_ok_outcome_intro fun ⟨c, p, bs⟩ R s0 hpc hrun hpre hsp => ?_
  exact (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords).mono_outcome
    (true, c, p, bs) R s0 hpc hrun hpre hsp (fun _ h => h)

/-- Region-local `subroutine_ok` for `memrchrSpecK keep masterMemrchrSpec` on any hook-free `P_sub`
    holding `coreMemrchrWords`. -/
theorem subroutine_ok_masterMemrchrK_of_hasWords (keep : BitVec 64 → Bool)
    {P_sub : Program} {entry : BitVec 64}
    (hsub_no : ∀ pc, P_sub.externAt? pc = none)
    (hwords : P_sub.hasWords entry coreMemrchrWords) :
    subroutine_ok P_sub entry (memrchrSpecK keep masterMemrchrSpec) := by
  refine subroutine_ok_mono (subroutine_ok_masterMemrchr_of_hasWords hsub_no hwords)
    (fun _ _ _ hp => ?_) (fun _ _ _ _ hq => hq)
  dsimp only [memrchrSpecK, memsetSpecK] at hp
  rw [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.2

/-- Concrete `pureWordsProg` (`260` B hull) `subroutine_ok` for `stdMemrchrSpec` (`F1`, `F2`). -/
theorem pureWordsProg_stdMemrchr_ok (base : BitVec 64) :
    subroutine_ok (pureWordsProg base coreMemrchrWords) base stdMemrchrSpec :=
  subroutine_ok_stdMemrchr_of_hasWords
    (pureWordsProg_externAt_none base coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords base)

/-- Concrete `pureWordsProg` (`260` B hull) `subroutine_ok` for `masterMemrchrSpec` (`F2`). -/
theorem pureWordsProg_masterMemrchr_ok (base : BitVec 64) :
    subroutine_ok (pureWordsProg base coreMemrchrWords) base masterMemrchrSpec :=
  subroutine_ok_masterMemrchr_of_hasWords
    (pureWordsProg_externAt_none base coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords base)

/-- Concrete `pureWordsProg` (`260` B hull) `subroutine_ok` for `memrchrSpecK keep masterMemrchrSpec`. -/
theorem pureWordsProg_masterMemrchrK_ok (keep : BitVec 64 → Bool) (base : BitVec 64) :
    subroutine_ok (pureWordsProg base coreMemrchrWords) base
      (memrchrSpecK keep masterMemrchrSpec) :=
  subroutine_ok_masterMemrchrK_of_hasWords keep
    (pureWordsProg_externAt_none base coreMemrchrWords)
    (pureWordsProg_memrchr_hasWords base)

/-! ## 3. W-Free Fallback `memrchrHook` Soundness (`F3`) -/

/-- W-free fallback soundness (`F3`): trusted `memrchrHook` (which takes zero `W : CliHooks`
    parameters) satisfies `masterMemrchrSpec` for both `ro = false` (`↦ₛ`) and `ro = true` (`↦ᵣ`). -/
theorem hookMemrchr_masterMemrchr_ok : HookOk memrchrHook masterMemrchrSpec := by
  intro ⟨ro, c, p, bs⟩ R s0 hrun hpre _hsp
  dsimp only [masterMemrchrSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlt⟩, hmem⟩
  have hlen : (s0.readReg64 .x2).toNat = bs.length := by
    rw [hx2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  have hlen_le : bs.length ≤ 2 ^ 64 := Nat.le_of_lt hlt
  have hmem_ro : s0.mem ⊨ (p ↦ᵣ bs) ∗ (stackFrameAt s0.sp 16 ∗ R) := by
    rw [sepConj_assoc] at hmem
    cases ro
    · exact Satisfies.pointsToBytes_to_ro hmem
    · exact hmem
  have hrd : s0.mem.readBytes p bs.length = bs :=
    (IsBlockRO.pointsToBytesRO p bs hlen_le).read hmem_ro
  have hcan : s0.mem.canRead p bs.length = true :=
    (IsBlockRO.pointsToBytesRO p bs hlen_le).canRead hlen_le hmem_ro
  have hmemrchr :
      memrchrHook s0 =
        match memrchrIdx c bs with
        | some i => retHook (fun s => (s.writeReg64 .x0 1#64).writeReg64 .x1 (BitVec.ofNat 64 i)) s0
        | none => retHook (fun s => s.writeReg64 .x0 0#64) s0 := by
    unfold memrchrHook memrchrIdx
    simp only [hx0, hx1, hlen, hcan, hrd, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rfl
  rw [hmemrchr]
  cases hidx : memrchrIdx c bs with
  | some i =>
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [masterMemrchrSpec]
    rw [lastIndexOf_eq_memrchrIdx, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, hmem⟩
    simp only [hidx, Option.map_some, RustAbi.optionU64, retHook, arm64_norm]
  | none =>
    refine ⟨Memory.KeepsFrozen.refl s0.mem, rfl, Or.inl ⟨⟨rfl, rfl, hrun⟩,
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩⟩
    dsimp only [masterMemrchrSpec]
    rw [lastIndexOf_eq_memrchrIdx, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨?_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩, hmem⟩
    simp only [hidx, Option.map_none, RustAbi.optionU64, retHook, arm64_norm]

/-- Read-write (`ro = false`) corollary of `hookMemrchr_masterMemrchr_ok`. -/
theorem hookMemrchr_masterMemrchrRW_ok : HookOk memrchrHook masterMemrchrSpecRW :=
  fun ⟨c, p, bs⟩ R s0 hrun hpre hsp =>
    hookMemrchr_masterMemrchr_ok (false, c, p, bs) R s0 hrun hpre hsp

/-- Read-only (`ro = true`) corollary of `hookMemrchr_masterMemrchr_ok`. -/
theorem hookMemrchr_masterMemrchrRO_ok : HookOk memrchrHook masterMemrchrSpecRO :=
  fun ⟨c, p, bs⟩ R s0 hrun hpre hsp =>
    hookMemrchr_masterMemrchr_ok (true, c, p, bs) R s0 hrun hpre hsp

/-- `memrchrHook` satisfies `memrchrSpecK keep masterMemrchrSpec` for any `keep` (W-free, `F3`). -/
theorem hookMemrchr_masterMemrchrK_ok (keep : BitVec 64 → Bool) :
    HookOk memrchrHook (memrchrSpecK keep masterMemrchrSpec) :=
  hookOk_memsetSpecK_of_plain keep hookMemrchr_masterMemrchr_ok

/-! ## 4. Consumer `HookOk` Consequence Lifts (`16 ≤ stk ∧ stk ≤ 2 ^ 64`, `F1`, `F5`)

Note: callers with `stk < 16` do **not** lift from `masterMemrchrSpec` because real `memrchr`
pushes a 16 B frame (`stp x29, x30, [sp, #-16]!`) and the ghost hook transitions to `.Exception`
whenever `stackFrameAt s0.sp 16` fails; `*Sat` siblings narrow those callers to `16 ≤ stk`. -/

private theorem optionU64_to_memrchrMatch {c : BitVec 8} {bs : List (BitVec 8)} {sf : State}
    (hret : RustAbi.optionU64.holds sf ((lastIndexOf c bs).map (BitVec.ofNat 64))) :
    match memrchrIdx c bs with
    | some i => sf.readReg64 .x0 = 1#64 ∧ sf.readReg64 .x1 = BitVec.ofNat 64 i
    | none => sf.readReg64 .x0 = 0#64 := by
  rw [lastIndexOf_eq_memrchrIdx] at hret
  cases hidx : memrchrIdx c bs with
  | none => simpa [hidx, RustAbi.optionU64] using hret
  | some i => simpa [hidx, RustAbi.optionU64] using hret

private theorem stackAt_split_frame16 {sp : BitVec 64} {stk : Nat}
    (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    stackAt sp stk = (stackFrameAt sp 16 ∗ memRegion (sp - BitVec.ofNat 64 stk) (stk - 16)) := by
  rw [stackAt_shrink sp stk 16 hstk.1 hstk.2, stackAt_eq_stackFrameAt sp 16 (by decide), sepConj_comm]

/-- Lift `HookOk f masterMemrchrSpec` (`ro = false`) to `HookOk f (MainHops.memrchrSpec stk)`
    for `16 ≤ stk ∧ stk ≤ 2 ^ 64`. -/
theorem hookOk_mainHopsMemrchr_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk) := by
  refine hookOk_map_frame_pureAbort (fun x => (false, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec,
      masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk]
    sep_entail
  · dsimp only [masterMemrchrSpec,
      CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ => Entails.pure_right ?_ (by sep_entail)
    exact ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩

/-- `K`-narrowed lift from `memrchrSpecK keep masterMemrchrSpec` to
    `memrchrSpecK keep (MainHops.memrchrSpec stk)` (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem hookOk_mainHopsMemrchrK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec))
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (memrchrSpecK keep (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun x => (false, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ => ?_)
  · dsimp only [CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec,
      masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk]
    sep_entail
  · dsimp only [masterMemrchrSpec,
      CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ => Entails.pure_right ?_ (by sep_entail)
    exact ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩

/-- Specialization of `hookOk_mainHopsMemrchr_of_master` at `extHookStack` (`16384`). -/
theorem hookOk_mainHopsMemrchr_extHookStack_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) :
    HookOk f (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack) :=
  hookOk_mainHopsMemrchr_of_master hh (by decide)

/-- Specialization of `hookOk_mainHopsMemrchrK_of_master` at `extHookStack` (`16384`). -/
theorem hookOk_mainHopsMemrchrK_extHookStack_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec)) :
    HookOk f
      (memrchrSpecK keep (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack)) :=
  hookOk_mainHopsMemrchrK_of_master keep hh (by decide)

/-- `withVmPreserved` lift to `MainHops.memrchrSpec stk` (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem hookOk_mainHopsMemrchrVm_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk)) :=
  hookOk_withVmPreserved (hookOk_mainHopsMemrchr_of_master hh hstk) hvm

/-- `K`-narrowed `withVmPreserved` lift to `MainHops.memrchrSpec stk` (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem hookOk_mainHopsMemrchrVmK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (memrchrSpecK keep
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec stk))) := by
  dsimp only [memrchrSpecK]
  rw [← memsetSpecK_withVmPreserved]
  exact hookOk_withVmPreserved (hookOk_mainHopsMemrchrK_of_master keep hh hstk) hvm

/-- Specialization of `hookOk_mainHopsMemrchrVm_of_master` at `extHookStack` (`16384`). -/
theorem hookOk_mainHopsMemrchrVm_extHookStack_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f
      (withVmPreserved (CryptoVerification.SignalSession.Cli.MainHops.memrchrSpec extHookStack)) :=
  hookOk_mainHopsMemrchrVm_of_master hh hvm (by decide)

/-- Lift `HookOk f masterMemrchrSpec` (`ro = false`) to `HookOk f (Memrchr.cliMemrchrSpec stk)`
    for `16 ≤ stk ∧ stk ≤ 2 ^ 64`. -/
theorem hookOk_cliMemrchr_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (cliMemrchrSpec stk) := by
  refine hookOk_map_frame_pureAbort (fun x => (false, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ => ?_)
  · dsimp only [cliMemrchrSpec, masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk]
    sep_entail
  · dsimp only [masterMemrchrSpec, cliMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ => Entails.pure_right ?_ (by sep_entail)
    exact ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩

/-- `K`-narrowed lift to `Memrchr.cliMemrchrSpec stk` (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem hookOk_cliMemrchrK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec))
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (memrchrSpecK keep (cliMemrchrSpec stk)) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun x => (false, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ => ?_)
  · dsimp only [cliMemrchrSpec, masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk]
    sep_entail
  · dsimp only [masterMemrchrSpec, cliMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ => Entails.pure_right ?_ (by sep_entail)
    exact ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩

/-- `withVmPreserved` lift to `Memrchr.cliMemrchrSpec stk` (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem hookOk_cliMemrchrVm_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withVmPreserved (cliMemrchrSpec stk)) :=
  hookOk_withVmPreserved (hookOk_cliMemrchr_of_master hh hstk) hvm

/-- `K`-narrowed `withVmPreserved` lift to `Memrchr.cliMemrchrSpec stk` (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem hookOk_cliMemrchrVmK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (memrchrSpecK keep (withVmPreserved (cliMemrchrSpec stk))) := by
  dsimp only [memrchrSpecK]
  rw [← memsetSpecK_withVmPreserved]
  exact hookOk_withVmPreserved (hookOk_cliMemrchrK_of_master keep hh hstk) hvm

/-- Lift `HookOk f masterMemrchrSpec` to `HookOk f CliExt.memrchrSpec` (`stk = extHookStack`). -/
theorem hookOk_cliExtMemrchr_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) :
    HookOk f CryptoVerification.SignalSession.CliExt.memrchrSpec := by
  rw [← cliMemrchrSpec_extHookStack]
  exact hookOk_cliMemrchr_of_master hh (by decide)

/-- `K`-narrowed lift to `CliExt.memrchrSpec` (`stk = extHookStack`). -/
theorem hookOk_cliExtMemrchrK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec)) :
    HookOk f (memrchrSpecK keep CryptoVerification.SignalSession.CliExt.memrchrSpec) := by
  rw [← cliMemrchrSpec_extHookStack]
  exact hookOk_cliMemrchrK_of_master keep hh (by decide)

/-- `withVmPreserved` lift to `CliExt.memrchrSpec` (`stk = extHookStack`). -/
theorem hookOk_cliExtMemrchrVm_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec) :=
  hookOk_withVmPreserved (hookOk_cliExtMemrchr_of_master hh) hvm

/-- `K`-narrowed `withVmPreserved` lift to `CliExt.memrchrSpec`. -/
theorem hookOk_cliExtMemrchrVmK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec))
    (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f
      (memrchrSpecK keep (withVmPreserved CryptoVerification.SignalSession.CliExt.memrchrSpec)) := by
  dsimp only [memrchrSpecK]
  rw [← memsetSpecK_withVmPreserved]
  exact hookOk_withVmPreserved (hookOk_cliExtMemrchrK_of_master keep hh) hvm

/-- `HookDischarge.Libc.Common.keepsFs` lift to `CliExt.memrchrSpec`. -/
theorem hookOk_cliExtMemrchr_keepsFs_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) :
    HookOk f (keepsFs CryptoVerification.SignalSession.CliExt.memrchrSpec) := by
  refine hookOk_map_frame_pureAbort (fun x => (false, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 extHookStack) (extHookStack - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ => ?_)
  · dsimp only [keepsFs, CryptoVerification.SignalSession.CliExt.memrchrSpec,
      masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 (by decide : 16 ≤ extHookStack ∧ extHookStack ≤ 2 ^ 64)]
    sep_entail
  · dsimp only [masterMemrchrSpec, keepsFs,
      CryptoVerification.SignalSession.CliExt.memrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 (by decide : 16 ≤ extHookStack ∧ extHookStack ≤ 2 ^ 64),
      sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ =>
      Entails.pure_right hst.1 <|
        Entails.pure_right ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩ (by sep_entail)

/-- Lift `HookOk f masterMemrchrSpec` (`ro = true`) to `HookOk f (CalleesRO.memrchrSpecRO stk)`
    for `16 ≤ stk ∧ stk ≤ 2 ^ 64`. -/
theorem hookOk_memrchrRO_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (memrchrSpecRO stk) := by
  refine hookOk_map_frame_pureAbort (fun x => (true, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ => ?_)
  · dsimp only [memrchrSpecRO, masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk]
    sep_entail
  · dsimp only [masterMemrchrSpec, memrchrSpecRO, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ => Entails.pure_right ?_ (by sep_entail)
    exact ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩

/-- `K`-narrowed lift to `CalleesRO.memrchrSpecRO stk` (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem hookOk_memrchrROK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec))
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (memrchrSpecK keep (memrchrSpecRO stk)) := by
  refine hookOk_memcpySpecK_map_frame_pureAbort keep (fun x => (true, x.c, x.p, x.bs))
    (fun _ s0 => memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - 16)) hh
    (fun x s0 => ?_)
    (fun x s0 sf _ _ => ?_)
  · dsimp only [memrchrSpecRO, masterMemrchrSpec, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk]
    sep_entail
  · dsimp only [masterMemrchrSpec, memrchrSpecRO, memcpySrc, cond]
    rw [stackAt_split_frame16 hstk, sepConj_assoc, sepConj_assoc]
    refine Entails.pure_left fun ⟨hret, hst⟩ => Entails.pure_right ?_ (by sep_entail)
    exact ⟨hst.2.1, hst.1, optionU64_to_memrchrMatch hret⟩

/-- Specialization of `hookOk_memrchrRO_of_master` at `extHookStack` (`16384`). -/
theorem hookOk_memrchrRO_extHookStack_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) :
    HookOk f (memrchrSpecRO extHookStack) :=
  hookOk_memrchrRO_of_master hh (by decide)

/-- Specialization of `hookOk_memrchrROK_of_master` at `extHookStack` (`16384`). -/
theorem hookOk_memrchrROK_extHookStack_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec)) :
    HookOk f (memrchrSpecK keep (memrchrSpecRO extHookStack)) :=
  hookOk_memrchrROK_of_master keep hh (by decide)

/-- `withVmPreserved` lift to `CalleesRO.memrchrSpecRO stk` (`16 ≤ stk ∧ stk ≤ 2 ^ 64`), discharging
    the inner contract consumed by `AddressRoPlacedBudget.address_ro_blk580_ok` /
    `address_ro_placed_ok(_rocl)`. -/
theorem hookOk_memrchrROVm_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) (hvm : ∀ s : State, VmPreserved s (f s))
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (withVmPreserved (memrchrSpecRO stk)) :=
  hookOk_withVmPreserved (hookOk_memrchrRO_of_master hh hstk) hvm

/-- `K`-narrowed `withVmPreserved` lift to `CalleesRO.memrchrSpecRO stk` (`16 ≤ stk ∧ stk ≤ 2 ^ 64`). -/
theorem hookOk_memrchrROVmK_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec))
    (hvm : ∀ s : State, VmPreserved s (f s))
    {stk : Nat} (hstk : 16 ≤ stk ∧ stk ≤ 2 ^ 64) :
    HookOk f (memrchrSpecK keep (withVmPreserved (memrchrSpecRO stk))) := by
  dsimp only [memrchrSpecK]
  rw [← memsetSpecK_withVmPreserved]
  exact hookOk_withVmPreserved (hookOk_memrchrROK_of_master keep hh hstk) hvm

/-- Specialization of `hookOk_memrchrROVm_of_master` at `extHookStack` (`16384`), matching
    `AddressRoPlacedBudget`'s `withVmPreserved (memrchrSpecRO extHookStack)` token-for-token. -/
theorem hookOk_memrchrROVm_extHookStack_of_master {f : State → State}
    (hh : HookOk f masterMemrchrSpec) (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f (withVmPreserved (memrchrSpecRO extHookStack)) :=
  hookOk_memrchrROVm_of_master hh hvm (by decide)

/-- Specialization of `hookOk_memrchrROVmK_of_master` at `extHookStack` (`16384`). -/
theorem hookOk_memrchrROVmK_extHookStack_of_master (keep : BitVec 64 → Bool) {f : State → State}
    (hh : HookOk f (memrchrSpecK keep masterMemrchrSpec))
    (hvm : ∀ s : State, VmPreserved s (f s)) :
    HookOk f (memrchrSpecK keep (withVmPreserved (memrchrSpecRO extHookStack))) :=
  hookOk_memrchrROVmK_of_master keep hh hvm (by decide)

/-- Alias re-exporting `MemsetCode.hookOk_memsetSpecK_of_plain` (`F5`). -/
abbrev hookOk_memrchrSpecK_of_plain := @hookOk_memsetSpecK_of_plain

/-- Alias re-exporting `MemsetCode.memsetSpecK_keepsFs` (`F5`). -/
abbrev memrchrSpecK_keepsFs := @memsetSpecK_keepsFs

/-- Alias re-exporting `MemsetCode.memsetSpecK_withVmPreserved` (`F5`). -/
abbrev memrchrSpecK_withVmPreserved := @memsetSpecK_withVmPreserved

/-- Alias re-exporting `MemsetCode.memsetSpecK_withOomPoolPreserved` (`F5`). -/
abbrev memrchrSpecK_withOomPoolPreserved := @memsetSpecK_withOomPoolPreserved

end LibsignalBinary.Proofs.SignalSession.Cli.HooksDehook.MemrchrCode
