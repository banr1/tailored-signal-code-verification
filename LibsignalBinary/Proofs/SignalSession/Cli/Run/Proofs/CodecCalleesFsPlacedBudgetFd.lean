/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Heap.Fine.SpecBudgetFine
public import LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase
import LibsignalBinary.Proofs.E2E.Run.NoSvcCommon
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import ProofLib.Hoare.LibcHooks
import Arm64.Trusted.Spec.RustRuntime

/-!
# Pure-`fs` Dischargers for `SignalMessage::try_from` (Block `85`) and `PreKeySignalMessage::try_from` (Block `111`)

Proves `sf.fs = s0.fs` on normal return (`tryFromPlacedSpecOkFs` and `pksmSlotSpecPlacedOkFs`) for
Blocks `85` and `111` on `lsProg_579 (cliGhostExterns g (cliExternsPlaced mmpl W))` at
`mallocngHookRustCliAllocBudget` from `CliGhostAllocHooks`.
-/

public section

set_option autoImplicit false
set_option linter.dupNamespace false

namespace LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd

open Arm64 ProofLib SepProp

/-! ## Section 1: Exact `Satisfies`-Preserving Execute-Bit Stripper (`stripCodecS`) -/

@[expose] def stripCodecPerm (inCode : Bool) (p : Perm) : Perm :=
  if inCode || !p.x then p
  else if p.r then { p with w := false, x := false }
  else { p with r := false, w := true, x := false }

@[expose] def stripCodecMem (keep : BitVec 64 → Bool) (m : Memory) : Memory :=
  ⟨fun a => match m.cells a with
    | some (some p, b) => some (some (stripCodecPerm (keep a) p), b)
    | other => other⟩

@[expose] def stripCodecS (keep : BitVec 64 → Bool) (s : State) : State :=
  s.setMem (stripCodecMem keep s.mem)

theorem stripCodec_read8 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripCodecMem keep m).read8 a = m.read8 a := by
  dsimp only [stripCodecMem, Memory.read8]
  rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl

private theorem stripCodec_isLazyFree (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripCodecMem keep m).isLazyFree a = m.isLazyFree a := by
  dsimp only [stripCodecMem, Memory.isLazyFree]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · simp only [stripCodecPerm]; split
    · rfl
    · split <;> rfl

private theorem stripCodec_isAnon (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripCodecMem keep m).isAnon a = m.isAnon a := by
  dsimp only [stripCodecMem, Memory.isAnon]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · simp only [stripCodecPerm]; split
    · rfl
    · split <;> rfl

theorem stripCodec_perm (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    (stripCodecMem keep m).perm a = (m.perm a).map (stripCodecPerm (keep a)) := by
  dsimp only [stripCodecMem, Memory.perm]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · rcases p with ⟨r, w, x, _, _⟩
    simp only [Option.map, Perm.rwx, stripCodecPerm]
    cases keep a <;> cases r <;> cases x <;> rfl

private theorem perm_rwx_props {m : Memory} {a : BitVec 64} {p : Perm}
    (hp : m.perm a = some p) : p.lazyFree = false ∧ p.anon = true := by
  unfold Memory.perm at hp
  cases hc : m.cells a with
  | none => simp [hc] at hp
  | some cb =>
    rcases cb with ⟨_ | q, _⟩ <;> simp [hc, Perm.rwx] at hp
    subst hp; exact ⟨rfl, rfl⟩

private theorem stripCodec_perm_props (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) :
    ((stripCodecMem keep m).perm a).r = (m.perm a).r ∧
    ((stripCodecMem keep m).perm a).mapped = (m.perm a).mapped ∧
    ((stripCodecMem keep m).perm a = some Perm.rw ↔ m.perm a = some Perm.rw) ∧
    ((stripCodecMem keep m).perm a = some Perm.protNone ↔ m.perm a = some Perm.protNone) := by
  rw [stripCodec_perm]
  unfold stripCodecPerm Perm.rw Perm.protNone
  generalize keep a = ic
  cases hp : m.perm a with
  | none => simp
  | some p =>
    obtain ⟨hlf, han⟩ := perm_rwx_props hp
    rcases p with ⟨r, w, x, lf, an⟩
    dsimp only at hlf han; subst hlf han
    cases ic <;> cases r <;> cases w <;> cases x <;> simp

theorem stripCodec_perm_of_keep {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (ha : keep a = true) :
    (stripCodecMem keep m).perm a = m.perm a := by
  rw [stripCodec_perm]; unfold stripCodecPerm
  simp only [ha, Bool.true_or, ↓reduceIte, Option.map_id']

theorem stripCodec_perm_x_imp {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64} :
    ((stripCodecMem keep m).perm a).x = true →
    (m.perm a).x = true ∧ keep a = true := by
  rw [stripCodec_perm]; unfold stripCodecPerm
  generalize keep a = ic
  cases m.perm a with
  | none => simp
  | some p =>
    rcases p with ⟨r, w, x, _, _⟩
    cases ic <;> cases r <;> cases w <;> cases x <;> simp

/-- Unconditional two-way `Satisfies` equivalence for `stripCodecMem keep` (no `ExecFrozen`
or `xoGuard` assumptions needed). -/
theorem satisfies_stripCodec_iff (keep : BitVec 64 → Bool) (m : Memory) (P : SepProp) :
    (stripCodecMem keep m ⊨ P) ↔ (m ⊨ P) := by
  constructor
  · intro hsat
    exact Arm64.Satisfies.of_perm_mono
      (fun a => (stripCodec_read8 keep m a).symm)
      (fun a hrw => (stripCodec_perm_props keep m a).2.2.1.mp hrw)
      (fun a hpn => (stripCodec_perm_props keep m a).2.2.2.mp hpn)
      (fun a hr => (stripCodec_perm_props keep m a).1.symm.trans hr)
      (fun a hm => (stripCodec_perm_props keep m a).2.1.symm.trans hm)
      (fun a hlf => (stripCodec_isLazyFree keep m a).symm.trans hlf)
      (fun a han => (stripCodec_isAnon keep m a).symm.trans han)
      hsat
  · intro hsat
    exact Arm64.Satisfies.of_perm_mono
      (fun a => stripCodec_read8 keep m a)
      (fun a hrw => (stripCodec_perm_props keep m a).2.2.1.mpr hrw)
      (fun a hpn => (stripCodec_perm_props keep m a).2.2.2.mpr hpn)
      (fun a hr => (stripCodec_perm_props keep m a).1.trans hr)
      (fun a hm => (stripCodec_perm_props keep m a).2.1.trans hm)
      (fun a hlf => (stripCodec_isLazyFree keep m a).trans hlf)
      (fun a han => (stripCodec_isAnon keep m a).trans han)
      hsat

private theorem stripCodec_frozen_imp {keep : BitVec 64 → Bool} {m : Memory} {a : BitVec 64}
    (hwx : ∀ p, m.perm a = some p → p.x = true → p.w = false)
    (hfr : (stripCodecMem keep m).Frozen a) : m.Frozen a := by
  unfold Memory.Frozen at hfr ⊢
  rw [stripCodec_perm] at hfr
  generalize keep a = ic at hfr
  cases hp : m.perm a with
  | none => rw [hp] at hfr; simp [Option.frozen] at hfr
  | some p =>
    have hwx' := hwx p hp
    rw [hp] at hfr
    rcases p with ⟨r, w, x, _, _⟩
    dsimp only [Option.map, Option.frozen, stripCodecPerm, Perm.frozen] at hwx' hfr ⊢
    cases ic <;> cases r <;> cases w <;> cases x <;> simp_all

theorem stripCodec_keepsFrozen (keep : BitVec 64 → Bool) {m₁ m₂ : Memory}
    (hwx : ∀ a p, m₁.perm a = some p → p.x = true → p.w = false)
    (hkf : m₁.KeepsFrozen m₂) :
    (stripCodecMem keep m₁).KeepsFrozen (stripCodecMem keep m₂) := by
  intro a hfr'
  obtain ⟨hr8, hp, hlf, han⟩ := hkf a (stripCodec_frozen_imp (hwx a) hfr')
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [stripCodec_read8, stripCodec_read8, hr8]
  · rw [stripCodec_perm, stripCodec_perm, hp]
  · rw [stripCodec_isLazyFree, stripCodec_isLazyFree, hlf]
  · rw [stripCodec_isAnon, stripCodec_isAnon, han]

private theorem stripCodec_countRw (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat), (stripCodecMem keep m).countRw a n = m.countRw a n
  | _, 0 => rfl
  | a, n + 1 => by
    unfold Memory.countRw Memory.countPerm
    have hrw : ((stripCodecMem keep m).perm a == some Perm.rw) = (m.perm a == some Perm.rw) :=
      Bool.eq_iff_iff.mpr (by simp [(stripCodec_perm_props keep m a).2.2.1])
    simp only [hrw]
    exact congrArg (_ + ·) (stripCodec_countRw keep m (a + 1#64) n)

private theorem stripCodec_allPerm_eq {keep : BitVec 64 → Bool} {m : Memory} {p : Option Perm → Bool}
    (hp : ∀ a, p ((stripCodecMem keep m).perm a) = p (m.perm a)) :
    ∀ (a : BitVec 64) (n : Nat), (stripCodecMem keep m).allPerm p a n = m.allPerm p a n
  | _, 0 => rfl
  | a, n + 1 => by simp only [Memory.allPerm, hp a, stripCodec_allPerm_eq hp (a + 1#64) n]

private theorem stripCodec_allNoLazyFree (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat), (stripCodecMem keep m).allNoLazyFree a n = m.allNoLazyFree a n
  | _, 0 => rfl
  | a, n + 1 => by
    simp only [Memory.allNoLazyFree, stripCodec_isLazyFree,
      stripCodec_allNoLazyFree keep m (a + 1#64) n]

theorem stripCodec_canRead (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (n : Nat) :
    (stripCodecMem keep m).canRead a n = m.canRead a n := by
  simp only [Memory.canRead, stripCodec_allPerm_eq (fun x => (stripCodec_perm_props keep m x).1),
    stripCodec_allNoLazyFree]

private theorem stripCodec_canWrite_of_true (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat), m.canWrite a n = true → (stripCodecMem keep m).canWrite a n = true
  | _, 0, _ => rfl
  | a, n + 1, hw => by
    unfold Memory.canWrite Memory.allPerm at hw ⊢
    simp only [Bool.and_eq_true] at hw ⊢
    refine ⟨?_, stripCodec_canWrite_of_true keep m (a + 1#64) n hw.2⟩
    rw [stripCodec_perm]
    unfold stripCodecPerm
    generalize keep a = ic
    cases hp : m.perm a with
    | none => rw [hp] at hw; simp at hw
    | some p =>
      rw [hp] at hw
      rcases p with ⟨r, w, x, _, _⟩
      cases ic <;> cases r <;> cases w <;> cases x <;> simp_all

private theorem stripCodec_write8 (keep : BitVec 64 → Bool) (m : Memory)
    (addr : BitVec 64) (val : BitVec 8) :
    (stripCodecMem keep m).write8 addr val = stripCodecMem keep (m.write8 addr val) := by
  ext a
  simp only [stripCodecMem, Memory.write8, Memory.rawPerm]
  by_cases ha : a = addr
  · subst ha; simp only [↓reduceIte]
    rcases m.cells a with _ | ⟨_ | p, _⟩
    · rfl
    · rfl
    · simp only [stripCodecPerm]; split
      · rfl
      · split <;> rfl
  · simp [ha]

private theorem stripCodec_write16 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (v : BitVec 16) :
    (stripCodecMem keep m).write16 a v = stripCodecMem keep (m.write16 a v) := by
  simp [Memory.write16, stripCodec_write8]

private theorem stripCodec_write32 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (v : BitVec 32) :
    (stripCodecMem keep m).write32 a v = stripCodecMem keep (m.write32 a v) := by
  simp [Memory.write32, stripCodec_write8]

private theorem stripCodec_write64 (keep : BitVec 64 → Bool) (m : Memory) (a : BitVec 64) (v : BitVec 64) :
    (stripCodecMem keep m).write64 a v = stripCodecMem keep (m.write64 a v) := by
  simp [Memory.write64, stripCodec_write8]

private theorem stripCodec_writeSized (keep : BitVec 64 → Bool) (m : Memory) (sz : MemWidth) (a v : BitVec 64) :
    (stripCodecMem keep m).writeSized sz a v = stripCodecMem keep (m.writeSized sz a v) := by
  cases sz <;> simp [Memory.writeSized, stripCodec_write8, stripCodec_write16,
    stripCodec_write32, stripCodec_write64]

private theorem stripCodec_writeSimdSized (keep : BitVec 64 → Bool) (m : Memory)
    (sz : SimdMemSize) (a : BitVec 64) (v : BitVec 128) :
    (stripCodecMem keep m).writeSimdSized sz a v = stripCodecMem keep (m.writeSimdSized sz a v) := by
  cases sz <;> simp [Memory.writeSimdSized, Memory.write128, stripCodec_write8,
    stripCodec_write16, stripCodec_write32, stripCodec_write64]

private theorem stripCodec_simdStoreRegs (keep : BitVec 64 → Bool) (sz : SimdMemSize)
    (vals : BitVec 5 → BitVec 128) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (m : Memory),
      simdStoreRegs sz vals n vt ea (stripCodecMem keep m) =
        stripCodecMem keep (simdStoreRegs sz vals n vt ea m)
  | 0, _, _, _ => rfl
  | n + 1, vt, ea, m => by
    simp only [simdStoreRegs, stripCodec_writeSimdSized, stripCodec_simdStoreRegs keep sz vals n]

private theorem stripCodec_readSized (keep : BitVec 64 → Bool) (m : Memory)
    (sz : MemWidth) (sg : Bool) (a : BitVec 64) :
    (stripCodecMem keep m).readSized sz sg a = m.readSized sz sg a := by
  cases sz <;> simp [Memory.readSized, Memory.read16, Memory.read32, Memory.read64, stripCodec_read8]

private theorem stripCodec_readSimdSized (keep : BitVec 64 → Bool) (m : Memory)
    (sz : SimdMemSize) (a : BitVec 64) :
    (stripCodecMem keep m).readSimdSized sz a = m.readSimdSized sz a := by
  cases sz <;> simp [Memory.readSimdSized, Memory.read16, Memory.read32, Memory.read64,
    Memory.read128, stripCodec_read8]

@[simp] theorem sc_mem (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).mem = stripCodecMem p s.mem := by cases s; rfl
@[simp] theorem sc_r64 (p : BitVec 64 → Bool) (s : State) (r : Reg) : (stripCodecS p s).readReg64 r = s.readReg64 r := by cases s; rfl
private theorem sc_r32 (p : BitVec 64 → Bool) (s : State) (r : Reg) : (stripCodecS p s).readReg32 r = s.readReg32 r := by cases s; rfl
private theorem sc_rr (p : BitVec 64 → Bool) (s : State) (w : Width) (r : Reg) : (stripCodecS p s).readReg w r = s.readReg w r := by cases s; rfl
private theorem sc_rv128 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) : (stripCodecS p s).readVReg128 r = s.readVReg128 r := by cases s; rfl
private theorem sc_rv128_eta (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).readVReg128 = s.readVReg128 := by funext r; cases s; rfl
private theorem sc_rv64 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) : (stripCodecS p s).readVReg64 r = s.readVReg64 r := by cases s; rfl
private theorem sc_rv32 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) : (stripCodecS p s).readVReg32 r = s.readVReg32 r := by cases s; rfl
@[simp] theorem sc_pc (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).pc = s.pc := by cases s; rfl
@[simp] theorem sc_sp (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).sp = s.sp := by cases s; rfl
@[simp] theorem sc_ps (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).pstate = s.pstate := by cases s; rfl
@[simp] theorem sc_fp (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).fpsr = s.fpsr := by cases s; rfl
@[simp] theorem sc_tp (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
private theorem sc_ewf (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).exclWillFail = s.exclWillFail := by cases s; rfl
private theorem sc_csp (p : BitVec 64 → Bool) (s : State) (r : Reg) : checkRegSPAligned (stripCodecS p s) r = checkRegSPAligned s r := by
  cases s; cases r <;> rfl
private theorem sc_casp (p : BitVec 64 → Bool) (s : State) (a : AddrMode) : checkAddrSPAligned (stripCodecS p s) a = checkAddrSPAligned s a := by
  cases s; cases a <;> rfl
private theorem sc_eam (p : BitVec 64 → Bool) (s : State) (a : AddrMode) : evalAddrMode (stripCodecS p s) a = evalAddrMode s a := by
  cases s; cases a <;> rfl
private theorem sc_adv (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).advancePC = stripCodecS p s.advancePC := by cases s; rfl
private theorem sc_spc (p : BitVec 64 → Bool) (s : State) (q : BitVec 64) : (stripCodecS p s).setPC q = stripCodecS p (s.setPC q) := by cases s; rfl
private theorem sc_w64 (p : BitVec 64 → Bool) (s : State) (r : Reg) (v : BitVec 64) :
    (stripCodecS p s).writeReg64 r v = stripCodecS p (s.writeReg64 r v) := by cases s; cases r <;> rfl
private theorem sc_w32 (p : BitVec 64 → Bool) (s : State) (r : Reg) (v : BitVec 32) :
    (stripCodecS p s).writeReg32 r v = stripCodecS p (s.writeReg32 r v) := sc_w64 p s r _
private theorem sc_w (p : BitVec 64 → Bool) (s : State) (w : Width) (r : Reg) (v : BitVec 64) :
    (stripCodecS p s).writeReg w r v = stripCodecS p (s.writeReg w r v) := sc_w64 p s r _
private theorem sc_wv128 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) (v : BitVec 128) :
    (stripCodecS p s).writeVReg128 r v = stripCodecS p (s.writeVReg128 r v) := by cases s; rfl
private theorem sc_wv64 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) (v : BitVec 64) :
    (stripCodecS p s).writeVReg64 r v = stripCodecS p (s.writeVReg64 r v) := sc_wv128 p s r _
private theorem sc_wv32 (p : BitVec 64 → Bool) (s : State) (r : BitVec 5) (v : BitVec 32) :
    (stripCodecS p s).writeVReg32 r v = stripCodecS p (s.writeVReg32 r v) := sc_wv128 p s r _
private theorem sc_sps (p : BitVec 64 → Bool) (s : State) (q : PState) : (stripCodecS p s).setPState q = stripCodecS p (s.setPState q) := by cases s; rfl
private theorem sc_sfp (p : BitVec 64 → Bool) (s : State) (f : BitVec 32) : (stripCodecS p s).setFpsr f = stripCodecS p (s.setFpsr f) := by cases s; rfl
private theorem sc_sofp (p : BitVec 64 → Bool) (s : State) (f : BitVec 32) : (stripCodecS p s).orFpsr f = stripCodecS p (s.orFpsr f) := by cases s; rfl
theorem sc_sst (p : BitVec 64 → Bool) (s : State) (st : ExecStatus) : (stripCodecS p s).setStatus st = stripCodecS p (s.setStatus st) := by cases s; rfl
theorem sc_wst (p : BitVec 64 → Bool) (s : State) (st : ExecStatus) :
    { stripCodecS p s with status := st } = stripCodecS p { s with status := st } := by cases s; rfl
private theorem sc_stp (p : BitVec 64 → Bool) (s : State) (v : BitVec 64) : setTpidrEl0 (stripCodecS p s) v = stripCodecS p (setTpidrEl0 s v) := by cases s; rfl
private theorem sc_sex (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).stepExclOracle = stripCodecS p s.stepExclOracle := by cases s; rfl
theorem sc_smem (p : BitVec 64 → Bool) (s : State) (m : Memory) :
    (stripCodecS p s).setMem (stripCodecMem p m) = stripCodecS p (s.setMem m) := by cases s; rfl
private theorem sc_as (p : BitVec 64 → Bool) (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) :
    applySimdResult (stripCodecS p s) rd r = stripCodecS p (applySimdResult s rd r) := by cases s; cases r <;> rfl
private theorem sc_ass (p : BitVec 64 → Bool) (s : State) (rd : BitVec 5) (r : Except String (BitVec 128)) (sat : Option (BitVec 32)) :
    applySimdSatResult (stripCodecS p s) rd r sat = stripCodecS p (applySimdSatResult s rd r sat) := by cases s; cases r <;> cases sat <;> rfl
private theorem sc_slr (p : BitVec 64 → Bool) (sz : SimdMemSize) (m : Memory) :
    ∀ (n : Nat) (vt : BitVec 5) (ea : BitVec 64) (s : State),
      simdLoadRegs sz (stripCodecMem p m) n vt ea (stripCodecS p s) = stripCodecS p (simdLoadRegs sz m n vt ea s)
  | 0, _, _, _ => rfl
  | n + 1, _, _, s => by simp only [simdLoadRegs, stripCodec_readSimdSized, sc_slr p sz m n, sc_wv128]
private theorem sc_ite (p : BitVec 64 → Bool) (c : Prop) [Decidable c] (a b : State) :
    (if c then stripCodecS p a else stripCodecS p b) = stripCodecS p (if c then a else b) := by split <;> rfl
@[simp] theorem sc_regs (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).regs = s.regs := by cases s; rfl
@[simp] theorem sc_vregs (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).vregs = s.vregs := by cases s; rfl
@[simp] theorem sc_bs (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).brkStart = s.brkStart := by cases s; rfl
@[simp] theorem sc_brk (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).brk = s.brk := by cases s; rfl
@[simp] theorem sc_fs (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).fs = s.fs := by cases s; rfl
@[simp] theorem sc_orc (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).oracle = s.oracle := by cases s; rfl
@[simp] theorem sc_oi (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).oracleIdx = s.oracleIdx := by cases s; rfl
@[simp] theorem sc_ef (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).exclFails = s.exclFails := by cases s; rfl
@[simp] theorem sc_tr (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).trace = s.trace := by cases s; rfl
@[simp] theorem sc_st (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).status = s.status := by cases s; rfl
@[simp] theorem sc_sym (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).symtab = s.symtab := by cases s; rfl
@[simp] theorem sc_sig (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).sigActions = s.sigActions := by cases s; rfl
@[simp] theorem sc_sas (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).sigAltStack = s.sigAltStack := by cases s; rfl
@[simp] theorem sc_pma (p : BitVec 64 → Bool) (s : State) : (stripCodecS p s).physMemAvail = s.physMemAvail := by cases s; rfl
private theorem sc_mk (p : BitVec 64 → Bool) {rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma} :
    State.mk rg vr sp pc ps (stripCodecMem p m) tp fp bs b fs o oi ef tr st sym sig sas pma =
      stripCodecS p (State.mk rg vr sp pc ps m tp fp bs b fs o oi ef tr st sym sig sas pma) := rfl

private theorem sc_cw1 (p : BitVec 64 → Bool) (m : Memory) (ea : BitVec 64) (n : Nat)
    (s t : State) :
    stripCodecS p (if !(stripCodecMem p m).canWrite ea n then
        s.setStatus (.Exception "permission fault") else t) =
      stripCodecS p (if !m.canWrite ea n then
        s.setStatus (.Exception "permission fault") else t) ∨
      (if !m.canWrite ea n then s.setStatus (.Exception "permission fault") else t).status =
        .Exception "permission fault" := by
  by_cases hcw : m.canWrite ea n = true
  · left; simp [hcw, stripCodec_canWrite_of_true p m ea n hcw]
  · right; simp [Bool.eq_false_iff.mpr hcw]

private theorem sc_cw2 (p : BitVec 64 → Bool) (m : Memory)
    (ea1 : BitVec 64) (n1 : Nat) (ea2 : BitVec 64) (n2 : Nat)
    (s t : State) :
    stripCodecS p (if !((stripCodecMem p m).canWrite ea1 n1 && (stripCodecMem p m).canWrite ea2 n2) then
        s.setStatus (.Exception "permission fault") else t) =
      stripCodecS p (if !(m.canWrite ea1 n1 && m.canWrite ea2 n2) then
        s.setStatus (.Exception "permission fault") else t) ∨
      (if !(m.canWrite ea1 n1 && m.canWrite ea2 n2) then
        s.setStatus (.Exception "permission fault") else t).status =
        .Exception "permission fault" := by
  by_cases hcw : (m.canWrite ea1 n1 && m.canWrite ea2 n2) = true
  · left
    have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hcw
    simp [h1, h2, stripCodec_canWrite_of_true p m ea1 n1 h1, stripCodec_canWrite_of_true p m ea2 n2 h2]
  · right; simp [Bool.eq_false_iff.mpr hcw]

private theorem sc_rcw (p : BitVec 64 → Bool) (m : Memory) (ea : BitVec 64) (n : Nat)
    (s t : State) :
    stripCodecS p (if !(m.canRead ea n && (stripCodecMem p m).canWrite ea n) then
        s.setStatus (.Exception "permission fault") else t) =
      stripCodecS p (if !(m.canRead ea n && m.canWrite ea n) then
        s.setStatus (.Exception "permission fault") else t) ∨
      (if !(m.canRead ea n && m.canWrite ea n) then
        s.setStatus (.Exception "permission fault") else t).status =
        .Exception "permission fault" := by
  by_cases hcw : (m.canRead ea n && m.canWrite ea n) = true
  · left
    have ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hcw
    simp [h1, h2, stripCodec_canWrite_of_true p m ea n h2]
  · right; simp [Bool.eq_false_iff.mpr hcw]

private theorem or_ex_ite_l' (p : BitVec 64 → Bool) (c : Prop) [Decidable c]
    (a b' b : State) {msg : String}
    (hb : stripCodecS p b' = stripCodecS p b ∨ b.status = .Exception msg) :
    stripCodecS p (if c then a else b') = stripCodecS p (if c then a else b) ∨
      (if c then a else b).status = .Exception msg := by
  by_cases hc : c
  · simp [hc]
  · simp [hc]; exact hb

private theorem or_ex_ite_r' (p : BitVec 64 → Bool) (c : Prop) [Decidable c]
    (a' a b : State) {msg : String}
    (ha : stripCodecS p a' = stripCodecS p a ∨ a.status = .Exception msg) :
    stripCodecS p (if c then a' else b) = stripCodecS p (if c then a else b) ∨
      (if c then a else b).status = .Exception msg := by
  by_cases hc : c
  · simp [hc]; exact ha
  · simp [hc]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 400000 in
/-- Every non-`SVC #0` ARM64 instruction commutes with `stripCodecS keep` whenever the unstripped
step does not fault with `.Exception`. -/
theorem execInst_stripCodec_of_noException {inst : Instr} (h : inst.isSvc0 = false)
    (keep : BitVec 64 → Bool) (s : State)
    (hnoex : ∀ msg, (execInst inst s).status ≠ .Exception msg) :
    execInst inst (stripCodecS keep s) = stripCodecS keep (execInst inst s) := by
  suffices hor : execInst inst (stripCodecS keep s) = stripCodecS keep (execInst inst s) ∨
      (execInst inst s).status = .Exception "permission fault" by
    rcases hor with heq | hex
    · exact heq
    · exact False.elim (hnoex _ hex)
  cases inst
  case system isHalt imm =>
    left; cases isHalt
    · by_cases himm : imm == 0#16
      · have heq : imm = 0#16 := of_decide_eq_true himm; subst heq; simp [Instr.isSvc0] at h
      · dsimp only [execInst, execInstWithSvc]; simp [himm, sc_sst]
    · dsimp only [execInst, execInstWithSvc]; by_cases himm : imm == 1#16 <;> simp [himm, sc_sst]
  case simdThreeSame q u size rm opcode rn rd =>
    left
    by_cases hop : opcode == 0b00011#5
    · have hsz : size = 0#2 ∨ size = 1#2 ∨ size = 2#2 ∨ size = 3#2 := by clear h hnoex; revert size; decide
      rcases hsz with rfl | rfl | rfl | rfl <;> cases u <;>
        (dsimp only [execInst, execInstWithSvc]; simp only [hop, ↓reduceIte, sc_rv128];
         split <;> simp only [sc_wv128, sc_adv, sc_ass])
    · dsimp only [execInst, execInstWithSvc]
      simp only [hop, Bool.false_eq_true, ↓reduceIte, sc_rv128, sc_regs, sc_vregs, sc_sp, sc_pc, sc_ps,
        sc_mem, sc_tp, sc_fp, sc_bs, sc_brk, sc_fs, sc_orc, sc_oi, sc_ef, sc_tr, sc_st, sc_sym, sc_sig, sc_sas, sc_pma,
        sc_mk, sc_adv, sc_wv128, sc_sst, sc_wst, sc_as, sc_ass, sc_ite]
  case st1SinglePost q rm opcode sBit size rn vt =>
    dsimp only [execInst, execInstWithSvc]
    by_cases h0 : opcode.extractLsb' 1 2 == 0#2 <;> by_cases h1 : opcode.extractLsb' 1 2 == 1#2 <;>
      by_cases hs0 : size.extractLsb' 0 1 == 0#1 <;>
      (simp only [h0, h1, hs0, Bool.false_eq_true, ↓reduceIte, sc_mem, sc_regs, sc_vregs, sc_sp, sc_pc,
         sc_ps, sc_tp, sc_fp, sc_bs, sc_brk, sc_fs, sc_orc, sc_oi, sc_ef, sc_tr, sc_st, sc_sym, sc_sig, sc_sas, sc_pma,
         sc_mk, sc_r64, sc_rv128, sc_csp,
         stripCodec_write8, stripCodec_write16, stripCodec_write32, stripCodec_write64,
         sc_smem, sc_w64, sc_adv, sc_sst, sc_wst, sc_ite];
       repeat' first
         | exact Or.inl rfl
         | exact sc_cw1 keep s.mem _ _ s _
         | refine or_ex_ite_l' keep _ _ _ _ ?_)
  case simdLdStMulti isLoad q size selem rn postIdx rm vt =>
    dsimp only [execInst, execInstWithSvc]
    by_cases hbad : (size == 3#2 && !q || !(selem == 2 || selem == 3 || selem == 4)) = true
    · left
      simp only [hbad, ↓reduceIte, sc_regs, sc_vregs, sc_sp, sc_pc, sc_ps, sc_mem, sc_tp, sc_fp,
        sc_bs, sc_brk, sc_fs, sc_orc, sc_oi, sc_ef, sc_tr, sc_st, sc_sym, sc_sig, sc_sas, sc_pma, sc_mk, sc_wst]
    · cases isLoad
      · by_cases h3 : selem ≥ 3 <;> by_cases h4 : selem ≥ 4 <;>
          (simp only [hbad, h3, h4, Bool.false_eq_true, ↓reduceIte, sc_r64, sc_rv128_eta, sc_mem, sc_csp,
             stripCodec_canRead, stripCodec_readSimdSized, stripCodec_simdStoreRegs,
             sc_w64, sc_wv128, sc_adv, sc_smem, sc_sst, sc_ite];
           exact or_ex_ite_l' keep _ _ _ _ (sc_cw1 keep s.mem _ _ s _))
      · left
        by_cases h3 : selem ≥ 3 <;> by_cases h4 : selem ≥ 4 <;>
          simp only [hbad, h3, h4, Bool.false_eq_true, ↓reduceIte, sc_r64, sc_rv128_eta, sc_mem, sc_csp,
            stripCodec_canRead, stripCodec_readSimdSized, stripCodec_simdStoreRegs,
            sc_w64, sc_wv128, sc_adv, sc_smem, sc_sst, sc_ite]
  case str _ _ addr | strSimd _ _ addr =>
    dsimp only [execInst, execInstWithSvc, execStr]
    rw [sc_casp, sc_eam]
    rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      (simp only [sc_mem, sc_r64, sc_rv128, stripCodec_writeSized, stripCodec_writeSimdSized,
         sc_w64, sc_w, sc_wv128, sc_smem, sc_adv, sc_sst, sc_ite];
       exact or_ex_ite_l' keep _ _ _ _ (sc_cw1 keep s.mem _ _ s _))
  case stp _ _ _ addr | stpSimd _ _ _ addr =>
    dsimp only [execInst, execInstWithSvc, execStp]
    rw [sc_casp, sc_eam]
    rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      (simp only [sc_mem, sc_r64, sc_rv128, stripCodec_writeSized, stripCodec_writeSimdSized,
         sc_w64, sc_w, sc_wv128, sc_smem, sc_adv, sc_sst, sc_ite];
       exact or_ex_ite_l' keep _ _ _ _ (sc_cw2 keep s.mem _ _ _ _ s _))
  case ldr _ _ _ _ addr | ldp _ _ _ _ addr | ldpSimd _ _ _ addr | ldrSimd _ _ addr =>
    left
    dsimp only [execInst, execInstWithSvc, execLdr, execLdp]
    rw [sc_casp, sc_eam]
    rcases evalAddrMode s addr with ⟨_, _ | ⟨_, _⟩⟩ <;>
      simp only [sc_mem, sc_r64, sc_rv128, stripCodec_canRead, stripCodec_readSized,
        stripCodec_readSimdSized, sc_w64, sc_w, sc_wv128, sc_smem, sc_adv, sc_sst, sc_ite]
  case addSubImm | logicalImm | moveWide | bitfield | extr | logicalShift | addSubShift
     | addSubExt | addSubCarry | condCompareReg | condCompareImm | condSelect
     | dataProc1 | dataProc2 | dataProc3 =>
    left
    dsimp only [execInst, execInstWithSvc, execAddSubImm, execLogicalImm, execMoveWide, execBitfield,
      execLogicalShift, execAddSubShift, execAddSubExt, execAddSubCarry, execCondCompare,
      execCondSelect, execDataProc1, execDataProc2, execDataProc3]
    simp only [sc_r64, sc_r32, sc_rr, sc_pc, sc_sp, sc_ps, sc_w64, sc_w32, sc_w, sc_sps, sc_adv, sc_ite]
    try ((repeat' split) <;> simp only [sc_w64, sc_w32, sc_w, sc_sps, sc_adv, sc_ite])
  all_goals
    dsimp only [execInst, execInstWithSvc, execLdrLit, execLdp, execStp, evalAddrMode]
    simp only [sc_mem, sc_regs, sc_vregs, sc_bs, sc_brk, sc_fs, sc_orc, sc_oi, sc_ef, sc_tr, sc_st,
      sc_sym, sc_sig, sc_sas, sc_pma, sc_mk, sc_r64, sc_r32, sc_rr, sc_rv128, sc_rv128_eta, sc_rv64, sc_rv32,
      sc_pc, sc_sp, sc_ps, sc_fp, sc_tp, sc_ewf, sc_csp, sc_casp, sc_eam,
      stripCodec_canRead, stripCodec_readSized, stripCodec_readSimdSized,
      stripCodec_write8, stripCodec_write16, stripCodec_write32, stripCodec_write64,
      stripCodec_writeSized, stripCodec_writeSimdSized, stripCodec_simdStoreRegs, sc_slr,
      sc_adv, sc_spc, sc_w64, sc_w32, sc_w, sc_wv128, sc_wv64, sc_wv32,
      sc_sps, sc_sfp, sc_sofp, sc_sst, sc_wst, sc_stp, sc_sex, sc_smem, sc_as, sc_ass, sc_ite]
    try exact Or.inl trivial
    repeat' first
      | exact Or.inl rfl
      | exact sc_cw1 keep s.mem _ _ s _
      | exact sc_cw2 keep s.mem _ _ _ _ s _
      | exact sc_rcw keep s.mem _ _ s _
      | refine or_ex_ite_l' keep _ _ _ _ ?_
      | refine or_ex_ite_r' keep _ _ _ _ ?_

/-! ## Section 2: Stripped `mallocng` Budget Instance & Off-Trajectory Hook Wrapper -/

open LibsignalBinary.Heap (
  AllocCallPreserved AllocCostModel AllocEvent BudgetLimits FitsEvents
  MallocngCostModelIface MallocngCostModelSound MallocngModelEnv
  NullAllowed OomPreserved PoolPreserved RustCliAllocBudget VmPreserved
  mallocngBudgetPool mallocngBudgetPoolAt mallocngBudgetPoolAt_transport
  mallocngBudgetPoolInv mallocngLiveM mallocngRustCliAllocBudget
  rustAllocEvents rustCliAllocBudgetSpec rustCliDeallocBudgetSpec
  rustCliReallocBudgetSpec rustDeallocEvents rustReallocEvents
  StaticMappedCover zeroBudgetLimits
)
open LibsignalBinary.Proofs.HookDischarge.CryptoMallocngBudgetBase (
  CodeBlocksPermRX CodeBlocksPermRXMem codeBlocksPermRX_of_keepsFrozen
  mallocngHookBudgetPool mallocngHookBudgetPool_transport
  mallocngHookBudgetPool_zero_transport mallocngHookRustCliAllocBudget
)
open VerifiedLibraries.Mallocng (mallocngAddrsOfPlacement)

@[expose] def CodeBlocksPermStrippedMem (keep : BitVec 64 → Bool) (mpl : Obj.MultiPlacement)
    (m : Memory) : Prop :=
  ∀ a : BitVec 64,
    (VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome = true →
    m.perm a = some (stripCodecPerm (keep a) Perm.rx)

abbrev CodeBlocksPermStripped (keep : BitVec 64 → Bool) (mpl : Obj.MultiPlacement)
    (s : State) : Prop :=
  CodeBlocksPermStrippedMem keep mpl s.mem

private theorem codeBlocksPermStripped_of_perm_eq {keep : BitVec 64 → Bool}
    {mpl : Obj.MultiPlacement} {m m' : Memory} (hperm : ∀ a, m'.perm a = m.perm a) :
    CodeBlocksPermStrippedMem keep mpl m' = CodeBlocksPermStrippedMem keep mpl m := by
  apply propext
  unfold CodeBlocksPermStrippedMem
  simp only [hperm]

private theorem codeBlocksPermStripped_of_rx (keep : BitVec 64 → Bool)
    {mpl : Obj.MultiPlacement} {m : Memory} (hrx : CodeBlocksPermRXMem mpl m) :
    CodeBlocksPermStrippedMem keep mpl (stripCodecMem keep m) := by
  intro a ha
  rw [stripCodec_perm, hrx a ha]
  rfl

private theorem stripCodec_rwBytes (keep : BitVec 64 → Bool) (m : Memory) :
    ProofLib.rwBytes (stripCodecMem keep m) = ProofLib.rwBytes m := by
  unfold ProofLib.rwBytes
  exact stripCodec_countRw keep m 0#64 (2 ^ 64)

private theorem stripCodec_physPlusRw (keep : BitVec 64 → Bool) (s : State) :
    ProofLib.physPlusRw (stripCodecS keep s) = ProofLib.physPlusRw s := by
  unfold ProofLib.physPlusRw
  simp only [sc_pma, sc_mem, stripCodec_rwBytes]

private theorem stripCodec_staticMappedCover (keep : BitVec 64 → Bool)
    (lim : BudgetLimits) (staticIvs ivs : List (BitVec 64 × Nat)) (m : Memory) :
    StaticMappedCover lim staticIvs ivs (stripCodecMem keep m) =
      StaticMappedCover lim staticIvs ivs m := by
  apply propext
  unfold StaticMappedCover
  simp only [(stripCodec_perm_props keep m _).2.1]

private theorem stripCodec_mallocngBudgetPool (keep : BitVec 64 → Bool)
    (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    mallocngBudgetPool M I γ mpl tp brkStart lim st (stripCodecS keep s) =
      mallocngBudgetPool M I γ mpl tp brkStart lim st s := by
  have hinv : ∀ staticIvs ivs,
      mallocngBudgetPoolInv lim staticIvs ivs (stripCodecS keep s) =
        mallocngBudgetPoolInv lim staticIvs ivs s := by
    intro staticIvs ivs
    apply propext
    unfold mallocngBudgetPoolInv
    simp only [sc_mem, stripCodec_staticMappedCover, stripCodec_physPlusRw]
  unfold mallocngBudgetPool mallocngBudgetPoolAt MallocngModelEnv
  simp only [hinv, sc_brk, sc_bs, sc_tp]

@[expose] def strippedMallocngPool (keep : BitVec 64 → Bool)
    (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) : SepProp :=
  if lim.enforced then
    VerifiedLibraries.mallocngLib.codeRO mpl ∗
      mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗
      ⌜lim.enforced = true → CodeBlocksPermStripped keep mpl s⌝
  else
    mallocngHookBudgetPool M I γ mpl tp brkStart lim st s

theorem strippedMallocngPool_transport (keep : BitVec 64 → Bool)
    (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) {s s' : State} (hvm : VmPreserved s s') :
    strippedMallocngPool keep M I γ mpl tp brkStart lim st s' =
      strippedMallocngPool keep M I γ mpl tp brkStart lim st s := by
  unfold strippedMallocngPool
  by_cases henf : lim.enforced = true
  · simp only [henf, ↓reduceIte]
    have hpool := mallocngBudgetPoolAt_transport M I γ (mallocngAddrsOfPlacement mpl) tp brkStart lim st hvm
    have hperm : ∀ a, s'.mem.perm a = s.mem.perm a := by
      intro a; unfold VmPreserved at hvm; simp_all
    have hcs := codeBlocksPermStripped_of_perm_eq (keep := keep) (mpl := mpl) hperm
    simp only [mallocngBudgetPool, hpool, CodeBlocksPermStripped, hcs]
  · simp only [henf]
    exact mallocngHookBudgetPool_transport M I γ mpl tp brkStart lim st hvm

@[expose] def strippedMallocngBudget (keep : BitVec 64 → Bool)
    (M : AllocCostModel) (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    RustCliAllocBudget M where
  pool := strippedMallocngPool keep M I γ mpl tp brkStart
  live := mallocngLiveM M I γ
  block_valid := (mallocngRustCliAllocBudget M I hS γ mpl tp brkStart).block_valid
  pool_transport lim st _ _ hvm :=
    strippedMallocngPool_transport keep M I γ mpl tp brkStart lim st hvm
  pool_zero_transport st _ _ hp :=
    mallocngHookBudgetPool_zero_transport M I γ mpl tp brkStart st hp

@[simp] theorem strippedMallocngBudget_pool (keep : BitVec 64 → Bool)
    (M : AllocCostModel) (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    (strippedMallocngBudget keep M I hS γ mpl tp brkStart).pool =
      strippedMallocngPool keep M I γ mpl tp brkStart := rfl

@[simp] theorem strippedMallocngBudget_repAlloc (keep : BitVec 64 → Bool)
    (M : AllocCostModel) (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    (strippedMallocngBudget keep M I hS γ mpl tp brkStart).repAlloc =
      (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).repAlloc := rfl

@[simp] theorem strippedMallocngBudget_live (keep : BitVec 64 → Bool)
    (M : AllocCostModel) (I : MallocngCostModelIface M) (hS : MallocngCostModelSound M I)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64) :
    (strippedMallocngBudget keep M I hS γ mpl tp brkStart).live =
      (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).live := rfl

theorem pool_rx_of_satisfies_mallocng
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s : State} {R : SepProp}
    (hsat : s.mem ⊨ (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim st s ∗ R) :
    lim.enforced = true → CodeBlocksPermRX mpl s := by
  change s.mem ⊨ (VerifiedLibraries.mallocngLib.codeRO mpl ∗
      mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗
      ⌜lim.enforced = true → CodeBlocksPermRX mpl s⌝) ∗ R at hsat
  have hEq :
      ((VerifiedLibraries.mallocngLib.codeRO mpl ∗
          mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗
          ⌜lim.enforced = true → CodeBlocksPermRX mpl s⌝) ∗ R) =
      (⌜lim.enforced = true → CodeBlocksPermRX mpl s⌝ ∗
        (VerifiedLibraries.mallocngLib.codeRO mpl ∗
          mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗ R)) := by ac_rfl
  rw [hEq, ProofLib.satisfies_pure_sepConj] at hsat
  exact hsat.1

theorem pool_stripped_of_satisfies
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s : State} {R : SepProp}
    (hsat : s.mem ⊨ (strippedMallocngBudget keep M I hS γ mpl tp brkStart).pool lim st s ∗ R) :
    lim.enforced = true → CodeBlocksPermStripped keep mpl s := by
  intro henf
  change s.mem ⊨ strippedMallocngPool keep M I γ mpl tp brkStart lim st s ∗ R at hsat
  unfold strippedMallocngPool at hsat
  simp only [henf, ↓reduceIte] at hsat
  have hEq :
      ((VerifiedLibraries.mallocngLib.codeRO mpl ∗
          mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗
          ⌜True → CodeBlocksPermStripped keep mpl s⌝) ∗ R) =
      (⌜True → CodeBlocksPermStripped keep mpl s⌝ ∗
        (VerifiedLibraries.mallocngLib.codeRO mpl ∗
          mallocngBudgetPool M I γ mpl tp brkStart lim st s ∗ R)) := by ac_rfl
  rw [hEq, ProofLib.satisfies_pure_sepConj] at hsat
  exact hsat.1 trivial

theorem satisfies_strippedPool_of_mallocng_keepOut
    {keep keep' : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s : State} {R : SepProp}
    (hagree : ∀ a, (VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome = true → keep' a = keep a)
    (hsat : s.mem ⊨ (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim st s ∗ R) :
    (stripCodecS keep' s).mem ⊨
      (strippedMallocngBudget keep M I hS γ mpl tp brkStart).pool lim st (stripCodecS keep' s) ∗ R := by
  have hrx := pool_rx_of_satisfies_mallocng hsat
  rw [sc_mem, satisfies_stripCodec_iff]
  change s.mem ⊨ strippedMallocngPool keep M I γ mpl tp brkStart lim st (stripCodecS keep' s) ∗ R
  unfold strippedMallocngPool
  by_cases henf : lim.enforced = true
  · simp only [henf, ↓reduceIte, stripCodec_mallocngBudgetPool]
    have hcs : CodeBlocksPermStripped keep mpl (stripCodecS keep' s) := by
      intro a ha
      rw [sc_mem, stripCodec_perm, hrx henf a ha, hagree a ha]
      rfl
    have hEq : (True → CodeBlocksPermStripped keep mpl (stripCodecS keep' s)) =
        (lim.enforced = true → CodeBlocksPermRX mpl s) :=
      propext ⟨fun _ _ => hrx henf, fun _ _ => hcs⟩
    rw [hEq]
    exact hsat
  · simp only [henf]
    change s.mem ⊨ mallocngHookBudgetPool M I γ mpl tp brkStart lim st (stripCodecS keep' s) ∗ R
    unfold mallocngHookBudgetPool
    have hEq : (lim.enforced = true → CodeBlocksPermRX mpl (stripCodecS keep' s)) =
        (lim.enforced = true → CodeBlocksPermRX mpl s) :=
      propext ⟨fun _ h => absurd h henf, fun _ h => absurd h henf⟩
    rw [stripCodec_mallocngBudgetPool, hEq]
    exact hsat

theorem satisfies_strippedPool_of_mallocng (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s : State} {R : SepProp}
    (hsat : s.mem ⊨ (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim st s ∗ R) :
    (stripCodecS keep s).mem ⊨
      (strippedMallocngBudget keep M I hS γ mpl tp brkStart).pool lim st (stripCodecS keep s) ∗ R :=
  satisfies_strippedPool_of_mallocng_keepOut (fun _ _ => rfl) hsat

theorem satisfies_mallocngPool_of_stripped (keep : BitVec 64 → Bool)
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s : State} {R : SepProp}
    (hrx : lim.enforced = true → CodeBlocksPermRX mpl s)
    (hsat : (stripCodecS keep s).mem ⊨
      (strippedMallocngBudget keep M I hS γ mpl tp brkStart).pool lim st (stripCodecS keep s) ∗ R) :
    s.mem ⊨ (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim st s ∗ R := by
  rw [sc_mem, satisfies_stripCodec_iff] at hsat
  change s.mem ⊨ strippedMallocngPool keep M I γ mpl tp brkStart lim st (stripCodecS keep s) ∗ R at hsat
  unfold strippedMallocngPool at hsat
  by_cases henf : lim.enforced = true
  · simp only [henf, ↓reduceIte, stripCodec_mallocngBudgetPool] at hsat
    have hcs : CodeBlocksPermStripped keep mpl (stripCodecS keep s) :=
      codeBlocksPermStripped_of_rx keep (hrx henf)
    have hEq : (True → CodeBlocksPermStripped keep mpl (stripCodecS keep s)) =
        (lim.enforced = true → CodeBlocksPermRX mpl s) :=
      propext ⟨fun _ _ => hrx henf, fun _ _ => hcs⟩
    rw [hEq] at hsat
    exact hsat
  · simp only [henf] at hsat
    change s.mem ⊨ mallocngHookBudgetPool M I γ mpl tp brkStart lim st (stripCodecS keep s) ∗ R at hsat
    unfold mallocngHookBudgetPool at hsat
    have hEq : (lim.enforced = true → CodeBlocksPermRX mpl (stripCodecS keep s)) =
        (lim.enforced = true → CodeBlocksPermRX mpl s) :=
      propext ⟨fun _ h => absurd h henf, fun _ h => absurd h henf⟩
    rw [stripCodec_mallocngBudgetPool, hEq] at hsat
    exact hsat

@[expose] def restoreRxPerm (inM : Bool) (p : Perm) : Perm :=
  if inM && !p.w && p.r then { p with x := true } else p

@[expose] def restoreMallocngRXMem (mpl : Obj.MultiPlacement) (m : Memory) : Memory :=
  ⟨fun a => match m.cells a with
    | some (some p, b) =>
      some (some (restoreRxPerm (VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome p), b)
    | other => other⟩

@[expose] def restoreMallocngRXS (mpl : Obj.MultiPlacement) (s : State) : State :=
  s.setMem (restoreMallocngRXMem mpl s.mem)

private theorem restoreRx_read8 (mpl : Obj.MultiPlacement) (m : Memory) (a : BitVec 64) :
    (restoreMallocngRXMem mpl m).read8 a = m.read8 a := by
  dsimp only [restoreMallocngRXMem, Memory.read8]
  rcases m.cells a with _ | ⟨_ | _, _⟩ <;> rfl

private theorem restoreRx_isLazyFree (mpl : Obj.MultiPlacement) (m : Memory) (a : BitVec 64) :
    (restoreMallocngRXMem mpl m).isLazyFree a = m.isLazyFree a := by
  dsimp only [restoreMallocngRXMem, Memory.isLazyFree]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · simp only [restoreRxPerm]; split <;> rfl

private theorem restoreRx_isAnon (mpl : Obj.MultiPlacement) (m : Memory) (a : BitVec 64) :
    (restoreMallocngRXMem mpl m).isAnon a = m.isAnon a := by
  dsimp only [restoreMallocngRXMem, Memory.isAnon]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · simp only [restoreRxPerm]; split <;> rfl

private theorem restoreRx_perm (mpl : Obj.MultiPlacement) (m : Memory) (a : BitVec 64) :
    (restoreMallocngRXMem mpl m).perm a =
      (m.perm a).map (restoreRxPerm (VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome) := by
  dsimp only [restoreMallocngRXMem, Memory.perm]
  rcases m.cells a with _ | ⟨_ | p, _⟩
  · rfl
  · rfl
  · rcases p with ⟨r, w, x, _, _⟩
    simp only [Option.map, Perm.rwx, restoreRxPerm]
    cases (VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome <;>
      cases r <;> cases w <;> cases x <;> rfl

private theorem restoreRx_perm_props (mpl : Obj.MultiPlacement) (m : Memory) (a : BitVec 64) :
    ((restoreMallocngRXMem mpl m).perm a).r = (m.perm a).r ∧
    ((restoreMallocngRXMem mpl m).perm a).mapped = (m.perm a).mapped ∧
    ((restoreMallocngRXMem mpl m).perm a = some Perm.rw ↔ m.perm a = some Perm.rw) ∧
    ((restoreMallocngRXMem mpl m).perm a = some Perm.protNone ↔ m.perm a = some Perm.protNone) := by
  rw [restoreRx_perm]
  unfold restoreRxPerm Perm.rw Perm.protNone
  generalize (VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome = im
  cases hp : m.perm a with
  | none => simp
  | some p =>
    obtain ⟨hlf, han⟩ := perm_rwx_props hp
    rcases p with ⟨r, w, x, lf, an⟩
    dsimp only at hlf han; subst hlf han
    cases im <;> cases r <;> cases w <;> cases x <;> simp

theorem satisfies_restoreMallocngRX_iff (mpl : Obj.MultiPlacement) (m : Memory) (P : SepProp) :
    (restoreMallocngRXMem mpl m ⊨ P) ↔ (m ⊨ P) := by
  constructor
  · intro hsat
    exact Arm64.Satisfies.of_perm_mono
      (fun a => (restoreRx_read8 mpl m a).symm)
      (fun a hrw => (restoreRx_perm_props mpl m a).2.2.1.mp hrw)
      (fun a hpn => (restoreRx_perm_props mpl m a).2.2.2.mp hpn)
      (fun a hr => (restoreRx_perm_props mpl m a).1.symm.trans hr)
      (fun a hm => (restoreRx_perm_props mpl m a).2.1.symm.trans hm)
      (fun a hlf => (restoreRx_isLazyFree mpl m a).symm.trans hlf)
      (fun a han => (restoreRx_isAnon mpl m a).symm.trans han)
      hsat
  · intro hsat
    exact Arm64.Satisfies.of_perm_mono
      (fun a => restoreRx_read8 mpl m a)
      (fun a hrw => (restoreRx_perm_props mpl m a).2.2.1.mpr hrw)
      (fun a hpn => (restoreRx_perm_props mpl m a).2.2.2.mpr hpn)
      (fun a hr => (restoreRx_perm_props mpl m a).1.trans hr)
      (fun a hm => (restoreRx_perm_props mpl m a).2.1.trans hm)
      (fun a hlf => (restoreRx_isLazyFree mpl m a).trans hlf)
      (fun a han => (restoreRx_isAnon mpl m a).trans han)
      hsat

private theorem restoreRx_countRw (mpl : Obj.MultiPlacement) (m : Memory) :
    ∀ (a : BitVec 64) (n : Nat), (restoreMallocngRXMem mpl m).countRw a n = m.countRw a n
  | _, 0 => rfl
  | a, n + 1 => by
    unfold Memory.countRw Memory.countPerm
    have hrw : ((restoreMallocngRXMem mpl m).perm a == some Perm.rw) = (m.perm a == some Perm.rw) :=
      Bool.eq_iff_iff.mpr (by simp [(restoreRx_perm_props mpl m a).2.2.1])
    simp only [hrw]
    exact congrArg (_ + ·) (restoreRx_countRw mpl m (a + 1#64) n)

private theorem restoreRx_mallocngBudgetPool
    (M : AllocCostModel) (I : MallocngCostModelIface M)
    (γ : GhostName) (mpl : Obj.MultiPlacement) (tp brkStart : BitVec 64)
    (lim : BudgetLimits) (st : M.σ) (s : State) :
    mallocngBudgetPool M I γ mpl tp brkStart lim st (restoreMallocngRXS mpl s) =
      mallocngBudgetPool M I γ mpl tp brkStart lim st s := by
  have hrw : ProofLib.rwBytes (restoreMallocngRXMem mpl s.mem) = ProofLib.rwBytes s.mem := by
    unfold ProofLib.rwBytes
    exact restoreRx_countRw mpl s.mem 0#64 (2 ^ 64)
  have hm : (restoreMallocngRXS mpl s).mem = restoreMallocngRXMem mpl s.mem := by cases s; rfl
  have hpma : (restoreMallocngRXS mpl s).physMemAvail = s.physMemAvail := by cases s; rfl
  have hbs : (restoreMallocngRXS mpl s).brkStart = s.brkStart := by cases s; rfl
  have hbrk : (restoreMallocngRXS mpl s).brk = s.brk := by cases s; rfl
  have htp : (restoreMallocngRXS mpl s).tpidrEl0 = s.tpidrEl0 := by cases s; rfl
  have hpprw : ProofLib.physPlusRw (restoreMallocngRXS mpl s) = ProofLib.physPlusRw s := by
    unfold ProofLib.physPlusRw
    simp only [hpma, hm, hrw]
  have hcov : ∀ staticIvs ivs,
      StaticMappedCover lim staticIvs ivs (restoreMallocngRXMem mpl s.mem) =
        StaticMappedCover lim staticIvs ivs s.mem := by
    intro staticIvs ivs
    apply propext
    unfold StaticMappedCover
    simp only [(restoreRx_perm_props mpl s.mem _).2.1]
  have hinv : ∀ staticIvs ivs,
      mallocngBudgetPoolInv lim staticIvs ivs (restoreMallocngRXS mpl s) =
        mallocngBudgetPoolInv lim staticIvs ivs s := by
    intro staticIvs ivs
    apply propext
    unfold mallocngBudgetPoolInv
    simp only [hm, hcov, hpprw]
  unfold mallocngBudgetPool mallocngBudgetPoolAt MallocngModelEnv
  simp only [hinv, htp, hbs, hbrk]

private theorem codeBlocksPermRX_restoreMallocngRX
    {keep : BitVec 64 → Bool} {mpl : Obj.MultiPlacement} {m : Memory}
    (hcs : CodeBlocksPermStrippedMem keep mpl m) :
    CodeBlocksPermRXMem mpl (restoreMallocngRXMem mpl m) := by
  intro a ha
  rw [restoreRx_perm, hcs a ha]
  cases keep a <;> simp [Option.map, stripCodecPerm, restoreRxPerm, ha, Perm.rx]

theorem satisfies_mallocngPool_restoreRx
    {keep : BitVec 64 → Bool}
    {M : AllocCostModel} {I : MallocngCostModelIface M} {hS : MallocngCostModelSound M I}
    {γ : GhostName} {mpl : Obj.MultiPlacement} {tp brkStart : BitVec 64}
    {lim : BudgetLimits} {st : M.σ} {s : State} {R : SepProp}
    (hsat : s.mem ⊨ (strippedMallocngBudget keep M I hS γ mpl tp brkStart).pool lim st s ∗ R) :
    (restoreMallocngRXS mpl s).mem ⊨
      (mallocngHookRustCliAllocBudget M I hS γ mpl tp brkStart).pool lim st
        (restoreMallocngRXS mpl s) ∗ R := by
  have hm : (restoreMallocngRXS mpl s).mem = restoreMallocngRXMem mpl s.mem := by cases s; rfl
  rw [hm, satisfies_restoreMallocngRX_iff]
  by_cases henf : lim.enforced = true
  · have hcs := pool_stripped_of_satisfies hsat henf
    have hrx : CodeBlocksPermRX mpl (restoreMallocngRXS mpl s) := by
      unfold CodeBlocksPermRX; rw [hm]
      exact codeBlocksPermRX_restoreMallocngRX hcs
    change s.mem ⊨ strippedMallocngPool keep M I γ mpl tp brkStart lim st s ∗ R at hsat
    unfold strippedMallocngPool at hsat
    simp only [henf, ↓reduceIte] at hsat
    change s.mem ⊨ (VerifiedLibraries.mallocngLib.codeRO mpl ∗
        mallocngBudgetPool M I γ mpl tp brkStart lim st (restoreMallocngRXS mpl s) ∗
        ⌜lim.enforced = true → CodeBlocksPermRX mpl (restoreMallocngRXS mpl s)⌝) ∗ R
    have hEq : (lim.enforced = true → CodeBlocksPermRX mpl (restoreMallocngRXS mpl s)) =
        (True → CodeBlocksPermStripped keep mpl s) :=
      propext ⟨fun _ _ => hcs, fun _ _ => hrx⟩
    rw [restoreRx_mallocngBudgetPool, hEq]
    exact hsat
  · change s.mem ⊨ strippedMallocngPool keep M I γ mpl tp brkStart lim st s ∗ R at hsat
    unfold strippedMallocngPool at hsat
    simp only [henf] at hsat
    change s.mem ⊨ mallocngHookBudgetPool M I γ mpl tp brkStart lim st (restoreMallocngRXS mpl s) ∗ R
    unfold mallocngHookBudgetPool at hsat ⊢
    have hEq : (lim.enforced = true → CodeBlocksPermRX mpl (restoreMallocngRXS mpl s)) =
        (lim.enforced = true → CodeBlocksPermRX mpl s) :=
      propext ⟨fun _ h => absurd h henf, fun _ h => absurd h henf⟩
    rw [restoreRx_mallocngBudgetPool, hEq]
    exact hsat

theorem keepsFrozen_offTraj_reStrip
    {keep : BitVec 64 → Bool} {mpl : Obj.MultiPlacement} {m₀ m₁ : Memory}
    (hcs : CodeBlocksPermStrippedMem keep mpl m₀)
    (hkf : (restoreMallocngRXMem mpl m₀).KeepsFrozen m₁) :
    m₀.KeepsFrozen
      (stripCodecMem (fun a => keep a || !(VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome) m₁) := by
  let keepOut := fun a => keep a || !(VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome
  intro a hfr₀
  by_cases hin : (VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome = true
  · have hp_rest : (restoreMallocngRXMem mpl m₀).perm a = some Perm.rx :=
      codeBlocksPermRX_restoreMallocngRX hcs a hin
    have hfr_rest : (restoreMallocngRXMem mpl m₀).Frozen a := by
      unfold Memory.Frozen; rw [hp_rest]; rfl
    obtain ⟨hrd₁, hp₁, hlf₁, han₁⟩ := hkf a hfr_rest
    have hp₁_rx : m₁.perm a = some Perm.rx := hp₁.trans hp_rest
    have hkout : keepOut a = keep a := by dsimp [keepOut]; simp [hin]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [stripCodec_read8, hrd₁, restoreRx_read8]
    · rw [stripCodec_perm, hp₁_rx]
      change Option.map (stripCodecPerm (keepOut a)) (some Perm.rx) = m₀.perm a
      rw [hkout, hcs a hin]; rfl
    · rw [stripCodec_isLazyFree, hlf₁, restoreRx_isLazyFree]
    · rw [stripCodec_isAnon, han₁, restoreRx_isAnon]
  · have hin_f : (VerifiedLibraries.mallocngLib.findCodeBlock mpl a).isSome = false :=
      Bool.eq_false_iff.mpr hin
    have hkout : keepOut a = true := by dsimp [keepOut]; simp [hin_f]
    have hp_rest : (restoreMallocngRXMem mpl m₀).perm a = m₀.perm a := by
      rw [restoreRx_perm, hin_f]; unfold restoreRxPerm; simp [Option.map_id']
    have hfr_rest : (restoreMallocngRXMem mpl m₀).Frozen a := by
      unfold Memory.Frozen at hfr₀ ⊢; rwa [hp_rest]
    obtain ⟨hrd₁, hp₁, hlf₁, han₁⟩ := hkf a hfr_rest
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [stripCodec_read8, hrd₁, restoreRx_read8]
    · rw [stripCodec_perm_of_keep hkout, hp₁, hp_rest]
    · rw [stripCodec_isLazyFree, hlf₁, restoreRx_isLazyFree]
    · rw [stripCodec_isAnon, han₁, restoreRx_isAnon]

private theorem stripCodec_readBytes (keep : BitVec 64 → Bool) (m : Memory) :
    ∀ (src : BitVec 64) (n : Nat), (stripCodecMem keep m).readBytes src n = m.readBytes src n
  | _, 0 => rfl
  | src, n + 1 => by
    simp only [Memory.readBytes, stripCodec_read8, stripCodec_readBytes keep m (src + 1#64) n]

private theorem stripCodec_writeBytes (keep : BitVec 64 → Bool) :
    ∀ (m : Memory) (dst : BitVec 64) (bs : List (BitVec 8)),
      (stripCodecMem keep m).writeBytes dst bs = stripCodecMem keep (m.writeBytes dst bs)
  | m, _, [] => rfl
  | m, dst, b :: bs => by
    simp only [Memory.writeBytes, stripCodec_write8, stripCodec_writeBytes keep (m.write8 dst b)]

theorem hookNoop_stripCodec (keep : BitVec 64 → Bool) (s : State) :
    ProofLib.hookNoop (stripCodecS keep s) = stripCodecS keep (ProofLib.hookNoop s) := by
  unfold ProofLib.hookNoop ProofLib.retHook
  simp only [id_eq, sc_r64, sc_spc]

theorem hookMemcpy_stripCodec (keep : BitVec 64 → Bool) (s : State) :
    ProofLib.hookMemcpy (stripCodecS keep s) = stripCodecS keep (ProofLib.hookMemcpy s) := by
  unfold ProofLib.hookMemcpy ProofLib.retHook
  simp only [sc_r64, sc_mem, stripCodec_readBytes, stripCodec_writeBytes, sc_smem, sc_spc]

theorem rustPanicked_stripCodec (keep : BitVec 64 → Bool) (s : State) :
    Rust.panicked (stripCodecS keep s) = stripCodecS keep (Rust.panicked s) := by
  cases s; rfl

end LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.CodecCalleesFsPlacedBudgetFd
