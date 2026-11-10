/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.ReadWritevFrame

/-!
# Vectored `readv` and `writev` Syscall Preservation and Commutation

Establishes state-map commutation (`RwvMapInv`, `execReadv_map_inv`,
`execWritev_map_inv`, `execReadv_symtab_comm`, `execWritev_symtab_comm`), non-`.Panicked`
status preservation, trace-event exclusion, and `FsState` predicate preservation for
Linux AArch64 `SYS_READV` (`execReadv`) and `SYS_WRITEV` (`execWritev`).
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev

open Arm64 ProofLib

/-! ## State-Map Commutation and Invariant Preservation -/

/-- Closure hypotheses showing that `g : State → State` commutes with all state reads and updates
    performed by `readIovecs`, `execIovLoop`, and `execRwvCommon`, and that `Inv : State → Prop`
    is preserved by register writes, `PC` advance, status updates, and register/`PC` replacement. -/
structure RwvMapInv (g : State → State) (Inv : State → Prop) : Prop where
  readReg64      : ∀ s r, (g s).readReg64 r = s.readReg64 r
  readReg32      : ∀ s r, (g s).readReg32 r = s.readReg32 r
  status         : ∀ s, (g s).status = s.status
  fs             : ∀ s, (g s).fs = s.fs
  allPermR       : ∀ s a n, (g s).mem.allPerm (·.r) a n = s.mem.allPerm (·.r) a n
  canRead        : ∀ s a n, (g s).mem.canRead a n = s.mem.canRead a n
  read64         : ∀ s a, (g s).mem.read64 a = s.mem.read64 a
  writeReg64     : ∀ s r v, (g s).writeReg64 r v = g (s.writeReg64 r v)
  advancePC      : ∀ s, (g s).advancePC = g s.advancePC
  setStatus      : ∀ s st, (g s).setStatus st = g (s.setStatus st)
  regsPc         : ∀ (s s0 : State),
    { g s with regs := (g s0).regs, pc := (g s0).pc } = g { s with regs := s0.regs, pc := s0.pc }
  inv_writeReg64 : ∀ {s} (r : Reg) (v : BitVec 64), Inv s → Inv (s.writeReg64 r v)
  inv_advancePC  : ∀ {s}, Inv s → Inv s.advancePC
  inv_setStatus  : ∀ {s} (st : ExecStatus), Inv s → Inv (s.setStatus st)
  inv_regsPc     : ∀ {s} (regs : RegFile) (pc : BitVec 64),
    Inv s → Inv { s with regs := regs, pc := pc }

theorem RwvMapInv.toRwvFrame {g : State → State} {Inv : State → Prop}
    (hg : RwvMapInv g Inv) : RwvFrame (fun a b => Inv a → Inv b) where
  refl _ h := h
  trans _ _ _ h1 h2 ha := h2 (h1 ha)
  reg _ r v h := hg.inv_writeReg64 r v h
  pc _ h := hg.inv_advancePC h
  status _ st h := hg.inv_setStatus st h
  regsPc _ regs pc h := hg.inv_regsPc regs pc h

private def mapExceptErr {ε ε' α : Type} (f : ε → ε') : Except ε α → Except ε' α
  | .ok a => .ok a
  | .error e => .error (f e)

private theorem readIovecs_map {g : State → State} {Inv : State → Prop}
    (hg : RwvMapInv g Inv) (s : State) :
    ∀ (n : Nat) (vec : BitVec 64),
      readIovecs (g s) vec n = mapExceptErr g (readIovecs s vec n)
  | 0, _ => rfl
  | n + 1, vec => by
    unfold readIovecs
    dsimp only
    rw [hg.allPermR s vec 16, hg.canRead s vec 16, hg.read64 s vec, hg.read64 s (vec + 8#64)]
    cases s.mem.allPerm (·.r) vec 16
    · simp only [Bool.not_false, ↓reduceIte, mapExceptErr]
      rw [hg.writeReg64, hg.advancePC]
    · cases s.mem.canRead vec 16
      · simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, mapExceptErr]
        rw [hg.setStatus]
      · cases (s.mem.read64 (vec + 8#64)).slt 0#64
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
          rw [readIovecs_map hg s n (vec + 16#64)]
          cases readIovecs s (vec + 16#64) n <;> rfl
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, mapExceptErr]
          rw [hg.writeReg64, hg.advancePC]

private theorem execIovLoop_map_inv {g : State → State} {Inv : State → Prop}
    (hg : RwvMapInv g Inv) {step : State → State}
    (hstep : ∀ x, Inv x → step (g x) = g (step x) ∧ Inv (step x)) (s0 : State) :
    ∀ (segs : List (BitVec 64 × BitVec 64)) (s : State) (acc : Nat),
      Inv s →
      execIovLoop step (g s0) (g s) acc segs = g (execIovLoop step s0 s acc segs) ∧
      Inv (execIovLoop step s0 s acc segs)
  | [], s, acc, hs =>
    ⟨by unfold execIovLoop; rw [hg.regsPc s s0, hg.writeReg64, hg.advancePC],
     hg.inv_advancePC (hg.inv_writeReg64 _ _ (hg.inv_regsPc _ _ hs))⟩
  | (base, len) :: rest, s, acc, hs => by
    let x := (({ s with regs := s0.regs, pc := s0.pc }.writeReg64 Reg.x1 base).writeReg64 Reg.x2 len)
    have hx_eq :
        (({ g s with regs := (g s0).regs, pc := (g s0).pc }.writeReg64 Reg.x1 base).writeReg64 Reg.x2 len) =
          g x := by
      dsimp only [x]
      rw [hg.regsPc s s0, hg.writeReg64, hg.writeReg64]
    have hx_inv : Inv x :=
      hg.inv_writeReg64 Reg.x2 len (hg.inv_writeReg64 Reg.x1 base (hg.inv_regsPc s0.regs s0.pc hs))
    obtain ⟨hstep_eq, hs'_inv⟩ := hstep x hx_inv
    have hloop_inv : Inv (execIovLoop step s0 s acc ((base, len) :: rest)) :=
      execIovLoop_preserves hg.toRwvFrame step (fun z hz => (hstep z hz).2) s0
        ((base, len) :: rest) s acc hs
    refine ⟨?_, hloop_inv⟩
    have hrp : { g (step x) with regs := (g s0).regs, pc := (g s0).pc } =
        g { step x with regs := s0.regs, pc := s0.pc } := hg.regsPc (step x) s0
    dsimp only at hrp
    change (
      let s' := step (({ g s with regs := (g s0).regs, pc := (g s0).pc }.writeReg64 Reg.x1 base).writeReg64 Reg.x2 len)
      match s'.status with
      | .Running =>
        let r := s'.readReg64 Reg.x0
        if r.slt 0#64 then
          if acc = 0 then ({ s' with regs := (g s0).regs, pc := (g s0).pc }.writeReg64 Reg.x0 r).advancePC
          else s'.setStatus (.Exception "vectored transfer failed after partial progress")
        else if r.toNat < len.toNat then
          ({ s' with regs := (g s0).regs, pc := (g s0).pc }.writeReg64 Reg.x0
            (BitVec.ofNat 64 (acc + r.toNat))).advancePC
        else execIovLoop step (g s0) s' (acc + r.toNat) rest
      | _ => s') =
      g (
        let s' := step x
        match s'.status with
        | .Running =>
          let r := s'.readReg64 Reg.x0
          if r.slt 0#64 then
            if acc = 0 then ({ s' with regs := s0.regs, pc := s0.pc }.writeReg64 Reg.x0 r).advancePC
            else s'.setStatus (.Exception "vectored transfer failed after partial progress")
          else if r.toNat < len.toNat then
            ({ s' with regs := s0.regs, pc := s0.pc }.writeReg64 Reg.x0
              (BitVec.ofNat 64 (acc + r.toNat))).advancePC
          else execIovLoop step s0 s' (acc + r.toNat) rest
        | _ => s')
    dsimp only
    rw [hx_eq, hstep_eq, hrp, hg.status (step x)]
    cases (step x).status with
    | Running =>
      dsimp only
      rw [hg.readReg64 (step x) Reg.x0]
      by_cases hslt : ((step x).readReg64 Reg.x0).slt 0#64 = true
      · simp only [hslt, ↓reduceIte]
        by_cases hacc : acc = 0
        · simp only [hacc, ↓reduceIte]
          rw [hg.writeReg64, hg.advancePC]
        · simp only [hacc, ↓reduceIte]
          exact hg.setStatus (step x) _
      · simp only [hslt, Bool.false_eq_true, ↓reduceIte]
        by_cases hlt : ((step x).readReg64 Reg.x0).toNat < len.toNat
        · simp only [hlt, ↓reduceIte]
          rw [hg.writeReg64, hg.advancePC]
        · simp only [hlt, ↓reduceIte]
          exact (execIovLoop_map_inv hg hstep s0 rest (step x)
            (acc + ((step x).readReg64 Reg.x0).toNat) hs'_inv).1
    | Halted => rfl
    | Exited _ => rfl
    | Signaled _ => rfl
    | Panicked => rfl
    | OutOfMemory => rfl
    | Exception _ => rfl

theorem execRwvCommon_map_inv {g : State → State} {Inv : State → Prop}
    (hg : RwvMapInv g Inv) {step : State → State}
    (hstep : ∀ x, Inv x → step (g x) = g (step x) ∧ Inv (step x))
    (isRead : Bool) (s : State) (hs : Inv s) :
    execRwvCommon step isRead (g s) = g (execRwvCommon step isRead s) ∧
    Inv (execRwvCommon step isRead s) := by
  have hinv : Inv (execRwvCommon step isRead s) :=
    execRwvCommon_preserves hg.toRwvFrame step (fun z hz => (hstep z hz).2) isRead s hs
  refine ⟨?_, hinv⟩
  have hpArg_eq : (((g s).writeReg64 Reg.x1 0#64).writeReg64 Reg.x2 0#64) =
      g ((s.writeReg64 Reg.x1 0#64).writeReg64 Reg.x2 0#64) := by
    rw [hg.writeReg64, hg.writeReg64]
  have hpArg_inv : Inv ((s.writeReg64 Reg.x1 0#64).writeReg64 Reg.x2 0#64) :=
    hg.inv_writeReg64 Reg.x2 0#64 (hg.inv_writeReg64 Reg.x1 0#64 hs)
  have hprobe_eq : step (g ((s.writeReg64 Reg.x1 0#64).writeReg64 Reg.x2 0#64)) =
      g (step ((s.writeReg64 Reg.x1 0#64).writeReg64 Reg.x2 0#64)) :=
    (hstep _ hpArg_inv).1
  unfold execRwvCommon
  dsimp only
  rw [hg.readReg64 s Reg.x1, hg.readReg32 s Reg.x2, hg.readReg32 s Reg.x0, hg.fs s, hpArg_eq]
  generalize (s.writeReg64 Reg.x1 0#64).writeReg64 Reg.x2 0#64 = pArg at hprobe_eq ⊢
  rw [hprobe_eq, hg.status (step pArg)]
  cases (step pArg).status with
  | Running =>
    dsimp only
    rw [hg.readReg64 (step pArg) Reg.x0]
    by_cases hpr : (((step pArg).readReg64 Reg.x0).slt 0#64 &&
        !(isRead && (step pArg).readReg64 Reg.x0 == -EISDIR)) = true
    · simp only [hpr, ↓reduceIte]
      rw [hg.writeReg64, hg.advancePC]
    · simp only [hpr, Bool.false_eq_true, ↓reduceIte]
      by_cases hc1 : (s.readReg32 Reg.x2).toNat > UIO_MAXIOV
      · simp only [hc1, ↓reduceIte]
        rw [hg.writeReg64, hg.advancePC]
      · simp only [hc1, ↓reduceIte]
        by_cases hc2 : (s.readReg32 Reg.x2).toNat = 0
        · simp only [hc2, ↓reduceIte]
          rw [hg.writeReg64, hg.advancePC]
        · simp only [hc2, ↓reduceIte]
          by_cases hc3 : (s.readReg64 Reg.x1).toNat + 16 * (s.readReg32 Reg.x2).toNat > USER_VA_LIMIT
          · simp only [hc3, ↓reduceIte]
            rw [hg.writeReg64, hg.advancePC]
          · simp only [hc3, ↓reduceIte]
            rw [readIovecs_map hg s (s.readReg32 Reg.x2).toNat (s.readReg64 Reg.x1)]
            cases readIovecs s (s.readReg64 Reg.x1) (s.readReg32 Reg.x2).toNat with
            | error _ => rfl
            | ok segs =>
              dsimp only [mapExceptErr]
              by_cases hc4 : (segs.map fun p => p.2.toNat).sum > MAX_RW_COUNT
              · simp only [hc4, ↓reduceIte]
                exact hg.setStatus s _
              · simp only [hc4, ↓reduceIte]
                by_cases hany : segs.any (fun p => p.1.toNat + p.2.toNat > USER_VA_LIMIT) = true
                · simp only [hany, ↓reduceIte]
                  rw [hg.writeReg64, hg.advancePC]
                · simp only [hany, Bool.false_eq_true, ↓reduceIte]
                  by_cases hc5 : (segs.map fun p => p.2.toNat).sum = 0
                  · simp only [hc5, ↓reduceIte]
                    rw [hg.writeReg64, hg.advancePC]
                  · simp only [hc5, ↓reduceIte]
                    cases s.fs.fds ((s.readReg32 Reg.x0).zeroExtend 64) with
                    | none =>
                      simp only [Bool.false_eq_true, ↓reduceIte]
                      exact (execIovLoop_map_inv hg hstep s segs s 0 hs).1
                    | some desc =>
                      dsimp only
                      by_cases hpos : (desc.kind == .localFile &&
                          decide (desc.offset + (segs.map fun p => p.2.toNat).sum > MAX_LFS_FILESIZE)) = true
                      · simp only [hpos, ↓reduceIte]
                        rw [hg.writeReg64, hg.advancePC]
                      · simp only [hpos, Bool.false_eq_true, ↓reduceIte]
                        exact (execIovLoop_map_inv hg hstep s segs s 0 hs).1
  | Halted => exact hg.setStatus s _
  | Exited _ => exact hg.setStatus s _
  | Signaled _ => exact hg.setStatus s _
  | Panicked => exact hg.setStatus s _
  | OutOfMemory => exact hg.setStatus s _
  | Exception _ => exact hg.setStatus s _

theorem execReadv_map_inv {g : State → State} {Inv : State → Prop}
    (hg : RwvMapInv g Inv)
    (hRead : ∀ x, Inv x → execRead (g x) = g (execRead x) ∧ Inv (execRead x))
    (s : State) (hs : Inv s) :
    execReadv (g s) = g (execReadv s) ∧ Inv (execReadv s) :=
  execRwvCommon_map_inv hg hRead true s hs

theorem execWritev_map_inv {g : State → State} {Inv : State → Prop}
    (hg : RwvMapInv g Inv)
    (hWrite : ∀ x, Inv x → execWrite (g x) = g (execWrite x) ∧ Inv (execWrite x))
    (s : State) (hs : Inv s) :
    execWritev (g s) = g (execWritev s) ∧ Inv (execWritev s) :=
  execRwvCommon_map_inv hg hWrite false s hs

theorem rwvMapInv_symtab (t : String → String → Option (BitVec 64)) :
    RwvMapInv (fun s => { s with symtab := t }) (fun _ => True) where
  readReg64 s _ := by cases s; rfl
  readReg32 s _ := by cases s; rfl
  status s := by cases s; rfl
  fs s := by cases s; rfl
  allPermR s _ _ := by cases s; rfl
  canRead s _ _ := by cases s; rfl
  read64 s _ := by cases s; rfl
  writeReg64 s r _ := by cases s; cases r <;> rfl
  advancePC s := by cases s; rfl
  setStatus s _ := by cases s; rfl
  regsPc s s0 := by cases s; cases s0; rfl
  inv_writeReg64 _ _ _ := trivial
  inv_advancePC _ := trivial
  inv_setStatus _ _ := trivial
  inv_regsPc _ _ _ := trivial

theorem execReadv_symtab_comm (t : String → String → Option (BitVec 64))
    (hRead : ∀ x : State, execRead { x with symtab := t } = { execRead x with symtab := t })
    (s : State) :
    execReadv { s with symtab := t } = { execReadv s with symtab := t } :=
  (execReadv_map_inv (rwvMapInv_symtab t) (fun x _ => ⟨hRead x, trivial⟩) s trivial).1

theorem execWritev_symtab_comm (t : String → String → Option (BitVec 64))
    (hWrite : ∀ x : State, execWrite { x with symtab := t } = { execWrite x with symtab := t })
    (s : State) :
    execWritev { s with symtab := t } = { execWritev s with symtab := t } :=
  (execWritev_map_inv (rwvMapInv_symtab t) (fun x _ => ⟨hWrite x, trivial⟩) s trivial).1

/-! ## Non-`.Panicked` Status Preservation -/

private theorem readIovecs_status_ne_panicked {s : State} (hs : s.status ≠ .Panicked) :
    ∀ (n : Nat) (vec : BitVec 64) (s' : State),
      readIovecs s vec n = .error s' → s'.status ≠ .Panicked := by
  intro n
  induction n with
  | zero => intro vec s' h; simp [readIovecs] at h
  | succ n ih =>
    intro vec s' h
    simp only [readIovecs] at h
    split at h
    · cases h; exact hs
    · split at h
      · cases h; nofun
      · split at h
        · cases h; exact hs
        · cases hrest : readIovecs s (vec + 16#64) n with
          | error e =>
            rw [hrest] at h
            simp only [Except.map] at h
            cases h
            exact ih _ _ hrest
          | ok l =>
            rw [hrest] at h
            simp [Except.map] at h

private theorem execIovLoop_status_ne_panicked {step : State → State}
    (hstep : ∀ x, x.status ≠ .Panicked → (step x).status ≠ .Panicked) (s0 : State) :
    ∀ (segs : List (BitVec 64 × BitVec 64)) (s : State) (acc : Nat),
      s.status ≠ .Panicked → (execIovLoop step s0 s acc segs).status ≠ .Panicked := by
  intro segs
  induction segs with
  | nil => intro s acc hs; exact hs
  | cons seg rest ih =>
    intro s acc hs
    obtain ⟨base, len⟩ := seg
    have hs' :
        (step (({ s with regs := s0.regs, pc := s0.pc }.writeReg64 Reg.x1 base).writeReg64 Reg.x2 len)).status ≠
          .Panicked :=
      hstep _ hs
    simp only [execIovLoop]
    split
    · split
      · split
        · exact hs'
        · nofun
      · split
        · exact hs'
        · exact ih _ _ hs'
    · exact hs'

theorem execRwvCommon_status_ne_panicked {step : State → State}
    (hstep : ∀ x, x.status ≠ .Panicked → (step x).status ≠ .Panicked)
    (isRead : Bool) (s : State) (hs : s.status ≠ .Panicked) :
    (execRwvCommon step isRead s).status ≠ .Panicked := by
  have hprobe : (step ((s.writeReg64 Reg.x1 0#64).writeReg64 Reg.x2 0#64)).status ≠ .Panicked :=
    hstep _ hs
  unfold execRwvCommon
  dsimp only
  split
  · split
    · exact hs
    · split
      · exact hs
      · split
        · exact hs
        · split
          · exact hs
          · split
            · rename_i s' h
              exact readIovecs_status_ne_panicked hs _ _ _ h
            · rename_i segs _
              split
              · intro hc; cases hc
              · split
                · exact hs
                · split
                  · exact hs
                  · split
                    · split
                      · exact hs
                      · exact execIovLoop_status_ne_panicked hstep s segs s 0 hs
                    · exact execIovLoop_status_ne_panicked hstep s segs s 0 hs
  · exact hprobe

theorem execReadv_status_ne_panicked
    (hRead : ∀ x : State, x.status ≠ .Panicked → (execRead x).status ≠ .Panicked)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execReadv s).status ≠ .Panicked :=
  execRwvCommon_status_ne_panicked hRead true s hs

theorem execWritev_status_ne_panicked
    (hWrite : ∀ x : State, x.status ≠ .Panicked → (execWrite x).status ≠ .Panicked)
    {s : State} (hs : s.status ≠ .Panicked) :
    (execWritev s).status ≠ .Panicked :=
  execRwvCommon_status_ne_panicked hWrite false s hs

/-! ## Trace Event Exclusion -/

private theorem writeReg64_trace (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).trace = s.trace := by
  cases s; cases r <;> rfl

private theorem advancePC_trace (s : State) : s.advancePC.trace = s.trace := by
  cases s; rfl

private theorem setStatus_trace (s : State) (st : ExecStatus) : (s.setStatus st).trace = s.trace := by
  cases s; rfl

private theorem regsPc_trace (s : State) (regs : RegFile) (pc : BitVec 64) :
    ({ s with regs := regs, pc := pc } : State).trace = s.trace := by
  cases s; rfl

theorem rwvFrame_traceNotMem (ev : TraceEvent) :
    RwvFrame (fun a b => ev ∉ a.trace → ev ∉ b.trace) where
  refl _ h := h
  trans _ _ _ h1 h2 ha := h2 (h1 ha)
  reg s r v h := by rw [writeReg64_trace s r v]; exact h
  pc s h := by rw [advancePC_trace s]; exact h
  status s st h := by rw [setStatus_trace s st]; exact h
  regsPc s regs pc h := by rw [regsPc_trace s regs pc]; exact h

theorem execReadv_trace_not_mem {ev : TraceEvent}
    (hRead : ∀ x : State, ev ∉ x.trace → ev ∉ (execRead x).trace)
    {s : State} (hs : ev ∉ s.trace) :
    ev ∉ (execReadv s).trace :=
  execReadv_preserves (rwvFrame_traceNotMem ev) hRead s hs

theorem execWritev_trace_not_mem {ev : TraceEvent}
    (hWrite : ∀ x : State, ev ∉ x.trace → ev ∉ (execWrite x).trace)
    {s : State} (hs : ev ∉ s.trace) :
    ev ∉ (execWritev s).trace :=
  execWritev_preserves (rwvFrame_traceNotMem ev) hWrite s hs

private theorem traceDeltaFree_of_eq {ev : TraceEvent} {a b : State} (h : b.trace = a.trace) :
    ∃ d : List TraceEvent, b.trace = a.trace ++ d ∧ ev ∉ d :=
  ⟨[], by simp [h]⟩

theorem rwvFrame_traceDeltaFree (ev : TraceEvent) :
    RwvFrame (fun a b => ∃ d : List TraceEvent, b.trace = a.trace ++ d ∧ ev ∉ d) where
  refl _ := traceDeltaFree_of_eq rfl
  trans _ _ _ h01 h12 := by
    rcases h01 with ⟨d1, hd1, hn1⟩
    rcases h12 with ⟨d2, hd2, hn2⟩
    refine ⟨d1 ++ d2, by rw [hd2, hd1, List.append_assoc], ?_⟩
    rw [List.mem_append, not_or]
    exact ⟨hn1, hn2⟩
  reg s r v := traceDeltaFree_of_eq (writeReg64_trace s r v)
  pc s := traceDeltaFree_of_eq (advancePC_trace s)
  status s st := traceDeltaFree_of_eq (setStatus_trace s st)
  regsPc s regs pc := traceDeltaFree_of_eq (regsPc_trace s regs pc)

theorem execReadv_traceDeltaFree {ev : TraceEvent}
    (hRead : ∀ x : State, ∃ d : List TraceEvent, (execRead x).trace = x.trace ++ d ∧ ev ∉ d)
    (s : State) :
    ∃ d : List TraceEvent, (execReadv s).trace = s.trace ++ d ∧ ev ∉ d :=
  execReadv_preserves (rwvFrame_traceDeltaFree ev) hRead s

theorem execWritev_traceDeltaFree {ev : TraceEvent}
    (hWrite : ∀ x : State, ∃ d : List TraceEvent, (execWrite x).trace = x.trace ++ d ∧ ev ∉ d)
    (s : State) :
    ∃ d : List TraceEvent, (execWritev s).trace = s.trace ++ d ∧ ev ∉ d :=
  execWritev_preserves (rwvFrame_traceDeltaFree ev) hWrite s

/-! ## `FsState` Predicate Preservation -/

private theorem writeReg64_fs (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).fs = s.fs := by
  cases s; cases r <;> rfl

private theorem advancePC_fs (s : State) : s.advancePC.fs = s.fs := by
  cases s; rfl

private theorem setStatus_fs (s : State) (st : ExecStatus) : (s.setStatus st).fs = s.fs := by
  cases s; rfl

private theorem regsPc_fs (s : State) (regs : RegFile) (pc : BitVec 64) :
    ({ s with regs := regs, pc := pc } : State).fs = s.fs := by
  cases s; rfl

theorem rwvFrame_fsPred (P : FsState → Prop) :
    RwvFrame (fun a b => P a.fs → P b.fs) where
  refl _ h := h
  trans _ _ _ h1 h2 ha := h2 (h1 ha)
  reg s r v h := by rw [writeReg64_fs s r v]; exact h
  pc s h := by rw [advancePC_fs s]; exact h
  status s st h := by rw [setStatus_fs s st]; exact h
  regsPc s regs pc h := by rw [regsPc_fs s regs pc]; exact h

theorem execReadv_fs_preserves {P : FsState → Prop}
    (hRead : ∀ x : State, P x.fs → P (execRead x).fs)
    {s : State} (hs : P s.fs) :
    P (execReadv s).fs :=
  execReadv_preserves (rwvFrame_fsPred P) hRead s hs

theorem execWritev_fs_preserves {P : FsState → Prop}
    (hWrite : ∀ x : State, P x.fs → P (execWrite x).fs)
    {s : State} (hs : P s.fs) :
    P (execWritev s).fs :=
  execWritev_preserves (rwvFrame_fsPred P) hWrite s hs

end LibsignalBinary.Proofs.SpecLemmas.SyscallReadWritev
