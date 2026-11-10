/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.Hooks
public import LibsignalBinary.Proofs.E2E.Run.NoSvcCommon

/-!
# Shared `tpidr_el0` and Executable-Region Step Invariant

Defines the executable-memory bound `ExecOnlyIn` and step invariant `TpidrInv` preserving
`tpidr_el0` and `ExecOnlyIn` across machine instructions and external hooks in the E2E binary.
-/

@[expose] public section

namespace CryptoVerification.E2E.Bin

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open ProofLib.ProgramReflection

/-- Every executable byte (`(m.perm a).x = true`) lies inside `[prog.base, prog.base + prog.code.length)`. -/
def ExecOnlyIn (prog : Program) (m : Memory) : Prop :=
  ∀ a, (m.perm a).x → (a - prog.base).toNat < prog.code.length

/-- Step invariant preserving `tpidrEl0` and `ExecOnlyIn` under `CodeLoaded`. -/
def TpidrInv (prog : Program) : Prop :=
  ∀ s1 s2, prog.CodeLoaded s1.mem → ExecOnlyIn prog s1.mem → Step prog s1 s2 →
    s2.tpidrEl0 = s1.tpidrEl0 ∧ ExecOnlyIn prog s2.mem

theorem execOnlyIn_congr {p1 p2 : Program} {m : Memory}
    (hb : p1.base = p2.base) (hc : p1.code.length = p2.code.length) :
    ExecOnlyIn p1 m ↔ ExecOnlyIn p2 m := by
  unfold ExecOnlyIn
  rw [hb, hc]

@[simp] theorem execOnlyIn_tripleRatchetProg (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (m : Memory) :
    ExecOnlyIn (tripleRatchetProg img C ctl abs) m = ExecOnlyIn (Program.ofImage img) m :=
  rfl

theorem execOnlyIn_ofImage_of_inRegion {img : Obj.Image} {m : Memory}
    (h : ∀ a, (m.perm a).x = true → InRegion img.base img.code.length a) :
    ExecOnlyIn (Program.ofImage img) m :=
  h

theorem execOnlyIn_tripleRatchetProgAt_iff {img : Obj.Image} (hloads : Obj.Loads libsignalSessionImage img)
    (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) (m : Memory) :
    ExecOnlyIn (tripleRatchetProgAt img.base C ctl abs) m ↔ ExecOnlyIn (Program.ofImage img) m := by
  rw [← tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact Iff.rfl

theorem codeLoaded_tripleRatchetProg_of_frozenLoaded {img : Obj.Image} {s : State}
    (hF : img.FrozenLoaded s) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProg img C ctl abs).CodeLoaded s.mem := by
  have h0 : (Program.ofImage img).CodeLoaded s.mem := (Obj.Image.frozenLoaded_iff.1 hF).1
  rw [Program.codeLoaded_iff] at h0 ⊢; exact h0

theorem codeLoaded_tripleRatchetProgAt_of_frozenLoaded {img : Obj.Image} {s : State}
    (hloads : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s)
    (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s.mem := by
  rw [← tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact codeLoaded_tripleRatchetProg_of_frozenLoaded hF C ctl abs

theorem Steps.tpidr_execOnly {prog : Program} (hInv : TpidrInv prog)
    {s1 s2 : State} (hL : prog.CodeLoaded s1.mem) (hEx : ExecOnlyIn prog s1.mem)
    (hst : Steps prog s1 s2) :
    s2.tpidrEl0 = s1.tpidrEl0 ∧ ExecOnlyIn prog s2.mem := by
  induction hst with
  | refl => exact ⟨rfl, hEx⟩
  | step h1 _ ih =>
    have ⟨htp1, hEx1⟩ := hInv _ _ hL hEx h1
    have ⟨htp2, hEx2⟩ := ih (h1.codeLoaded hL) hEx1
    exact ⟨htp2.trans htp1, hEx2⟩

theorem Steps.tpidrEl0_eq {prog : Program} (hInv : TpidrInv prog)
    {s1 s2 : State} (hL : prog.CodeLoaded s1.mem) (hEx : ExecOnlyIn prog s1.mem)
    (hst : Steps prog s1 s2) :
    s2.tpidrEl0 = s1.tpidrEl0 :=
  (Steps.tpidr_execOnly hInv hL hEx hst).1

theorem Steps.execOnlyIn {prog : Program} (hInv : TpidrInv prog)
    {s1 s2 : State} (hL : prog.CodeLoaded s1.mem) (hEx : ExecOnlyIn prog s1.mem)
    (hst : Steps prog s1 s2) :
    ExecOnlyIn prog s2.mem :=
  (Steps.tpidr_execOnly hInv hL hEx hst).2

theorem segExit_of_subroutine_ok_tpidr {α β : Type} {prog : Program} {spec : Spec α} {g : α} {R : SepProp}
    {calleeEntry : BitVec 64} {calleeSpec : Spec β} {gc : β} {Rc : SepProp}
    {s0 s1 : State} {next : State → Prop}
    (hInv : TpidrInv prog)
    (hEx : ExecOnlyIn prog s1.mem)
    (hCallee : subroutine_ok prog calleeEntry calleeSpec)
    (hpc : s1.pc = calleeEntry)
    (hrun : s1.status = .Running)
    (hal : s1.spAligned = true)
    (hpre : s1.mem ⊨ calleeSpec.pre gc s1 ∗ Rc)
    (hpost : ∀ s2, Steps prog s1 s2 → s2.tpidrEl0 = s1.tpidrEl0 → ExecOnlyIn prog s2.mem →
      (Returned s1 s2 ∧ CallingConventionPreserved s1 s2 ∧
       s2.mem ⊨ calleeSpec.post gc s1 s2 ∗ Rc) →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hpanic : ∀ s2, s2.status = .Panicked → s2.mem ⊨ calleeSpec.onPanic gc s1 s2 ∗ Rc →
      next s2 ∨ SubroutineOutcome spec g R s0 s2)
    (hexit : ∀ code s2, s2.mem ⊨ calleeSpec.onExit gc code s1 s2 ∗ Rc →
      s2.mem ⊨ spec.onExit g code s0 s2 ∗ R)
    (hoom : ∀ s2, s2.status = .OutOfMemory → s2.mem ⊨ calleeSpec.onOom gc s1 s2 ∗ Rc →
      next s2 ∨ SubroutineOutcome spec g R s0 s2 := by
      intro _ _ h; exact (not_satisfies_false_sepConj h).elim) :
    prog.CodeLoaded s1.mem →
      ∃ s2, Steps prog s1 s2 ∧ (next s2 ∨ SubroutineOutcome spec g R s0 s2) := by
  intro hL
  obtain ⟨s2, hst, hout, -⟩ := hCallee.no_fault_before_outcome gc Rc s1 hpc hrun hpre hal hL
  refine ⟨s2, hst, ?_⟩
  rcases hout with hok | ⟨hpan, hmp⟩ | ⟨code, hex, hme⟩ | ⟨hoom_st, hmo⟩
  · have ⟨htp, hEx2⟩ := Steps.tpidr_execOnly hInv hL hEx hst
    exact hpost s2 hst htp hEx2 hok
  · exact hpanic s2 hpan hmp
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨code, hex, hexit code s2 hme⟩)))
  · exact hoom s2 hoom_st hmo

namespace TpidrAux

def isMsrOp (i : Instr) : Bool := i.isMsr

def isMsrOpt : Option Instr → Bool
  | some i => isMsrOp i
  | none => false

theorem execInst_tpidrEl0 {inst : Instr} (h : isMsrOp inst = false) (s : State) :
    (execInst inst s).tpidrEl0 = s.tpidrEl0 :=
  Arm64.execInst_tpidrEl0_of_not_isMsr h s

/-- `prog.evalInst` preserves `tpidr_el0` whenever `isMsrOp inst = false`. -/
theorem evalInst_tpidrEl0 {prog : Program} {inst : Instr} (h : isMsrOp inst = false)
    (s : State) : (prog.evalInst inst s).tpidrEl0 = s.tpidrEl0 := by
  cases hsvc : inst.isSvc0
  · rw [evalInst_eq_execInst_of_not_isSvc0 hsvc]; exact execInst_tpidrEl0 h s
  · cases inst with
    | system isHint imm =>
      cases isHint
      · have heq : imm = 0#16 := by simpa [Instr.isSvc0] using hsvc
        subst heq
        exact evalSvc_tpidrEl0 _ s
      · simp [Instr.isSvc0] at hsvc
    | _ => simp [Instr.isSvc0] at hsvc

theorem isMsrOpt_decode_eq_false_of_not_msr (w : BitVec 32)
    (h : isMsrWord w = false) :
    isMsrOpt (decode w) = false := by
  cases hd : decode w with
  | none => rfl
  | some i => exact Arm64.decode_not_isMsr hd h

theorem msr_mask_eq_false_of_bytes {b0 b1 b2 b3 : BitVec 8}
    (h : (b3 == 0xd5#8 && (b2 &&& 0xf0#8) == 0x10#8) = false) :
    isMsrWord (b3 ++ b2 ++ b1 ++ b0) = false := by
  unfold isMsrWord
  bv_bits

def noMsrTree : WordTree → Bool
  | .empty => true
  | .leaf _ _ b2 b3 => !(b3 == 0xd5#8 && (b2 &&& 0xf0#8) == 0x10#8)
  | .node _ l r => noMsrTree l && noMsrTree r

private theorem drop_all_toBytesAux :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)),
      t.checkSize? = some n →
      (t.toBytesAux acc).drop (4 * n) = acc
  | .empty, _, acc, h => by cases h; rfl
  | .leaf _ _ _ _, _, acc, h => by cases h; rfl
  | .node lw l r, _, acc, h => by
    simp only [WordTree.checkSize?] at h
    split at h <;> try contradiction
    rename_i nl nr hl hr
    split at h <;> try contradiction
    simp only [Option.some.injEq] at h; subst h
    have hadd : 4 * (nl + nr) = 4 * nl + 4 * nr := Nat.mul_add 4 nl nr
    rw [WordTree.toBytesAux, hadd, ← List.drop_drop,
        drop_all_toBytesAux l (r.toBytesAux acc) hl,
        drop_all_toBytesAux r acc hr]

theorem noMsrTree_drop_toBytesAux :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)) (j : Nat),
      t.checkSize? = some n →
      noMsrTree t = true →
      j < n →
      ∃ b0 b1 b2 b3 rest,
        (t.toBytesAux acc).drop (4 * j) = b0 :: b1 :: b2 :: b3 :: rest ∧
        (b3 == 0xd5#8 && (b2 &&& 0xf0#8) == 0x10#8) = false
  | .empty, _, _, _, hsz, _, hj => by cases hsz; omega
  | .leaf b0 b1 b2 b3, _, acc, j, hsz, hno, hj => by
    cases hsz
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [noMsrTree, Bool.not_eq_true'] at hno
    exact ⟨b0, b1, b2, b3, acc, rfl, hno⟩
  | .node lw l r, _, acc, j, hsz, hno, hj => by
    simp only [WordTree.checkSize?] at hsz
    split at hsz <;> try contradiction
    rename_i nl nr hl hr
    split at hsz <;> try contradiction
    rename_i hlw
    have hlw_eq : lw = nl := beq_iff_eq.mp hlw
    subst hlw_eq
    simp only [Option.some.injEq] at hsz; subst hsz
    simp only [noMsrTree, Bool.and_eq_true] at hno
    by_cases hlt : j < lw
    · exact noMsrTree_drop_toBytesAux l (r.toBytesAux acc) j hl hno.1 hlt
    · have hj_eq : 4 * j = 4 * lw + 4 * (j - lw) := by omega
      rw [WordTree.toBytesAux, hj_eq, ← List.drop_drop,
          drop_all_toBytesAux l (r.toBytesAux acc) hl]
      exact noMsrTree_drop_toBytesAux r acc (j - lw) hr hno.2 (by omega)

set_option maxRecDepth 2000000 in
theorem libsignalSessionCode_tree_noMsr :
    noMsrTree libsignalSessionCode_tree = true := by
  rfl_kernel

theorem readWordOff_bind_decode_noMsr {prog : Program} {t : WordTree} {n : Nat}
    (hcode : prog.code = t.toBytesAux [])
    (hsz : t.checkSize? = some n)
    (hno : noMsrTree t = true)
    (off : Nat) (hoff : off % 4 = 0) (hlt : off + 4 ≤ 4 * n) :
    isMsrOpt ((prog.readWordOff off).bind decode) = false := by
  have hj_lt : off / 4 < n := by omega
  have hoff_eq : off = 4 * (off / 4) := by omega
  obtain ⟨b0, b1, b2, b3, rest, hdrop, hbytes⟩ :=
    noMsrTree_drop_toBytesAux t [] (off / 4) hsz hno hj_lt
  unfold Program.readWordOff
  simp only [hoff, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hcode, hoff_eq, hdrop]
  simp only [Option.bind_some]
  exact isMsrOpt_decode_eq_false_of_not_msr (b3 ++ b2 ++ b1 ++ b0)
    (msr_mask_eq_false_of_bytes hbytes)

theorem fetchMem_noMsr_of_forall_readWordOff {prog : Program} {m : Memory}
    (hL : prog.CodeLoaded m)
    (hlen4 : prog.code.length % 4 = 0)
    (hx : ∀ a, (m.perm a).x = true → InRegion prog.base prog.code.length a)
    (hno : ∀ off, off % 4 = 0 → off + 4 ≤ prog.code.length →
      isMsrOpt ((prog.readWordOff off).bind decode) = false)
    (pc : BitVec 64) :
    isMsrOpt (prog.fetchMem m pc) = false := by
  unfold Program.fetchMem
  split
  · rfl
  split
  · rfl
  rename_i h_align
  split
  · rfl
  rename_i h_exec
  simp only [Bool.not_eq_true'] at h_exec
  have h_exec' : m.canExec pc 4 = true := Bool.eq_true_of_not_eq_false h_exec
  have h_al : pc.toNat % 4 = 0 := by omega
  have hx0 : (m.perm pc).x = true := by
    unfold Memory.canExec Memory.allPerm at h_exec'
    simp only [Bool.and_eq_true] at h_exec'
    exact h_exec'.1
  have hin : InRegion prog.base prog.code.length pc := hx pc hx0
  unfold InRegion at hin
  obtain ⟨hbase_al, hno_wrap, hcode⟩ := Program.codeLoaded_iff.1 hL
  generalize hoff : (pc - prog.base).toNat = off
  rw [hoff] at hin
  have hpc_eq : pc = prog.base + BitVec.ofNat 64 off := by
    rw [← hoff, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_arith
  have hpc_nat : pc.toNat = prog.base.toNat + off := by
    rw [hpc_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hoff_al : off % 4 = 0 := by omega
  have hoff_lt : off + 4 ≤ prog.code.length := by omega
  have hno_inst := hno off hoff_al hoff_lt
  have hb_k : ∀ k (hk : k < 4),
      m.read8 (pc + BitVec.ofNat 64 k) = prog.code[off + k]'(by omega) := by
    intro k hk
    have e : pc + BitVec.ofNat 64 k = prog.base + BitVec.ofNat 64 (off + k) := by
      rw [hpc_eq, BitVec.ofNat_add, BitVec.add_assoc]
    rw [e]
    exact (hcode (off + k) (by omega)).1
  unfold Program.readWordOff at hno_inst
  simp only [hoff_al, ne_eq, not_true_eq_false, ↓reduceIte] at hno_inst
  rcases hdrop : prog.code.drop off with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, tl⟩⟩⟩⟩
  · exfalso; have := congrArg List.length hdrop; simp at this; omega
  · exfalso; have := congrArg List.length hdrop; simp at this; omega
  · exfalso; have := congrArg List.length hdrop; simp at this; omega
  · exfalso; have := congrArg List.length hdrop; simp at this; omega
  · rw [hdrop] at hno_inst
    simp only [Option.bind_some] at hno_inst
    have hget : ∀ k (hk : k < 4),
        prog.code[off + k]'(by omega) = (b0 :: b1 :: b2 :: b3 :: tl)[k]'(by simp; omega) := by
      intro k hk
      simp only [← hdrop, List.getElem_drop]
    have hr : m.read32 pc = b3 ++ b2 ++ b1 ++ b0 := by
      have h0 := hb_k 0 (by omega); have h1 := hb_k 1 (by omega)
      have h2 := hb_k 2 (by omega); have h3 := hb_k 3 (by omega)
      have g0 := hget 0 (by omega); have g1 := hget 1 (by omega)
      have g2 := hget 2 (by omega); have g3 := hget 3 (by omega)
      simp only [Memory.read32]
      simp only [List.getElem_cons_succ, List.getElem_cons_zero] at g0 g1 g2 g3
      rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, h0, g0,
        show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, h1, g1,
        show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, h2, g2,
        show (3#64 : BitVec 64) = BitVec.ofNat 64 3 from rfl, h3, g3]
    rw [hr]
    exact hno_inst

theorem fetchMem_ne_svc0_of_loads {img : Obj.Image} (hloads : Obj.Loads libsignalSessionImage img)
    {prog : Program} (hc : prog.code = img.code)
    {m : Memory} (hL : prog.CodeLoaded m) (hx : ExecOnlyIn prog m) (pc : BitVec 64) :
    prog.fetchMem m pc ≠ some Run.svc0 := by
  have hcode_eq : prog.code = libsignalSessionCode_tree.toBytesAux [] := by
    rw [hc, (ProofLib.ObjectLoad.Loads.canonical hloads).1]
    exact libsignalSessionCode_code_eq
  have hcode_len : prog.code.length = num% (ls_field% codeLen) := by
    rw [hc, (ProofLib.ObjectLoad.Loads.canonical hloads).1]
    exact Run.NoSvcAux.libsignalSessionImage_code_length
  refine Run.NoSvcAux.fetchMem_ne_of_forall_readWordOff hL (by omega) hx
    (fun off hoff hlt => ?_) pc
  exact Run.NoSvcAux.readWordOff_bind_decode_ne_svc0 hcode_eq
    libsignalSessionCode_tree_size Run.NoSvcAux.libsignalSessionCode_tree_noSvc0
    off hoff (by omega)

theorem fetchMem_noMsr_of_loads {img : Obj.Image} (hloads : Obj.Loads libsignalSessionImage img)
    {prog : Program} (hc : prog.code = img.code)
    {m : Memory} (hL : prog.CodeLoaded m) (hx : ExecOnlyIn prog m) (pc : BitVec 64) :
    isMsrOpt (prog.fetchMem m pc) = false := by
  have hcode_eq : prog.code = libsignalSessionCode_tree.toBytesAux [] := by
    rw [hc, (ProofLib.ObjectLoad.Loads.canonical hloads).1]
    exact libsignalSessionCode_code_eq
  have hcode_len : prog.code.length = num% (ls_field% codeLen) := by
    rw [hc, (ProofLib.ObjectLoad.Loads.canonical hloads).1]
    exact Run.NoSvcAux.libsignalSessionImage_code_length
  refine fetchMem_noMsr_of_forall_readWordOff hL (by omega) hx
    (fun off hoff hlt => ?_) pc
  exact readWordOff_bind_decode_noMsr hcode_eq
    libsignalSessionCode_tree_size libsignalSessionCode_tree_noMsr
    off hoff (by omega)

/-! ### Hook `tpidrEl0` and `mem.perm` preservation -/

@[local simp] theorem tpidrEl0_retHook (f : State → State) (s : State) :
    (retHook f s).tpidrEl0 = (f s).tpidrEl0 := by unfold retHook; cases (f s); rfl

@[local simp] theorem mem_retHook (f : State → State) (s : State) :
    (retHook f s).mem = (f s).mem := rfl

@[local simp] theorem tpidrEl0_writeReg64 (s : State) (r : Reg) (v : BitVec 64) :
    (s.writeReg64 r v).tpidrEl0 = s.tpidrEl0 := by cases s; cases r <;> rfl

@[local simp] theorem tpidrEl0_setMem (s : State) (m : Memory) :
    (s.setMem m).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp] theorem tpidrEl0_setPC (s : State) (pc : BitVec 64) :
    (s.setPC pc).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp] theorem tpidrEl0_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp] theorem mem_setStatus (s : State) (st : ExecStatus) :
    (s.setStatus st).mem = s.mem := rfl

@[local simp] theorem tpidrEl0_hookNoop (s : State) :
    (hookNoop s).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp] theorem mem_hookNoop (s : State) :
    (hookNoop s).mem = s.mem := rfl

@[local simp] theorem tpidrEl0_panicked (s : State) :
    (Rust.panicked s).tpidrEl0 = s.tpidrEl0 := by cases s; rfl

@[local simp] theorem mem_panicked (s : State) :
    (Rust.panicked s).mem = s.mem := rfl

theorem tpidrSafe_of_tpidr_perm {f : State → State}
    (htp : ∀ s, (f s).tpidrEl0 = s.tpidrEl0)
    (hperm : ∀ s, (f s).mem.perm = s.mem.perm) (s : State) :
    (f s).tpidrEl0 = s.tpidrEl0 ∧ ∀ a, ((f s).mem.perm a).x → (s.mem.perm a).x := by
  refine ⟨htp s, fun a hx => ?_⟩
  rwa [hperm s] at hx

theorem sessionExterns_tpidrSafe (C : Crypto) (name : String) (f : State → State)
    (hf : CryptoVerification.LibsignalSession.sessionExterns C.F (fun _ => none) name = some f)
    (s : State) :
    (f s).tpidrEl0 = s.tpidrEl0 ∧ ∀ a, ((f s).mem.perm a).x → (s.mem.perm a).x := by
  unfold CryptoVerification.LibsignalSession.sessionExterns at hf
  split_ifs at hf with h1 h2 h3 h4 h5 h6 h7 h8 <;> simp only [Option.some.injEq] at hf
  · subst hf
    exact tpidrSafe_of_tpidr_perm
      (fun s => by simp [LibsignalHmac.compress256Hook, LibsignalAesCbc.returnToLinkRegister])
      (fun s => by simp [LibsignalHmac.compress256Hook, LibsignalAesCbc.returnToLinkRegister]) s
  · subst hf
    exact tpidrSafe_of_tpidr_perm
      (fun s => by simp [hookMemcpy])
      (fun s => by simp [hookMemcpy]) s
  · subst hf
    exact tpidrSafe_of_tpidr_perm
      (fun s => by simp [hookMemmove, hookMemcpy])
      (fun s => by simp [hookMemmove, hookMemcpy]) s
  · subst hf
    exact tpidrSafe_of_tpidr_perm
      (fun s => by simp [hookMemset])
      (fun s => by simp [hookMemset]) s
  · subst hf
    exact tpidrSafe_of_tpidr_perm (fun _ => rfl) (fun _ => rfl) s
  · subst hf
    exact tpidrSafe_of_tpidr_perm (fun _ => rfl) (fun _ => rfl) s
  · subst hf
    exact tpidrSafe_of_tpidr_perm (fun _ => rfl) (fun _ => rfl) s

theorem decodeVarintSlowHook_tpidrSafe {fromHook : State → State}
    (hfrom : ∀ s, (fromHook s).tpidrEl0 = s.tpidrEl0 ∧
      ∀ a, ((fromHook s).mem.perm a).x → (s.mem.perm a).x)
    (s : State) :
    (decodeVarintSlowHook fromHook s).tpidrEl0 = s.tpidrEl0 ∧
      ∀ a, ((decodeVarintSlowHook fromHook s).mem.perm a).x → (s.mem.perm a).x := by
  refine ⟨?_, fun a hx => ?_⟩
  · unfold decodeVarintSlowHook
    dsimp only
    split
    · simp
    · split
      · simp only [tpidrEl0_setPC, tpidrEl0_writeReg64]
        exact (hfrom _).1.trans (by simp)
      · exact (hfrom _).1.trans (by simp)
  · unfold decodeVarintSlowHook at hx
    dsimp only at hx
    split at hx
    · simpa using hx
    · split at hx
      · have hx' := (hfrom _).2 a (by simpa using hx)
        simpa using hx'
      · have hx' := (hfrom _).2 a hx
        simpa using hx'

theorem tripleRatchetExterns_tpidrSafe {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (hHooks : BinHooks C A S abs) (name : String) (f : State → State)
    (hf : Rust.withPanics (tripleRatchetExterns C ctl abs) name = some f) (s : State) :
    (f s).tpidrEl0 = s.tpidrEl0 ∧ ∀ a, ((f s).mem.perm a).x → (s.mem.perm a).x := by
  unfold Rust.withPanics at hf
  split_ifs at hf with hpan
  · simp only [Option.some.injEq] at hf; subst hf
    exact ⟨rfl, fun _ hx => hx⟩
  · unfold tripleRatchetExterns at hf
    cases h1 : CryptoVerification.LibsignalSession.sessionExterns C.F (fun _ => none) name with
    | some h =>
      rw [h1] at hf; simp only [Option.some.injEq] at hf; subst hf
      exact sessionExterns_tpidrSafe C name h h1 s
    | none =>
      rw [h1] at hf
      dsimp only at hf
      split_ifs at hf with hd hp hs hrng hno
      · simp only [Option.some.injEq] at hf; subst hf
        exact tpidrSafe_of_tpidr_perm (fun s => by simp [diffieHellmanHook]) (fun s => by simp [diffieHellmanHook]) s
      · simp only [Option.some.injEq] at hf; subst hf
        exact tpidrSafe_of_tpidr_perm (fun s => by simp [pubFromSecretHook]) (fun s => by simp [pubFromSecretHook]) s
      · simp only [Option.some.injEq] at hf; subst hf
        exact tpidrSafe_of_tpidr_perm (fun s => by simp [zeroizeSecretHook]) (fun s => by simp [zeroizeSecretHook]) s
      · simp only [Option.some.injEq] at hf; subst hf
        exact tpidrSafe_of_tpidr_perm (fun s => by simp [rngFillHook]) (fun s => by simp [rngFillHook]) s
      · exact hHooks.tpidrSafe name f hf s

theorem findSome?_stubs_some {α : Type} (ext : String → Option α) (off : Nat) :
    ∀ (stubs : List (String × Nat)) {f : α},
      (stubs.findSome? fun (n, o) => if o == off then ext n else none) = some f →
      ∃ name, ext name = some f
  | [], _, h => by simp at h
  | (n, o) :: tl, _, h => by
    simp only [List.findSome?_cons] at h
    cases ho : o == off
    · simp only [ho, Bool.false_eq_true, ↓reduceIte] at h
      exact findSome?_stubs_some ext off tl h
    · simp only [ho, ↓reduceIte] at h
      cases he : ext n with
      | none =>
        rw [he] at h
        exact findSome?_stubs_some ext off tl h
      | some f0 =>
        rw [he] at h
        simp only [Option.some.injEq] at h
        exact ⟨n, h ▸ he⟩

theorem externAt?_eq_findSome? {prog : Program} (hov : prog.overrides = fun _ => none)
    (pc : BitVec 64) :
    prog.externAt? pc =
      prog.stubs.findSome? fun (n, o) =>
        if o == (pc - prog.base).toNat then prog.externs n else none := by
  unfold Program.externAt? Program.hookAtOff?
  rw [hov]
  have hsym : (prog.symbols.findSome? fun (_ : String × Nat) => (none : Option (State → State))) = none :=
    Program.findSome?_eq_none_of_forall fun _ _ => rfl
  simp only [ite_self, hsym, Option.or_none]

end TpidrAux

theorem tpidrInv_binProg {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {img : Obj.Image} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hHooks : BinHooks C A S abs) :
    TpidrInv (tripleRatchetProg img C ctl abs) := by
  intro s1 s2 hL hEx hstep
  have hfields := Run.tripleRatchetProg_fields img C ctl abs
  cases hstep with
  | @exec inst _ h_fetch =>
    have hne : inst ≠ Run.svc0 := fun heq =>
      TpidrAux.fetchMem_ne_svc0_of_loads hloads hfields.2.1 hL hEx s1.pc
        (h_fetch.trans (congrArg some heq))
    have hmsr_opt : TpidrAux.isMsrOpt
        ((tripleRatchetProg img C ctl abs).fetchMem s1.mem s1.pc) = false :=
      TpidrAux.fetchMem_noMsr_of_loads hloads hfields.2.1 hL hEx s1.pc
    rw [h_fetch] at hmsr_opt
    have hperm : (execInst inst s1).mem.perm = s1.mem.perm :=
      (Run.NoSvcAux.execInst_keepsPerm hne s1).elim
    have hsvc : inst.isSvc0 = false := by
      cases inst <;> simp_all [Instr.isSvc0, Run.svc0]
    rw [evalInst_eq_execInst_of_not_isSvc0 hsvc]
    refine ⟨TpidrAux.execInst_tpidrEl0 hmsr_opt s1, fun a hx => ?_⟩
    rw [hperm] at hx
    exact hEx a hx
  | halt_unmapped _ _ _ =>
    exact ⟨rfl, hEx⟩
  | extern_fault _ _ _ =>
    exact ⟨rfl, hEx⟩
  | @extern f _ h_ext _ _ =>
    have hf' := (TpidrAux.externAt?_eq_findSome? hfields.2.2.1 s1.pc).symm.trans h_ext
    obtain ⟨name, hext⟩ := TpidrAux.findSome?_stubs_some _ _ _ hf'
    rw [hfields.2.2.2.2] at hext
    have ⟨htp, hperm_x⟩ := TpidrAux.tripleRatchetExterns_tpidrSafe hHooks name f hext s1
    exact ⟨htp, fun a hx => hEx a (hperm_x a hx)⟩

theorem tpidrInv_tripleRatchetProgAt {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {img : Obj.Image} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hHooks : BinHooks C A S abs) :
    TpidrInv (tripleRatchetProgAt img.base C ctl abs) := by
  rw [← tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact tpidrInv_binProg hloads hHooks

theorem tpidr_execOnly_of_steps_tripleRatchetProg {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {img : Obj.Image} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hHooks : BinHooks C A S abs)
    {s1 s2 : State} (hF : img.FrozenLoaded s1)
    (hEx : ExecOnlyIn (Program.ofImage img) s1.mem)
    (hst : Steps (tripleRatchetProg img C ctl abs) s1 s2) :
    s2.tpidrEl0 = s1.tpidrEl0 ∧ ExecOnlyIn (Program.ofImage img) s2.mem :=
  Steps.tpidr_execOnly (tpidrInv_binProg hloads hHooks)
    (codeLoaded_tripleRatchetProg_of_frozenLoaded hF C ctl abs) hEx hst

theorem tpidr_execOnly_of_steps_tripleRatchetProgAt {C : Crypto} {A : RustAlloc} {S : SpqrModel}
    {img : Obj.Image} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hHooks : BinHooks C A S abs)
    {s1 s2 : State} (hF : img.FrozenLoaded s1)
    (hEx : ExecOnlyIn (Program.ofImage img) s1.mem)
    (hst : Steps (tripleRatchetProgAt img.base C ctl abs) s1 s2) :
    s2.tpidrEl0 = s1.tpidrEl0 ∧ ExecOnlyIn (Program.ofImage img) s2.mem := by
  rw [← tripleRatchetProg_eq_tripleRatchetProgAt hloads] at hst
  exact tpidr_execOnly_of_steps_tripleRatchetProg hloads hHooks hF hEx hst

end CryptoVerification.E2E.Bin
