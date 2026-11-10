/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Proofs.CodeLayout
public import ProofLib.OpcodeExclusion
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.Placed.PlacedCallSym
import LibsignalBinary.Proofs.E2E.Record.Support.ImageWitness
import GeneratedLean.LibsignalSessionObj

@[expose] public section

namespace CryptoVerification.E2E.Run

open Arm64 ProofLib
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet


/-- `svc #0`, the only ARM64 instruction in the model that executes a system call (`execSyscall`). -/
def svc0 : Instr := .system false 0#16

namespace NoSvcAux

@[irreducible] def KeepsPerm (m m' : Memory) : Prop :=
  m'.perm = m.perm

theorem KeepsPerm.refl (m : Memory) : KeepsPerm m m := by
  unfold KeepsPerm; rfl

theorem KeepsPerm.elim {m m' : Memory} (h : KeepsPerm m m') : m'.perm = m.perm := by
  unfold KeepsPerm at h; exact h

theorem KeepsPerm.of_perm_eq {m m' : Memory} (h : m'.perm = m.perm) : KeepsPerm m m' := by
  unfold KeepsPerm; exact h

private theorem not_isSvc0_of_ne_svc0 {inst : Instr} (h : inst ≠ svc0) :
    inst.isSvc0 = false := by
  cases inst <;> simp_all [Instr.isSvc0, svc0]

theorem execInst_keepsPerm {inst : Instr} (h : inst ≠ svc0) (s : State) :
    KeepsPerm s.mem (execInst inst s).mem :=
  KeepsPerm.of_perm_eq (Arm64.execInst_perm_of_not_isSvc0 (not_isSvc0_of_ne_svc0 h) s)

theorem execInst_trace {inst : Instr} (h : inst ≠ svc0) (s : State) :
    (execInst inst s).trace = s.trace :=
  Arm64.execInst_trace_of_not_isSvc0 (not_isSvc0_of_ne_svc0 h) s

/-! ## `sessionCode_noSvc` helpers -/

open ProofLib.ProgramReflection

def isSvc0Op (i : Instr) : Bool := i.isSvc0

def isSvc0Opt : Option Instr → Bool
  | some i => isSvc0Op i
  | none => false

theorem isSvc0Opt_decode_eq_false_of_not_svc (w : BitVec 32)
    (h : isSvc0Word w = false) :
    isSvc0Opt (decode w) = false := by
  cases hd : decode w with
  | none => rfl
  | some i => exact Arm64.decode_not_isSvc0 hd h

theorem svc_mask_eq_false_of_bytes {b0 b1 b2 b3 : BitVec 8}
    (h : (b3 == 0xd4#8 && b0 == 0x01#8 && b1 == 0x00#8 && b2 == 0x00#8) = false) :
    isSvc0Word (b3 ++ b2 ++ b1 ++ b0) = false := by
  unfold isSvc0Word
  bv_bits

def noSvc0Tree : WordTree → Bool
  | .empty => true
  | .leaf b0 b1 b2 b3 => !(b3 == 0xd4#8 && b0 == 0x01#8 && b1 == 0x00#8 && b2 == 0x00#8)
  | .node _ l r => noSvc0Tree l && noSvc0Tree r

private theorem drop_all_toBytesAux' :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)),
      t.checkSize? = some n →
      (t.toBytesAux acc).drop (4 * n) = acc
  | .empty, _, acc, h => by
    cases h; rfl
  | .leaf _ _ _ _, _, acc, h => by
    cases h; rfl
  | .node lw l r, _, acc, h => by
    simp only [WordTree.checkSize?] at h
    split at h <;> try contradiction
    rename_i nl nr hl hr
    split at h <;> try contradiction
    simp only [Option.some.injEq] at h; subst h
    have hadd : 4 * (nl + nr) = 4 * nl + 4 * nr := Nat.mul_add 4 nl nr
    rw [WordTree.toBytesAux, hadd, ← List.drop_drop,
        drop_all_toBytesAux' l (r.toBytesAux acc) hl,
        drop_all_toBytesAux' r acc hr]

theorem noSvc0Tree_drop_toBytesAux :
    ∀ (t : WordTree) {n : Nat} (acc : List (BitVec 8)) (j : Nat),
      t.checkSize? = some n →
      noSvc0Tree t = true →
      j < n →
      ∃ b0 b1 b2 b3 rest,
        (t.toBytesAux acc).drop (4 * j) = b0 :: b1 :: b2 :: b3 :: rest ∧
        (b3 == 0xd4#8 && b0 == 0x01#8 && b1 == 0x00#8 && b2 == 0x00#8) = false
  | .empty, _, _, _, hsz, _, hj => by
    cases hsz; omega
  | .leaf b0 b1 b2 b3, _, acc, j, hsz, hno, hj => by
    cases hsz
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [noSvc0Tree, Bool.not_eq_true'] at hno
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
    simp only [noSvc0Tree, Bool.and_eq_true] at hno
    by_cases hlt : j < lw
    · exact noSvc0Tree_drop_toBytesAux l (r.toBytesAux acc) j hl hno.1 hlt
    · have hj_eq : 4 * j = 4 * lw + 4 * (j - lw) := by omega
      rw [WordTree.toBytesAux, hj_eq, ← List.drop_drop,
          drop_all_toBytesAux' l (r.toBytesAux acc) hl]
      exact noSvc0Tree_drop_toBytesAux r acc (j - lw) hr hno.2 (by omega)

set_option maxRecDepth 2000000 in
theorem libsignalSessionCode_tree_noSvc0 :
    noSvc0Tree libsignalSessionCode_tree = true := by
  rfl_kernel

theorem readWordOff_bind_decode_ne_svc0 {prog : Program} {t : WordTree} {n : Nat}
    (hcode : prog.code = t.toBytesAux [])
    (hsz : t.checkSize? = some n)
    (hno : noSvc0Tree t = true)
    (off : Nat) (hoff : off % 4 = 0) (hlt : off + 4 ≤ 4 * n) :
    (prog.readWordOff off).bind decode ≠ some svc0 := by
  have hj_lt : off / 4 < n := by omega
  have hoff_eq : off = 4 * (off / 4) := by omega
  obtain ⟨b0, b1, b2, b3, rest, hdrop, hbytes⟩ :=
    noSvc0Tree_drop_toBytesAux t [] (off / 4) hsz hno hj_lt
  unfold Program.readWordOff
  simp only [hoff, ne_eq, not_true_eq_false, ↓reduceIte]
  rw [hcode, hoff_eq, hdrop]
  simp only [Option.bind_some]
  intro hdec
  have his : isSvc0Opt (decode (b3 ++ b2 ++ b1 ++ b0)) = true := by
    rw [hdec]; rfl
  have hfalse := isSvc0Opt_decode_eq_false_of_not_svc (b3 ++ b2 ++ b1 ++ b0)
    (svc_mask_eq_false_of_bytes hbytes)
  rw [his] at hfalse
  contradiction

theorem fetchMem_ne_of_forall_readWordOff {prog : Program} {m : Memory} {inst : Instr}
    (hL : prog.CodeLoaded m)
    (hlen4 : prog.code.length % 4 = 0)
    (hx : ∀ a, (m.perm a).x = true → InRegion prog.base prog.code.length a)
    (hno : ∀ off, off % 4 = 0 → off + 4 ≤ prog.code.length →
      (prog.readWordOff off).bind decode ≠ some inst)
    (pc : BitVec 64) :
    prog.fetchMem m pc ≠ some inst := by
  unfold Program.fetchMem
  split
  · simp
  split
  · simp
  rename_i h_align
  split
  · simp
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

theorem readWordOff_congr {p1 p2 : Program} (hc : p1.code = p2.code) (off : Nat) :
    p1.readWordOff off = p2.readWordOff off := by
  unfold Program.readWordOff
  rw [hc]

theorem ofImage_code (img : Obj.Image) : (Program.ofImage img).code = img.code := rfl

theorem libsignalSessionImage_code_length : libsignalSessionImage.code.length = num% (ls_field% codeLen) := by
  change libsignalSessionCode.code.length = num% (ls_field% codeLen)
  rw [libsignalSessionCode_code_eq]
  exact Record.ImageWitness.WordTree.length_toBytesAux_nil' libsignalSessionCode_tree
    libsignalSessionCode_tree_size

end NoSvcAux

/-- Evaluates `tripleRatchetProg` field projections without unfolding `img`. -/
theorem tripleRatchetProg_fields (img : Obj.Image) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProg img C ctl abs).base = img.base ∧
    (tripleRatchetProg img C ctl abs).code = img.code ∧
    (tripleRatchetProg img C ctl abs).overrides = (fun _ => none) ∧
    (tripleRatchetProg img C ctl abs).stubs = img.stubs ∧
    (tripleRatchetProg img C ctl abs).externs =
      Rust.withPanics (tripleRatchetExterns C ctl abs) :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩


/-- Every instruction other than `svc #0` preserves memory permissions and the trace. -/
theorem execInst_perm_trace {inst : Instr} (h : inst ≠ svc0) (s : State) :
    (∀ a, (execInst inst s).mem.perm a = s.mem.perm a) ∧ (execInst inst s).trace = s.trace := by
  exact ⟨congrFun (NoSvcAux.execInst_keepsPerm h s).elim, NoSvcAux.execInst_trace h s⟩


/-! ## Relocatable `[LibsignalPlacement]` `noSvc0` helpers -/

section PlacedNoSvc0

open Arm64.Obj CryptoVerification ProofLib.ProgramReflection

/-- Preserved-bit check guaranteeing that relocation patching of template word `w` with relocation
    kind `k` (`patchRelocWord` or `CodeBlock.patchGotOrTlsIeRelaxed`) never produces `0xd4000001#32`
    under any placement. -/
def relocWordNoSvc0 (k : RelocKind) (w : BitVec 32) : Bool :=
  match k with
  | .call26 | .jump26 => (w &&& 0xfc000000#32) != 0xd4000000#32
  | .adrpHi21 | .adrpHi21Nc | .adrGotPage | .tlsieAdrGottprelPage21 | .adrPrelLo21 =>
    (w &&& 0x9f00001f#32) != 0x94000001#32
  | .addLo12 | .ldst8Lo12 | .ldst16Lo12 | .ldst32Lo12 | .ldst64Lo12
  | .ld64GotLo12Nc | .tlsieLd64GottprelLo12Nc | .ldst128Lo12
  | .tlsleAddTprelHi12 | .tlsleAddTprelLo12 | .tlsleAddTprelLo12Nc
  | .tlsleLdst8TprelLo12Nc | .tlsleLdst16TprelLo12Nc | .tlsleLdst32TprelLo12Nc
  | .tlsleLdst64TprelLo12Nc | .tlsleLdst128TprelLo12Nc =>
    (w &&& 0xffc003ff#32) != 0xd4000001#32
  | .condbr19 | .ldPrelLo19 => (w &&& 0xff00001f#32) != 0xd4000001#32
  | .tstbr14 => (w &&& 0xfff8001f#32) != 0xd4000001#32
  | .prel32 => false
  | .abs64 | .abs32 => w != 0xd4000001#32
  | .tlsdescAdrPage21 | .tlsdescLd64Lo12 | .tlsdescAddLo12 | .tlsdescCall => true
  | .tlsleMovwTprelG1 | .tlsleMovwTprelG0 => (w &&& 0xbfe0001f#32) != 0x94000001#32
  | .tlsleMovwTprelG1Nc | .tlsleMovwTprelG0Nc => (w &&& 0xffe0001f#32) != 0xd4000001#32

/-- Consume all leading relocation entries at byte offset `off`, verifying `relocWordNoSvc0` against
    the current 32-bit little-endian word `w`. -/
def consumeRelocsAt (off : Nat) (w : BitVec 32) : List RelocEntry → Option (List RelocEntry)
  | r :: rs =>
    if r.off == off then
      if relocWordNoSvc0 r.kind w then consumeRelocsAt off w rs
      else none
    else some (r :: rs)
  | [] => some []

/-- Tail-recursive linear-time check that `bs` has length divisible by 4, contains no `svc #0` word
(`0xd4000001`), and satisfies `relocWordNoSvc0` at all sorted relocation entries `rs`. -/
def scanCodeRelocs (off : Nat) : List (BitVec 8) → List RelocEntry → Bool
  | b0 :: b1 :: b2 :: b3 :: rest, rs =>
    if (b3 == 0xd4#8 && b0 == 0x01#8 && b1 == 0x00#8 && b2 == 0x00#8) then false
    else
      match consumeRelocsAt off (b3 ++ b2 ++ b1 ++ b0) rs with
      | some rs' => scanCodeRelocs (off + 4) rest rs'
      | none => false
  | [], [] => true
  | _, _ => false

/-- Linear-time checker that a `CodeBlock` is 4-byte aligned and contains no `svc #0` word before
    or after relocation patching under any `Placement`. -/
def blockNoSvc0 (blk : CodeBlock) : Bool :=
  scanCodeRelocs 0 blk.code blk.relocs

/-- Linear-time checker that every block of a `MultiPlacedLib` satisfies `blockNoSvc0`. -/
def allBlocksNoSvc0 (lib : MultiPlacedLib) : Bool :=
  lib.blocks.all blockNoSvc0

set_option maxRecDepth 2000000 in
theorem libsignalSessionLib_noSvc0 : allBlocksNoSvc0 libsignalSessionLib = true := by
  rfl_kernel

private theorem ne_svc0Word_of_mask {w mask : BitVec 32}
    (h : (w &&& mask) ≠ (0xd4000001#32 &&& mask)) :
    isSvc0Word w = false := by
  unfold isSvc0Word
  rw [beq_eq_false_iff_ne]
  intro heq
  exact h (congrArg (· &&& mask) heq)

private theorem isSvc0Word_nopWord : isSvc0Word nopWord = false := by
  decide

private theorem and_shift_disjoint (a K M : BitVec 32) (s : Nat)
    (hd : ∀ i : Fin 32, (!decide (i.val < s) && K.getLsbD (i.val - s) && M.getLsbD i.val) = false) :
    ((a &&& K) <<< s) &&& M = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hdi := hd ⟨i, hi⟩
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_zero, hi, decide_true]
  revert hdi
  cases (!decide (i < s)) <;> cases a.getLsbD (i - s) <;> cases K.getLsbD (i - s) <;>
    cases M.getLsbD i <;> decide

private theorem mask_or_zero {w x M : BitVec 32} (hx : x &&& M = 0#32) :
    ((w &&& M) ||| x) &&& M = w &&& M := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hxi : (x &&& M).getLsbD i = false := by rw [hx]; simp
  rw [BitVec.getLsbD_and] at hxi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
  revert hxi
  cases w.getLsbD i <;> cases x.getLsbD i <;> cases M.getLsbD i <;> decide

private theorem or_and_zero {x y M : BitVec 32} (hx : x &&& M = 0#32) (hy : y &&& M = 0#32) :
    (x ||| y) &&& M = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hxi : (x &&& M).getLsbD i = false := by rw [hx]; simp
  have hyi : (y &&& M).getLsbD i = false := by rw [hy]; simp
  rw [BitVec.getLsbD_and] at hxi hyi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero]
  revert hxi hyi
  cases x.getLsbD i <;> cases y.getLsbD i <;> cases M.getLsbD i <;> decide

private theorem mask_adr_eq (w a b : BitVec 32) :
    ((w &&& 0x9f00001f#32) ||| (((a &&& 0x3#32) <<< 29) ||| ((b &&& 0x7ffff#32) <<< 5))) &&&
      0x9f00001f#32 = w &&& 0x9f00001f#32 :=
  mask_or_zero (or_and_zero
    (and_shift_disjoint a 0x3#32 0x9f00001f#32 29 (by decide))
    (and_shift_disjoint b 0x7ffff#32 0x9f00001f#32 5 (by decide)))

private theorem isSvc0Word_adrWord_mask {w : BitVec 32} (place target : BitVec 64)
    (hw : (w &&& 0x9f00001f#32) != 0x94000001#32) :
    isSvc0Word (adrWord w place target) = false := by
  apply ne_svc0Word_of_mask (mask := 0x9f00001f#32)
  unfold adrWord adrWordOff
  rw [mask_adr_eq]
  exact bne_iff_ne.mp hw

private theorem isSvc0Word_adrTemplate (w : BitVec 32) (place target : BitVec 64) :
    isSvc0Word (adrWord (adrTemplate w) place target) = false := by
  refine isSvc0Word_adrWord_mask place target ?_
  rw [bne_iff_ne]
  intro heq
  have hb31 : ((adrTemplate w) &&& 0x9f00001f#32).getLsbD 31 = (0x94000001#32 : BitVec 32).getLsbD 31 :=
    congrArg (·.getLsbD 31) heq
  unfold adrTemplate at hb31
  simp at hb31

private theorem mask_branch_eq (w a : BitVec 32) :
    ((w &&& 0xfc000000#32) ||| (a &&& 0x03ffffff#32)) &&& 0xfc000000#32 =
      w &&& 0xfc000000#32 := by
  have hd : ((a &&& 0x03ffffff#32) <<< 0) &&& 0xfc000000#32 = 0#32 :=
    and_shift_disjoint a 0x03ffffff#32 0xfc000000#32 0 (by decide)
  rw [BitVec.shiftLeft_zero] at hd
  exact mask_or_zero hd

private theorem isSvc0Word_branchWord {w : BitVec 32} (place target : BitVec 64)
    (hw : (w &&& 0xfc000000#32) != 0xd4000000#32) :
    isSvc0Word (branchWord w place target) = false := by
  apply ne_svc0Word_of_mask (mask := 0xfc000000#32)
  unfold branchWord
  rw [mask_branch_eq]
  exact bne_iff_ne.mp hw

private theorem isSvc0Word_adrpWord {w : BitVec 32} (place target : BitVec 64)
    (hw : (w &&& 0x9f00001f#32) != 0x94000001#32) :
    isSvc0Word (adrpWord w place target) = false := by
  apply ne_svc0Word_of_mask (mask := 0x9f00001f#32)
  unfold adrpWord adrpWordOff
  rw [mask_adr_eq]
  exact bne_iff_ne.mp hw

private theorem mask_lo12_eq (w a : BitVec 32) :
    ((w &&& 0xffc003ff#32) ||| ((a &&& 0xfff#32) <<< 10)) &&& 0xffc003ff#32 =
      w &&& 0xffc003ff#32 :=
  mask_or_zero (and_shift_disjoint a 0xfff#32 0xffc003ff#32 10 (by decide))

private theorem isSvc0Word_lo12Word (scale : Nat) {w : BitVec 32} (target : BitVec 64)
    (hw : (w &&& 0xffc003ff#32) != 0xd4000001#32) :
    isSvc0Word (lo12Word scale w target) = false := by
  apply ne_svc0Word_of_mask (mask := 0xffc003ff#32)
  unfold lo12Word
  rw [mask_lo12_eq]
  exact bne_iff_ne.mp hw

private theorem isSvc0Word_tprelHi12Word {w : BitVec 32} (target : BitVec 64)
    (hw : (w &&& 0xffc003ff#32) != 0xd4000001#32) :
    isSvc0Word (tprelHi12Word w target) = false := by
  apply ne_svc0Word_of_mask (mask := 0xffc003ff#32)
  unfold tprelHi12Word
  rw [mask_lo12_eq]
  exact bne_iff_ne.mp hw

private theorem mask_imm19_eq (w a : BitVec 32) :
    ((w &&& 0xff00001f#32) ||| ((a &&& 0x7ffff#32) <<< 5)) &&& 0xff00001f#32 =
      w &&& 0xff00001f#32 :=
  mask_or_zero (and_shift_disjoint a 0x7ffff#32 0xff00001f#32 5 (by decide))

private theorem isSvc0Word_imm19Word {w : BitVec 32} (place target : BitVec 64)
    (hw : (w &&& 0xff00001f#32) != 0xd4000001#32) :
    isSvc0Word (imm19Word w place target) = false := by
  apply ne_svc0Word_of_mask (mask := 0xff00001f#32)
  unfold imm19Word imm19WordOff
  rw [mask_imm19_eq]
  exact bne_iff_ne.mp hw

private theorem mask_tstbr14_eq (w a : BitVec 32) :
    ((w &&& 0xfff8001f#32) ||| ((a &&& 0x3fff#32) <<< 5)) &&& 0xfff8001f#32 =
      w &&& 0xfff8001f#32 :=
  mask_or_zero (and_shift_disjoint a 0x3fff#32 0xfff8001f#32 5 (by decide))

private theorem isSvc0Word_tstbr14Word {w : BitVec 32} (place target : BitVec 64)
    (hw : (w &&& 0xfff8001f#32) != 0xd4000001#32) :
    isSvc0Word (tstbr14Word w place target) = false := by
  apply ne_svc0Word_of_mask (mask := 0xfff8001f#32)
  unfold tstbr14Word tstbr14WordOff
  rw [mask_tstbr14_eq]
  exact bne_iff_ne.mp hw

private theorem mask_movwSigned_pos_eq (w a : BitVec 32) :
    (((w &&& 0xbfe0001f#32) ||| 0x40000000#32) ||| ((a &&& 0xffff#32) <<< 5)) &&& 0xbfe0001f#32 =
      w &&& 0xbfe0001f#32 := by
  have hor : (((w &&& 0xbfe0001f#32) ||| 0x40000000#32) ||| ((a &&& 0xffff#32) <<< 5)) =
      (w &&& 0xbfe0001f#32) ||| (0x40000000#32 ||| ((a &&& 0xffff#32) <<< 5)) :=
    BitVec.or_assoc _ _ _
  rw [hor]
  exact mask_or_zero (or_and_zero rfl
    (and_shift_disjoint a 0xffff#32 0xbfe0001f#32 5 (by decide)))

private theorem mask_movwSigned_neg_eq (w a : BitVec 32) :
    ((w &&& 0xbfe0001f#32) ||| ((a &&& 0xffff#32) <<< 5)) &&& 0xbfe0001f#32 =
      w &&& 0xbfe0001f#32 :=
  mask_or_zero (and_shift_disjoint a 0xffff#32 0xbfe0001f#32 5 (by decide))

private theorem isSvc0Word_movwSignedWord (shift : Nat) {w : BitVec 32} (target : BitVec 64)
    (hw : (w &&& 0xbfe0001f#32) != 0x94000001#32) :
    isSvc0Word (movwSignedWord shift w target) = false := by
  unfold movwSignedWord
  dsimp only
  split
  · apply ne_svc0Word_of_mask (mask := 0xbfe0001f#32)
    rw [mask_movwSigned_pos_eq]
    exact bne_iff_ne.mp hw
  · apply ne_svc0Word_of_mask (mask := 0xbfe0001f#32)
    rw [mask_movwSigned_neg_eq]
    exact bne_iff_ne.mp hw

private theorem mask_movwNc_eq (w a : BitVec 32) :
    ((w &&& 0xffe0001f#32) ||| ((a &&& 0xffff#32) <<< 5)) &&& 0xffe0001f#32 =
      w &&& 0xffe0001f#32 :=
  mask_or_zero (and_shift_disjoint a 0xffff#32 0xffe0001f#32 5 (by decide))

private theorem isSvc0Word_movwNcWord (shift : Nat) {w : BitVec 32} (target : BitVec 64)
    (hw : (w &&& 0xffe0001f#32) != 0xd4000001#32) :
    isSvc0Word (movwNcWord shift w target) = false := by
  apply ne_svc0Word_of_mask (mask := 0xffe0001f#32)
  unfold movwNcWord
  dsimp only
  rw [mask_movwNc_eq]
  exact bne_iff_ne.mp hw

private theorem isSvc0Word_tlsdescAdrPage21Word (target : BitVec 64) :
    isSvc0Word (tlsdescAdrPage21Word target) = false := by
  unfold isSvc0Word tlsdescAdrPage21Word
  rw [beq_eq_false_iff_ne]
  intro heq
  have hb26 := congrArg (·.getLsbD 26) heq
  simp at hb26

private theorem isSvc0Word_tlsdescLd64Lo12Word (target : BitVec 64) :
    isSvc0Word (tlsdescLd64Lo12Word target) = false := by
  unfold isSvc0Word tlsdescLd64Lo12Word
  rw [beq_eq_false_iff_ne]
  intro heq
  have hb29 := congrArg (·.getLsbD 29) heq
  simp at hb29

private theorem isSvc0Word_patchRelocWord {k : RelocKind} {w : BitVec 32}
    (place target : BitVec 64) (hw : relocWordNoSvc0 k w = true) :
    isSvc0Word (patchRelocWord k w place target) = false := by
  match k, hw with
  | .call26, hw | .jump26, hw => exact isSvc0Word_branchWord place target hw
  | .adrpHi21, hw | .adrpHi21Nc, hw | .adrGotPage, hw | .tlsieAdrGottprelPage21, hw =>
    exact isSvc0Word_adrpWord place target hw
  | .addLo12, hw | .ldst8Lo12, hw
  | .tlsleAddTprelLo12, hw | .tlsleAddTprelLo12Nc, hw | .tlsleLdst8TprelLo12Nc, hw =>
    exact isSvc0Word_lo12Word 0 target hw
  | .ldst16Lo12, hw | .tlsleLdst16TprelLo12Nc, hw => exact isSvc0Word_lo12Word 1 target hw
  | .ldst32Lo12, hw | .tlsleLdst32TprelLo12Nc, hw => exact isSvc0Word_lo12Word 2 target hw
  | .ldst64Lo12, hw | .ld64GotLo12Nc, hw | .tlsieLd64GottprelLo12Nc, hw
  | .tlsleLdst64TprelLo12Nc, hw => exact isSvc0Word_lo12Word 3 target hw
  | .ldst128Lo12, hw | .tlsleLdst128TprelLo12Nc, hw => exact isSvc0Word_lo12Word 4 target hw
  | .condbr19, hw | .ldPrelLo19, hw => exact isSvc0Word_imm19Word place target hw
  | .tstbr14, hw => exact isSvc0Word_tstbr14Word place target hw
  | .adrPrelLo21, hw => exact isSvc0Word_adrWord_mask place target hw
  | .prel32, hw => simp [relocWordNoSvc0] at hw
  | .abs64, hw | .abs32, hw =>
    unfold patchRelocWord isSvc0Word
    rw [beq_eq_false_iff_ne]
    exact bne_iff_ne.mp hw
  | .tlsdescAdrPage21, _ => exact isSvc0Word_tlsdescAdrPage21Word target
  | .tlsdescLd64Lo12, _ => exact isSvc0Word_tlsdescLd64Lo12Word target
  | .tlsdescAddLo12, _ | .tlsdescCall, _ => exact isSvc0Word_nopWord
  | .tlsleAddTprelHi12, hw => exact isSvc0Word_tprelHi12Word target hw
  | .tlsleMovwTprelG1, hw => exact isSvc0Word_movwSignedWord 16 target hw
  | .tlsleMovwTprelG1Nc, hw => exact isSvc0Word_movwNcWord 16 target hw
  | .tlsleMovwTprelG0, hw => exact isSvc0Word_movwSignedWord 0 target hw
  | .tlsleMovwTprelG0Nc, hw => exact isSvc0Word_movwNcWord 0 target hw

private theorem isSvc0Word_patchGotOrTlsIeRelaxed {k : RelocKind} {w : BitVec 32}
    (place target : BitVec 64) (hw : relocWordNoSvc0 k w = true) :
    isSvc0Word (CodeBlock.patchGotOrTlsIeRelaxed w place target k) = false := by
  cases k
  case adrGotPage =>
    exact isSvc0Word_nopWord
  case ld64GotLo12Nc =>
    simp only [CodeBlock.patchGotOrTlsIeRelaxed]
    refine isSvc0Word_lo12Word 0 target ?_
    rw [bne_iff_ne]
    intro heq
    have hb30 := congrArg (·.getLsbD 30) heq
    unfold ldrToAddWord at hb30
    simp at hb30
  case tlsieAdrGottprelPage21 =>
    unfold isSvc0Word CodeBlock.patchGotOrTlsIeRelaxed tlsieMovzWord
    rw [beq_eq_false_iff_ne]
    intro heq
    have hb26 := congrArg (·.getLsbD 26) heq
    simp at hb26
  case tlsieLd64GottprelLo12Nc =>
    unfold isSvc0Word CodeBlock.patchGotOrTlsIeRelaxed tlsieMovkWord
    rw [beq_eq_false_iff_ne]
    intro heq
    have hb29 := congrArg (·.getLsbD 29) heq
    simp at hb29
  all_goals
    simp only [CodeBlock.patchGotOrTlsIeRelaxed]
    exact isSvc0Word_patchRelocWord place target hw

private theorem mem_of_consumeRelocsAt {off : Nat} {w : BitVec 32} {rs rs' : List RelocEntry}
    (hc : consumeRelocsAt off w rs = some rs') :
    ∀ r ∈ rs, (r.off = off ∧ relocWordNoSvc0 r.kind w = true) ∨ r ∈ rs' := by
  induction rs with
  | nil =>
    intro r hr; cases hr
  | cons r0 rest ih =>
    simp only [consumeRelocsAt] at hc
    split at hc
    · rename_i hoff
      split at hc
      · rename_i hok
        intro r hr
        rcases List.mem_cons.mp hr with rfl | hmem
        · exact Or.inl ⟨beq_iff_eq.mp hoff, hok⟩
        · exact ih hc r hmem
      · contradiction
    · simp only [Option.some.injEq] at hc
      subst hc
      intro r hr
      exact Or.inr hr

private theorem scanCodeRelocs_spec :
    ∀ (bs : List (BitVec 8)) (off : Nat) (rs : List RelocEntry),
      scanCodeRelocs off bs rs = true →
      bs.length % 4 = 0 ∧
      (∀ j, 4 * j + 4 ≤ bs.length → isSvc0Word (wordOfBytesLE bs (4 * j)) = false) ∧
      (∀ r ∈ rs, ∃ j, r.off = off + 4 * j ∧
        relocWordNoSvc0 r.kind (wordOfBytesLE bs (4 * j)) = true)
  | [], _, [], _ =>
    ⟨rfl, fun _ hlt => by simp at hlt, fun _ hr => by cases hr⟩
  | [], _, _ :: _, h => by simp [scanCodeRelocs] at h
  | [_], _, _, h => by simp [scanCodeRelocs] at h
  | [_, _], _, _, h => by simp [scanCodeRelocs] at h
  | [_, _, _], _, _, h => by simp [scanCodeRelocs] at h
  | b0 :: b1 :: b2 :: b3 :: rest, off, rs, h => by
    simp only [scanCodeRelocs] at h
    split at h
    · contradiction
    · rename_i hnot
      have hbytes : (b3 == 0xd4#8 && b0 == 0x01#8 && b1 == 0x00#8 && b2 == 0x00#8) = false :=
        Bool.eq_false_iff.mpr hnot
      split at h
      · rename_i rs' hcons
        obtain ⟨hal, hwords, hrels⟩ := scanCodeRelocs_spec rest (off + 4) rs' h
        refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
        · intro j hj
          cases j with
          | zero =>
            rw [Nat.mul_zero, wordOfBytesLE_cons4_zero]
            exact NoSvcAux.svc_mask_eq_false_of_bytes hbytes
          | succ j' =>
            rw [wordOfBytesLE_cons4]
            exact hwords j' (by simp only [List.length_cons] at hj; omega)
        · intro r hr
          rcases mem_of_consumeRelocsAt hcons r hr with ⟨hroff, hrok⟩ | hr'
          · refine ⟨0, by omega, ?_⟩
            rwa [Nat.mul_zero, wordOfBytesLE_cons4_zero]
          · obtain ⟨j', hjoff, hjok⟩ := hrels r hr'
            refine ⟨j' + 1, by omega, ?_⟩
            rwa [wordOfBytesLE_cons4]
      · contradiction

private theorem isSvc0Word_patchedWord_of_blockNoSvc0 {blk : CodeBlock} (pl : Placement)
    (hblk : blockNoSvc0 blk = true) {off : Nat}
    (hoff : off % 4 = 0) (hlt : off + 4 ≤ blk.code.length) :
    isSvc0Word (blk.patchedWord pl off) = false := by
  obtain ⟨_hal, hwords, hrels⟩ := scanCodeRelocs_spec blk.code 0 blk.relocs hblk
  unfold CodeBlock.patchedWord
  cases hrel : blk.relocAt? off with
  | none =>
    simp only
    have hoff_eq : off = 4 * (off / 4) := by omega
    rw [CodeBlock.wordAt, hoff_eq]
    exact hwords (off / 4) (by omega)
  | some r =>
    have hrmem : r ∈ blk.relocs := CodeBlock.relocAt?_mem hrel
    have hroff : r.off = off := CodeBlock.relocAt?_off hrel
    obtain ⟨j, hjoff, hjok⟩ := hrels r hrmem
    have hr_ok : relocWordNoSvc0 r.kind (blk.wordAt off) = true := by
      rw [CodeBlock.wordAt, ← hroff, hjoff, Nat.zero_add]
      exact hjok
    simp only
    split
    · exact isSvc0Word_nopWord
    split
    · exact isSvc0Word_adrTemplate _ _ _
    split
    · exact isSvc0Word_adrTemplate _ _ _
    split
    · exact isSvc0Word_patchGotOrTlsIeRelaxed _ _ hr_ok
    · exact isSvc0Word_patchRelocWord _ _ hr_ok

private theorem blockNoSvc0_of_allBlocksNoSvc0 {lib : MultiPlacedLib}
    (hall : allBlocksNoSvc0 lib = true) {i : Nat} (hi : i < lib.blocks.length) :
    blockNoSvc0 (lib.blockLib i).text = true := by
  unfold allBlocksNoSvc0 at hall
  have hmem : lib.blocks[i] ∈ lib.blocks := List.getElem_mem hi
  have hget : (lib.blockLib i).text = lib.blocks[i] := by
    simp [MultiPlacedLib.blockLib, List.getD_eq_getElem?_getD, hi]
  rw [hget]
  exact List.all_eq_true.mp hall _ hmem

theorem libsignalSessionLib_blockNoSvc0 {i : Nat} {bi : Nat} [LsBlockBound bi] (hi : i < bi) :
    blockNoSvc0 (libsignalSessionLib.blockLib i).text = true :=
  blockNoSvc0_of_allBlocksNoSvc0 libsignalSessionLib_noSvc0
    (by have := LsBlockBound.le_blocks (n := bi); rw [libsignalSessionLib_blocks_length]; omega)

theorem libsignalSessionLib_blockProgram_code_length (pl : MultiPlacement)
    {i : Nat} {bi : Nat} [LsBlockBound bi] (hi : i < bi)
    (X O : String → Option (State → State)) (svc : State → State) :
    (libsignalSessionLib.blockProgram pl i X O svc).code.length =
      (libsignalSessionLib.blockLib i).text.code.length := by
  obtain ⟨hal, _, _⟩ := scanCodeRelocs_spec _ 0 _ (libsignalSessionLib_blockNoSvc0 hi)
  exact CodeBlock.length_patched_of_aligned _ hal

theorem libsignalSessionLib_blockProgram_readWordOff_ne_svc0_gen (pl : MultiPlacement)
    {i : Nat} {bi : Nat} [LsBlockBound bi] (hi : i < bi)
    (X O : String → Option (State → State)) (svc : State → State)
    {off : Nat} (hoff : off % 4 = 0)
    (hlt : off + 4 ≤ (libsignalSessionLib.blockLib i).text.code.length) :
    ((libsignalSessionLib.blockProgram pl i X O svc).readWordOff off).bind decode ≠ some svc0 := by
  have hblk := libsignalSessionLib_blockNoSvc0 hi
  have hrw : (libsignalSessionLib.blockProgram pl i X O svc).readWordOff off =
      some ((libsignalSessionLib.blockLib i).text.patchedWord
        (libsignalSessionLib.blockPlacement pl i) off) :=
    CodeBlock.readWordOff_patched rfl hoff hlt
  rw [hrw, Option.bind_some]
  intro hdec
  have his : NoSvcAux.isSvc0Opt
      (decode ((libsignalSessionLib.blockLib i).text.patchedWord
        (libsignalSessionLib.blockPlacement pl i) off)) = true := by
    rw [hdec]; rfl
  have hfalse := NoSvcAux.isSvc0Opt_decode_eq_false_of_not_svc _
    (isSvc0Word_patchedWord_of_blockNoSvc0 (libsignalSessionLib.blockPlacement pl i) hblk hoff hlt)
  rw [his] at hfalse
  contradiction

/-- For any unmutated block `i < 624` under `[LibsignalPlacement]`, no aligned word in
    `libsignalSessionLib.blockProgram lsmpl i H (fun _ => none) Syscall.standard` decodes to `svc0`. -/
theorem libsignalSessionLib_blockProgram_readWordOff_ne_svc0 [LibsignalPlacement]
    {i : Nat} {bi : Nat} [LsBlockBound bi] (hi : i < bi) (_hunmut : (i ∈ libsignalMutatedBlocks) = false)
    {H : LibsignalHooks} {m : Memory}
    (_hL : (libsignalSessionLib.blockProgram lsmpl i H (fun _ => none) Syscall.standard).CodeLoaded m)
    {off : Nat} (hoff : off % 4 = 0)
    (hlt : off + 4 ≤ (libsignalSessionLib.blockLib i).text.code.length) :
    ((libsignalSessionLib.blockProgram lsmpl i H (fun _ => none) Syscall.standard).readWordOff off).bind
      decode ≠ some svc0 :=
  libsignalSessionLib_blockProgram_readWordOff_ne_svc0_gen lsmpl hi H (fun _ => none) Syscall.standard
    hoff hlt

theorem libsignalSessionLib_blockProgram_readWordOff_ne_svc0' [LibsignalPlacement]
    {i : Nat} {bi : Nat} [LsBlockBound bi] (hi : i < bi) (_hunmut : (i ∈ libsignalMutatedBlocks) = false)
    {H : LibsignalHooks} {m : Memory}
    (_hL : (libsignalSessionLib.blockProgram lsmpl i H (fun _ => none) Syscall.standard).CodeLoaded m)
    {off : Nat} (hoff : off % 4 = 0)
    (hlt : off + 4 ≤
      (libsignalSessionLib.blockProgram lsmpl i H (fun _ => none) Syscall.standard).code.length) :
    ((libsignalSessionLib.blockProgram lsmpl i H (fun _ => none) Syscall.standard).readWordOff off).bind
      decode ≠ some svc0 := by
  rw [libsignalSessionLib_blockProgram_code_length lsmpl hi] at hlt
  exact libsignalSessionLib_blockProgram_readWordOff_ne_svc0_gen lsmpl hi H (fun _ => none)
    Syscall.standard hoff hlt

/-- For any block `i < 624` under `[LibsignalFullPlacement]`, no aligned word in
    `libsignalSessionLib.blockProgram lsmpl i H (fun _ => none) Syscall.standard` decodes to `svc0`. -/
theorem libsignalSessionLib_full_blockProgram_readWordOff_ne_svc0 [LibsignalFullPlacement]
    {i : Nat} {bi : Nat} [LsBlockBound bi] (hi : i < bi) {H : LibsignalHooks}
    {off : Nat} (hoff : off % 4 = 0)
    (hlt : off + 4 ≤ (libsignalSessionLib.blockLib i).text.code.length) :
    ((libsignalSessionLib.blockProgram lsmpl i H (fun _ => none) Syscall.standard).readWordOff off).bind
      decode ≠ some svc0 :=
  libsignalSessionLib_blockProgram_readWordOff_ne_svc0_gen lsmpl hi H (fun _ => none) Syscall.standard
    hoff hlt

private theorem fetchMem_ne_svc0_of_block (pl : MultiPlacement) (prog : Program) {m : Memory}
    {i : Nat} (hi : i < libsignalSessionLib.blocks.length)
    {X : String → Option (State → State)} {pc : BitVec 64}
    (hL : (libsignalSessionLib.blockProgram pl i X (fun _ => none) Syscall.standard).CodeLoaded m)
    (hin : InRegion (pl.base i) (libsignalSessionLib.blockLib i).text.code.length pc) :
    prog.fetchMem m pc ≠ some svc0 := by
  set bprog := libsignalSessionLib.blockProgram pl i X (fun _ => none) Syscall.standard
  have hblk : blockNoSvc0 (libsignalSessionLib.blockLib i).text = true :=
    blockNoSvc0_of_allBlocksNoSvc0 libsignalSessionLib_noSvc0 hi
  obtain ⟨hlen4_blk, _, _⟩ := scanCodeRelocs_spec _ 0 _ hblk
  have hlen_eq : bprog.code.length = (libsignalSessionLib.blockLib i).text.code.length :=
    CodeBlock.length_patched_of_aligned _ hlen4_blk
  have hlen4 : bprog.code.length % 4 = 0 := by rw [hlen_eq]; exact hlen4_blk
  unfold Program.fetchMem
  split
  · simp
  split
  · simp
  rename_i h_align
  split
  · simp
  have h_al : pc.toNat % 4 = 0 := by omega
  unfold InRegion at hin
  have hbase : bprog.base = pl.base i := rfl
  rw [← hbase, ← hlen_eq] at hin
  obtain ⟨hbase_al, hno_wrap, hcode⟩ := Program.codeLoaded_iff.1 hL
  generalize hoff : (pc - bprog.base).toNat = off
  rw [hoff] at hin
  have hpc_eq : pc = bprog.base + BitVec.ofNat 64 off := by
    rw [← hoff, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    bv_arith
  have hpc_nat : pc.toNat = bprog.base.toNat + off := by
    rw [hpc_eq, BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]
  have hoff_al : off % 4 = 0 := by omega
  have hoff_lt : off + 4 ≤ bprog.code.length := by omega
  have hno_inst : (bprog.readWordOff off).bind decode ≠ some svc0 := by
    have hrw : bprog.readWordOff off =
        some ((libsignalSessionLib.blockLib i).text.patchedWord
          (libsignalSessionLib.blockPlacement pl i) off) :=
      CodeBlock.readWordOff_patched rfl hoff_al (by omega)
    rw [hrw, Option.bind_some]
    intro hdec
    have his : NoSvcAux.isSvc0Opt
        (decode ((libsignalSessionLib.blockLib i).text.patchedWord
          (libsignalSessionLib.blockPlacement pl i) off)) = true := by
      rw [hdec]; rfl
    have hfalse := NoSvcAux.isSvc0Opt_decode_eq_false_of_not_svc _
      (isSvc0Word_patchedWord_of_blockNoSvc0 (libsignalSessionLib.blockPlacement pl i) hblk hoff_al (by omega))
    rw [his] at hfalse
    exact Bool.noConfusion hfalse
  have hb_k : ∀ k (hk : k < 4),
      m.read8 (pc + BitVec.ofNat 64 k) = bprog.code[off + k]'(by omega) := by
    intro k hk
    have e : pc + BitVec.ofNat 64 k = bprog.base + BitVec.ofNat 64 (off + k) := by
      rw [hpc_eq, BitVec.ofNat_add, BitVec.add_assoc]
    rw [e]
    exact (hcode (off + k) (by omega)).1
  unfold Program.readWordOff at hno_inst
  simp only [hoff_al, ne_eq, not_true_eq_false, ↓reduceIte] at hno_inst
  rcases hdrop : bprog.code.drop off with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, tl⟩⟩⟩⟩
  · exfalso; have := congrArg List.length hdrop; simp at this; omega
  · exfalso; have := congrArg List.length hdrop; simp at this; omega
  · exfalso; have := congrArg List.length hdrop; simp at this; omega
  · exfalso; have := congrArg List.length hdrop; simp at this; omega
  · rw [hdrop] at hno_inst
    simp only [Option.bind_some] at hno_inst
    have hget : ∀ k (hk : k < 4),
        bprog.code[off + k]'(by omega) = (b0 :: b1 :: b2 :: b3 :: tl)[k]'(by simp; omega) := by
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

private theorem fetchMem_ne_of_not_exec (prog : Program) {m : Memory} {inst : Instr}
    {pc : BitVec 64} (hnx : ¬ (m.perm pc).x = true) :
    prog.fetchMem m pc ≠ some inst := by
  unfold Program.fetchMem
  split
  · simp
  split
  · simp
  split
  · simp
  rename_i h_exec
  simp only [Bool.not_eq_true'] at h_exec
  have h_exec' : m.canExec pc 4 = true := Bool.eq_true_of_not_eq_false h_exec
  unfold Memory.canExec Memory.allPerm at h_exec'
  simp only [Bool.and_eq_true] at h_exec'
  exact absurd h_exec'.1 hnx

/-- Multi-block `fetchMem` `svc0`-exclusion under `[LibsignalPlacement]` (`LibsignalCodeLoaded lsmpl m`). -/
theorem libsignalSessionLib_fetchMem_ne_svc0_of_lscl [LibsignalPlacement]
    (prog : Program) {m : Memory}
    (hcl : LibsignalCodeLoaded lsmpl m)
    {bi : Nat} [LsBlockBound bi]
    (hx : ∀ a, (m.perm a).x = true →
      ∃ i, i < bi ∧ (i ∈ libsignalMutatedBlocks) = false ∧
        InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a)
    (pc : BitVec 64) :
    prog.fetchMem m pc ≠ some svc0 := by
  by_cases hexec : (m.perm pc).x = true
  · obtain ⟨i, hi, hunmut, hin⟩ := hx pc hexec
    have hbi := LsBlockBound.le_blocks (n := bi)
    exact fetchMem_ne_svc0_of_block lsmpl prog (by rw [libsignalSessionLib_blocks_length]; omega)
      (hcl i (Nat.lt_of_lt_of_le hi hbi) hunmut (fun _ => none) (fun _ => none) Syscall.standard) hin
  · exact fetchMem_ne_of_not_exec prog hexec

/-- Multi-block `fetchMem` `svc0`-exclusion under `[LibsignalFullPlacement]` (`libsignalSessionLib.CodeLoaded lsmpl m`). -/
theorem libsignalSessionLib_fetchMem_ne_svc0_of_codeLoaded [LibsignalFullPlacement]
    (prog : Program) {m : Memory}
    (hcl : libsignalSessionLib.CodeLoaded lsmpl m)
    (hx : ∀ a, (m.perm a).x = true →
      ∃ i, i < libsignalSessionLib.blocks.length ∧
        InRegion (lsmpl.base i) (libsignalSessionLib.blockLib i).text.code.length a)
    (pc : BitVec 64) :
    prog.fetchMem m pc ≠ some svc0 := by
  by_cases hexec : (m.perm pc).x = true
  · obtain ⟨i, hi_len, hin⟩ := hx pc hexec
    have hL : (libsignalSessionLib.blockProgram lsmpl i (fun _ => none) (fun _ => none)
        Syscall.standard).CodeLoaded m := by
      have h := hcl i hi_len
      rwa [Program.codeLoaded_iff] at h ⊢
    exact fetchMem_ne_svc0_of_block lsmpl prog hi_len hL hin
  · exact fetchMem_ne_of_not_exec prog hexec

end PlacedNoSvc0

end CryptoVerification.E2E.Run
