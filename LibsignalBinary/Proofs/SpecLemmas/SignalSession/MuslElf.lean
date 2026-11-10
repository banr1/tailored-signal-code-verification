/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.MuslElfBlock
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.InitStack
import ProofLib.SepLogic.Basic

@[expose] public section

set_option autoImplicit false

/-!
# musl Startup on the Loaded CLI ELF

Proves `musl_startup`: from `ElfImage.loadState` on valid CLI arguments under the segment
hypotheses `CliElfMusl` and the 8 MiB stack budget (`cliStackSize`, DEV-CLI7), execution
of `Program.ofImage img E` reaches `main` with `w0 = argc`, `x1 = argv`, `sp = sp0 - 48`,
`lr = entry + 0x854`, unchanged filesystem and trace, and separation-logic footprint
`(argvAt x1 argv ∗ stackAt sp stk ∗ R) ∗ muslFiniFr entry`.
-/

namespace CryptoVerification.SignalSession.MuslElf

open Arm64 Arm64.Process ProofLib CryptoVerification.SignalSession.MuslExit
  CryptoVerification.SignalSession.MuslStart CryptoVerification.SignalSession.InitStack

/-! ## Segment Slices -/

theorem disjointAligned_tail_below (r : Snapshot.Region) :
    ∀ (rest : List Snapshot.Region), regionsDisjointAndAligned rest = true →
      (∀ q ∈ rest.take 1, r.start.toNat + r.bytes.length ≤ q.start.toNat) →
      ∀ q ∈ rest, r.start.toNat + r.bytes.length ≤ q.start.toNat
  | [], _, _ => by simp
  | [q], _, h => by simpa using h
  | q1 :: q2 :: rest, hd, h => by
    have h1 : r.start.toNat + r.bytes.length ≤ q1.start.toNat := h q1 (by simp)
    simp only [regionsDisjointAndAligned, Bool.and_eq_true, decide_eq_true_eq] at hd
    obtain ⟨⟨_, h12⟩, hd'⟩ := hd
    have ih := disjointAligned_tail_below r (q2 :: rest) hd' (by
      intro q hq
      simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hq
      subst hq
      omega)
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact h1
    · exact ih q hq

/-- In a `regionsDisjointAndAligned` list, every region before `segs[k]` ends at or below its
start. -/
theorem disjointAligned_prefix_below :
    ∀ (segs : List Snapshot.Region), regionsDisjointAndAligned segs = true →
      ∀ (k : Nat) (hk : k < segs.length),
        (segs.take k).all (Snapshot.Below segs[k].start) = true
  | [], _, k, hk => by simp at hk
  | r :: rest, hd, k, hk => by
    have hrest : regionsDisjointAndAligned rest = true := by
      cases rest with
      | nil => rfl
      | cons q rest =>
        simp only [regionsDisjointAndAligned, Bool.and_eq_true] at hd
        exact hd.2
    have hbelow : ∀ q ∈ rest, r.start.toNat + r.bytes.length ≤ q.start.toNat := by
      cases rest with
      | nil => simp
      | cons q rest =>
        have hd' := hd
        simp only [regionsDisjointAndAligned, Bool.and_eq_true, decide_eq_true_eq] at hd'
        exact disjointAligned_tail_below r (q :: rest) hd'.2 (by
          intro q' hq'
          simp only [List.take_succ_cons, List.take_zero, List.mem_singleton] at hq'
          subst hq'
          exact hd'.1.2)
    cases k with
    | zero => simp
    | succ k =>
      have hk' : k < rest.length := by simp at hk; omega
      simp only [List.take_succ_cons, List.all_cons, List.getElem_cons_succ, Bool.and_eq_true]
      refine ⟨?_, disjointAligned_prefix_below rest hrest k hk'⟩
      simp only [Snapshot.Below, decide_eq_true_eq]
      exact hbelow _ (List.getElem_mem hk')

theorem wellFormed_disjointAligned (elf : ElfImage) (hwf : elf.WellFormed = true) :
    regionsDisjointAndAligned elf.segments = true := by
  unfold ElfImage.WellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  exact hwf.1.1.1.2

/-- Bytes `bs` at `a` form a slice of a segment of `elf` with permission `p`. -/
def SegSlice (elf : ElfImage) (a : BitVec 64) (bs : List (BitVec 8)) (p : Perm) : Prop :=
  ∃ (k : Nat) (hk : k < elf.segments.length) (off : Nat),
    elf.segments[k].perm = p ∧ a = elf.segments[k].start + BitVec.ofNat 64 off ∧
    (elf.segments[k].bytes.drop off).take bs.length = bs

theorem SegSlice.holdsBytes {elf : ElfImage} {a : BitVec 64} {bs : List (BitVec 8)} {p : Perm}
    (h : SegSlice elf a bs p) (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ stackBase) {inputs : ProcessInputs} {s0 : State}
    (hload : elf.loadState inputs = .ok s0) :
    Obj.HoldsBytes s0.mem a bs (fun _ => p.rwx) := by
  obtain ⟨k, hk, off, hp, rfl, hbs⟩ := h
  have hsegs := segs_below elf hwf hbrk
  have hw := hsegs _ (List.getElem_mem hk)
  have := ElfImage.holdsBytes_of_segment_slice elf hload k hk
    (disjointAligned_prefix_below _ (wellFormed_disjointAligned elf hwf) k hk)
    (by have := stackBase_eq; omega) off bs hbs
  rw [hp] at this
  exact this

theorem SegSlice.bound {elf : ElfImage} {a : BitVec 64} {bs : List (BitVec 8)} {p : Perm}
    (h : SegSlice elf a bs p) (hne : bs ≠ []) (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ stackBase) :
    a.toNat + bs.length ≤ stackBase := by
  obtain ⟨k, hk, off, -, rfl, hbs⟩ := h
  have hw := segs_below elf hwf hbrk _ (List.getElem_mem hk)
  have hlen : bs.length = min bs.length (elf.segments[k].bytes.length - off) := by
    conv => lhs; rw [← hbs]
    rw [List.length_take, List.length_drop]
  have hpos : 0 < bs.length := by
    cases bs with
    | nil => exact absurd rfl hne
    | cons _ _ => simp
  have hoff : off + bs.length ≤ elf.segments[k].bytes.length := by omega
  have hsb := stackBase_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : off % 2 ^ 64 = off := Nat.mod_eq_of_lt (by omega)
  rw [h1, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Bytes held read-write at `a` are supported on their absolute addresses (base `0`). -/
theorem supportedOn_of_holdsBytes_rw {m : Memory} {a : BitVec 64} {bs : List (BitVec 8)}
    (hbnd : a.toNat + bs.length < 2 ^ 64) (h : Obj.HoldsBytes m a bs (fun _ => .rw)) :
    SupportedOn 0#64 (fun k => a.toNat ≤ k ∧ k < a.toNat + bs.length) m (a ↦ₛ bs) := by
  have e : a = 0#64 + BitVec.ofNat 64 a.toNat := by
    rw [BitVec.zero_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [e] at h
  have := SupportedOn.of_holdsBytes_rw (b := 0#64) (off := a.toNat) hbnd h
  rw [← e] at this
  exact this

/-- Zero read-write cells hold zero bytes. -/
theorem holdsBytes_zero {m : Memory} {a : BitVec 64} {n : Nat}
    (hz : ∀ i < n, m.cells (a + BitVec.ofNat 64 i) = some (some Perm.rw, 0#8)) :
    Obj.HoldsBytes m a (List.replicate n 0#8) (fun _ => .rw) := by
  intro i hi
  rw [List.length_replicate] at hi
  have := hz i hi
  refine ⟨?_, ?_, ?_⟩
  · simp only [Memory.read8, this, List.getElem_replicate]
  · simp only [Memory.perm, this]; rfl
  · simp only [Memory.isLazyFree, this]; rfl

theorem unpackL_replicate_zero (n : Nat) :
    unpackL (List.replicate n 0#64) = List.replicate (8 * n) 0#8 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, unpackL, List.flatMap_cons, ← unpackL, ih,
      show 8 * (n + 1) = 8 + 8 * n by omega, List.replicate_add]
    rfl

/-- A successful load starts at the entry point, running, with the inputs' file system and an
empty trace. -/
theorem loadState_fields {elf : ElfImage} {inputs : ProcessInputs} {s0 : State}
    (h : elf.loadState inputs = .ok s0) :
    s0.pc = elf.entry ∧ s0.status = .Running ∧ s0.fs = initFsState inputs ∧ s0.trace = [] := by
  dsimp only [ElfImage.loadState, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h; · contradiction
  split at h; · contradiction
  split at h; · contradiction
  generalize hb : buildInitialStack elf inputs = r at h
  cases r with
  | error _ => contradiction
  | ok pair =>
    obtain ⟨sp, reg⟩ := pair
    cases h
    exact ⟨rfl, rfl, rfl, rfl⟩

theorem startArgv0_eq (p : BitVec 64) :
    (p ↦ₛ (bytesOfString "libsignal-cli" ++ [0#8])) = StartArgv0 p := by
  have e : bytesOfString "libsignal-cli" ++ [0#8] =
      [0x6c#8, 0x69#8, 0x62#8, 0x73#8, 0x69#8, 0x67#8, 0x6e#8, 0x61#8, 0x6c#8, 0x2d#8, 0x63#8,
       0x6c#8, 0x69#8, 0x00#8] := by decide
  rw [e]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp, BitVec.add_assoc,
    BitVec.reduceAdd, StartArgv0]

private theorem rearr1' {A R C T X : SepProp} (h : R ∗ T ⊢ X) :
    (A ∗ R) ∗ (C ∗ T) ⊢ A ∗ (C ∗ X) := by
  rw [sepConj_assoc, sepConj_left_comm R C T]
  exact sepConj_mono_right (sepConj_mono_right h)

/-- `argvAt_of_packed` for a non-empty list, keeping the first pointer explicit. -/
theorem packed_cons (base a : BitVec 64) (s : List (BitVec 8)) (ss : List (List (BitVec 8))) :
    (a ↦ₛ (packAddrs base 0 (s :: ss) ++ [0#64]).flatMap (Obj.bytesLE 8)) ∗
        (base ↦ₛ (s :: ss).flatMap (· ++ [0#8])) ⊢
      (a ↦₆₄ base) ∗ (cStrAt base s ∗ argvAt (a + 8#64) ss) := by
  have hoff : base + BitVec.ofNat 64 (s ++ [0#8]).length =
      base + BitVec.ofNat 64 (0 + s.length + 1) := by
    rw [List.length_append, List.length_singleton, Nat.zero_add]
  rw [packAddrs, List.cons_append, List.flatMap_cons, List.flatMap_cons,
    pointsToBytes_append a (Obj.bytesLE 8 _), bytesLE8_length,
    pointsToBytes_append base (s ++ [0#8]), hoff]
  have h0 : base + BitVec.ofNat 64 0 = base := BitVec.add_zero base
  rw [h0, bytesLE8_eq, ← pointsTo64_eq_pointsToBytes]
  unfold cStrAt
  exact rearr1' (argvAt_of_packed base ss (a + 8#64) (0 + s.length + 1))

private theorem rearr3' {A P W D S T X : SepProp} (h : P ∗ S ⊢ X) :
    A ∗ (P ∗ ((W ∗ D) ∗ (S ∗ T))) ⊢ A ∗ (X ∗ (W ∗ anyHeap)) := by
  have e : A ∗ (P ∗ ((W ∗ D) ∗ (S ∗ T))) = A ∗ ((P ∗ S) ∗ (W ∗ (D ∗ T))) := by ac_rfl
  rw [e]
  exact sepConj_mono_right (sepConj_mono h (sepConj_mono_right (entails_anyHeap _)))

/-- `frame_entails_aux` with `argv[0]`'s pointer and bytes explicit. -/
theorem frame_split (elf : ElfImage) (strs : List (List (BitVec 8))) (s0 : List (BitVec 8))
    (ss : List (List (BitVec 8))) (hs : strs = s0 :: ss)
    (hfit : 8 * tableWords strs + infoLen strs ≤ cliStackSize) :
    (BitVec.ofNat 64 (sp0 strs) ↦ₛ frameBytes elf strs) ⊢
      (BitVec.ofNat 64 (sp0 strs) ↦₆₄ BitVec.ofNat 64 strs.length) ∗
        ((((BitVec.ofNat 64 (sp0 strs) + 8#64) ↦₆₄ argvBase strs) ∗
          (cStrAt (argvBase strs) s0 ∗
            argvAt (BitVec.ofNat 64 (sp0 strs) + 8#64 + 8#64) ss)) ∗
        (((BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2))) ↦₆₄*
            auxWords elf strs) ∗ anyHeap)) := by
  have e1 : BitVec.ofNat 64 (argcBytes strs).length = 8#64 := rfl
  have hp : (ptrBytes strs).length = 8 * (strs.length + 1) := by
    unfold ptrBytes ptrWords
    simp only [flatMap_bytesLE_length, List.length_append, packAddrs_length, List.length_singleton]
  have hu : (unpackL (auxWords elf strs)).length = 8 * 39 := by
    rw [unpackL_length, auxWords_length]
  have hr : (restBytes elf strs).length = 8 * (39 + (strs.length + 41) % 2) := by
    unfold restBytes restWords
    simp only [flatMap_bytesLE_length, List.length_append, List.length_cons, List.length_nil,
      List.length_replicate]
  have hh : (headBytes strs).length = 16 + infoPadLen strs + 8 := by
    unfold headBytes
    simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
  have e2 : BitVec.ofNat 64 (sp0 strs) + 8#64 + BitVec.ofNat 64 (ptrBytes strs).length =
      BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2)) := by
    rw [hp, BitVec.add_assoc]
    congr 1
    simp only [BitVec.ofNat_add_ofNat]
    congr 1
    omega
  have e3 : BitVec.ofNat 64 (sp0 strs) + BitVec.ofNat 64 (8 * (strs.length + 2)) +
      BitVec.ofNat 64 (restBytes elf strs ++ headBytes strs).length =
      argvBase strs := by
    rw [List.length_append, hr, hh]
    unfold argvBase platformAddr
    simp only [BitVec.ofNat_add_ofNat]
    congr 1
    have := top_eq
    have := cliStackSize_eq
    unfold sp0 infoBase tableWords at *
    omega
  have hrest : restBytes elf strs ++ headBytes strs =
      unpackL (auxWords elf strs) ++
        ((List.replicate ((strs.length + 41) % 2) (0#64)).flatMap (Obj.bytesLE 8) ++
          headBytes strs) := by
    unfold restBytes unpackL
    rw [restWords_eq, List.flatMap_append, List.append_assoc]
    rfl
  unfold frameBytes
  rw [pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    pointsToBytes_append _ (strBytes strs), e1,
    e2, e3, hrest, pointsToBytes_append, hu, ← pointsToWords64_eq_pointsToBytes,
    show argcBytes strs = unpack64 (BitVec.ofNat 64 strs.length) from rfl,
    ← pointsTo64_eq_pointsToBytes]
  subst hs
  exact rearr3' (packed_cons (argvBase (s0 :: ss))
    (BitVec.ofNat 64 (sp0 (s0 :: ss)) + 8#64) s0 ss)

/-- argc, `argv[0]`'s pointer and `auxWords` are `StartProc` and the `AT_NULL` value word. -/
theorem startProc_eq (elf : ElfImage) (strs : List (List (BitVec 8))) (sp envp n : BitVec 64)
    (hphent : elf.phent = 56) (hphnum : elf.phnum = 11) :
    ((sp ↦₆₄ n) ∗ ((sp + 8#64) ↦₆₄ argvBase strs) ∗
      (envp ↦₆₄* auxWords elf strs)) =
    (StartProc sp envp (argvBase strs) elf.phdrVaddr
        (BitVec.ofNat 64 Obj.pageSize) 0#64 0#64 elf.entry 1000#64 1000#64 (platformAddr strs)
        0x3#64 100#64 (BitVec.ofNat 64 (infoBase strs)) 0#64 (execfnAddr strs)
        (n.extractLsb' 0 32) (n.extractLsb' 32 32) ∗
      ((envp + 304#64) ↦₆₄ 0#64)) := by
  unfold auxWords
  rw [hphent, hphnum, pointsTo64_split32 sp n]
  simp only [AuxvTag.null, AuxvTag.phdr, AuxvTag.phent, AuxvTag.phnum, AuxvTag.pagesz,
    AuxvTag.base, AuxvTag.flags, AuxvTag.entry, AuxvTag.uid, AuxvTag.euid, AuxvTag.gid,
    AuxvTag.egid, AuxvTag.platform, AuxvTag.hwcap, AuxvTag.clktck, AuxvTag.secure,
    AuxvTag.random, AuxvTag.hwcap2, AuxvTag.execfn, pointsToWords64_cons, pointsToWords64_nil,
    sepConj_emp, sepConj_assoc, BitVec.add_assoc, BitVec.reduceAdd, StartProc]

theorem envp_eq (sp : BitVec 64) (k : Nat) (hk : k < 2 ^ 31) :
    sp + 8#64 + BitVec.signExtend 64 ((BitVec.ofNat 64 k).extractLsb' 0 32) <<< 3 + 8#64 =
      sp + BitVec.ofNat 64 (8 * (k + 2)) := by
  have hm : ((BitVec.ofNat 64 k).extractLsb' 0 32).msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt]
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.shiftLeft_eq,
    Nat.reducePow]
  omega

theorem x0_eq (k : Nat) :
    (((((BitVec.ofNat 64 k).extractLsb' 0 32).zeroExtend 64).truncate 32).zeroExtend 64
      : BitVec 64).setWidth 32 = BitVec.ofNat 32 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofNat, Nat.shiftRight_zero, Nat.reducePow]
  omega

theorem al_of_mod (sp : BitVec 64) (h : sp.toNat % 16 = 0) : (sp &&& 15#64 == 0#64) = true := by
  have e : (sp &&& 15#64).toNat = sp.toNat % 16 := by
    simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod sp.toNat 4
  rw [beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [e, h]; rfl

theorem and_neg16 (x : BitVec 64) (h : x.toNat % 16 = 0) : x &&& -16#64 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  have hb : ∀ j : Fin 64, (-16#64 : BitVec 64).getLsbD j.val = decide (4 ≤ j.val) := by decide
  rw [hb ⟨i, hi⟩]
  by_cases h4 : 4 ≤ i
  · simp [h4]
  · simp only [h4, decide_false, Bool.and_false]
    simp only [BitVec.getLsbD, Nat.testBit, Nat.shiftRight_eq_div_pow]
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases this with rfl | rfl | rfl | rfl <;> simp <;> omega

/-- Combines the 432 bytes left below `sp0 - 48` by `musl_start_block` with the remaining stack into `stackAt (sp0 - 48) stk ∗ anyHeap`. -/
theorem stack_rebuild (sp lo : BitVec 64) (L stk : Nat)
    (hsp : sp.toNat = lo.toNat + L + 480) (hstk : stk ≤ L + 432) :
    memRegion (sp - 480#64) 432 ∗ memRegion lo L ⊢ stackAt (sp - 48#64) stk ∗ anyHeap := by
  have hlt := sp.isLt
  have e1 : sp - 480#64 = lo + BitVec.ofNat 64 L := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  rw [e1, sepConj_comm, ← memRegion_split lo L 432 (by omega)]
  have e2 : sp - 48#64 - BitVec.ofNat 64 stk = lo + BitVec.ofNat 64 (L + 432 - stk) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  unfold stackAt
  rw [e2, memRegion_split' (b := lo) (n := L + 432 - stk) (k := stk) (N := L + 432) (by omega) rfl
    (by omega), sepConj_comm]
  exact sepConj_mono_right (entails_anyHeap _)

/-! ## ELF Header and Segment Facts -/

theorem wf_phent (elf : ElfImage) (hwf : elf.WellFormed = true) : elf.phent = 56 := by
  unfold ElfImage.WellFormed at hwf
  simp only [Bool.and_eq_true, beq_iff_eq] at hwf
  exact hwf.1.1.1.1.2

theorem entry_bound (elf : ElfImage) (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ stackBase) : elf.entry.toNat + 4 ≤ stackBase := by
  have hsegs := segs_below elf hwf hbrk
  unfold ElfImage.WellFormed at hwf
  simp only [Bool.and_eq_true] at hwf
  have he := hwf.1.1.2
  unfold entryInExecRegion at he
  simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at he
  obtain ⟨-, r, hr, h⟩ := he
  have h4 := h.2
  have := hsegs r hr
  omega

/-- Read-only ELF segment-slice witnesses for the 17 program-header words read by `StartPhdrs`. -/
structure PhdrsMapped (elf : ElfImage) (ph : BitVec 64) : Prop where
  p0_type : SegSlice elf ph (unpack32 6#32) .ro
  p0_vaddr : SegSlice elf (ph + 16#64) (unpack64 ph) .ro
  p1_type : SegSlice elf (ph + 56#64) (unpack32 1#32) .ro
  p2_type : SegSlice elf (ph + 112#64) (unpack32 1#32) .ro
  p3_type : SegSlice elf (ph + 168#64) (unpack32 1#32) .ro
  p4_type : SegSlice elf (ph + 224#64) (unpack32 1#32) .ro
  p5_type : SegSlice elf (ph + 280#64) (unpack32 1#32) .ro
  p6_type : SegSlice elf (ph + 336#64) (unpack32 1#32) .ro
  p7_type : SegSlice elf (ph + 392#64) (unpack32 1#32) .ro
  p8_type : SegSlice elf (ph + 448#64) (unpack32 1#32) .ro
  p9_type : SegSlice elf (ph + 504#64) (unpack32 7#32) .ro
  p9_vaddr : SegSlice elf (ph + 520#64) (unpack64 0#64) .ro
  p9_filesz : SegSlice elf (ph + 536#64) (unpack64 0#64) .ro
  p9_memsz : SegSlice elf (ph + 544#64) (unpack64 0#64) .ro
  p9_align : SegSlice elf (ph + 552#64) (unpack64 0#64) .ro
  p10_type : SegSlice elf (ph + 560#64) (unpack32 0x6474e551#32) .ro
  p10_memsz : SegSlice elf (ph + 600#64) (unpack64 0#64) .ro

/-- ELF segment-slice hypotheses required by `musl_startup` (entry text, program headers, and musl writable statics). -/
structure CliElfMusl (elf : ElfImage) (code : List (BitVec 8)) : Prop where
  entry_page : elf.entry &&& 0xfff#64 = 0#64
  text : SegSlice elf elf.entry code .rx
  phnum : elf.phnum = 11
  phdrs : PhdrsMapped elf elf.phdrVaddr
  phdr_ne : elf.phdrVaddr + 504#64 ≠ 0#64
  rw : ∃ h0 g3 g4 ia F : BitVec 64, h0.extractLsb' 0 32 = 0x20000#32 ∧
    SegSlice elf (elf.entry + 0x2000#64) (unpackL (muslRwWords h0 g3 g4 ia F)) .rw

theorem ro32_intro {elf : ElfImage} {a : BitVec 64} {v : BitVec 32}
    (h : SegSlice elf a (unpack32 v) .ro) (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ stackBase) {inputs : ProcessInputs} {s0 : State}
    (hload : elf.loadState inputs = .ok s0) {P : SepProp} (hP : s0.mem ⊨ P) :
    s0.mem ⊨ (a ↦₃₂ᵣ v) ∗ P := by
  rw [pointsTo32RO_eq_pointsToBytesRO]
  exact Satisfies.of_holdsBytes_ro (h.holdsBytes hwf hbrk hload)
    (by rw [unpack32_length]; decide) hP

theorem ro64_intro {elf : ElfImage} {a : BitVec 64} {v : BitVec 64}
    (h : SegSlice elf a (unpack64 v) .ro) (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ stackBase) {inputs : ProcessInputs} {s0 : State}
    (hload : elf.loadState inputs = .ok s0) {P : SepProp} (hP : s0.mem ⊨ P) :
    s0.mem ⊨ (a ↦₆₄ᵣ v) ∗ P := by
  rw [pointsTo64RO_eq_pointsToBytesRO]
  exact Satisfies.of_holdsBytes_ro (h.holdsBytes hwf hbrk hload)
    (by rw [unpack64_length]; decide) hP

theorem sat_startPhdrs {elf : ElfImage} {ph : BitVec 64} (h : PhdrsMapped elf ph)
    (hwf : elf.WellFormed = true) (hbrk : elf.brkStart.toNat ≤ stackBase)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0)
    {P : SepProp} (hP : s0.mem ⊨ P) : s0.mem ⊨ StartPhdrs ph ∗ P := by
  have r32 : ∀ {a : BitVec 64} {v : BitVec 32} {Q : SepProp},
      SegSlice elf a (unpack32 v) .ro → s0.mem ⊨ Q → s0.mem ⊨ (a ↦₃₂ᵣ v) ∗ Q :=
    fun hs hQ => ro32_intro hs hwf hbrk hload hQ
  have r64 : ∀ {a : BitVec 64} {v : BitVec 64} {Q : SepProp},
      SegSlice elf a (unpack64 v) .ro → s0.mem ⊨ Q → s0.mem ⊨ (a ↦₆₄ᵣ v) ∗ Q :=
    fun hs hQ => ro64_intro hs hwf hbrk hload hQ
  simp only [StartPhdrs, sepConj_assoc]
  exact r32 h.p0_type (r64 h.p0_vaddr (r32 h.p1_type (r32 h.p2_type (r32 h.p3_type
    (r32 h.p4_type (r32 h.p5_type (r32 h.p6_type (r32 h.p7_type (r32 h.p8_type
    (r32 h.p9_type (r64 h.p9_vaddr (r64 h.p9_filesz (r64 h.p9_memsz (r64 h.p9_align
    (r32 h.p10_type (r64 h.p10_memsz hP))))))))))))))))

theorem codeLoaded_of_text {elf : ElfImage} {code : List (BitVec 8)} (hC : CliElfMusl elf code)
    (hwf : elf.WellFormed = true) (hbrk : elf.brkStart.toNat ≤ stackBase)
    {inputs : ProcessInputs} {s0 : State} (hload : elf.loadState inputs = .ok s0) :
    ({ base := elf.entry, code } : Program).CodeLoaded s0.mem := by
  have hh := hC.text.holdsBytes hwf hbrk hload
  have hsb := stackBase_eq
  refine Program.CodeLoaded.intro ?_ ?_ (fun i hi => hh i hi)
  · have e : (elf.entry &&& 0xfff#64).toNat = elf.entry.toNat % 4096 := by
      simp only [BitVec.toNat_and]; exact Nat.and_two_pow_sub_one_eq_mod _ 12
    have h0 := congrArg BitVec.toNat hC.entry_page
    rw [e, BitVec.toNat_ofNat] at h0
    show elf.entry.toNat % 4 = 0
    omega
  · show elf.entry.toNat + code.length ≤ 2 ^ 64
    cases code with
    | nil => have := elf.entry.isLt; simp only [List.length_nil]; omega
    | cons b bs =>
      have := hC.text.bound (by simp) hwf hbrk
      omega

/-! ## Stack and Footprint Assembly -/

theorem cStr_eq (p : BitVec 64) : cStrAt p (bytesOfString "libsignal-cli") = StartArgv0 p := by
  unfold cStrAt; exact startArgv0_eq p

/-- Splits `L + 480` zero bytes from `lo` into 60 zero words at `sp - 480` and `memRegion lo L`. -/
theorem zeros_split (sp lo : BitVec 64) (L : Nat) (hsp : sp = lo + BitVec.ofNat 64 (L + 480)) :
    (lo ↦ₛ List.replicate (L + 480) 0#8) ⊢
      ((sp - 480#64) ↦₆₄* List.replicate 60 0#64) ∗ memRegion lo L := by
  have e : lo + BitVec.ofNat 64 L = sp - 480#64 := by
    subst hsp
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  have h1 := pointsToBytes_entails_memRegion lo (List.replicate L 0#8)
  rw [List.length_replicate] at h1
  rw [List.replicate_add, pointsToBytes_append, List.length_replicate, e,
    pointsToWords64_eq_pointsToBytes, unpackL_replicate_zero, sepConj_comm (lo ↦ₛ _)]
  exact sepConj_mono_right h1

theorem pre_assemble {m : Memory} {A P8 C Ar W X Zh Zl Mw R SP L A0 Ph : SepProp}
    (hm : m ⊨ (A ∗ ((P8 ∗ (C ∗ Ar)) ∗ (W ∗ X))) ∗ ((Zh ∗ Zl) ∗ (Mw ∗ R)))
    (hsp : (A ∗ P8 ∗ W) = SP ∗ L) (hc : C = A0)
    (hph : ∀ Q, m ⊨ Q → m ⊨ Ph ∗ Q) :
    m ⊨ SP ∗ A0 ∗ Ph ∗ Mw ∗ Zh ∗ ((L ∗ Ar) ∗ (Zl ∗ (R ∗ X))) := by
  have e : (A ∗ ((P8 ∗ (C ∗ Ar)) ∗ (W ∗ X))) ∗ ((Zh ∗ Zl) ∗ (Mw ∗ R)) =
      (A ∗ P8 ∗ W) ∗ (C ∗ (Mw ∗ (Zh ∗ (Ar ∗ (Zl ∗ (R ∗ X)))))) := by ac_rfl
  rw [e, hsp, hc] at hm
  have h2 := hph _ hm
  have e2 : Ph ∗ ((SP ∗ L) ∗ (A0 ∗ (Mw ∗ (Zh ∗ (Ar ∗ (Zl ∗ (R ∗ X))))))) =
      SP ∗ A0 ∗ Ph ∗ Mw ∗ Zh ∗ ((L ∗ Ar) ∗ (Zl ∗ (R ∗ X))) := by ac_rfl
  rw [e2] at h2
  exact h2

theorem pick3 {A B C D : SepProp} : A ∗ B ∗ C ∗ D ⊢ C ∗ (A ∗ B ∗ D) := by
  rw [sepConj_left_comm B C D, sepConj_left_comm A C]
  exact Entails.refl _

theorem fini_intro (B F : BitVec 64) :
    ((B + 0x2030#64) ↦₆₄ᵣ F) ∗ ((B + 0x2038#64) ↦₆₄ᵣ F) ⊢ muslFiniFr B := by
  unfold muslFiniFr
  exact Entails.sepExists_right F (Entails.refl _)

theorem argvAt_cli (a p : BitVec 64) (ss : List (List (BitVec 8))) :
    (a ↦₆₄ p) ∗ StartArgv0 p ∗ argvAt (a + 8#64) ss ⊢
      argvAt a (bytesOfString "libsignal-cli" :: ss) := by
  simp only [argvAt]
  refine Entails.sepExists_right p ?_
  rw [cStr_eq]
  exact Entails.refl _

theorem post_finish {m : Memory}
    {SP A0 F1 F2 Mr L Ar Zl R X SPr P8 F1r F2r Garg Gstk Fini : SepProp}
    (hm : m ⊨ SP ∗ A0 ∗ F1 ∗ F2 ∗ Mr ∗ ((L ∗ Ar) ∗ (Zl ∗ (R ∗ X))))
    (hSP : SP ⊢ P8 ∗ SPr) (hfz : F1 ∗ F2 ⊢ |==> (F1r ∗ F2r)) (hfini : F1r ∗ F2r ⊢ Fini)
    (harg : P8 ∗ A0 ∗ Ar ⊢ Garg) (hstk : Mr ∗ Zl ⊢ Gstk ∗ anyHeap) :
    m ⊨ (Garg ∗ Gstk ∗ R) ∗ Fini := by
  have e1 : SP ∗ A0 ∗ F1 ∗ F2 ∗ Mr ∗ ((L ∗ Ar) ∗ (Zl ∗ (R ∗ X))) =
      (F1 ∗ F2) ∗ (SP ∗ (A0 ∗ (Mr ∗ (L ∗ (Ar ∗ (Zl ∗ (R ∗ X))))))) := by ac_rfl
  rw [e1] at hm
  have h2 := Satisfies.of_bupd_frame_left hfz hm
  have h3 := Arm64.Satisfies.mono (sepConj_mono hfini (sepConj_mono_left hSP)) h2
  have e2 : Fini ∗ ((P8 ∗ SPr) ∗ (A0 ∗ (Mr ∗ (L ∗ (Ar ∗ (Zl ∗ (R ∗ X))))))) =
      ((((P8 ∗ A0 ∗ Ar) ∗ (Mr ∗ Zl)) ∗ R) ∗ Fini) ∗ (SPr ∗ L ∗ X) := by ac_rfl
  rw [e2] at h3
  have h4 := Arm64.Satisfies.mono
    (sepConj_mono_left (sepConj_mono_left (sepConj_mono_left (sepConj_mono harg hstk)))) h3
  have e3 : (((Garg ∗ (Gstk ∗ anyHeap)) ∗ R) ∗ Fini) ∗ (SPr ∗ L ∗ X) =
      ((Garg ∗ Gstk ∗ R) ∗ Fini) ∗ (anyHeap ∗ SPr ∗ L ∗ X) := by ac_rfl
  rw [e3] at h4
  exact sat_of_entails_frame h4 (Entails.refl _)

theorem toNat_ofNat_add (a b : Nat) (h : a + b < 2 ^ 64) :
    (BitVec.ofNat 64 a + BitVec.ofNat 64 b).toNat = a + b := by
  rw [BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem sub_add_eq' (a b : Nat) (h : b + 8371824 ≤ a) : a = b + (a - b - 480 + 480) := by omega

theorem argvBase_ne (argv : List String)
    (hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ 16384) :
    argvBase (cliStrs argv) ≠ 0#64 := by
  obtain ⟨-, -, hlo⟩ := cli_bounds argv hfits
  have htop := top_eq
  have hsb := stackBase_eq
  have hle := le_alignUp16 (upperRawLen (cliStrs argv))
  intro h
  have h1 := congrArg BitVec.toNat h
  unfold argvBase platformAddr at h1
  simp only [BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat] at h1
  have : sp0 (cliStrs argv) ≤ infoBase (cliStrs argv) := by unfold sp0; omega
  have : infoBase (cliStrs argv) + (16 + infoPadLen (cliStrs argv)) + 8 ≤ top := by
    unfold infoBase infoLen infoPadLen upperRawLen at *; omega
  omega

/-! ## Argument and Stack Budgets -/

/-- Maximum initial-stack byte budget (16 KiB) for CLI arguments, NUL terminators, and `argv` pointers. -/
abbrev cliArgBudget : Nat := 16384

/-- Stack byte budget available to `main` below its entry `sp`: `cliStackSize - cliArgBudget - 448`. -/
abbrev cliStackBudget : Nat := cliStackSize - cliArgBudget - 448

theorem stackBudget_le {stk : Nat} (h : stk ≤ cliStackBudget) : stk ≤ 8371776 := by
  have := cliStackSize_eq
  unfold cliStackBudget cliArgBudget at h
  omega

set_option maxHeartbeats 3200000 in
/-- Under `CliElfMusl` and `ArgvFitsInitialStack`, loading the CLI succeeds and `Program.ofImage img E`
steps from `_start` to `main` (`entry - 89668`) with `w0 = argc`, `x1 = argv`, `sp = sp0 - 48`,
`lr = entry + 0x854`, unchanged filesystem and trace, and `(argvAt x1 argv ∗ stackAt sp stk ∗ R) ∗ muslFiniFr entry`. -/
theorem musl_startup {li : Obj.LinkedImage} {img : Obj.Image} (himg : Obj.Loads li img)
    (E : String → Option (State → State)) {elf : ElfImage} {code : List (BitVec 8)}
    (hC : CliElfMusl elf code) (hwf : elf.WellFormed = true)
    (hbrk : elf.brkStart.toNat ≤ stackBase)
    (hend : img.base.toNat + img.code.length ≤ elf.entry.toNat)
    (hf : MuslStartFetch ({ code } : Program) 0#64)
    (argv : List String) (stdin : List (BitVec 8)) (files : List (String × List (BitVec 8)))
    (dirs : List String)
    (hargs : ∀ a ∈ argv, ∀ c ∈ a.toList, 0 < c.toNat ∧ c.toNat < 128)
    (hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ cliArgBudget)
    (hdirs : ∀ d ∈ dirs, Arm64.hasLeadingSlash d = false ∧ Arm64.hasDotDot d = false)
    (hfiles : ∀ f ∈ files,
      (Arm64.hasLeadingSlash f.1 = false ∧ Arm64.hasDotDot f.1 = false) ∧
        f.2.length ≤ Arm64.MAX_LFS_FILESIZE)
    (stk : Nat) (hstk : stk ≤ cliStackBudget) {R : SepProp} {S : Nat → Prop}
    (hR : ∀ s0, elf.loadState (processInputs ("libsignal-cli" :: argv) stdin files dirs) = .ok s0 →
      SupportedOn 0#64 S s0.mem R)
    (hS : ∀ k, S k → k < stackBase ∧
      ¬((elf.entry + 0x2000#64).toNat ≤ k ∧ k < (elf.entry + 0x2000#64).toNat + 600)) :
    ∃ s0 sm, elf.loadState (processInputs ("libsignal-cli" :: argv) stdin files dirs) = .ok s0 ∧
      Steps (Program.ofImage img E) s0 sm ∧ sm.pc = elf.entry - 85504#64 ∧
      sm.status = .Running ∧ sm.spAligned = true ∧ sm.sp = s0.sp - 48#64 ∧
      (sm.readReg64 .x0).setWidth 32 = BitVec.ofNat 32 (argv.length + 1) ∧
      sm.readReg64 .x1 = s0.sp + 8#64 ∧ sm.readReg64 .lr = elf.entry + 0x854#64 ∧
      sm.fs = s0.fs ∧ sm.trace = s0.trace ∧
      (sm.mem ⊨ (argvAt (sm.readReg64 .x1) (cliStrs argv) ∗ stackAt sm.sp stk ∗ R) ∗
        muslFiniFr elf.entry) ∧
      stk ≤ sm.sp.toNat := by
  replace hstk : stk ≤ 8371776 := stackBudget_le hstk
  replace hfits : (argv.map fun a => a.length + 1 + 8).sum ≤ 16384 := hfits
  obtain ⟨hload, hsp0, hal16, hlo, hlen, hfr, hzero, -⟩ :=
    loadState_cli_layout elf argv stdin files dirs hwf hbrk hargs hfits hdirs hfiles
  generalize elf.rawState (processInputs ("libsignal-cli" :: argv) stdin files dirs) = s0
    at hload hsp0 hfr hzero
  obtain ⟨hpc0, hrun0, -, -⟩ := loadState_fields hload
  obtain ⟨hfit, -, -⟩ := cli_bounds argv hfits
  have hphent := wf_phent elf hwf
  have heb := entry_bound elf hwf hbrk
  have hsb := stackBase_eq
  have htop := top_eq
  have hspn := toNat_sp0 (cliStrs argv)
  have hk : (cliStrs argv).length < 2 ^ 31 := by
    have := argv_length_le argv hfits
    rw [cliStrs_length]; omega
  obtain ⟨h0, g3, g4, ia, F, hh0, hrw⟩ := hC.rw
  have hML : (unpackL (muslRwWords h0 g3 g4 ia F)).length = 600 := by
    rw [unpackL_length]; rfl
  have hne : unpackL (muslRwWords h0 g3 g4 ia F) ≠ [] := by
    intro h; have := congrArg List.length h; rw [hML] at this; simp at this
  have hMb := hrw.bound hne hwf hbrk
  rw [hML] at hMb
  have hFs := supportedOn_of_holdsBytes_rw (by rw [hspn]; omega) hfr
  have hZb : Obj.HoldsBytes s0.mem (BitVec.ofNat 64 stackBase)
      (List.replicate (sp0 (cliStrs argv) - stackBase - 480 + 480) 0#8) (fun _ => .rw) := by
    apply holdsBytes_zero
    intro i hi
    have hi' : i < sp0 (cliStrs argv) - stackBase - 480 + 480 := hi
    have e := toNat_ofNat_add stackBase i (by omega)
    apply hzero
    · rw [e]; exact Nat.le_add_right _ _
    · rw [e]; clear e; omega
  have hZs := supportedOn_of_holdsBytes_rw (by rw [toNat_stackBase, List.length_replicate]; omega)
    hZb
  have hMs := supportedOn_of_holdsBytes_rw (by omega) (hrw.holdsBytes hwf hbrk hload)
  rw [← pointsToWords64_eq_pointsToBytes] at hMs
  have hRs := hR s0 hload
  have hMR := hMs.sepConj hRs (by
    intro k h1 h2
    obtain ⟨h1a, h1b⟩ := h1
    exact (hS k h2).2 ⟨h1a, by omega⟩)
  have hZMR := hZs.sepConj hMR (by
    intro k h1 h2
    obtain ⟨h1a, h1b⟩ := h1
    simp only [toNat_stackBase, List.length_replicate] at h1a h1b
    rcases h2 with ⟨h2a, h2b⟩ | h2
    · omega
    · have := (hS k h2).1; omega)
  have hall := hFs.sepConj hZMR (by
    intro k h1 h2
    obtain ⟨h1a, h1b⟩ := h1
    rw [hspn] at h1a h1b
    rcases h2 with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩ | h2
    · simp only [toNat_stackBase, List.length_replicate] at h2a h2b; omega
    · omega
    · have := (hS k h2).1; omega)
  have hsat := hall.satisfies
  have hzsp : s0.sp = BitVec.ofNat 64 stackBase +
      BitVec.ofNat 64 (sp0 (cliStrs argv) - stackBase - 480 + 480) := by
    rw [hsp0, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat 64) (sub_add_eq' _ _ hlo)
  have hsat2 := Arm64.Satisfies.mono (sepConj_mono
    (frame_split elf (cliStrs argv) (bytesOfString "libsignal-cli") (argv.map bytesOfString) rfl
      hfit)
    (sepConj_mono_left (zeros_split s0.sp _ _ hzsp))) hsat
  rw [← hsp0] at hsat2
  have hpre := pre_assemble hsat2
    (startProc_eq elf (cliStrs argv) s0.sp
      (s0.sp + BitVec.ofNat 64 (8 * ((cliStrs argv).length + 2)))
      (BitVec.ofNat 64 (cliStrs argv).length) hphent hC.phnum)
    (cStr_eq _) (fun Q hQ => sat_startPhdrs hC.phdrs hwf hbrk hload hQ)
  have hend' : img.base.toNat + img.code.length ≤ elf.entry.toNat := hend
  obtain ⟨sm, hsteps, hpc', hrun', hregs, hpost⟩ := musl_start_block himg E (B := elf.entry)
    (code := code) hend' (by omega) hf hC.entry_page (s := s0)
    (codeLoaded_of_text hC hwf hbrk hload) hpc0 hrun0
    (al_of_mod _ (by rw [hsp0, hspn]; exact hal16))
    (and_neg16 _ (by rw [hsp0, hspn]; exact hal16))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (envp_eq s0.sp (cliStrs argv).length hk).symm
    (argvBase_ne argv hfits) hC.phdr_ne h0 g3 g4 ia F hh0 hpre
  delta Hop7Regs at hregs
  obtain ⟨hsp', hx0, hx1, -, hlr, hfs, htr⟩ := hregs
  refine ⟨s0, sm, hload, hsteps, hpc', hrun', ?_, hsp', ?_, hx1, hlr, hfs, htr, ?_, ?_⟩
  · unfold State.spAligned
    rw [hsp']
    exact spAligned_sub48 _ (al_of_mod _ (by rw [hsp0, hspn]; exact hal16))
  · rw [hx0, cliStrs_length]
    exact x0_eq _
  · rw [hx1, hsp']
    exact post_finish hpost pick3
      (bupd_sep (pointsTo64_freeze_ro _ _) (pointsTo64_freeze_ro _ _)) (fini_intro _ _)
      (argvAt_cli _ _ _)
      (stack_rebuild s0.sp (BitVec.ofNat 64 stackBase) (sp0 (cliStrs argv) - stackBase - 480) stk
        (by rw [hsp0, hspn, toNat_stackBase]; omega) (by omega))
  · rw [hsp', hsp0]
    have := sp0_le_top (cliStrs argv)
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega

end CryptoVerification.SignalSession.MuslElf
