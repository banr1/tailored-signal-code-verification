/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Multi
public import ProofLib.Process.FsLemmas
public import ProofLib.SepLogic.WP.StepsProcess

/-!
# Placement-Generic Block Execution Helpers

Provides reusable helpers for stepping rebased `Obj.MultiPlacedLib` blocks across straight-line
segments and subroutine calls, including `sepWP_block_to_rebase`, `seqCodeLoaded`,
`sepWP_seg_rebase`, and `sepWP_seg_rebase_pure` for lifting `svc #0`-free segments (`checkBlockNoSvc0`)
with OS and VM process fields unchanged.
-/

@[expose] public section

set_option autoImplicit false

namespace ProofLib

open Arm64 Arm64.Obj Arm64.Process ProofLib.StdStartup

section
arm64_proof_prelude

/-- Little-endian bytes of a list of 32-bit instruction words. -/
def wordsLE (ws : List (BitVec 32)) : List (BitVec 8) :=
  ws.flatMap fun w => [w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8]

/-- Wrap a `subroutine_ok` contract in `lib.withCodeLoaded mpl`. -/
theorem subroutine_ok_withCodeLoaded (lib : MultiPlacedLib) (mpl : MultiPlacement)
    {α : Type} {P : Program} {entry : BitVec 64} {spec : Spec α}
    (hraw : subroutine_ok P entry spec) :
    subroutine_ok P entry (lib.withCodeLoaded mpl spec) := by
  apply subroutine_ok.of_codeLoaded
  intro x R s0 hpc hrun hpre hsp _hcl
  have hpre' : s0.mem ⊨ spec.pre x s0 ∗ R := by
    have hp : s0.mem ⊨ ⌜lib.CodeLoaded mpl s0.mem⌝ ∗ (spec.pre x s0 ∗ R) := by
      simpa [MultiPlacedLib.withCodeLoaded, sepConj_assoc] using hpre
    exact ((satisfies_pure_sepConj _ _ _).mp hp).2
  exact hraw.mono_outcome x R s0 hpc hrun hpre' hsp (fun _ hout => hout)

/-- Rewrite `lib.fnAddr mpl sym` to `mpl.base j` for a block-offset-`0` symbol `sym`. -/
theorem fnAddr_eq_base {lib : MultiPlacedLib} {mpl : MultiPlacement}
    (hpl : lib.Placeable mpl) (j : Nat) (sym : String)
    (hj : j < lib.blocks.length := by decide)
    (hl : lookup sym lib.blocks[j].symbols = some 0 := by decide) :
    lib.fnAddr mpl sym = mpl.base j := by
  have hblk := lookupBlockSym_of_lookup hj hpl.symbols_nodup hl
  simp [MultiPlacedLib.fnAddr, hblk]

/-- Switch a `SepWP` goal on `lib.blockProgram mpl j` to the rebased block program
    `((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none))` where
    `gen_placed_fetches` lemmas fire. -/
theorem sepWP_block_to_rebase {lib : MultiPlacedLib} {mpl : MultiPlacement} (j : Nat)
    (hj : j < lib.blocks.length) {target_pc : BitVec 64} {s : State}
    {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : lib.CodeLoaded mpl s.mem)
    (h : SepWP ((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none))
      target_pc s Pre post oom) :
    SepWP (lib.blockProgram mpl j) target_pc s Pre post oom :=
  SepWP.of_sameHooks
    (by intro pc; simp)
    rfl ((hcl j hj).of_base_code rfl rfl) h

/-- Split a `SepWP` proof (including non-trivial `oom` obligations) at an intermediate PC `mid`
    and re-establish `lib.CodeLoaded mpl sm.mem` at `mid` across any preceding steps. -/
theorem seqCodeLoaded {lib : MultiPlacedLib} {mpl : MultiPlacement}
    {prog : Program} {mid target_pc : BitVec 64}
    {s : State} {Pre : SepProp} {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : lib.CodeLoaded mpl s.mem)
    (h : SepWP prog mid s Pre (fun sm Pm => lib.CodeLoaded mpl sm.mem → SepWP prog target_pc sm Pm post oom) oom) :
    SepWP prog target_pc s Pre post oom := by
  refine SepWP.of_reaches_pc fun R hm hL_P => ?_
  obtain ⟨sm, hsteps1, hout1⟩ := SepWP.to_reaches_pc h hm hL_P
  rcases hout1 with ⟨_, _, _, hmm, hcont⟩ | ⟨hrun_m, hoom⟩
  · obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc
      (hcont fun k hk => hsteps1.codeLoaded (hcl k hk)) hmm (hsteps1.codeLoaded hL_P)
    exact ⟨sf, hsteps1.trans hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hrun_m, hoom⟩⟩

/-- Run a straight-line segment of block `j` (`(lib.blockProgram mpl j).rebase ...`)
    up to `mid` from any hook-free `Syscall.standard` program `P`, refreshing `CodeLoaded`. -/
theorem sepWP_seg_rebase {lib : MultiPlacedLib} {mpl : MultiPlacement} {P : Program}
    (hext : ∀ pc, P.externAt? pc = none) (hsvc : P.svc = Syscall.standard)
    (j : Nat) (hj : j < lib.blocks.length)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp} {post : State → SepProp → Prop}
    {oom : State → SepProp}
    (hcl : lib.CodeLoaded mpl s.mem)
    (hseg : SepWP ((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none))
      mid s Pre (fun sm Pm => lib.CodeLoaded mpl sm.mem → SepWP P target_pc sm Pm post oom) oom) :
    SepWP P target_pc s Pre post oom :=
  seqCodeLoaded hcl <| SepWP.of_sameHooks (by intro pc; simp [hext pc])
    (by simp [hsvc, MultiPlacedLib.blockProgram, PlacedLib.program]) ((hcl j hj).of_base_code rfl rfl) hseg

/-- Relocation kinds whose patched encodings cannot produce `svc #0` (`0xd400_0001`). -/
def relocKindSafeNoSvc0 : Obj.RelocKind → Bool
  | .call26 | .jump26 | .addLo12
  | .ldst8Lo12 | .ldst16Lo12 | .ldst32Lo12 | .ldst64Lo12 | .ldst128Lo12 => true
  | .adrpHi21 => true
  | _ => false

/-- Byte-level check that no patched word in `blk` starting at `off` encodes `svc #0`. -/
def checkBytesNoSvc0 (blk : Obj.CodeBlock) : Nat → List (BitVec 8) → Bool
  | _, [] => true
  | off, b0 :: b1 :: b2 :: b3 :: rest =>
    let w := Obj.wordOfBytesLE [b0, b1, b2, b3] 0
    (match blk.relocAt? off with
     | none => w != 0xd400_0001#32
     | some r => ((w &&& 0xfc00_0000#32) != 0xd400_0000#32) &&
        ((r.kind != .adrpHi21) || ((w &&& 0x0400_0000#32) == 0#32))) &&
    checkBytesNoSvc0 blk (off + 4) rest
  | _, _ => false

/-- Decidable check that a `CodeBlock` contains no `svc #0` instruction under any valid placement. -/
def checkBlockNoSvc0 (blk : Obj.CodeBlock) : Bool :=
  checkBytesNoSvc0 blk 0 blk.code && blk.relocs.all (fun r => relocKindSafeNoSvc0 r.kind)

private theorem checkBytesNoSvc0_wordOfBytesLE (blk : Obj.CodeBlock) :
    ∀ (k off : Nat) (bs : List (BitVec 8)), checkBytesNoSvc0 blk off bs = true → 4 * k + 4 ≤ bs.length →
      (let w := Obj.wordOfBytesLE bs (4 * k)
       match blk.relocAt? (off + 4 * k) with
       | none => w != 0xd400_0001#32
       | some r => ((w &&& 0xfc00_0000#32) != 0xd400_0000#32) &&
         ((r.kind != .adrpHi21) || ((w &&& 0x0400_0000#32) == 0#32))) = true
  | 0, off, bs, hchk, hlen => by
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [checkBytesNoSvc0, Bool.and_eq_true] at hchk; simpa [Obj.wordOfBytesLE] using hchk.1
  | k + 1, off, bs, hchk, hlen => by
    match bs with
    | [] | [_] | [_, _] | [_, _, _] => simp only [List.length_cons, List.length_nil] at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      simp only [checkBytesNoSvc0, Bool.and_eq_true] at hchk
      have ih := checkBytesNoSvc0_wordOfBytesLE blk k (off + 4) rest hchk.2
        (by simp only [List.length_cons] at hlen; omega)
      have h0 : 4 * (k + 1) = 4 * k + 4 := by omega
      have heq_w : Obj.wordOfBytesLE (b0 :: b1 :: b2 :: b3 :: rest) (4 * (k + 1)) =
          Obj.wordOfBytesLE rest (4 * k) := by
        simp only [Obj.wordOfBytesLE, h0]; rfl
      have heq_off : off + 4 * (k + 1) = off + 4 + 4 * k := by omega
      simpa [heq_w, heq_off] using ih

private theorem checkBytesNoSvc0_mod4 (blk : Obj.CodeBlock) :
    ∀ (off : Nat) (bs : List (BitVec 8)), checkBytesNoSvc0 blk off bs = true → bs.length % 4 = 0
  | _, [], _ => rfl
  | _, [_], h | _, [_, _], h | _, [_, _, _], h => by simp [checkBytesNoSvc0] at h
  | off, _ :: _ :: _ :: _ :: rest, h => by
    simp only [checkBytesNoSvc0, Bool.and_eq_true] at h
    have ih := checkBytesNoSvc0_mod4 blk (off + 4) rest h.2; simp only [List.length_cons]; omega

private theorem adrWord_adrTemplate_ne_svc0 (w : BitVec 32) (place target : BitVec 64) :
    Obj.adrWord (Obj.adrTemplate w) place target ≠ 0xd400_0001#32 := by
  intro h; have hb := congrArg (fun v => v.getLsbD 26) h
  simp [Obj.adrWord, Obj.adrWordOff, Obj.adrTemplate] at hb

private theorem adrpWord_ne_svc0 {w : BitVec 32} (hw26 : w &&& 0x0400_0000#32 = 0#32)
    (place target : BitVec 64) : Obj.adrpWord w place target ≠ 0xd400_0001#32 := by
  intro h
  have hb26 : w[26] = false := by
    have := congrArg (fun v => v.getLsbD 26) hw26
    simpa [BitVec.getLsbD_eq_getElem (by decide : 26 < 32)] using this
  have hb := congrArg (fun v => v.getLsbD 26) h; simp [Obj.adrpWord, Obj.adrpWordOff, hb26] at hb

private theorem mask_top6_shiftLeft_10 (x : BitVec 32) :
    ((x &&& 0xfff#32) <<< 10) &&& 0xfc00_0000#32 = 0#32 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have hm : (!decide (i < 10) && (0xfff#32).getLsbD (i - 10) && (0xfc00_0000#32).getLsbD i) = false := by
    revert hi; revert i; decide
  rw [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_zero]
  simp only [hi, decide_true, Bool.true_and]
  cases h1 : (!decide (i < 10)) <;> cases h2 : (0xfff#32).getLsbD (i - 10) <;>
    cases h3 : (0xfc00_0000#32).getLsbD i <;> (rw [h1, h2, h3] at hm; first | contradiction | simp)

private theorem branchWord_ne_svc0 {w : BitVec 32} (hw : w &&& 0xfc00_0000#32 ≠ 0xd400_0000#32)
    (place target : BitVec 64) : Obj.branchWord w place target ≠ 0xd400_0001#32 := by
  intro h; have hm := congrArg (· &&& 0xfc00_0000#32) h
  have hr : ((Obj.branchWord w place target) &&& 0xfc00_0000#32) = w &&& 0xfc00_0000#32 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    have hf : ((0x03ff_ffff#32).getLsbD i && (0xfc00_0000#32).getLsbD i) = false := by
      revert hi; revert i; decide
    dsimp only [Obj.branchWord]
    rw [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_and]
    cases h1 : (0x03ff_ffff#32).getLsbD i <;> cases h2 : (0xfc00_0000#32).getLsbD i <;>
      (rw [h1, h2] at hf; first | contradiction | simp)
  rw [hr] at hm; exact hw hm

private theorem lo12Word_ne_svc0 (scale : Nat) {w : BitVec 32}
    (hw : w &&& 0xfc00_0000#32 ≠ 0xd400_0000#32) (target : BitVec 64) :
    Obj.lo12Word scale w target ≠ 0xd400_0001#32 := by
  intro h; have hm := congrArg (· &&& 0xfc00_0000#32) h
  have hr : (Obj.lo12Word scale w target &&& 0xfc00_0000#32) = w &&& 0xfc00_0000#32 := by
    dsimp only [Obj.lo12Word]
    rw [BitVec.and_or_distrib_right, mask_top6_shiftLeft_10, BitVec.or_zero, BitVec.and_assoc]; rfl
  rw [hr] at hm; exact hw hm

private theorem patchedWord_not_isSvc0 {blk : Obj.CodeBlock} (pl : Obj.Placement)
    (hchk : checkBlockNoSvc0 blk = true) {off : Nat}
    (hal : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) :
    Arm64.isSvc0Word (blk.patchedWord pl off) = false := by
  unfold checkBlockNoSvc0 at hchk; simp only [Bool.and_eq_true, List.all_eq_true] at hchk
  rcases hchk with ⟨hbytes, hrelocs⟩
  have hoff_eq : 4 * (off / 4) = off := by omega
  have hw_off := checkBytesNoSvc0_wordOfBytesLE blk (off / 4) 0 blk.code hbytes (by omega)
  simp only [Nat.zero_add, hoff_eq] at hw_off
  change (match blk.relocAt? off with
    | none => blk.wordAt off != 0xd400_0001#32
    | some r => ((blk.wordAt off &&& 0xfc00_0000#32) != 0xd400_0000#32) &&
      ((r.kind != .adrpHi21) || ((blk.wordAt off &&& 0x0400_0000#32) == 0#32))) = true at hw_off
  suffices hne : blk.patchedWord pl off ≠ 0xd400_0001#32 from beq_false_of_ne hne
  unfold Obj.CodeBlock.patchedWord
  cases hr : blk.relocAt? off with
  | none => rw [hr] at hw_off; exact bne_iff_ne.mp hw_off
  | some r =>
    dsimp only; rw [hr] at hw_off; simp only [Bool.and_eq_true] at hw_off
    have hw_top : blk.wordAt off &&& 0xfc00_0000#32 ≠ 0xd400_0000#32 := bne_iff_ne.mp hw_off.1
    have hw_adrp := hw_off.2
    have hrmem : r ∈ blk.relocs := List.mem_of_find?_eq_some hr
    have hksafe := hrelocs r hrmem
    have hngot : r.kind.isGotOrTlsIe = false := by
      cases hk : r.kind <;> rw [hk] at hksafe <;> first | contradiction | rfl
    simp only [hngot, Bool.false_and]
    split
    · decide
    · split
      · exact adrWord_adrTemplate_ne_svc0 _ _ _
      · cases hk : r.kind
        all_goals rw [hk] at hksafe; try contradiction
        · exact branchWord_ne_svc0 hw_top _ _
        · exact branchWord_ne_svc0 hw_top _ _
        · rw [hk] at hw_adrp; simp only [bne_self_eq_false, Bool.false_or, beq_iff_eq] at hw_adrp
          exact adrpWord_ne_svc0 hw_adrp _ _
        · exact lo12Word_ne_svc0 0 hw_top _
        · exact lo12Word_ne_svc0 0 hw_top _
        · exact lo12Word_ne_svc0 1 hw_top _
        · exact lo12Word_ne_svc0 2 hw_top _
        · exact lo12Word_ne_svc0 3 hw_top _
        · exact lo12Word_ne_svc0 4 hw_top _

private theorem bytesAllWords_of_drop4 {pw : BitVec 32 → Bool} :
    ∀ (n : Nat) (bs : List (BitVec 8)), bs.length = 4 * n →
      (∀ k < n, match bs.drop (4 * k) with
        | b0 :: b1 :: b2 :: b3 :: _ => pw (b3 ++ b2 ++ b1 ++ b0) = true | _ => True) →
      Arm64.bytesAllWords pw bs = true
  | 0, bs, hlen, _ => by cases bs with | nil => rfl | cons _ _ => simp at hlen
  | n + 1, bs, hlen, h => by
    match bs with
    | [] => simp at hlen
    | [_] | [_, _] | [_, _, _] => simp at hlen; omega
    | b0 :: b1 :: b2 :: b3 :: rest =>
      have h0 : pw (b3 ++ b2 ++ b1 ++ b0) = true := by simpa using h 0 (Nat.zero_lt_succ n)
      have hrest : Arm64.bytesAllWords pw rest = true :=
        bytesAllWords_of_drop4 n rest (by simp at hlen; omega) fun k hk => by
          have hk' := h (k + 1) (Nat.succ_lt_succ hk); have heq : 4 * (k + 1) = 4 + 4 * k := by omega
          rw [heq, ← List.drop_drop] at hk'; simpa using hk'
      simp [Arm64.bytesAllWords, h0, hrest]

theorem blockProgram_rebase_allInstrs_not_isSvc0 (lib : MultiPlacedLib) (mpl : MultiPlacement)
    (j : Nat) (hchk : checkBlockNoSvc0 (lib.blockLib j).text = true) :
    ((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)).allInstrs (fun i => !i.isSvc0) = true := by
  let prog := (lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let blk := (lib.blockLib j).text; let pl := lib.blockPlacement mpl j
  have hcode : prog.code = blk.patched pl := rfl
  have hmod4 : blk.code.length % 4 = 0 := by
    unfold checkBlockNoSvc0 at hchk; simp only [Bool.and_eq_true] at hchk
    exact checkBytesNoSvc0_mod4 blk 0 blk.code hchk.1
  have hdiv : prog.code.length = 4 * (blk.code.length / 4) := by rw [hcode, Obj.CodeBlock.length_patched]
  refine Program.allInstrs_of_allWords (fun _ _ hd hpw => Arm64.decode_not_isSvc0 hd hpw) ?_
  unfold Program.allWords; refine bytesAllWords_of_drop4 (blk.code.length / 4) prog.code hdiv fun k hk => ?_
  have hal : (4 * k) % 4 = 0 := by omega
  have hlen : 4 * k + 4 ≤ blk.code.length := by omega
  have hrw : prog.readWordOff (4 * k) = some (blk.patchedWord pl (4 * k)) :=
    Obj.CodeBlock.readWordOff_patched hcode hal hlen
  unfold Program.readWordOff at hrw; simp only [hal, ne_eq, not_true_eq_false, ↓reduceIte] at hrw
  match hdrop : prog.code.drop (4 * k) with
  | [] | [_] | [_, _] | [_, _, _] => simp [hdrop] at hrw
  | b0 :: b1 :: b2 :: b3 :: _ =>
    rw [hdrop] at hrw; injection hrw with hw; dsimp only
    rw [hw, patchedWord_not_isSvc0 pl hchk hal hlen]; rfl

private theorem strip_codeLoaded_of_keep {prog : Program} {m : Memory} (hL : prog.CodeLoaded m) :
    prog.CodeLoaded (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := by
  refine Program.CodeLoaded.intro hL.aligned hL.no_wrap fun i hi => ?_
  have hno := hL.no_wrap
  have hsub : prog.base + BitVec.ofNat 64 i - prog.base = BitVec.ofNat 64 i := by bv_omega
  have hkeep : ProofLib.progKeep prog (prog.base + BitVec.ofNat 64 i) = true := by
    unfold ProofLib.progKeep; rw [hsub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact decide_eq_true hi
  rw [ProofLib.strip_read8, ProofLib.strip_perm_of_keep hkeep, ProofLib.strip_isLazyFree]
  exact ⟨hL.byte_eq i hi, hL.perm_eq i hi, hL.isLazyFree_eq i hi⟩

private theorem strip_execOnlyIn_of_keep (prog : Program) (m : Memory) :
    prog.ExecOnlyIn (ProofLib.stripExecOutside (ProofLib.progKeep prog) m) := fun _ hpx =>
  of_decide_eq_true (ProofLib.strip_perm_x_imp hpx).2

private theorem steps_start_running_local {Q : Program} {s sf : State}
    (h : Steps Q s sf) (hr : sf.status = .Running) : s.status = .Running := by
  cases h with | refl => exact hr | step h1 _ => cases h1 <;> assumption

private theorem steps_rebase_lift_strip {P R_j : Program}
    (hext_P : ∀ pc, P.externAt? pc = none) (hext_R : ∀ pc, R_j.externAt? pc = none)
    (hall : R_j.allInstrs (fun i => !i.isSvc0) = true)
    {s1' sf' : State} (hsteps : Steps R_j s1' sf') (hrun_f : sf'.status = .Running) :
    ∀ (s1 : State), s1' = ProofLib.stripS (ProofLib.progKeep R_j) s1 → R_j.CodeLoaded s1.mem →
      ∃ sf : State, sf' = ProofLib.stripS (ProofLib.progKeep R_j) sf ∧ Steps P s1 sf ∧
        ProofLib.NonSyscallPreserved s1 sf := by
  induction hsteps with
  | refl => intro s1 hs1 _; exact ⟨s1, hs1, .refl s1, ProofLib.NonSyscallPreserved.refl s1⟩
  | @step sa' sb' sc' h1 hrest ih =>
    intro s1 hsa hL1; have hrb' : sb'.status = .Running := steps_start_running_local hrest hrun_f; subst hsa
    cases h1 with
    | halt_unmapped _ _ _ => cases s1; cases hrb'
    | extern _ he _ _ => rw [hext_R] at he; cases he
    | extern_fault _ he _ => rw [hext_R] at he; cases he
    | @exec inst hr1' hfe' =>
      have hr1 : s1.status = .Running := (by cases s1; exact hr1')
      have hL1' : R_j.CodeLoaded (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem := strip_codeLoaded_of_keep hL1
      have hexec' : R_j.ExecOnlyIn (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem :=
        strip_execOnlyIn_of_keep R_j s1.mem
      have hnsvc0 : inst.isSvc0 = false := by
        simpa using Program.fetchMem_of_allInstrs hall hL1' hexec' _ inst hfe'
      have hfe_P : P.fetchMem s1.mem s1.pc = some inst := by
        have hpc_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).pc = s1.pc := (by cases s1; rfl)
        have hmem_eq : (ProofLib.stripS (ProofLib.progKeep R_j) s1).mem =
            ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem := (by cases s1; rfl)
        rw [hpc_eq, hmem_eq] at hfe'; unfold Program.fetchMem at hfe' ⊢; rw [hext_R] at hfe'; rw [hext_P]
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hfe' ⊢
        by_cases hal_pc : s1.pc.toNat % 4 = 0
        · simp only [hal_pc, ne_eq, not_true_eq_false, ↓reduceIte] at hfe' ⊢
          split at hfe'
          · contradiction
          · rename_i hce'
            have hce : s1.mem.canExec s1.pc 4 = true := by
              simp only [Bool.not_eq_true', Bool.not_eq_false] at hce'
              unfold Memory.canExec at hce' ⊢; rw [Memory.allPerm_iff] at hce' ⊢; intro k hk
              have hxk := hce' k hk; rwa [ProofLib.strip_perm_of_keep (ProofLib.strip_perm_x_imp hxk).2] at hxk
            have hr32 : (ProofLib.stripExecOutside (ProofLib.progKeep R_j) s1.mem).read32 s1.pc =
                s1.mem.read32 s1.pc := by
              simp [Memory.read32, ProofLib.strip_read8]
            rw [hr32] at hfe'; simp only [hce, Bool.not_true, Bool.false_eq_true, ↓reduceIte]; exact hfe'
        · simp only [hal_pc, ne_eq, not_false_eq_true, ↓reduceIte] at hfe'; contradiction
      have hev_R : R_j.evalInst inst (ProofLib.stripS (ProofLib.progKeep R_j) s1) =
          ProofLib.stripS (ProofLib.progKeep R_j) (execInst inst s1) := by
        rw [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0, ProofLib.execInst_stripS hnsvc0]
      have hstep_P : Step P s1 (execInst inst s1) := by
        have := Step.exec (prog := P) hr1 hfe_P
        rwa [Arm64.evalInst_eq_execInst_of_not_isSvc0 hnsvc0] at this
      obtain ⟨sf, hsf_eq, hsteps_P, hnsp_rest⟩ := ih hrun_f (execInst inst s1) hev_R (hstep_P.codeLoaded hL1)
      exact ⟨sf, hsf_eq, .step hstep_P hsteps_P,
        ProofLib.NonSyscallPreserved.trans (ProofLib.execInst_nonSyscallPreserved_of_not_isSvc0 hnsvc0 s1) hnsp_rest⟩

/-- Equality of all CPU/architectural registers and status between `a` and `b`
    (satisfied between `s` and `stripS keep s`). -/
structure SameCpuState (a b : State) : Prop where
  regs_eq : a.regs = b.regs
  vregs_eq : a.vregs = b.vregs
  sp_eq : a.sp = b.sp
  pc_eq : a.pc = b.pc
  pstate_eq : a.pstate = b.pstate
  tpidrEl0_eq : a.tpidrEl0 = b.tpidrEl0
  fpsr_eq : a.fpsr = b.fpsr
  status_eq : a.status = b.status
  sigActions_eq : a.sigActions = b.sigActions

theorem SameCpuState.readReg64 {a b : State} (h : SameCpuState a b) (r : Reg) :
    a.readReg64 r = b.readReg64 r := by
  cases r <;> simp [State.readReg64, h.regs_eq, h.sp_eq]

theorem SameCpuState.readReg32 {a b : State} (h : SameCpuState a b) (r : Reg) :
    a.readReg32 r = b.readReg32 r := by
  simp [State.readReg32, h.readReg64 r]

theorem SameCpuState.spAligned {a b : State} (h : SameCpuState a b) :
    a.spAligned = b.spAligned := by simp [State.spAligned, h.sp_eq]

theorem SameCpuState.calleeSavedVRegs {a b : State} (h : SameCpuState a b) :
    calleeSavedVRegs a = calleeSavedVRegs b :=
  congrArg VRegFile.calleeSaved h.vregs_eq

@[reducible] def sameCpuRhs {a b : State} (_ : SameCpuState a b) : State := b

theorem SameCpuState.of_stripS_right {keep : BitVec 64 → Bool} {a b : State}
    (hb : b = ProofLib.stripS keep a) : SameCpuState a b := by
  subst hb; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameCpuState.of_stripS_left {keep : BitVec 64 → Bool} {a b : State}
    (ha : a = ProofLib.stripS keep b) : SameCpuState b a := by
  subst ha; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem nonSyscallPreserved_toVmFields {s0 sf : State}
    (h : ProofLib.NonSyscallPreserved s0 sf) : VmFieldsPreserved s0 sf :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun a => congrFun h.2.1 a⟩

theorem syscallPreserved_of_seg {s s' sm' sm : State}
    (h_in : SameCpuState s' s) (h_out : SameCpuState sm sm')
    (hnsp : ProofLib.NonSyscallPreserved s sm)
    (htp : sm'.tpidrEl0 = s'.tpidrEl0) (hsig : sm'.sigActions = s'.sigActions) :
    SyscallPreserved s sm :=
  ⟨h_out.tpidrEl0_eq.trans (htp.trans h_in.tpidrEl0_eq),
   h_out.sigActions_eq.trans (hsig.trans h_in.sigActions_eq),
   nonSyscallPreserved_toVmFields hnsp⟩

/-- Run a pure (`svc #0`-free) segment of block `j` (`(lib.blockProgram mpl j).rebase ...`)
    up to `mid` from any hook-free program `P`, automatically refreshing `CodeLoaded` and supplying
    `ProofLib.NonSyscallPreserved s sm` (`fs`, `trace`, `mem.perm`, `brk`, `brkStart`, `physMemAvail`,
    and `oracleIdx` preserved). -/
theorem sepWP_seg_rebase_pure {lib : MultiPlacedLib} {mpl : MultiPlacement} {P : Program}
    (hext : ∀ pc, P.externAt? pc = none)
    (j : Nat) (hj : j < lib.blocks.length)
    (hchk : checkBlockNoSvc0 (lib.blockLib j).text = true := by decide)
    {mid target_pc : BitVec 64} {s : State} {Pre : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hcl : lib.CodeLoaded mpl s.mem)
    (hseg : ∀ s' : State, SameCpuState s' s →
      SepWP ((lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)) mid s' Pre (fun sm' Pm =>
        ∀ sm : State, SameCpuState sm sm' → lib.CodeLoaded mpl sm.mem →
          ProofLib.NonSyscallPreserved s sm → SepWP P target_pc sm Pm post oom)) :
    SepWP P target_pc s Pre post oom := by
  let R_j := (lib.blockProgram mpl j).rebase (mpl.base j) (fun _ => none)
  let keep := ProofLib.progKeep R_j; have hL_R : R_j.CodeLoaded s.mem := (hcl j hj).of_base_code rfl rfl
  have hext_R : ∀ pc, R_j.externAt? pc = none := (by intro pc; simp [R_j])
  have hall : R_j.allInstrs (fun i => !i.isSvc0) = true :=
    blockProgram_rebase_allInstrs_not_isSvc0 lib mpl j hchk
  refine SepWP.of_reaches_pc fun R hm => ?_
  obtain ⟨R_view, hm_strip, hunstrip⟩ := ProofLib.strip_frame keep hm
  have hcpu_in : SameCpuState (ProofLib.stripS keep s) s := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨sm', hsteps', hout'⟩ := SepWP.to_reaches_pc
    (hseg (ProofLib.stripS keep s) hcpu_in) hm_strip (strip_codeLoaded_of_keep hL_R)
  rcases hout' with ⟨hpc_m', hrun_m', Pm, hmm', hcont⟩ | ⟨_, hoom⟩
  · obtain ⟨sm, hsm_eq, hsteps_P, hnsp⟩ :=
      steps_rebase_lift_strip hext hext_R hall hsteps' hrun_m' s rfl hL_R
    have hcl_m : lib.CodeLoaded mpl sm.mem := fun k hk => hsteps_P.codeLoaded (hcl k hk)
    have hperm_eq : ∀ a, sm.mem.perm a = s.mem.perm a := fun a => congrFun hnsp.2.1 a
    have hmm'_mem : ProofLib.stripExecOutside keep sm.mem ⊨ Pm ∗ R_view := by
      have hm_eq : sm'.mem = ProofLib.stripExecOutside keep sm.mem := (by rw [hsm_eq]; rfl)
      rwa [← hm_eq]
    have hmm : sm.mem ⊨ Pm ∗ R := hunstrip hperm_eq hmm'_mem
    have hwp_cont := hcont sm (SameCpuState.of_stripS_left hsm_eq) hcl_m hnsp
    exact fun hL_P => by
      obtain ⟨sf, hsteps2, hout2⟩ := SepWP.to_reaches_pc hwp_cont hmm (hsteps_P.codeLoaded hL_P)
      exact ⟨sf, hsteps_P.trans hsteps2, hout2⟩
  · rcases (satisfies_pure_sepConj _ _ _).mp hoom with ⟨hf, _⟩; exact False.elim hf

end

end ProofLib
