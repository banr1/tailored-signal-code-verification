/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Fetch
public import ProofLib.SepLogic.WP

/-!
# Relaxable `ADRP`+`ADD` Pairs

Proves `Obj.CodeBlock.sepWP_relaxablePair`, a unified `SepWP` rule for stepping across a
relaxable `ADRP Xd, sym` + `ADD Xd, Xd, :lo12:sym` pair under both the unrelaxed encoding and
linker relaxation to `NOP` + `ADR Xd, sym`.
-/

@[expose] public section

namespace Arm64
namespace Obj

open ProofLib

/-- Two register writes to the same `Xd`, each followed by a `PC` advance (with the second
    instruction fetched at `pc + 4`), collapse to one write. -/
theorem pair_state (s : State) (rd : BitVec 5) (pc v1 v2 : BitVec 64) :
    (((((s.setPC pc).writeReg64 (.gpr rd) v1).advancePC).setPC (pc + 4#64)).writeReg64
        (.gpr rd) v2).advancePC =
      (s.writeReg64 (.gpr rd) v2).setPC (pc + 8#64) := by
  have h8 : pc + 4#64 + 4#64 = pc + 8#64 := by bv_lin
  cases s
  simp only [State.setPC, State.writeReg64, State.advancePC, State.mk.injEq, h8, and_true]
  split
  · rfl
  · simp only [RegFile.write, RegFile.mk.injEq]
    funext i
    split <;> rfl

/-- `NOP` then a write to `Xd`, each followed by a `PC` advance. -/
theorem nop_pair_state (s : State) (rd : BitVec 5) (pc v : BitVec 64) :
    ((((s.setPC pc).advancePC).setPC (pc + 4#64)).writeReg64 (.gpr rd) v).advancePC =
      (s.writeReg64 (.gpr rd) v).setPC (pc + 8#64) := by
  have h8 : pc + 4#64 + 4#64 = pc + 8#64 := by bv_lin
  cases s
  simp only [State.setPC, State.writeReg64, State.advancePC, h8]

theorem readReg64_pair (s : State) {rd : BitVec 5} (h : rd ≠ 31#5) (pc pc' v : BitVec 64) :
    ((((s.setPC pc).writeReg64 (.gpr rd) v).advancePC).setPC pc').readReg64 (.gpr rd) = v := by
  simp [State.readReg64, State.writeReg64, State.advancePC, State.setPC, RegFile.read,
    RegFile.write, h]

theorem rd_fields_of_pair {w0 w1 : BitVec 32} {rd : BitVec 5} (hrd : w0.extractLsb' 0 5 = rd)
    (h1 : (w0 &&& 0x1f#32) = (w1 &&& 0x1f#32))
    (h2 : ((w1 >>> 5) &&& 0x1f#32) = (w0 &&& 0x1f#32)) :
    w1.extractLsb' 0 5 = rd ∧ w1.extractLsb' 5 5 = rd := by
  subst hrd
  constructor <;> bv_bits

theorem adrTemplate_mask (w : BitVec 32) : adrTemplate w &&& 0x9f000000#32 = 0x10000000#32 := by
  unfold adrTemplate; bv_bits

theorem adrTemplate_rd (w : BitVec 32) : (adrTemplate w).extractLsb' 0 5 = w.extractLsb' 0 5 := by
  unfold adrTemplate; bv_bits

theorem fromZRBits_of_ne {rd : BitVec 5} (h : rd ≠ 31#5) : Reg.fromZRBits rd = .gpr rd := by
  simp [Reg.fromZRBits, h]

theorem fromSPBits_of_ne {rd : BitVec 5} (h : rd ≠ 31#5) : Reg.fromSPBits rd = .gpr rd := by
  simp [Reg.fromSPBits, h]

namespace CodeBlock

/-- Unfolded `relaxableAt`: the `ADRP` relocation `r` at `off`, the `ADD` relocation `r2` at
    `off + 4` with the same symbol and addend, and the opcode/register conditions. -/
theorem relaxableAt_spec {blk : CodeBlock} {off : Nat} {r : RelocEntry}
    (h : blk.relaxableAt off = true) (hr : blk.relocAt? off = some r) :
    ∃ r2, blk.relocAt? (off + 4) = some r2 ∧ r.kind = .adrpHi21 ∧ r2.kind = .addLo12 ∧
      r.sym = r2.sym ∧ r.addend = r2.addend ∧
      blk.wordAt off &&& 0x9f000000#32 = 0x90000000#32 ∧
      blk.wordAt (off + 4) &&& 0xffc00000#32 = 0x91000000#32 ∧
      (blk.wordAt off &&& 0x1f#32) = (blk.wordAt (off + 4) &&& 0x1f#32) ∧
      ((blk.wordAt (off + 4) >>> 5) &&& 0x1f#32) = (blk.wordAt off &&& 0x1f#32) := by
  unfold relaxableAt at h
  rw [hr] at h
  cases h2 : blk.relocAt? (off + 4) with
  | none => rw [h2] at h; simp at h
  | some r2 =>
    rw [h2] at h
    simp only [isAdrpWord, isAddImm64Word, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hk1, hk2⟩, hs⟩, ha⟩, hw0⟩, hw1⟩, hm1⟩, hm2⟩, _⟩ := h
    exact ⟨r2, rfl, hk1, hk2, hs, ha, hw0, hw1, hm1, hm2⟩

/-- A site whose relocation is not an `ADRP` page relocation does not start a relaxable pair. -/
theorem relaxableAt_false_of_kind {blk : CodeBlock} {off : Nat} {r : RelocEntry}
    (hr : blk.relocAt? off = some r) (hk : r.kind ≠ .adrpHi21) : blk.relaxableAt off = false := by
  unfold relaxableAt
  rw [hr]
  split
  · next r1 r2 h1 h2 =>
    cases h1
    simp [hk]
  · rfl

/-- A site whose relocation is not an `ADD :lo12:` relocation is not the second word of a
    relaxable pair. -/
theorem relaxableAt_false_of_next_kind {blk : CodeBlock} {off : Nat} {r : RelocEntry}
    (hr : blk.relocAt? (off + 4) = some r) (hk : r.kind ≠ .addLo12) :
    blk.relaxableAt off = false := by
  unfold relaxableAt
  rw [hr]
  split
  · next r1 r2 h1 h2 =>
    cases h2
    simp [hk]
  · rfl

/-- At a relaxable pair `off` (`ADRP Xd` with relocation `r`, then `ADD Xd, Xd`, `Xd ≠ X31`),
    executing both words from `pc = pl.base + off` sets `Xd := blk.target pl r` and
    `pc := pc + 8`, and changes nothing else, whether or not the linker relaxed the pair
    (`pl.relax off`). -/
theorem sepWP_relaxablePair {blk : CodeBlock} {pl : Placement} {prog : Program} {off : Nat}
    {r : RelocEntry} {rd : BitVec 5} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : blk.Placeable pl) (hbase : prog.base = pl.base) (hcode : prog.code = blk.patched pl)
    (hrel : blk.relaxableAt off = true) (hr : blk.relocAt? off = some r)
    (hrd : (blk.wordAt off).extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (hh0 : prog.hookAtOff? off = none) (hh4 : prog.hookAtOff? (off + 4) = none)
    (hpc : s.pc = pl.base + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP prog tgt
      ((s.writeReg64 (.gpr rd) (blk.target pl r)).setPC (pl.base + BitVec.ofNat 64 (off + 8)))
      P post oom) :
    SepWP prog tgt s P post oom := by
  have h8 : pl.base + BitVec.ofNat 64 (off + 8) = s.pc + 8#64 := by
    rw [hpc, BitVec.ofNat_add, BitVec.add_assoc]
  rw [h8] at hnext
  obtain ⟨r2, hr2, hk1, hk2, hsym, hadd, hw0, hw1, hm1, hm2⟩ := relaxableAt_spec hrel hr
  have hT2 : blk.target pl r2 = blk.target pl r := by simp only [target, hsym, hadd]
  have hroff := relocAt?_off hr
  have hr2off := relocAt?_off hr2
  obtain ⟨hal, hlen, hrange⟩ := hP.relocs_ok r (relocAt?_mem hr)
  obtain ⟨-, hlen2, -⟩ := hP.relocs_ok r2 (relocAt?_mem hr2)
  rw [hroff] at hal hlen hrange
  rw [hr2off] at hlen2
  have hnw := hP.no_wrap
  obtain ⟨hrd1, hrn1⟩ := rd_fields_of_pair hrd hm1 hm2
  have hfetch : ∀ k, k < 8 → k % 4 = 0 →
      prog.fetch (pl.base + BitVec.ofNat 64 (off + k)) = decode (blk.patchedWord pl (off + k)) :=
    fun k hk hk4 => by
      rw [← hbase]
      refine Program.fetch_of_readWordOff (by omega) ?_
        (readWordOff_patched hcode (by omega) (by omega))
      rcases (by omega : k = 0 ∨ k = 4) with rfl | rfl
      · exact hh0
      · exact hh4
  have hf0 := hfetch 0 (by omega) rfl
  have hf4 := hfetch 4 (by omega) rfl
  rw [Nat.add_zero] at hf0
  have hplace4 : pl.base + BitVec.ofNat 64 (off + 4) = s.pc + 4#64 := by
    rw [hpc, BitVec.ofNat_add, BitVec.add_assoc]
  rw [hplace4] at hf4
  -- The second word never starts a pair, and the first is never a pair's second word.
  have hnr4 : blk.relaxedAt pl (off + 4) = false :=
    relaxedAt_of_relaxableAt_false (relaxableAt_false_of_kind hr2 (by rw [hk2]; decide))
  have hnrm4 : off < 4 ∨ blk.relaxedAt pl (off - 4) = false := by
    by_cases h4 : off < 4
    · exact .inl h4
    · refine .inr (relaxedAt_of_relaxableAt_false (relaxableAt_false_of_next_kind
        (r := r) (by rw [show off - 4 + 4 = off by omega]; exact hr) (by rw [hk1]; decide)))
  have hreg : Reg.fromZRBits rd = .gpr rd := fromZRBits_of_ne hrd31
  cases hrx : pl.relax off with
  | false =>
    have h0 : blk.relaxedAt pl off = false := by simp [relaxedAt, hrx]
    have hb1 : blk.b2bNext? r = none := by simp [b2bNext?, hk1]
    have hb2 : blk.b2bNext? r2 = none := by simp [b2bNext?, hk2]
    have hw0' := patchedWord_of_notRelaxed (pl := pl) hr h0 hnrm4
    have hw1' := patchedWord_of_notRelaxed (pl := pl) hr2 hnr4 (.inr (by
      rw [show off + 4 - 4 = off by omega]; exact h0))
    rw [relocTarget_of_b2bNext_none hb1, hk1] at hw0'
    rw [relocTarget_of_b2bNext_none hb2, hk2, hT2] at hw1'
    rw [relocTarget_of_b2bNext_none hb1, hk1] at hrange
    change AdrpInRange _ _ at hrange
    rw [hw0'] at hf0
    rw [hw1'] at hf4
    simp only [patchRelocWord] at hf0 hf4
    rw [decode_adrpWord hw0 hrange, hrd, hreg] at hf0
    rw [decode_addLo12Word hw1, hrd1, hrn1, fromSPBits_of_ne hrd31] at hf4
    refine SepWP.step_pure (s' := ((s.setPC (pl.base + BitVec.ofNat 64 off)).writeReg64 (.gpr rd)
        (pageOf (blk.target pl r))).advancePC) hpc hrun hf0 ?_ rfl ?_
    · simp only [Program.evalInst, execInstWithSvc, ite_true, State.pc_setPC]
      rw [adrp_pageOf_cancel]
    refine SepWP.step_pure (s' := (((((s.setPC (pl.base + BitVec.ofNat 64 off)).writeReg64 (.gpr rd)
        (pageOf (blk.target pl r))).advancePC).setPC (s.pc + 4#64)).writeReg64 (.gpr rd)
        (blk.target pl r)).advancePC) ?_ ?_ hf4 ?_ rfl ?_
    · simp [State.writeReg64, State.advancePC, State.setPC, hpc]
    · simpa [State.writeReg64, State.advancePC, State.setPC] using hrun
    · simp only [Program.evalInst, execInstWithSvc, execAddSubImm, Bool.false_eq_true,
        ↓reduceIte, zeroExtend_truncate_lo12Of, evalAddSub_w64_add, State.readReg,
        State.writeReg, readReg64_pair _ hrd31, pageOf_add_lo12Of]
    · rw [hpc, pair_state, ← hpc]; exact hnext
  | true =>
    have h0 : blk.relaxedAt pl off = true := by simp [relaxedAt, hrel, hrx]
    have hw0' := patchedWord_of_relaxed (pl := pl) hr h0
    have hw1' := patchedWord_of_relaxedPrev (pl := pl) hr2 hnr4 (by omega)
      (by rw [show off + 4 - 4 = off by omega]; exact h0)
    have hadr := hP.relaxed_ok off r2 h0 hr2
    rw [hT2, hplace4] at hadr
    rw [hw0'] at hf0
    rw [hw1', hT2, hplace4, decode_adrWord (adrTemplate_mask _) hadr, adrTemplate_rd, hrd1,
      hreg] at hf4
    have hnop : decode nopWord = some .nop := rfl
    rw [hnop] at hf0
    refine SepWP.step_pure (s' := (s.setPC (pl.base + BitVec.ofNat 64 off)).advancePC)
      hpc hrun hf0 rfl rfl ?_
    refine SepWP.step_pure (s' := ((((s.setPC (pl.base + BitVec.ofNat 64 off)).advancePC).setPC
        (s.pc + 4#64)).writeReg64 (.gpr rd) (blk.target pl r)).advancePC) ?_ ?_ hf4 ?_ rfl ?_
    · simp [State.advancePC, State.setPC, hpc]
    · simpa [State.advancePC, State.setPC] using hrun
    · simp only [Program.evalInst, execInstWithSvc, Bool.false_eq_true, ↓reduceIte,
        State.pc_setPC]
      congr 2
      bv_lin
    · rw [hpc, nop_pair_state, ← hpc]; exact hnext

/-- `sepWP_relaxablePair` with hook-freedom of the two words as one `hookFree` range. -/
theorem sepWP_relaxablePair_of_hookFree {blk : CodeBlock} {pl : Placement} {prog : Program}
    {off : Nat} {r : RelocEntry} {rd : BitVec 5} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : blk.Placeable pl) (hbase : prog.base = pl.base) (hcode : prog.code = blk.patched pl)
    (hrel : blk.relaxableAt off = true) (hr : blk.relocAt? off = some r)
    (hrd : (blk.wordAt off).extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (hhook : prog.hookFree off 8)
    (hpc : s.pc = pl.base + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP prog tgt
      ((s.writeReg64 (.gpr rd) (blk.target pl r)).setPC (pl.base + BitVec.ofNat 64 (off + 8)))
      P post oom) :
    SepWP prog tgt s P post oom :=
  sepWP_relaxablePair hP hbase hcode hrel hr hrd hrd31
    (Program.hookAtOff?_eq_none_of_hookFree hhook (by omega) (by omega))
    (Program.hookAtOff?_eq_none_of_hookFree hhook (by omega) (by omega)) hpc hrun hnext

end CodeBlock

end Obj
end Arm64
