/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Placed.Pair

/-!
# Plain `ADRP` and `:lo12:` Load/Store Sites

Stepping and fetch rules for placed libraries at unpaired `ADRP Xd, sym+k` sites (whose `:lo12:`
user is a possibly non-adjacent `LDR` or `STR`) and scaled GPR `:lo12:` load/store sites.
Step the `ADRP` with `PlacedLib.sepWP_rebase_adrpPlain`, supply the `:lo12:` instruction fetch via
`PlacedLib.fetch_rebase_ldstLo12_of_placeable`, and recombine `pageOf T + lo12Of T = T` via
`pageOf_add_lo12Of`.
-/

@[expose] public section

namespace Arm64
namespace Obj

open ProofLib

/-- One register write followed by a `PC` advance, from `pc`. -/
theorem write_advance_state (s : State) (rd : BitVec 5) (pc v : BitVec 64) :
    ((s.setPC pc).writeReg64 (.gpr rd) v).advancePC = (s.writeReg64 (.gpr rd) v).setPC (pc + 4#64) := by
  cases s
  simp only [State.setPC, State.writeReg64, State.advancePC]

/-- The scale (`log2` of the access size) of a scaled GPR `:lo12:` load/store relocation. -/
def ldstLo12Scale : RelocKind → Option Nat
  | .ldst8Lo12 => some 0
  | .ldst16Lo12 => some 1
  | .ldst32Lo12 => some 2
  | .ldst64Lo12 => some 3
  | _ => none

theorem patchRelocWord_of_ldstLo12Scale {kind : RelocKind} {scale : Nat}
    (h : ldstLo12Scale kind = some scale) (w : BitVec 32) (place target : BitVec 64) :
    patchRelocWord kind w place target = lo12Word scale w target := by
  cases kind <;> simp only [ldstLo12Scale, reduceCtorEq, Option.some.injEq] at h <;> subst h <;> rfl

theorem lo12Aligned_of_ldstLo12Scale {kind : RelocKind} {scale : Nat}
    (h : ldstLo12Scale kind = some scale) {place target : BitVec 64}
    (hin : CodeRelocInRange kind place target) : Lo12Aligned scale target := by
  cases kind <;> simp only [ldstLo12Scale, reduceCtorEq, Option.some.injEq] at h <;> subst h
  · exact lo12Aligned_zero target
  all_goals exact hin

theorem ldstLo12Scale_kind_ne {kind : RelocKind} {scale : Nat}
    (h : ldstLo12Scale kind = some scale) :
    kind ≠ .adrpHi21 ∧ kind ≠ .addLo12 ∧ kind ≠ .call26 ∧ kind ≠ .jump26 ∧
      kind.isGotOrTlsIe = false := by
  cases kind <;> simp_all [ldstLo12Scale, RelocKind.isGotOrTlsIe]

namespace CodeBlock

/-- At a relocated site that is neither part of a relaxable pair nor a branch, the patched word is
    `patchRelocWord` with target `blk.target pl r`. -/
theorem patchedWord_of_unpaired {blk : CodeBlock} {pl : Placement} {off : Nat} {r : RelocEntry}
    (hr : blk.relocAt? off = some r) (hnrel : blk.relaxableAt off = false)
    (hka : r.kind ≠ .addLo12)
    (hkc : r.kind ≠ .call26) (hkj : r.kind ≠ .jump26)
    (hng : r.kind.isGotOrTlsIe = false := by
      first | rfl | decide | (simp only [*, RelocKind.isGotOrTlsIe]; rfl)) :
    blk.patchedWord pl off = patchRelocWord r.kind (blk.wordAt off)
      (pl.base + BitVec.ofNat 64 off) (blk.target pl r) := by
  have hb : blk.b2bNext? r = none := by simp [b2bNext?, hkc, hkj]
  have hm4 : off < 4 ∨ blk.relaxedAt pl (off - 4) = false := by
    by_cases h4 : off < 4
    · exact .inl h4
    · exact .inr (relaxedAt_of_relaxableAt_false (relaxableAt_false_of_next_kind
        (r := r) (by rw [show off - 4 + 4 = off by omega]; exact hr) hka))
  rw [patchedWord_of_notRelaxed hr (relaxedAt_of_relaxableAt_false hnrel) hm4 hng,
    relocTarget_of_b2bNext_none hb]

/-- At an unpaired `ADRP Xd` site (`R_AARCH64_ADR_PREL_PG_HI21`, `Xd != X31`), one step from
    `pc = pl.base + off` sets `Xd := pageOf (blk.target pl r)` and `pc := pc + 4`. -/
theorem sepWP_adrpPlain {blk : CodeBlock} {pl : Placement} {prog : Program} {off : Nat}
    {r : RelocEntry} {rd : BitVec 5} {tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : blk.Placeable pl) (hbase : prog.base = pl.base) (hcode : prog.code = blk.patched pl)
    (hr : blk.relocAt? off = some r) (hk : r.kind = .adrpHi21)
    (hnrel : blk.relaxableAt off = false)
    (hw : blk.wordAt off &&& 0x9f000000#32 = 0x90000000#32)
    (hrd : (blk.wordAt off).extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (hh0 : prog.hookAtOff? off = none)
    (hpc : s.pc = pl.base + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP prog tgt
      ((s.writeReg64 (.gpr rd) (pageOf (blk.target pl r))).setPC
        (pl.base + BitVec.ofNat 64 (off + 4)))
      P post oom) :
    SepWP prog tgt s P post oom := by
  have hroff := relocAt?_off hr
  obtain ⟨hal, hlen, hrange⟩ := hP.relocs_ok r (relocAt?_mem hr)
  rw [hroff] at hal hlen hrange
  have hnw := hP.no_wrap
  have hb : blk.b2bNext? r = none := by simp [b2bNext?, hk]
  rw [relocTarget_of_b2bNext_none hb, hk] at hrange
  change AdrpInRange _ _ at hrange
  have hm4 : off < 4 ∨ blk.relaxedAt pl (off - 4) = false := by
    by_cases h4 : off < 4
    · exact .inl h4
    · exact .inr (relaxedAt_of_relaxableAt_false (relaxableAt_false_of_next_kind
        (r := r) (by rw [show off - 4 + 4 = off by omega]; exact hr) (by rw [hk]; decide)))
  have hw0 := patchedWord_of_notRelaxed (pl := pl) hr (relaxedAt_of_relaxableAt_false hnrel) hm4
  rw [relocTarget_of_b2bNext_none hb, hk] at hw0
  have hf0 : prog.fetch (pl.base + BitVec.ofNat 64 off) = decode (blk.patchedWord pl off) := by
    rw [← hbase]
    exact Program.fetch_of_readWordOff (by omega) hh0 (readWordOff_patched hcode hal hlen)
  rw [hw0] at hf0
  simp only [patchRelocWord] at hf0
  rw [decode_adrpWord hw hrange, hrd, fromZRBits_of_ne hrd31] at hf0
  have h4 : pl.base + BitVec.ofNat 64 (off + 4) = pl.base + BitVec.ofNat 64 off + 4#64 := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  rw [h4] at hnext
  refine SepWP.step_pure (s' := ((s.setPC (pl.base + BitVec.ofNat 64 off)).writeReg64 (.gpr rd)
      (pageOf (blk.target pl r))).advancePC) hpc hrun hf0 ?_ rfl ?_
  · simp only [Program.evalInst, execInstWithSvc, ite_true, State.pc_setPC]
    rw [adrp_pageOf_cancel]
  · rw [write_advance_state]; exact hnext

/-- At a GPR load/store site with a `:lo12:` relocation of scale `scale`, the fetched instruction
    is the template instruction with immediate `lo12Of (blk.target pl r)`, independent of
    `prog.base`. -/
theorem fetch_ldstLo12 {blk : CodeBlock} {pl : Placement} {prog : Program} {off : Nat}
    {r : RelocEntry} {scale : Nat} {inst : Instr}
    (hcode : prog.code = blk.patched pl)
    (hr : blk.relocAt? off = some r) (hk : ldstLo12Scale r.kind = some scale)
    (hal4 : off % 4 = 0) (hlen : off + 4 ≤ blk.code.length) (hlt : off < 2 ^ 64)
    (hh : prog.hookAtOff? off = none)
    (hscale : ((blk.wordAt off).extractLsb' 30 2).toNat = scale)
    (hw1 : blk.wordAt off &&& 0x3f000000#32 = 0x39000000#32)
    (hw2 : (blk.wordAt off &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (hal : Lo12Aligned scale (blk.target pl r))
    (hinst : mkLoadStoreInst scale ((blk.wordAt off).extractLsb' 22 2).toNat
      (Reg.fromZRBits ((blk.wordAt off).extractLsb' 0 5))
      (.Offset (Reg.fromSPBits ((blk.wordAt off).extractLsb' 5 5)) (lo12Of (blk.target pl r))) =
        some inst) :
    prog.fetch (prog.base + BitVec.ofNat 64 off) = some inst := by
  obtain ⟨hka, hkadd, hkc, hkj, hng⟩ := ldstLo12Scale_kind_ne hk
  have hnrel : blk.relaxableAt off = false := relaxableAt_false_of_kind hr hka
  rw [Program.fetch_of_readWordOff hlt hh (readWordOff_patched hcode hal4 hlen),
    patchedWord_of_unpaired hr hnrel hkadd hkc hkj hng,
    patchRelocWord_of_ldstLo12Scale hk, decode_ldstGprLo12Word hscale hw1 hw2 hal, hinst]

end CodeBlock

namespace PlacedLib

variable {X O : String → Option (State → State)} {svc : State → State}

/-- `CodeBlock.sepWP_adrpPlain` for a rebased placed program `(lib.program pl X O).rebase b X' O'`
    with `b = pl.base`, the target named `T`, and the next `pc` written `b + (off + 4)`. -/
theorem sepWP_rebase_adrpPlain {lib : PlacedLib} {pl : Placement} {off off4 : Nat}
    {X' O' : String → Option (State → State)} {b : BitVec 64}
    {r : RelocEntry} {rd : BitVec 5} {T tgt : BitVec 64} {s : State} {P : SepProp}
    {post : State → SepProp → Prop} {oom : State → SepProp}
    (hP : lib.Placeable pl) (hb : b = pl.base)
    (hr : lib.text.relocAt? off = some r) (hk : r.kind = .adrpHi21)
    (hnrel : lib.text.relaxableAt off = false) {w : BitVec 32} (hwd : lib.text.wordAt off = w)
    (hw : w &&& 0x9f000000#32 = 0x90000000#32)
    (hrd : w.extractLsb' 0 5 = rd) (hrd31 : rd ≠ 31#5)
    (hT : lib.text.target pl r = T) (h4 : off + 4 = off4)
    (hh0 : ((lib.program pl X O svc).rebase b X' O').hookAtOff? off = none)
    (hpc : s.pc = b + BitVec.ofNat 64 off) (hrun : s.status = .Running)
    (hnext : SepWP ((lib.program pl X O svc).rebase b X' O') tgt
      ((s.writeReg64 (.gpr rd) (pageOf T)).setPC (b + BitVec.ofNat 64 off4)) P post oom) :
    SepWP ((lib.program pl X O svc).rebase b X' O') tgt s P post oom := by
  subst hb hT h4 hwd
  exact CodeBlock.sepWP_adrpPlain hP.text (by simp) (by simp) hr hk hnrel hw hrd hrd31 hh0 hpc
    hrun hnext

/-- `CodeBlock.fetch_ldstLo12` for a rebased placed program, at any base `b`, with the target
    named `T`. -/
theorem fetch_rebase_ldstLo12 {lib : PlacedLib} {pl : Placement} {off : Nat}
    {X' O' : String → Option (State → State)} {b : BitVec 64}
    {r : RelocEntry} {scale : Nat} {T : BitVec 64} {inst : Instr}
    (hr : lib.text.relocAt? off = some r) (hk : ldstLo12Scale r.kind = some scale)
    (hal4 : off % 4 = 0) (hlen : off + 4 ≤ lib.text.code.length) (hlt : off < 2 ^ 64)
    (hh : ((lib.program pl X O svc).rebase b X' O').hookAtOff? off = none)
    {w : BitVec 32} (hwd : lib.text.wordAt off = w)
    (hscale : (w.extractLsb' 30 2).toNat = scale)
    (hw1 : w &&& 0x3f000000#32 = 0x39000000#32)
    (hw2 : (w &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (hT : lib.text.target pl r = T) (hal : Lo12Aligned scale T)
    (hinst : mkLoadStoreInst scale (w.extractLsb' 22 2).toNat (Reg.fromZRBits (w.extractLsb' 0 5))
      (.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of T)) = some inst) :
    ((lib.program pl X O svc).rebase b X' O').fetch (b + BitVec.ofNat 64 off) = some inst := by
  subst hT hwd
  have := CodeBlock.fetch_ldstLo12 (prog := (lib.program pl X O svc).rebase b X' O')
    (by simp) hr hk hal4 hlen hlt hh hscale hw1 hw2 hal hinst
  simpa using this

/-- `fetch_rebase_ldstLo12` with the alignment of the target taken from `Placeable` (the
    relocation's `CodeRelocInRange` fact). -/
theorem fetch_rebase_ldstLo12_of_placeable {lib : PlacedLib} {pl : Placement} {off : Nat}
    {X' O' : String → Option (State → State)} {b : BitVec 64}
    {r : RelocEntry} {scale : Nat} {T : BitVec 64} {inst : Instr}
    (hP : lib.Placeable pl)
    (hr : lib.text.relocAt? off = some r) (hk : ldstLo12Scale r.kind = some scale)
    (hh : ((lib.program pl X O svc).rebase b X' O').hookAtOff? off = none)
    {w : BitVec 32} (hwd : lib.text.wordAt off = w)
    (hscale : (w.extractLsb' 30 2).toNat = scale)
    (hw1 : w &&& 0x3f000000#32 = 0x39000000#32)
    (hw2 : (w &&& 0xffc00000#32 == 0xf9800000#32) = false)
    (hT : lib.text.target pl r = T)
    (hinst : mkLoadStoreInst scale (w.extractLsb' 22 2).toNat (Reg.fromZRBits (w.extractLsb' 0 5))
      (.Offset (Reg.fromSPBits (w.extractLsb' 5 5)) (lo12Of T)) = some inst) :
    ((lib.program pl X O svc).rebase b X' O').fetch (b + BitVec.ofNat 64 off) = some inst := by
  have hroff := CodeBlock.relocAt?_off hr
  obtain ⟨hal4, hlen, hrange⟩ := hP.text.relocs_ok r (CodeBlock.relocAt?_mem hr)
  rw [hroff] at hal4 hlen hrange
  have hnw := hP.text.no_wrap
  obtain ⟨-, -, hkc, hkj, hng⟩ := ldstLo12Scale_kind_ne hk
  have hb : lib.text.b2bNext? r = none := by simp [CodeBlock.b2bNext?, hkc, hkj]
  rw [CodeBlock.relocInRange_of_not_gotOrTlsIe hng,
    CodeBlock.relocTarget_of_b2bNext_none hb, hT] at hrange
  exact fetch_rebase_ldstLo12 hr hk hal4 hlen (by omega) hh hwd hscale hw1 hw2 hT
    (lo12Aligned_of_ldstLo12Scale hk hrange) hinst

end PlacedLib

end Obj
end Arm64
