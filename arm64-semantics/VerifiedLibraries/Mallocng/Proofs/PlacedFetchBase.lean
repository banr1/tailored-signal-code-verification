/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import VerifiedLibraries.Mallocng.Proofs.PlacedCode
public meta import Lean
public meta import ProofLib.GenDecodes
public meta import Arm64.Trusted.ISA.Decode
public meta import VerifiedLibraries.Mallocng.Spec.PlacedLib

/-!
# Shared Relocation Helpers and Placed Fetch Generator

Provides block-generic relocation and `:lo12:` fetch lemmas alongside `gen_blk_reloc_steps`, which
generates per-block relocation pair-step and fetch lemmas and checks instruction coverage across
all offsets of a `mallocng` code block.
-/

set_option autoImplicit false

namespace VerifiedLibraries.Mallocng.Proofs

@[expose] public section

open Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection VerifiedLibraries.Mallocng

/-! ## Block-generic relocation helpers -/

theorem blk_wordAt {lib : PlacedLib} {t : WordTree} {n off j : Nat}
    (hcode : lib.text.code = t.toBytes) (hsize : t.checkSize? = some n)
    {b0 b1 b2 b3 : BitVec 8} {w : BitVec 32}
    (hoff : 4 * j = off)
    (hget : t.getQuad? j = some (b0, b1, b2, b3))
    (hw : wordOfBytesLE [b0, b1, b2, b3] 0 = w) :
    lib.text.wordAt off = w := by
  subst hoff hw
  exact GenPlacedFetches.wordAt_of_getQuad? hcode hsize hget

theorem blk_word_rd {lib : PlacedLib} {off : Nat} {w : BitVec 32} {rd : BitVec 5}
    (hw : lib.text.wordAt off = w) (hrd : w.extractLsb' 0 5 = rd) :
    (lib.text.wordAt off).extractLsb' 0 5 = rd := by
  rw [hw]; exact hrd

theorem blk_relaxableAt_false_first_none {lib : PlacedLib} {off : Nat}
    (h1 : lib.text.relocAt? off = none) :
    lib.text.relaxableAt off = false := by
  unfold CodeBlock.relaxableAt; rw [h1]

theorem blk_relaxableAt_false_none {lib : PlacedLib} {off : Nat} {r1 : RelocEntry}
    (h2 : lib.text.relocAt? (off + 4) = none)
    (_h1 : lib.text.relocAt? off = some r1) :
    lib.text.relaxableAt off = false := by
  unfold CodeBlock.relaxableAt; rw [h2]; cases lib.text.relocAt? off <;> rfl

theorem blk_relaxableAt_false_some {lib : PlacedLib} {off : Nat} {r1 r2 : RelocEntry}
    {w0 w1 : BitVec 32}
    (h1 : lib.text.relocAt? off = some r1)
    (h2 : lib.text.relocAt? (off + 4) = some r2)
    (hw0 : lib.text.wordAt off = w0)
    (hw1 : lib.text.wordAt (off + 4) = w1)
    (hchk : (r1.kind == .adrpHi21 && r2.kind == .addLo12 && r1.sym == r2.sym &&
      r1.addend == r2.addend && isAdrpWord w0 && isAddImm64Word w1 &&
      (w0 &&& 0x1f#32) == (w1 &&& 0x1f#32) && ((w1 >>> 5) &&& 0x1f#32) == (w0 &&& 0x1f#32) &&
      (w0 &&& 0x1f#32) != 0x1f#32) =
      false) :
    lib.text.relaxableAt off = false := by
  unfold CodeBlock.relaxableAt; rw [h1, h2, hw0, hw1]; exact hchk

theorem blk_target_ext_zero {lib : PlacedLib} {pl : Placement} {r : RelocEntry} {sym : String}
    (hs : r.sym = sym) (hl : lookup sym lib.text.symbols = none) (ha : r.addend = 0) :
    lib.text.target pl r = pl.ρ sym := by
  simp only [CodeBlock.target, CodeBlock.resolve, hs, hl, addSignedAddr, ha]; rfl

theorem blk_target_ext_pos {lib : PlacedLib} {pl : Placement} {r : RelocEntry} {sym : String}
    {k : Nat}
    (hs : r.sym = sym) (hl : lookup sym lib.text.symbols = none)
    (ha : r.addend = (k : Int)) (hk : ((k : Int) == 0) = false) :
    lib.text.target pl r = pl.ρ sym + BitVec.ofNat 64 k := by
  simp only [CodeBlock.target, CodeBlock.resolve, hs, hl, addSignedAddr, ha, hk]; rfl

private theorem placedProgram_rebase_code0 (lib : PlacedLib) (pl : Placement)
    (b : BitVec 64) (X : String → Option (Arm64.State → Arm64.State)) :
    ((lib.program pl).rebase b X).code = lib.text.patched pl := rfl

private theorem placedProgram_rebase_base0 (lib : PlacedLib) (pl : Placement)
    (b : BitVec 64) (X : String → Option (Arm64.State → Arm64.State)) :
    ((lib.program pl).rebase b X).base = b := rfl

set_option linter.literalFetch false in
theorem fetch_rebase_addLo12_of_placeable {lib : PlacedLib} {pl : Placement} {off : Nat}
    {X : String → Option (Arm64.State → Arm64.State)} {b : BitVec 64}
    {r : RelocEntry} {T : BitVec 64} {w : BitVec 32} {rd rn : Reg}
    (hP : lib.Placeable pl)
    (hr : lib.text.relocAt? off = some r) (hk : r.kind = .addLo12)
    (hm4 : off < 4 ∨ lib.text.relaxableAt (off - 4) = false)
    (hh : ((lib.program pl).rebase b X).hookAtOff? off = none)
    (hwd : lib.text.wordAt off = w)
    (hw : w &&& 0xffc00000#32 = 0x91000000#32)
    (hT : lib.text.target pl r = T)
    (hrd : Reg.fromSPBits (w.extractLsb' 0 5) = rd)
    (hrn : Reg.fromSPBits (w.extractLsb' 5 5) = rn) :
    ((lib.program pl).rebase b X).fetch (b + BitVec.ofNat 64 off) =
      some (.addSubImm .W64 .ADD rd rn ((lo12Of T).truncate 12) false) := by
  subst hT hwd
  have hroff := CodeBlock.relocAt?_off hr
  obtain ⟨hal4, hlen, -⟩ := hP.text.relocs_ok r (CodeBlock.relocAt?_mem hr)
  rw [hroff] at hal4 hlen
  have _hnw := hP.text.no_wrap
  have hnrel : lib.text.relaxableAt off = false :=
    CodeBlock.relaxableAt_false_of_kind hr (by rw [hk]; decide)
  have hm4' : off < 4 ∨ lib.text.relaxedAt pl (off - 4) = false :=
    hm4.imp id CodeBlock.relaxedAt_of_relaxableAt_false
  have hb0 : lib.text.b2bNext? r = none := by simp [CodeBlock.b2bNext?, hk]
  have hpw := CodeBlock.patchedWord_of_notRelaxed (pl := pl) hr
    (CodeBlock.relaxedAt_of_relaxableAt_false hnrel) hm4'
  rw [CodeBlock.relocTarget_of_b2bNext_none hb0, hk] at hpw
  have hf := Program.fetch_of_readWordOff (prog := (lib.program pl).rebase b X)
    (by omega) hh (CodeBlock.readWordOff_patched (pl := pl)
      (placedProgram_rebase_code0 lib pl b X) hal4 hlen)
  rw [placedProgram_rebase_base0] at hf
  rw [hpw] at hf
  simp only [patchRelocWord] at hf
  rw [decode_addLo12Word hw, hrd, hrn] at hf
  exact hf

end

/-! ## Per-block projection, relocation step, and `:lo12:` fetch generator -/

public section
syntax (name := declCoreBlockStx) "decl_core_block " num num ident ident : command
syntax (name := genBlkRelocStepsStx) "gen_blk_reloc_steps " ident num num : command
end

public meta section

open Lean Elab Command Meta Arm64 Arm64.Obj ProofLib ProofLib.ProgramReflection

macro_rules
  | `(decl_core_block $idx:num $nwords:num $tag:ident $blkDef:ident) => do
    let mkName (pfx : String) : Lean.Ident :=
      Lean.mkIdent (Lean.Name.mkSimple s!"{pfx}{tag.getId.toString}")
    let libId := mkName "blkLib_"
    let plId := mkName "blkPl_"
    let plbId := mkName "blkPlaceable_"
    let pc0Id := mkName "blkPC0_"
    let pcId := mkName "blkPC_"
    let plBaseId := mkName "blkPl_base_"
    let plRhoId := mkName "blkPl_ρ_"
    let progEqId := mkName "mallocngBlockProg_eq_"
    let fetchEqId := mkName "blkPC_rebase_fetch_"
    let externNoneId := mkName "externAt?_blkPC_rebase_"
    let textProgId := mkName "blkTextProg_"
    let treeId := mkName "blkTree_"
    let codeEqId := mkName "blkCodeEq_"
    let sizeEqId := mkName "blkSizeEq_"
    let symCharsId := mkName "blkSymChars_"
    let symsEqId := mkName "blkSymsEq_"
    let symsFreshId := mkName "blkSymsFresh_"
    `(
      def $libId : PlacedLib := VerifiedLibraries.mallocngLib.blockLib $idx
      def $plId [MallocngMultiPlacement] : Placement := VerifiedLibraries.mallocngLib.blockPlacement mmpl $idx
      theorem $plbId [MallocngMultiPlacement] : ($libId).Placeable $plId :=
        VerifiedLibraries.mallocngLib.placeable_blockLib (i := $idx) (by decide) MallocngMultiPlacement.placeable
      def $pc0Id [MallocngMultiPlacement] : Program := ($libId).program $plId
      def $pcId [MallocngMultiPlacement] : Program :=
        ($libId).program $plId (fun _ => none) (fun _ => none) msvc
      @[simp, arm64_norm, wp_norm] theorem $plBaseId [MallocngMultiPlacement] :
          ($plId).base = mbase $idx := rfl
      @[simp, arm64_norm, wp_norm] theorem $plRhoId [MallocngMultiPlacement] (s : String) :
          ($plId).ρ s = VerifiedLibraries.mallocngLib.resolve mmpl s := rfl
      theorem $progEqId [MallocngMultiPlacement] :
          mallocngBlockProg mmpl $idx msvc = ($pcId).rebase (mbase $idx) (fun _ => none) := rfl
      @[simp, arm64_norm] theorem $fetchEqId [MallocngMultiPlacement] (b : BitVec 64)
          (X : String → Option (Arm64.State → Arm64.State)) (pc : BitVec 64) :
          (($pcId).rebase b X).fetch pc = (($pc0Id).rebase b X).fetch pc := rfl
      @[simp] theorem $externNoneId [MallocngMultiPlacement] (b : BitVec 64) (pc : BitVec 64) :
          (($pcId).rebase b (fun _ => none)).externAt? pc = none :=
        externAt?_placedProgram_rebase_none $libId $plId msvc b pc
      def $textProgId : Program := { code := ($blkDef).code, symbols := ($blkDef).symbols }
      set_option maxRecDepth 200000 in
      def $treeId : WordTree := word_tree_of% $textProgId
      set_option maxRecDepth 200000 in
      theorem $codeEqId : ($libId).text.code = ($treeId).toBytes := by rfl_kernel
      set_option maxRecDepth 200000 in
      theorem $sizeEqId : ($treeId).checkSize? = some $nwords := by rfl_kernel
      def $symCharsId : List (List Char × Nat) := sym_chars_of% $textProgId
      set_option maxRecDepth 200000 in
      theorem $symsEqId : ($libId).text.symbols = toStringSymbols $symCharsId := by rfl_kernel
      set_option maxRecDepth 200000 in
      theorem $symsFreshId : allFreshCharSymbols $symCharsId = true := by rfl_kernel
      set_option maxHeartbeats 0 in
      set_option maxRecDepth 200000 in
      gen_placed_fnOffs $pcId $libId $symCharsId $symsEqId $symsFreshId
    )

def hexStrOf (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

def relocKindName : RelocKind → Name
  | .call26 => ``RelocKind.call26
  | .jump26 => ``RelocKind.jump26
  | .adrpHi21 => ``RelocKind.adrpHi21
  | .adrpHi21Nc => ``RelocKind.adrpHi21Nc
  | .addLo12 => ``RelocKind.addLo12
  | .ldst8Lo12 => ``RelocKind.ldst8Lo12
  | .ldst16Lo12 => ``RelocKind.ldst16Lo12
  | .ldst32Lo12 => ``RelocKind.ldst32Lo12
  | .ldst64Lo12 => ``RelocKind.ldst64Lo12
  | .ldst128Lo12 => ``RelocKind.ldst128Lo12
  | .condbr19 => ``RelocKind.condbr19
  | .ldPrelLo19 => ``RelocKind.ldPrelLo19
  | .tstbr14 => ``RelocKind.tstbr14
  | .adrPrelLo21 => ``RelocKind.adrPrelLo21
  | .prel32 => ``RelocKind.prel32
  | .abs64 => ``RelocKind.abs64
  | .abs32 => ``RelocKind.abs32
  | .adrGotPage => ``RelocKind.adrGotPage
  | .ld64GotLo12Nc => ``RelocKind.ld64GotLo12Nc
  | .tlsieAdrGottprelPage21 => ``RelocKind.tlsieAdrGottprelPage21
  | .tlsieLd64GottprelLo12Nc => ``RelocKind.tlsieLd64GottprelLo12Nc
  | .tlsdescAdrPage21 => ``RelocKind.tlsdescAdrPage21
  | .tlsdescLd64Lo12 => ``RelocKind.tlsdescLd64Lo12
  | .tlsdescAddLo12 => ``RelocKind.tlsdescAddLo12
  | .tlsdescCall => ``RelocKind.tlsdescCall
  | .tlsleAddTprelHi12 => ``RelocKind.tlsleAddTprelHi12
  | .tlsleAddTprelLo12 => ``RelocKind.tlsleAddTprelLo12
  | .tlsleAddTprelLo12Nc => ``RelocKind.tlsleAddTprelLo12Nc
  | .tlsleMovwTprelG1 => ``RelocKind.tlsleMovwTprelG1
  | .tlsleMovwTprelG1Nc => ``RelocKind.tlsleMovwTprelG1Nc
  | .tlsleMovwTprelG0 => ``RelocKind.tlsleMovwTprelG0
  | .tlsleMovwTprelG0Nc => ``RelocKind.tlsleMovwTprelG0Nc
  | .tlsleLdst8TprelLo12Nc => ``RelocKind.tlsleLdst8TprelLo12Nc
  | .tlsleLdst16TprelLo12Nc => ``RelocKind.tlsleLdst16TprelLo12Nc
  | .tlsleLdst32TprelLo12Nc => ``RelocKind.tlsleLdst32TprelLo12Nc
  | .tlsleLdst64TprelLo12Nc => ``RelocKind.tlsleLdst64TprelLo12Nc
  | .tlsleLdst128TprelLo12Nc => ``RelocKind.tlsleLdst128TprelLo12Nc

def evalBlkRelocs (idx : Nat) : MetaM (Array (Nat × Name × String × Int × Bool)) := do
  let blk := VerifiedLibraries.mallocngLib.blocks.getD idx { code := [] }
  return (blk.relocs.map fun r =>
    (r.off, relocKindName r.kind, r.sym, r.addend, r.localSym)).toArray

def evalTreeWord (treeName : Name) (off : Nat) :
    MetaM (Nat × Nat × Nat × Nat × UInt32) := do
  let treeVal ← ProofLib.GenDecodes.treeValueOf treeName
  let (b0, b1, b2, b3) ← ProofLib.GenDecodes.quadOfTreeVal treeVal off
  let w : UInt32 := UInt32.ofNat (b0 + 256 * (b1 + 256 * (b2 + 256 * b3)))
  return (b0, b1, b2, b3, w)

def mkRelocStx (off : Nat) (kn : Name) (sym : String) (addend : Int)
    (localSym : Bool) : CommandElabM (TSyntax `term) := do
  let offL := Syntax.mkNumLit (toString off)
  let knId := mkIdent kn
  let symL := Syntax.mkStrLit sym
  let addStx ← if addend >= 0 then
    let kL := Syntax.mkNumLit (toString addend.toNat)
    `(($kL : Int))
  else
    let kL := Syntax.mkNumLit (toString (-addend).toNat)
    `(-($kL : Int))
  let locId := mkIdent (if localSym then ``Bool.true else ``Bool.false)
  `({ off := $offL, kind := $knId, sym := $symL, addend := $addStx, localSym := $locId : RelocEntry })

def mkExtTargetStx (plId : Ident) (sym : String) (addend : Int) :
    CommandElabM (TSyntax `term) := do
  let symLit := Syntax.mkStrLit sym
  if addend == 0 then
    `(($plId).ρ $symLit)
  else if addend > 0 then
    let kLit := Syntax.mkNumLit (toString addend.toNat)
    `(($plId).ρ $symLit + BitVec.ofNat 64 $kLit)
  else
    throwError "negative addend {addend} on {sym}"

elab_rules : command
  | `(gen_blk_reloc_steps $tag:ident $idxStx:num $nwStx:num) => do
    let tagStr := tag.getId.toString
    let idx := idxStx.getNat
    let nwords := nwStx.getNat
    let libId := mkIdent (Name.mkSimple s!"blkLib_{tagStr}")
    let plId := mkIdent (Name.mkSimple s!"blkPl_{tagStr}")
    let plbId := mkIdent (Name.mkSimple s!"blkPlaceable_{tagStr}")
    let pc0Id := mkIdent (Name.mkSimple s!"blkPC0_{tagStr}")
    let pcId := mkIdent (Name.mkSimple s!"blkPC_{tagStr}")
    let treeName := `VerifiedLibraries.Mallocng.Proofs ++ Name.mkSimple s!"blkTree_{tagStr}"
    let codeEqId := mkIdent (Name.mkSimple s!"blkCodeEq_{tagStr}")
    let sizeEqId := mkIdent (Name.mkSimple s!"blkSizeEq_{tagStr}")
    let relocs ← liftTermElabM (evalBlkRelocs idx)

    let mkWordStx (off : Nat) : CommandElabM (TSyntax `term × UInt32) := do
      let (b0, b1, b2, b3, w) ← liftTermElabM (evalTreeWord treeName off)
      let jL := Syntax.mkNumLit (toString (off / 4))
      let b0L := Syntax.mkNumLit (toString b0)
      let b1L := Syntax.mkNumLit (toString b1)
      let b2L := Syntax.mkNumLit (toString b2)
      let b3L := Syntax.mkNumLit (toString b3)
      let wL := Syntax.mkNumLit (toString w.toNat)
      let stx ← `(blk_wordAt (lib := $libId) $codeEqId $sizeEqId (j := $jL)
        (b0 := BitVec.ofNat 8 $b0L) (b1 := BitVec.ofNat 8 $b1L)
        (b2 := BitVec.ofNat 8 $b2L) (b3 := BitVec.ofNat 8 $b3L)
        (w := BitVec.ofNat 32 $wL) rfl (by rfl_kernel) rfl)
      return (stx, w)

    let mut skipNextOff : Option Nat := none
    let mut relaxPairOffs : Array Nat := #[]
    for (off, kn, sym, addend, locSym) in relocs do
      if skipNextOff == some off then
        skipNextOff := none
        continue
      let hex := hexStrOf off
      let offLit := Syntax.mkNumLit (toString off)
      let r0Stx ← mkRelocStx off kn sym addend locSym
      let (hw0Stx, w0) ← mkWordStx off

      if kn == ``RelocKind.adrpHi21 then
        let rd := w0.toNat % 32
        let rdL := Syntax.mkNumLit (toString rd)
        let nextRel? := relocs.find? (·.1 == off + 4)
        let isRelaxable ← match nextRel? with
          | some (_, kn2, sym2, add2, _) =>
            if kn2 == ``RelocKind.addLo12 && sym2 == sym && add2 == addend then
              let (_, _, _, _, w1) ← liftTermElabM (evalTreeWord treeName (off + 4))
              pure ((w0 &&& 0x9f000000) == 0x90000000 &&
                    (w1 &&& 0xffc00000) == 0x91000000 &&
                    (w1.toNat % 32) == rd && ((w1.toNat >>> 5) % 32) == rd && rd != 31)
            else pure false
          | none => pure false
        let thmId := mkIdent (Name.mkSimple s!"blkPC_{tagStr}_pairStep_0x{hex}")
        let bId := mkIdent `b
        let vStx ← mkExtTargetStx plId sym addend
        let symLit := Syntax.mkStrLit sym
        let hTStx ← if addend == 0 then
          `(blk_target_ext_zero (lib := $libId) (pl := $plId) (r := $r0Stx) (sym := $symLit)
              rfl (by rfl_kernel) rfl)
        else
          let kL := Syntax.mkNumLit (toString addend.toNat)
          `(blk_target_ext_pos (lib := $libId) (pl := $plId) (r := $r0Stx) (sym := $symLit)
              (k := $kL) rfl (by rfl_kernel) rfl rfl)
        if isRelaxable then
          skipNextOff := some (off + 4)
          relaxPairOffs := relaxPairOffs.push off
          let some (_, kn2, sym2, add2, loc2) := nextRel? | unreachable!
          let r1Stx ← mkRelocStx (off + 4) kn2 sym2 add2 loc2
          let (hw1Stx, _) ← mkWordStx (off + 4)
          let off8L := Syntax.mkNumLit (toString (off + 8))
          elabCommand (← `(
            theorem $thmId [MallocngMultiPlacement] ($bId : BitVec 64)
                (X : String → Option (Arm64.State → Arm64.State))
                {tgt : BitVec 64} {s : Arm64.State} {P : SepProp}
                {post : Arm64.State → SepProp → Prop}
                {oom : Arm64.State → SepProp}
                (hb : $bId = mbase $idxStx)
                (hpc : s.pc = $bId + BitVec.ofNat 64 $offLit)
                (hrun : s.status = ExecStatus.Running)
                (hnext : SepWP (($pcId).rebase $bId X) tgt
                  ((s.writeReg64 (.gpr (BitVec.ofNat 5 $rdL)) $vStx).setPC
                    ($bId + BitVec.ofNat 64 $off8L)) P post oom) :
                SepWP (($pcId).rebase $bId X) tgt s P post oom :=
              sepWP_blk_relaxablePair $codeEqId $sizeEqId $plbId (r := $r0Stx)
                (GenPlacedFetches.relaxableAt_of_words (r1 := $r0Stx) (r2 := $r1Stx)
                  (by rfl_kernel) (by rfl_kernel) $hw0Stx $hw1Stx rfl)
                (by rfl_kernel)
                (blk_word_rd $hw0Stx rfl)
                (by decide) rfl (by decide) (by decide) hb (fun _ => $hTStx) hpc hrun hnext
          ))
        else
          let off4L := Syntax.mkNumLit (toString (off + 4))
          let hnrelStx ← match nextRel? with
            | none => `(blk_relaxableAt_false_none (lib := $libId) (r1 := $r0Stx)
                (by rfl_kernel) (by rfl_kernel))
            | some (_, kn2, sym2, add2, loc2) => do
              let r1Stx ← mkRelocStx (off + 4) kn2 sym2 add2 loc2
              let (hw1Stx, _) ← mkWordStx (off + 4)
              `(blk_relaxableAt_false_some (lib := $libId) (r1 := $r0Stx) (r2 := $r1Stx)
                  (by rfl_kernel) (by rfl_kernel) $hw0Stx $hw1Stx rfl)
          elabCommand (← `(
            theorem $thmId [MallocngMultiPlacement] ($bId : BitVec 64)
                (X : String → Option (Arm64.State → Arm64.State))
                {tgt : BitVec 64} {s : Arm64.State} {P : SepProp}
                {post : Arm64.State → SepProp → Prop}
                {oom : Arm64.State → SepProp}
                (hb : $bId = mbase $idxStx)
                (hpc : s.pc = $bId + BitVec.ofNat 64 $offLit)
                (hrun : s.status = ExecStatus.Running)
                (hnext : SepWP (($pcId).rebase $bId X) tgt
                  ((s.writeReg64 (.gpr (BitVec.ofNat 5 $rdL)) (pageOf $vStx)).setPC
                    ($bId + BitVec.ofNat 64 $off4L)) P post oom) :
                SepWP (($pcId).rebase $bId X) tgt s P post oom :=
              sepWP_blk_adrpPlain $codeEqId $sizeEqId $plbId (r := $r0Stx)
                (by rfl_kernel) rfl $hnrelStx $hw0Stx rfl rfl (by decide) $hTStx rfl
                (by decide) hb hpc hrun hnext
          ))
        continue

      let scale? : Option Nat :=
        if kn == ``RelocKind.ldst8Lo12 then some 0
        else if kn == ``RelocKind.ldst16Lo12 then some 1
        else if kn == ``RelocKind.ldst32Lo12 then some 2
        else if kn == ``RelocKind.ldst64Lo12 then some 3
        else none
      if let some scale := scale? then
        let bId := mkIdent `b
        let vStx ← mkExtTargetStx plId sym addend
        let symLit := Syntax.mkStrLit sym
        let hTStx ← if addend == 0 then
          `(blk_target_ext_zero (lib := $libId) (pl := $plId) (r := $r0Stx) (sym := $symLit)
              rfl (by rfl_kernel) rfl)
        else
          let kL := Syntax.mkNumLit (toString addend.toNat)
          `(blk_target_ext_pos (lib := $libId) (pl := $plId) (r := $r0Stx) (sym := $symLit)
              (k := $kL) rfl (by rfl_kernel) rfl rfl)
        let scaleL := Syntax.mkNumLit (toString scale)
        let opc := (w0.toNat >>> 22) % 4
        let rt := w0.toNat % 32
        let rn := (w0.toNat >>> 5) % 32
        let rtStx ← if rt == 31 then `(Reg.xzr) else
          let rtL := Syntax.mkNumLit (toString rt)
          `(Reg.gpr (BitVec.ofNat 5 $rtL))
        let rnStx ← if rn == 31 then `(Reg.sp) else
          let rnL := Syntax.mkNumLit (toString rn)
          `(Reg.gpr (BitVec.ofNat 5 $rnL))
        let addrStx ← `(AddrMode.Offset $rnStx (lo12Of $vStx))
        let szStx ← match scale with
          | 0 => `(MemWidth.B8)
          | 1 => `(MemWidth.H16)
          | 2 => `(MemWidth.W32)
          | _ => `(MemWidth.X64)
        let instStx ← match opc with
          | 0 => `(Instr.str $szStx $rtStx $addrStx)
          | 1 =>
            let rwStx ← if scale == 3 then `(RegWidth.W64) else `(RegWidth.W32)
            `(Instr.ldr $rwStx $szStx false $rtStx $addrStx)
          | 2 => `(Instr.ldr RegWidth.W64 $szStx true $rtStx $addrStx)
          | _ => `(Instr.ldr RegWidth.W32 $szStx true $rtStx $addrStx)
        let fetchId := mkIdent (Name.mkSimple s!"blkPC0_{tagStr}_rebase_fetch_0x{hex}")
        elabCommand (← `(
          set_option linter.literalFetch false in
          @[simp, arm64_norm]
          theorem $fetchId [MallocngMultiPlacement] ($bId : BitVec 64)
              (X : String → Option (Arm64.State → Arm64.State)) :
              (($pc0Id).rebase $bId X).fetch ($bId + BitVec.ofNat 64 $offLit) = some $instStx :=
            PlacedLib.fetch_rebase_ldstLo12_of_placeable (r := $r0Stx) (scale := $scaleL)
              $plbId (by rfl_kernel) rfl
              (GenPlacedFetches.hookAtOff?_rebase_of_placeable (b := $bId) (X := X)
                $codeEqId $sizeEqId $plbId (by decide))
              $hw0Stx rfl rfl rfl $hTStx rfl
        ))
        continue

      if kn == ``RelocKind.addLo12 then
        let fetchName := `VerifiedLibraries.Mallocng.Proofs ++
          Name.mkSimple s!"blkPC0_{tagStr}_rebase_fetch_0x{hex}"
        if (← getEnv).contains fetchName then
          continue
        let bId := mkIdent `b
        let vStx ← mkExtTargetStx plId sym addend
        let symLit := Syntax.mkStrLit sym
        let hTStx ← if addend == 0 then
          `(blk_target_ext_zero (lib := $libId) (pl := $plId) (r := $r0Stx) (sym := $symLit)
              rfl (by rfl_kernel) rfl)
        else
          let kL := Syntax.mkNumLit (toString addend.toNat)
          `(blk_target_ext_pos (lib := $libId) (pl := $plId) (r := $r0Stx) (sym := $symLit)
              (k := $kL) rfl (by rfl_kernel) rfl rfl)
        let rd := w0.toNat % 32
        let rn := (w0.toNat >>> 5) % 32
        let rdStx ← if rd == 31 then `(Reg.sp) else
          let rdL := Syntax.mkNumLit (toString rd)
          `(Reg.gpr (BitVec.ofNat 5 $rdL))
        let rnStx ← if rn == 31 then `(Reg.sp) else
          let rnL := Syntax.mkNumLit (toString rn)
          `(Reg.gpr (BitVec.ofNat 5 $rnL))
        let hm4Stx ← if off < 4 then
          `(Or.inl (by decide))
        else match relocs.find? (·.1 == off - 4) with
          | none =>
            `(Or.inr (blk_relaxableAt_false_first_none (lib := $libId) (by rfl_kernel)))
          | some (_, knP, symP, addP, locP) => do
            let rPStx ← mkRelocStx (off - 4) knP symP addP locP
            if knP != ``RelocKind.adrpHi21 then
              `(Or.inr (CodeBlock.relaxableAt_false_of_kind (r := $rPStx) (by rfl_kernel) (by decide)))
            else
              let (hwPStx, _) ← mkWordStx (off - 4)
              `(Or.inr (blk_relaxableAt_false_some (lib := $libId) (r1 := $rPStx) (r2 := $r0Stx)
                  (by rfl_kernel) (by rfl_kernel) $hwPStx $hw0Stx rfl))
        let fetchId := mkIdent (Name.mkSimple s!"blkPC0_{tagStr}_rebase_fetch_0x{hex}")
        elabCommand (← `(
          set_option linter.literalFetch false in
          @[simp, arm64_norm]
          theorem $fetchId [MallocngMultiPlacement] ($bId : BitVec 64)
              (X : String → Option (Arm64.State → Arm64.State)) :
              (($pc0Id).rebase $bId X).fetch ($bId + BitVec.ofNat 64 $offLit) =
                some (.addSubImm .W64 .ADD $rdStx $rnStx ((lo12Of $vStx).truncate 12) false) :=
            fetch_rebase_addLo12_of_placeable (r := $r0Stx) $plbId (by rfl_kernel) rfl
              $hm4Stx
              (GenPlacedFetches.hookAtOff?_rebase_of_placeable (b := $bId) (X := X)
                $codeEqId $sizeEqId $plbId (by decide))
              $hw0Stx rfl $hTStx rfl rfl
        ))
        continue

    -- Emit `blkPC_<tag>_rebase_fetch_base` and `blkPC_<tag>_rebase_fetch_0x<hex>` aliases so
    -- `VCGen.tryCloseFetchFromHasCode` resolves fetches on `(blkPC_<tag>).rebase b X` in O(1),
    -- then verify instruction coverage across all `nwords` offsets of this block.
    liftTermElabM do
      let ns := `VerifiedLibraries.Mallocng.Proofs
      let fetchEq := ns ++ Name.mkSimple s!"blkPC_rebase_fetch_{tagStr}"
      let aliasOne (oldSuffix newSuffix : String) : MetaM Unit := do
        let env ← getEnv
        let oldName := ns ++ Name.mkSimple oldSuffix
        let newName := ns ++ Name.mkSimple newSuffix
        if let some info := env.find? oldName then
          unless env.contains newName do
            let (newTy, val) ← forallBoundedTelescope info.type (some 3) fun xs body => do
              let some (_, lhs, rhs) := body.eq?
                | throwError "expected equality in {oldName}"
              let pc := lhs.getArg! 1
              let step1 := mkApp4 (mkConst fetchEq) xs[0]! xs[1]! xs[2]! pc
              let step2 := mkAppN (mkConst oldName (info.levelParams.map Level.param)) xs
              let some (_, newLhs, _) := (← inferType step1).eq?
                | throwError "expected equality in {fetchEq}"
              let newBody ← mkEq newLhs rhs
              let prf ← mkEqTrans step1 step2
              return (← mkForallFVars xs newBody, ← mkLambdaFVars xs prf)
            ProofLib.GenDecodes.addThm newName newTy val
      aliasOne s!"blkPC0_{tagStr}_rebase_fetch_base" s!"blkPC_{tagStr}_rebase_fetch_base"
      for j in [:nwords] do
        let hex := hexStrOf (4 * j)
        aliasOne s!"blkPC0_{tagStr}_rebase_fetch_0x{hex}" s!"blkPC_{tagStr}_rebase_fetch_0x{hex}"

    let env ← getEnv
    for j in [:nwords] do
      let off := 4 * j
      let hex := hexStrOf off
      let fetchNm := `VerifiedLibraries.Mallocng.Proofs ++ Name.mkSimple s!"blkPC_{tagStr}_rebase_fetch_0x{hex}"
      let pairNm := `VerifiedLibraries.Mallocng.Proofs ++ Name.mkSimple s!"blkPC_{tagStr}_pairStep_0x{hex}"
      let covered := env.contains fetchNm || env.contains pairNm ||
        (off >= 4 && relaxPairOffs.contains (off - 4))
      if !covered then
        throwError "PlacedFetchBase: block {tagStr} offset 0x{hex} has neither fetch nor pairStep!"

end

end VerifiedLibraries.Mallocng.Proofs
