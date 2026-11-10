/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Lean.Data.Json
public import Arm64

/-!
# Placed Module Evaluator CLI

Command-line evaluator (`placed_eval`) for `MultiPlacedLib` placements. Given a JSON library and
`MultiPlacement` description, checks `MultiPlacedLib.Placeable`, code/data region disjointness, and
AArch64 Variant I TLS layout invariants, then materializes patched code words, data bytes, and TLS
initializers.
-/

@[expose] public section

open Lean
open Arm64
open Arm64.Obj

namespace Arm64.Testing.Harness.PlacedEval

def toHex64 (bv : BitVec 64) : String :=
  let digits := "0123456789abcdef".toList
  Id.run do
    let mut n := bv.toNat
    let mut chars : List Char := []
    for _ in [0:16] do
      let d := n % 16
      chars := (digits[d]?.getD '0') :: chars
      n := n / 16
    return "0x" ++ String.ofList chars

def toHex32 (bv : BitVec 32) : String :=
  let digits := "0123456789abcdef".toList
  Id.run do
    let mut n := bv.toNat
    let mut chars : List Char := []
    for _ in [0:8] do
      let d := n % 16
      chars := (digits[d]?.getD '0') :: chars
      n := n / 16
    return "0x" ++ String.ofList chars

def parseHex64 (s : String) : Except String (BitVec 64) := do
  let body := if s.startsWith "0x" || s.startsWith "0X" then (s.drop 2).toString else s
  let mut acc : Nat := 0
  for c in body.toList do
    let d ←
      if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
      else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
      else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
      else .error s!"invalid hex digit '{c}' in '{s}'"
    acc := acc * 16 + d
  return BitVec.ofNat 64 acc

def parseNatField (j : Json) (field : String) : Except String Nat := do
  let v ← j.getObjVal? field
  if let .ok n := v.getNat? then
    return n
  if let .ok s := v.getStr? then
    let body := if s.startsWith "0x" || s.startsWith "0X" then (s.drop 2).toString else s
    let mut acc : Nat := 0
    for c in body.toList do
      let d ←
        if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
        else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
        else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
        else .error s!"invalid hex digit '{c}' in field '{field}'"
      acc := acc * 16 + d
    return acc
  throw s!"field '{field}' must be Nat or hex string"

def parseOptNatField (j : Json) (field : String) (defaultVal : Nat) : Except String Nat := do
  match j.getObjVal? field with
  | .ok .null | .error _ => return defaultVal
  | .ok _ => parseNatField j field

def parseOptIntField (j : Json) (field : String) (defaultVal : Int) : Except String Int := do
  match j.getObjVal? field with
  | .ok .null | .error _ => return defaultVal
  | .ok v => v.getInt?

def parseOptBoolField (j : Json) (field : String) (defaultVal : Bool) : Except String Bool := do
  match j.getObjVal? field with
  | .ok .null | .error _ => return defaultVal
  | .ok v => v.getBool?

def parseU64Val (v : Json) : Except String (BitVec 64) := do
  if let .ok n := v.getNat? then
    return BitVec.ofNat 64 n
  if let .ok s := v.getStr? then
    return ← parseHex64 s
  throw s!"expected u64 (Nat or hex string), got {v.compress}"

def parseBytesHex (s : String) : Except String (List (BitVec 8)) := do
  let body := if s.startsWith "0x" || s.startsWith "0X" then (s.drop 2).toString else s
  let chars := body.toList
  if chars.length % 2 != 0 then
    throw s!"odd-length hex string ({chars.length} chars)"
  let rec go : List Char → Except String (List (BitVec 8))
    | [] => .ok []
    | c1 :: c2 :: rest => do
      let nib (c : Char) : Except String Nat :=
        if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
        else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
        else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
        else .error s!"invalid hex digit '{c}'"
      let b := (← nib c1) * 16 + (← nib c2)
      let tail ← go rest
      return BitVec.ofNat 8 b :: tail
    | [_] => .error "unreachable odd hex length"
  go chars

def bytesToHex (bs : List (BitVec 8)) : String := Id.run do
  let hexDigits : Array Char := #['0','1','2','3','4','5','6','7','8','9','a','b','c','d','e','f']
  let mut out : String := ""
  for b in bs do
    let n := b.toNat
    out := out.push (hexDigits[(n / 16) % 16]!)
    out := out.push (hexDigits[n % 16]!)
  return out

def parseRelocKind (s : String) : Except String RelocKind :=
  match s with
  | "call26" | "R_AARCH64_CALL26" => .ok .call26
  | "jump26" | "R_AARCH64_JUMP26" => .ok .jump26
  | "adrpHi21" | "R_AARCH64_ADR_PREL_PG_HI21" => .ok .adrpHi21
  | "adrpHi21Nc" | "R_AARCH64_ADR_PREL_PG_HI21_NC" => .ok .adrpHi21Nc
  | "addLo12" | "R_AARCH64_ADD_ABS_LO12_NC" => .ok .addLo12
  | "ldst8Lo12" | "R_AARCH64_LDST8_ABS_LO12_NC" => .ok .ldst8Lo12
  | "ldst16Lo12" | "R_AARCH64_LDST16_ABS_LO12_NC" => .ok .ldst16Lo12
  | "ldst32Lo12" | "R_AARCH64_LDST32_ABS_LO12_NC" => .ok .ldst32Lo12
  | "ldst64Lo12" | "R_AARCH64_LDST64_ABS_LO12_NC" => .ok .ldst64Lo12
  | "ldst128Lo12" | "R_AARCH64_LDST128_ABS_LO12_NC" => .ok .ldst128Lo12
  | "condbr19" | "R_AARCH64_CONDBR19" => .ok .condbr19
  | "tstbr14" | "R_AARCH64_TSTBR14" => .ok .tstbr14
  | "ldPrelLo19" | "R_AARCH64_LD_PREL_LO19" => .ok .ldPrelLo19
  | "adrPrelLo21" | "R_AARCH64_ADR_PREL_LO21" => .ok .adrPrelLo21
  | "prel32" | "R_AARCH64_PREL32" => .ok .prel32
  | "abs64" | "R_AARCH64_ABS64" => .ok .abs64
  | "abs32" | "R_AARCH64_ABS32" => .ok .abs32
  | "adrGotPage" | "R_AARCH64_ADR_GOT_PAGE" => .ok .adrGotPage
  | "ld64GotLo12Nc" | "R_AARCH64_LD64_GOT_LO12_NC" => .ok .ld64GotLo12Nc
  | "tlsieAdrGottprelPage21" | "R_AARCH64_TLSIE_ADR_GOTTPREL_PAGE21" => .ok .tlsieAdrGottprelPage21
  | "tlsieLd64GottprelLo12Nc" | "R_AARCH64_TLSIE_LD64_GOTTPREL_LO12_NC" => .ok .tlsieLd64GottprelLo12Nc
  | "tlsdescAdrPage21" | "R_AARCH64_TLSDESC_ADR_PAGE21" => .ok .tlsdescAdrPage21
  | "tlsdescLd64Lo12" | "R_AARCH64_TLSDESC_LD64_LO12" => .ok .tlsdescLd64Lo12
  | "tlsdescAddLo12" | "R_AARCH64_TLSDESC_ADD_LO12" => .ok .tlsdescAddLo12
  | "tlsdescCall" | "R_AARCH64_TLSDESC_CALL" => .ok .tlsdescCall
  | "tlsleAddTprelHi12" | "R_AARCH64_TLSLE_ADD_TPREL_HI12" => .ok .tlsleAddTprelHi12
  | "tlsleAddTprelLo12" | "R_AARCH64_TLSLE_ADD_TPREL_LO12" => .ok .tlsleAddTprelLo12
  | "tlsleAddTprelLo12Nc" | "R_AARCH64_TLSLE_ADD_TPREL_LO12_NC" => .ok .tlsleAddTprelLo12Nc
  | "tlsleLdst8TprelLo12Nc" | "R_AARCH64_TLSLE_LDST8_TPREL_LO12_NC" => .ok .tlsleLdst8TprelLo12Nc
  | "tlsleLdst16TprelLo12Nc" | "R_AARCH64_TLSLE_LDST16_TPREL_LO12_NC" => .ok .tlsleLdst16TprelLo12Nc
  | "tlsleLdst32TprelLo12Nc" | "R_AARCH64_TLSLE_LDST32_TPREL_LO12_NC" => .ok .tlsleLdst32TprelLo12Nc
  | "tlsleLdst64TprelLo12Nc" | "R_AARCH64_TLSLE_LDST64_TPREL_LO12_NC" => .ok .tlsleLdst64TprelLo12Nc
  | "tlsleLdst128TprelLo12Nc" | "R_AARCH64_TLSLE_LDST128_TPREL_LO12_NC" => .ok .tlsleLdst128TprelLo12Nc
  | "tlsleMovwTprelG1" | "R_AARCH64_TLSLE_MOVW_TPREL_G1" => .ok .tlsleMovwTprelG1
  | "tlsleMovwTprelG1Nc" | "R_AARCH64_TLSLE_MOVW_TPREL_G1_NC" => .ok .tlsleMovwTprelG1Nc
  | "tlsleMovwTprelG0" | "R_AARCH64_TLSLE_MOVW_TPREL_G0" => .ok .tlsleMovwTprelG0
  | "tlsleMovwTprelG0Nc" | "R_AARCH64_TLSLE_MOVW_TPREL_G0_NC" => .ok .tlsleMovwTprelG0Nc
  | other => .error s!"unknown RelocKind '{other}'"

def parseRelocEntry (j : Json) : Except String RelocEntry := do
  let off ← parseNatField j "off"
  let kindStr ← (j.getObjVal? "kind").bind Json.getStr?
  let kind ← parseRelocKind kindStr
  let sym ← (j.getObjVal? "sym").bind Json.getStr?
  let addend ← parseOptIntField j "addend" 0
  let localSym ← parseOptBoolField j "local_sym" false
  return { off, kind, sym, addend, localSym }

def parseCodeBlock (j : Json) : Except String CodeBlock := do
  let codeHex ← (j.getObjVal? "code_hex").bind Json.getStr?
  let code ← parseBytesHex codeHex
  let align ← parseOptNatField j "align" 4
  let symbols ← match j.getObjVal? "symbols" with
    | .ok .null | .error _ => pure []
    | .ok (.arr arr) =>
      arr.toList.mapM fun sj => do
        let name ← (sj.getObjVal? "name").bind Json.getStr?
        let off ← parseNatField sj "off"
        return (name, off)
    | .ok _ => throw "'symbols' must be an array"
  let relocs ← match j.getObjVal? "relocs" with
    | .ok .null | .error _ => pure []
    | .ok (.arr arr) => arr.toList.mapM parseRelocEntry
    | .ok _ => throw "'relocs' must be an array"
  let externs ← match j.getObjVal? "externs" with
    | .ok .null | .error _ => pure []
    | .ok (.arr arr) => arr.toList.mapM Json.getStr?
    | .ok _ => throw "'externs' must be an array"
  let weakRefs ← match j.getObjVal? "weak_refs" with
    | .ok .null | .error _ => pure []
    | .ok (.arr arr) => arr.toList.mapM Json.getStr?
    | .ok _ => throw "'weak_refs' must be an array"
  return { code, align, symbols, relocs, externs, weakRefs }

def parseSymDataInfo (defaultRo : Bool) (j : Json) : Except String SymDataInfo := do
  let sym ← (j.getObjVal? "sym").bind Json.getStr?
  let align ← parseOptNatField j "align" 1
  let readOnly ← parseOptBoolField j "read_only" defaultRo
  let bytesHex ← match j.getObjVal? "bytes_hex" with
    | .ok .null | .error _ => pure ""
    | .ok v => v.getStr?
  let bytes ← parseBytesHex bytesHex
  let zeroTail ← parseOptNatField j "zero_tail" 0
  let relocs ← match j.getObjVal? "relocs" with
    | .ok .null | .error _ => pure []
    | .ok (.arr arr) => arr.toList.mapM parseRelocEntry
    | .ok _ => throw "'relocs' must be an array"
  return { sym, align, readOnly, bytes, zeroTail, relocs }

def parseAddrPairs (j : Json) (field : String) : Except String (List (String × BitVec 64)) := do
  match j.getObjVal? field with
  | .ok .null | .error _ => return []
  | .ok (.arr arr) =>
    arr.toList.mapM fun item => do
      let name ← (item.getObjVal? "name").bind Json.getStr?
      let addrVal ← item.getObjVal? "addr"
      let addr ← parseU64Val addrVal
      return (name, addr)
  | .ok (.obj kvs) =>
    kvs.toArray.toList.mapM fun ⟨k, v⟩ => do
      let addr ← parseU64Val v
      return (k, addr)
  | .ok _ => throw s!"'{field}' must be an array or object"

def parsePerBlockOffsets (j : Json) (field : String) : Except String (List (List Nat)) := do
  match j.getObjVal? field with
  | .ok .null | .error _ => return []
  | .ok (.arr arr) =>
    arr.toList.mapM fun sub => do
      match sub with
      | .arr offs => offs.toList.mapM Json.getNat?
      | _ => throw s!"'{field}' elements must be arrays of Nat"
  | .ok _ => throw s!"'{field}' must be an array of arrays"

/-- Decidable check for `CodeRelocInRange kind place target`. -/
def checkCodeRelocInRange (kind : RelocKind) (place target : BitVec 64) : Bool :=
  let sInRange (lo hi : Int) (d : BitVec 64) : Bool :=
    decide (lo ≤ d.toInt) && decide (d.toInt < hi)
  match kind with
  | .call26 | .jump26 =>
    decide ((target - place).toNat % 4 = 0) && sInRange (-134217728) 134217728 (target - place)
  | .adrpHi21 | .adrGotPage | .tlsieAdrGottprelPage21 =>
    sInRange (-4294967296) 4294967296 (pageOf target - pageOf place)
  | .adrpHi21Nc => true
  | .addLo12 | .ldst8Lo12 => true
  | .ldst16Lo12 => (target &&& 1#64) == 0#64
  | .ldst32Lo12 => (target &&& 3#64) == 0#64
  | .ldst64Lo12 | .ld64GotLo12Nc | .tlsieLd64GottprelLo12Nc => (target &&& 7#64) == 0#64
  | .ldst128Lo12 => (target &&& 15#64) == 0#64
  | .condbr19 | .ldPrelLo19 =>
    decide ((target - place).toNat % 4 = 0) && sInRange (-1048576) 1048576 (target - place)
  | .tstbr14 =>
    decide ((target - place).toNat % 4 = 0) && sInRange (-32768) 32768 (target - place)
  | .adrPrelLo21 => sInRange (-1048576) 1048576 (target - place)
  | .prel32 => sInRange (-2147483648) 2147483648 (target - place)
  | .abs64 | .abs32 => false
  | .tlsdescAdrPage21 | .tlsdescLd64Lo12 | .tlsdescAddLo12 | .tlsdescCall =>
    decide (target.toNat < 4294967296)
  | .tlsleAddTprelHi12 => decide (target.toNat < 16777216)
  | .tlsleAddTprelLo12 => decide (target.toNat < 4096)
  | .tlsleAddTprelLo12Nc | .tlsleLdst8TprelLo12Nc => true
  | .tlsleLdst16TprelLo12Nc => (target &&& 1#64) == 0#64
  | .tlsleLdst32TprelLo12Nc => (target &&& 3#64) == 0#64
  | .tlsleLdst64TprelLo12Nc => (target &&& 7#64) == 0#64
  | .tlsleLdst128TprelLo12Nc => (target &&& 15#64) == 0#64
  | .tlsleMovwTprelG1 => sInRange (-4294967296) 4294967296 target
  | .tlsleMovwTprelG1Nc => true
  | .tlsleMovwTprelG0 => sInRange (-65536) 65536 target
  | .tlsleMovwTprelG0Nc => true

/-- Decidable check for `CodeBlock.relocInRange blk pl kind off place target`. -/
def checkRelocInRange (blk : CodeBlock) (pl : Placement) (kind : RelocKind) (off : Nat)
    (place target : BitVec 64) : Bool :=
  let sInRange (lo hi : Int) (d : BitVec 64) : Bool :=
    decide (lo ≤ d.toInt) && decide (d.toInt < hi)
  match kind with
  | .adrGotPage =>
    if blk.gotPairAt off && pl.relax off then true
    else sInRange (-4294967296) 4294967296 (pageOf target - pageOf place)
  | .ld64GotLo12Nc =>
    if 4 ≤ off && blk.gotPairAt (off - 4) && pl.relax (off - 4) then
      sInRange (-1048576) 1048576 (target - place)
    else if 4 ≤ off && blk.gotPairAt (off - 4) && pl.relax off then true
    else (target &&& 7#64) == 0#64
  | .tlsieAdrGottprelPage21 =>
    if blk.tlsieRelaxableAt off && pl.relax off then
      decide (target.toNat < 4294967296)
    else sInRange (-4294967296) 4294967296 (pageOf target - pageOf place)
  | .tlsieLd64GottprelLo12Nc =>
    if blk.tlsieRelaxableAt off && pl.relax off then
      decide (target.toNat < 4294967296)
    else (target &&& 7#64) == 0#64
  | _ => checkCodeRelocInRange kind place target

def checkRangesDisjoint (b1 n1 b2 n2 : Nat) : Bool :=
  decide (b1 + n1 ≤ b2 ∨ b2 + n2 ≤ b1)

def checkCodeBlockPlaceable (blk : CodeBlock) (pl : Placement) (idx : Nat) :
    Option String := Id.run do
  let len := blk.code.length
  if !(0 < blk.align && blk.align % 4 == 0) then
    return some s!"block {idx}: invalid align {blk.align}"
  if pl.base.toNat % blk.align != 0 then
    return some s!"block {idx}: base {toHex64 pl.base} not aligned to {blk.align}"
  if !(pl.base.toNat + len ≤ 2 ^ 64) then
    return some s!"block {idx}: code range wraps 64-bit address space"
  if len % 4 != 0 then
    return some s!"block {idx}: code length {len} not a multiple of 4"
  if !decide ((blk.relocs.map (·.off)).Nodup) then
    return some s!"block {idx}: duplicate relocation offsets"
  for r in blk.relocs do
    if r.off % 4 != 0 || !(r.off + 4 ≤ len) then
      return some s!"block {idx}: relocation at {r.off} out of bounds or misaligned"
    let place := pl.base + BitVec.ofNat 64 r.off
    let target := blk.relocTarget pl r.off r
    if !checkRelocInRange blk pl r.kind r.off place target then
      return some s!"block {idx}: relocation at 0x{String.ofList (Nat.toDigits 16 r.off)} ({repr r.kind} -> {r.sym}+{r.addend}, place={toHex64 place}, target={toHex64 target}) out of range"
  for r in blk.relocs do
    let off := r.off
    if blk.relaxedAt pl off || (blk.gotPairAt off && pl.relax off) then
      match blk.relocAt? (off + 4) with
      | some r2 =>
        let place4 := pl.base + BitVec.ofNat 64 (off + 4)
        let tgt := blk.target pl r2
        let d := tgt - place4
        if !(decide (-(2 ^ 20 : Int) ≤ d.toInt) && decide (d.toInt < (2 ^ 20 : Int))) then
          return some s!"block {idx}: relaxed ADRP+ADD/GOT at 0x{String.ofList (Nat.toDigits 16 off)} out of ADR ±1 MiB range"
      | none => pure ()
    if blk.tlsieRelaxableAt off && pl.relax off then
      let tgt := blk.target pl r
      if !(decide (0 ≤ tgt.toInt) && decide (tgt.toInt < (2 ^ 32 : Int))) then
        return some s!"block {idx}: relaxed TLSIE at 0x{String.ofList (Nat.toDigits 16 off)} out of 32-bit TP range"
  for (sname, soff) in blk.symbols do
    if soff % 4 != 0 || !(soff ≤ len) then
      return some s!"block {idx}: symbol {sname} offset {soff} invalid"
  for ext in blk.externs do
    if (lookup ext blk.symbols).isSome then
      return some s!"block {idx}: extern {ext} is also a block symbol"
    if !(len ≤ (pl.ρ ext - pl.base).toNat) then
      return some s!"block {idx}: extern {ext} at {toHex64 (pl.ρ ext)} overlaps block"
  return none

def checkDataReloc (lib : MultiPlacedLib) (mpl : MultiPlacement)
    (addr : BitVec 64) (n : Nat) (r : RelocEntry) : Bool :=
  let t := addSignedAddr (lib.resolve mpl r.sym) r.addend
  let sInRange (lo hi : Int) (d : BitVec 64) : Bool :=
    decide (lo ≤ d.toInt) && decide (d.toInt < hi)
  decide (0 < dataRelocWidth r.kind) && decide (r.off + dataRelocWidth r.kind ≤ n) &&
    match r.kind with
    | .abs32 => sInRange (-2147483648) 4294967296 t
    | .prel32 => sInRange (-2147483648) 2147483648 (t - (addr + BitVec.ofNat 64 r.off))
    | _ => true

/-- Check `MultiPlacedLib.Placeable lib mpl` plus pairwise code/data disjointness and
    AArch64 Variant I TLS block validity. Returns `none` when valid or `some reason` when invalid. -/
def checkValidPlacement (lib : MultiPlacedLib) (tls : List SymDataInfo)
    (mpl : MultiPlacement) : Option String := Id.run do
  let mut idx := 0
  for blk in lib.blocks do
    if let some err := checkCodeBlockPlaceable blk (lib.blockPlacement mpl idx) idx then
      return some err
    idx := idx + 1
  if !decide (((lib.blocks.flatMap (·.symbols)).map (·.1)).Nodup) then
    return some "duplicate symbol names across code blocks"
  if !decide ((lib.data.map (·.sym)).Nodup) then
    return some "duplicate data symbol names"
  if !decide ((tls.map (·.sym)).Nodup) then
    return some "duplicate TLS symbol names"
  let blks := lib.blocks.toArray
  for i in [0:blks.size] do
    for j in [i+1:blks.size] do
      let b1 := (mpl.base i).toNat
      let n1 := blks[i]!.code.length
      let b2 := (mpl.base j).toNat
      let n2 := blks[j]!.code.length
      if !checkRangesDisjoint b1 n1 b2 n2 then
        return some s!"code blocks {i} and {j} overlap"
  let dataArr := lib.data.toArray
  for i in [0:dataArr.size] do
    let d := dataArr[i]!
    let a := mpl.ρ d.sym
    let sz := d.bytes.length + d.zeroTail
    if (lookupBlockSym d.sym lib.blocks).isSome then
      return some s!"data symbol {d.sym} collides with code block symbol"
    if !(0 < d.align && a.toNat % d.align == 0) then
      return some s!"data symbol {d.sym} at {toHex64 a} not aligned to {d.align}"
    if !(a.toNat + sz ≤ 2 ^ 64) then
      return some s!"data symbol {d.sym} wraps 64-bit address space"
    for r in d.relocs do
      if !checkDataReloc lib mpl a d.bytes.length r then
        return some s!"data relocation in {d.sym} at {r.off} ({repr r.kind}) invalid or out of range"
    for bi in [0:blks.size] do
      if !checkRangesDisjoint (mpl.base bi).toNat blks[bi]!.code.length a.toNat sz then
        return some s!"data symbol {d.sym} overlaps code block {bi}"
    for j in [i+1:dataArr.size] do
      let d2 := dataArr[j]!
      let a2 := mpl.ρ d2.sym
      let sz2 := d2.bytes.length + d2.zeroTail
      if !checkRangesDisjoint a.toNat sz a2.toNat sz2 then
        return some s!"data symbols {d.sym} and {d2.sym} overlap"
  -- AArch64 Variant I reserves the first 16 bytes at TP for the TCB header (`tprel >= 16`).
  let tlsArr := tls.toArray
  for i in [0:tlsArr.size] do
    let d := tlsArr[i]!
    let a := mpl.ρ d.sym
    let sz := d.bytes.length + d.zeroTail
    if (lookupBlockSym d.sym lib.blocks).isSome then
      return some s!"TLS symbol {d.sym} collides with code block symbol"
    if !(0 < d.align && a.toNat % d.align == 0) then
      return some s!"TLS symbol {d.sym} at tprel {toHex64 a} not aligned to {d.align}"
    if !(16 ≤ a.toNat) then
      return some s!"TLS symbol {d.sym} at tprel {toHex64 a} overlaps 16-byte AArch64 TCB header"
    if !(a.toNat + sz ≤ 2 ^ 64) then
      return some s!"TLS symbol {d.sym} wraps 64-bit address space"
    for r in d.relocs do
      if !checkDataReloc lib mpl a d.bytes.length r then
        return some s!"TLS relocation in {d.sym} at {r.off} ({repr r.kind}) invalid or out of range"
    for j in [i+1:tlsArr.size] do
      let d2 := tlsArr[j]!
      let a2 := mpl.ρ d2.sym
      let sz2 := d2.bytes.length + d2.zeroTail
      if !checkRangesDisjoint a.toNat sz a2.toNat sz2 then
        return some s!"TLS symbols {d.sym} and {d2.sym} overlap"
  return none

def evalPlacedJson (root : Json) : Except String Json := do
  let name ← match root.getObjVal? "name" with
    | .ok (.str s) => pure s
    | _ => pure "placed_module"
  let blocksJson ← root.getObjVal? "blocks"
  let .arr blockArr := blocksJson | throw "'blocks' must be an array"
  let blocks ← blockArr.toList.mapM parseCodeBlock
  let data ← match root.getObjVal? "data" with
    | .ok .null | .error _ => pure []
    | .ok (.arr arr) => arr.toList.mapM (parseSymDataInfo true)
    | .ok _ => throw "'data' must be an array"
  let tls ← match root.getObjVal? "tls" with
    | .ok .null | .error _ => pure []
    | .ok (.arr arr) => arr.toList.mapM (parseSymDataInfo false)
    | .ok _ => throw "'tls' must be an array"
  let exports ← match root.getObjVal? "exports" with
    | .ok .null | .error _ => pure []
    | .ok (.arr arr) => arr.toList.mapM Json.getStr?
    | .ok _ => throw "'exports' must be an array"
  let plJson ← root.getObjVal? "placement"
  let basesJson ← match plJson.getObjVal? "code_addrs" with
    | .ok v => pure v
    | .error _ => plJson.getObjVal? "bases"
  let .arr basesArr := basesJson | throw "'code_addrs'/'bases' must be an array"
  let bases ← basesArr.toList.mapM parseU64Val
  let rhoPairs ← parseAddrPairs plJson "rho"
  let dataPairs ← parseAddrPairs plJson "data_addrs"
  let tlsPairs ← parseAddrPairs plJson "tls_addrs"
  let allPairs := rhoPairs ++ dataPairs ++ tlsPairs
  let relaxLists ← parsePerBlockOffsets plJson "relax"
  let b2bLists ← parsePerBlockOffsets plJson "b2b"
  let undefWeak ← match plJson.getObjVal? "undef_weak" with
    | .ok .null | .error _ => pure []
    | .ok (.arr arr) => arr.toList.mapM Json.getStr?
    | .ok _ => throw "'undef_weak' must be an array"

  let lib : MultiPlacedLib := { name, blocks, data, exports }
  let mpl : MultiPlacement :=
    { base := fun i => bases.getD i 0#64
      ρ := fun s => (lookup s allPairs).getD 0#64
      relax := fun i off => (relaxLists.getD i []).contains off
      b2b := fun i off => (b2bLists.getD i []).contains off
      undefWeak := fun s => undefWeak.contains s }

  match checkValidPlacement lib tls mpl with
  | some errMsg =>
    return Json.mkObj [
      ("valid", Json.bool false),
      ("error", Json.str errMsg),
      ("code", Json.arr #[]),
      ("data", Json.arr #[]),
      ("tls", Json.arr #[])
    ]
  | none =>
    let mut codeOut : Array Json := #[]
    let mut i : Nat := 0
    for blk in lib.blocks do
      let bpl := lib.blockPlacement mpl i
      let patchedBytes := blk.patched bpl
      let nWords := blk.code.length / 4
      let words : Array Json := (List.range nWords).toArray.map fun j =>
        Json.str (toHex32 (blk.patchedWord bpl (4 * j)))
      codeOut := codeOut.push (Json.mkObj [
        ("index", Json.num i),
        ("base", Json.str (toHex64 (mpl.base i))),
        ("bytes_hex", Json.str (bytesToHex patchedBytes)),
        ("words", Json.arr words)
      ])
      i := i + 1
    let dataOut : Array Json := lib.data.toArray.map fun d =>
      let patched := lib.patchedData mpl d
      Json.mkObj [
        ("sym", Json.str d.sym),
        ("addr", Json.str (toHex64 (mpl.ρ d.sym))),
        ("bytes_hex", Json.str (bytesToHex patched))
      ]
    let tlsOut : Array Json := tls.toArray.map fun d =>
      let patched := lib.patchedData mpl d
      Json.mkObj [
        ("sym", Json.str d.sym),
        ("tprel", Json.str (toHex64 (mpl.ρ d.sym))),
        ("bytes_hex", Json.str (bytesToHex patched))
      ]
    return Json.mkObj [
      ("valid", Json.bool true),
      ("code", Json.arr codeOut),
      ("data", Json.arr dataOut),
      ("tls", Json.arr tlsOut)
    ]

end Arm64.Testing.Harness.PlacedEval

open Arm64.Testing.Harness.PlacedEval

def main (args : List String) : IO UInt32 := do
  let input ← match args with
    | [] | ["-"] =>
      let stdin ← IO.getStdin
      stdin.readToEnd
    | [path] =>
      IO.FS.readFile path
    | _ =>
      IO.eprintln "Usage: placed_eval [<json-path> | -]"
      return 2
  let json ← match Json.parse input with
    | .ok j => pure j
    | .error e =>
      IO.eprintln s!"placed_eval JSON parse error: {e}"
      return 2
  match evalPlacedJson json with
  | .ok out =>
    IO.println out.compress
    return 0
  | .error e =>
    IO.eprintln s!"placed_eval error: {e}"
    return 2
