/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import ProofLib.Process.Core

/-!
# Fast ELF64 Parser

CPS-forced ELF64 `ET_EXEC` parser (`fastParse`) and loader check (`ElfImage.fastWellFormed`,
`ElfImage.fastLoadState`) for fast kernel reduction, together with equivalence theorems
(`fastParse_eq_parse`, `ElfImage.parse_of_fastParse`, `ElfImage.loadState_eq_rawState_fast`).
-/

@[expose] public section

namespace Arm64.Process

open ProofLib

/-- Compute `bs.length` using `Nat.succ` directly so kernel reduction avoids unfolding
    `HAdd.hAdd` / `Add.add` on every byte. -/
def fastLen : List (BitVec 8) → Nat
  | [] => 0
  | _ :: bs => Nat.succ (fastLen bs)

@[simp] theorem fastLen_eq_length (bs : List (BitVec 8)) : fastLen bs = bs.length := by
  induction bs with
  | nil => rfl
  | cons _ _ ih => simp [fastLen, ih]

/-- Force `bs` to WHNF (`[]` or `b :: rest`) before passing it to `k`, so the kernel reduces
    a slice once instead of duplicating an unevaluated thunk across uses of `k`'s parameter. -/
def withForcedList {α : Type} (bs : List (BitVec 8)) (k : List (BitVec 8) → α) : α :=
  match bs with
  | [] => k []
  | b :: rest => k (b :: rest)

@[simp] theorem withForcedList_eq {α : Type} (bs : List (BitVec 8)) (k : List (BitVec 8) → α) :
    withForcedList bs k = k bs := by
  cases bs <;> rfl

/-- Force `n` to WHNF (`0` or `k + 1`) before passing it to `f`, so the kernel evaluates
    `n` once instead of duplicating an unevaluated `Nat` thunk across uses of `f`'s parameter. -/
def withForcedNat {α : Type} (n : Nat) (f : Nat → α) : α :=
  match n with
  | 0 => f 0
  | k + 1 => f (k + 1)

@[simp] theorem withForcedNat_eq {α : Type} (n : Nat) (f : Nat → α) :
    withForcedNat n f = f n := by
  cases n <;> rfl

def drop8 (bs : List (BitVec 8)) : List (BitVec 8) :=
  List.casesOn bs [] fun _ bs1 =>
  List.casesOn bs1 [] fun _ bs2 =>
  List.casesOn bs2 [] fun _ bs3 =>
  List.casesOn bs3 [] fun _ bs4 =>
  List.casesOn bs4 [] fun _ bs5 =>
  List.casesOn bs5 [] fun _ bs6 =>
  List.casesOn bs6 [] fun _ bs7 =>
  List.casesOn bs7 [] fun _ bs8 => bs8

@[simp] theorem drop8_eq_drop (bs : List (BitVec 8)) : drop8 bs = bs.drop 8 := by
  rcases bs with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩ <;> rfl

def drop24 (bs : List (BitVec 8)) : List (BitVec 8) :=
  drop8 (drop8 (drop8 bs))

@[simp] theorem drop24_eq_drop (bs : List (BitVec 8)) : drop24 bs = bs.drop 24 := by
  simp [drop24, List.drop_drop]

def drop56 (bs : List (BitVec 8)) : List (BitVec 8) :=
  drop8 (drop8 (drop8 (drop8 (drop8 (drop8 (drop8 bs))))))

@[simp] theorem drop56_eq_drop (bs : List (BitVec 8)) : drop56 bs = bs.drop 56 := by
  simp [drop56, List.drop_drop]

def drop64 (bs : List (BitVec 8)) : List (BitVec 8) :=
  drop8 (drop56 bs)

@[simp] theorem drop64_eq_drop (bs : List (BitVec 8)) : drop64 bs = bs.drop 64 := by
  simp [drop64, List.drop_drop]

def drop512 (bs : List (BitVec 8)) : List (BitVec 8) :=
  drop64 (drop64 (drop64 (drop64 (drop64 (drop64 (drop64 (drop64 bs)))))))

@[simp] theorem drop512_eq_drop (bs : List (BitVec 8)) : drop512 bs = bs.drop 512 := by
  simp [drop512, List.drop_drop]

/-- Compute `bs.length` in 64-byte blocks up to `k` blocks, falling back to `fastLen`. -/
def fastLen64 : Nat → List (BitVec 8) → Nat
  | 0, bs => fastLen bs
  | k + 1, bs =>
    match drop64 bs with
    | [] => fastLen bs
    | b :: rest => 64 + fastLen64 k (b :: rest)

@[simp] theorem fastLen64_eq_length : ∀ (k : Nat) (bs : List (BitVec 8)),
    fastLen64 k bs = bs.length
  | 0, bs => fastLen_eq_length bs
  | k + 1, bs => by
    unfold fastLen64
    split
    · exact fastLen_eq_length bs
    · rename_i b rest hdrop
      rw [fastLen64_eq_length k (b :: rest)]
      have hlen : (bs.drop 64).length = (b :: rest).length := by
        rw [← drop64_eq_drop, hdrop]
      have hpos : (b :: rest).length > 0 := Nat.succ_pos _
      rw [List.length_drop] at hlen
      omega

/-- Compute `bs.length` in 512-byte blocks up to `k` blocks, then 64-byte blocks. -/
def fastLen512 : Nat → List (BitVec 8) → Nat
  | 0, bs => fastLen64 8 bs
  | k + 1, bs =>
    match drop512 bs with
    | [] => fastLen64 8 bs
    | b :: rest => 512 + fastLen512 k (b :: rest)

@[simp] theorem fastLen512_eq_length : ∀ (k : Nat) (bs : List (BitVec 8)),
    fastLen512 k bs = bs.length
  | 0, bs => fastLen64_eq_length 8 bs
  | k + 1, bs => by
    unfold fastLen512
    split
    · exact fastLen64_eq_length 8 bs
    · rename_i b rest hdrop
      rw [fastLen512_eq_length k (b :: rest)]
      have hlen : (bs.drop 512).length = (b :: rest).length := by
        rw [← drop512_eq_drop, hdrop]
      have hpos : (b :: rest).length > 0 := Nat.succ_pos _
      rw [List.length_drop] at hlen
      omega

/-- Drop `q` 64-byte blocks from `bs`, forcing each 64-byte step to WHNF. -/
def drop64Blocks : Nat → List (BitVec 8) → List (BitVec 8)
  | 0, bs => bs
  | q + 1, bs => withForcedList (drop64 bs) (drop64Blocks q)

@[simp] theorem drop64Blocks_eq_drop (q : Nat) (bs : List (BitVec 8)) :
    drop64Blocks q bs = bs.drop (q * 64) := by
  induction q generalizing bs with
  | zero => simp [drop64Blocks]
  | succ q ih =>
    simp [drop64Blocks, ih, List.drop_drop, Nat.add_mul, Nat.add_comm]

/-- Drop `q` 512-byte blocks from `bs`, forcing each 512-byte step to WHNF. -/
def drop512Blocks : Nat → List (BitVec 8) → List (BitVec 8)
  | 0, bs => bs
  | q + 1, bs => withForcedList (drop512 bs) (drop512Blocks q)

@[simp] theorem drop512Blocks_eq_drop (q : Nat) (bs : List (BitVec 8)) :
    drop512Blocks q bs = bs.drop (q * 512) := by
  induction q generalizing bs with
  | zero => simp [drop512Blocks]
  | succ q ih =>
    simp [drop512Blocks, ih, List.drop_drop, Nat.add_mul, Nat.add_comm]

/-- Drop `n` bytes from `bs` in 512-byte blocks, 64-byte blocks, and `n % 64` tail bytes. -/
def fastDrop (n : Nat) (bs : List (BitVec 8)) : List (BitVec 8) :=
  (drop64Blocks ((n % 512) / 64) (drop512Blocks (n / 512) bs)).drop (n % 64)

@[simp] theorem fastDrop_eq_drop (n : Nat) (bs : List (BitVec 8)) :
    fastDrop n bs = bs.drop n := by
  simp only [fastDrop, drop64Blocks_eq_drop, drop512Blocks_eq_drop, List.drop_drop]
  congr 1
  omega

/-- Take `q` 8-byte blocks from `bs` using direct `List.casesOn`. -/
def take8Blocks : Nat → List (BitVec 8) → List (BitVec 8)
  | 0, _ => []
  | q + 1, bs =>
    List.casesOn bs [] fun b0 bs1 =>
    List.casesOn bs1 [b0] fun b1 bs2 =>
    List.casesOn bs2 [b0, b1] fun b2 bs3 =>
    List.casesOn bs3 [b0, b1, b2] fun b3 bs4 =>
    List.casesOn bs4 [b0, b1, b2, b3] fun b4 bs5 =>
    List.casesOn bs5 [b0, b1, b2, b3, b4] fun b5 bs6 =>
    List.casesOn bs6 [b0, b1, b2, b3, b4, b5] fun b6 bs7 =>
    List.casesOn bs7 [b0, b1, b2, b3, b4, b5, b6] fun b7 bs8 =>
    b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: take8Blocks q bs8

@[simp] theorem take8Blocks_eq_take (q : Nat) (bs : List (BitVec 8)) :
    take8Blocks q bs = bs.take (q * 8) := by
  induction q generalizing bs with
  | zero => simp [take8Blocks]
  | succ q ih =>
    have hmul : (q + 1) * 8 = q * 8 + 8 := by omega
    rw [hmul]
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, bs8⟩⟩⟩⟩⟩⟩⟩⟩ <;>
      simp [take8Blocks, ih]

/-- Take `n` bytes from `bs` in 8-byte blocks followed by `n % 8` tail bytes. -/
def fastTake (n : Nat) (bs : List (BitVec 8)) : List (BitVec 8) :=
  let q := n / 8
  let r := n % 8
  if r == 0 then
    take8Blocks q bs
  else
    take8Blocks q bs ++ (fastDrop (q * 8) bs).take r

@[simp] theorem fastTake_eq_take (n : Nat) (bs : List (BitVec 8)) :
    fastTake n bs = bs.take n := by
  simp only [fastTake, take8Blocks_eq_take, fastDrop_eq_drop]
  split
  · rename_i hr
    have h : (n / 8) * 8 = n := by
      have := beq_iff_eq.mp hr
      omega
    rw [h]
  · rw [← List.take_add]
    congr 1
    omega

/-- Compute `bs.length` by jumping to `hint` via `fastDrop` and counting the remaining tail. -/
def fastFileSize (bs : List (BitVec 8)) (hint : Nat) : Nat :=
  match fastDrop hint bs with
  | [] => fastLen512 4096 bs
  | _ :: rest => hint + Nat.succ (fastLen512 4096 rest)

@[simp] theorem fastFileSize_eq_length (bs : List (BitVec 8)) (hint : Nat) :
    fastFileSize bs hint = bs.length := by
  unfold fastFileSize
  rw [fastDrop_eq_drop]
  split
  · exact fastLen512_eq_length 4096 bs
  · rename_i b rest hdrop
    rw [fastLen512_eq_length 4096 rest]
    have hlen : (bs.drop hint).length = rest.length + 1 := by
      rw [hdrop]; rfl
    rw [List.length_drop] at hlen
    omega

/-- Map each region `r` to `(r, r.bytes.length)` forcing `fastLen512 4096 r.bytes` once. -/
def mapRegionsWithLen : List Snapshot.Region → List (Snapshot.Region × Nat)
  | [] => []
  | r :: rs =>
    withForcedNat (fastLen512 4096 r.bytes) fun len =>
      (r, len) :: mapRegionsWithLen rs

@[simp] theorem mapRegionsWithLen_eq :
    ∀ (rs : List Snapshot.Region),
      mapRegionsWithLen rs = rs.map (fun r => (r, r.bytes.length))
  | [] => rfl
  | r :: rs => by
    simp [mapRegionsWithLen, mapRegionsWithLen_eq rs]

def regionAlignedValidWithLen (r : Snapshot.Region) (len : Nat) : Bool :=
  r.start.toNat ≥ Obj.pageSize &&
  r.start.toNat % Obj.pageSize == 0 &&
  len > 0 &&
  len % Obj.pageSize == 0 &&
  r.start.toNat + len ≤ 2 ^ 48 &&
  !(r.perm.w && r.perm.x) &&
  (r.perm.r || r.perm.w || r.perm.x)

@[simp] theorem regionAlignedValidWithLen_eq (r : Snapshot.Region) :
    regionAlignedValidWithLen r r.bytes.length = regionAlignedValid r := rfl

def fastRegionsDisjointAndAligned : List (Snapshot.Region × Nat) → Bool
  | [] => true
  | [(r, len)] => regionAlignedValidWithLen r len
  | (r1, len1) :: (r2, len2) :: rest =>
    regionAlignedValidWithLen r1 len1 &&
    r1.start.toNat + len1 ≤ r2.start.toNat &&
    fastRegionsDisjointAndAligned ((r2, len2) :: rest)

@[simp] theorem fastRegionsDisjointAndAligned_eq :
    ∀ (rs : List Snapshot.Region),
      fastRegionsDisjointAndAligned (rs.map (fun r => (r, r.bytes.length))) =
        regionsDisjointAndAligned rs
  | [] => rfl
  | [r] => rfl
  | r1 :: r2 :: rest => by
    have ih := fastRegionsDisjointAndAligned_eq (r2 :: rest)
    simp only [List.map] at ih ⊢
    simp [fastRegionsDisjointAndAligned, regionsDisjointAndAligned, ih]

def fastEntryInExecRegion (entry : BitVec 64) (regions : List (Snapshot.Region × Nat)) : Bool :=
  entry.toNat % 4 == 0 &&
  regions.any fun (r, len) =>
    r.perm.x &&
    r.start.toNat ≤ entry.toNat &&
    entry.toNat + 4 ≤ r.start.toNat + len

@[simp] theorem fastEntryInExecRegion_eq (entry : BitVec 64) (regions : List Snapshot.Region) :
    fastEntryInExecRegion entry (regions.map (fun r => (r, r.bytes.length))) =
      entryInExecRegion entry regions := by
  simp [fastEntryInExecRegion, entryInExecRegion, List.any_map, Function.comp_def]

/-- Equivalent to `ElfImage.WellFormed`, computing each segment's byte length once. -/
def fastWellFormed (img : ElfImage) : Bool :=
  let regsWithLen := mapRegionsWithLen img.segments
  !img.segments.isEmpty &&
  img.phent == 56 &&
  fastRegionsDisjointAndAligned regsWithLen &&
  fastEntryInExecRegion img.entry regsWithLen &&
  img.brkStart.toNat % Obj.pageSize == 0 &&
  regsWithLen.all (fun (r, len) => r.start.toNat + len ≤ img.brkStart.toNat)

@[simp] theorem fastWellFormed_eq (img : ElfImage) :
    fastWellFormed img = img.WellFormed := by
  simp [fastWellFormed, ElfImage.WellFormed, List.all_map, Function.comp_def]

def fastParseProgramHeader (bytes : List (BitVec 8)) (fileSize : Nat) (ph : List (BitVec 8))
    (ePhoff ePhBytes : Nat) (accRegions : List Snapshot.Region) (accPhdrVaddr : BitVec 64)
    (accMaxEnd : Nat) : Except String (List Snapshot.Region × BitVec 64 × Nat) := do
  let pType   := listReadU32LE ph 0
  let pFlags  := listReadU32LE ph 4
  let pOffset := listReadU64LE ph 8
  let pVaddr  := listReadU64LE ph 16
  let pFilesz := listReadU64LE ph 32
  let pMemsz  := listReadU64LE ph 40
  if pType == 0 then
    pure (accRegions, accPhdrVaddr, accMaxEnd)
  else if pType == 2 then
    .error "ElfImage.parse: dynamic ELF (PT_DYNAMIC) is not supported"
  else if pType == 3 then
    .error "ElfImage.parse: dynamic interpreter (PT_INTERP) is not supported"
  else if pType == 6 then
    pure (accRegions, BitVec.ofNat 64 pVaddr, accMaxEnd)
  else if pType == 0x6474e551 then
    if (pFlags &&& 1) != 0 then
      .error "ElfImage.parse: executable stack (PT_GNU_STACK with PF_X) is not supported"
    else
      pure (accRegions, accPhdrVaddr, accMaxEnd)
  else if pType == 4 || pType == 7 || pType == 0x6474e550 || pType == 0x6474e552 ||
          pType == 0x6474e553 || pType == 0x70000002 then
    pure (accRegions, accPhdrVaddr, accMaxEnd)
  else if pType == 1 then
    if pMemsz == 0 then
      pure (accRegions, accPhdrVaddr, accMaxEnd)
    else
      if pOffset + pFilesz > fileSize then
        .error "ElfImage.parse: PT_LOAD segment exceeds file size"
      if pFilesz > pMemsz then
        .error "ElfImage.parse: PT_LOAD p_filesz exceeds p_memsz"
      if pVaddr < Obj.pageSize then
        .error "ElfImage.parse: PT_LOAD maps below first page (0x1000)"
      if pVaddr % Obj.pageSize != pOffset % Obj.pageSize then
        .error "ElfImage.parse: PT_LOAD p_vaddr and p_offset are not page-congruent"
      let perm : Perm :=
        { r := (pFlags &&& 4) != 0
          w := (pFlags &&& 2) != 0
          x := (pFlags &&& 1) != 0 }
      if perm.w && perm.x then
        .error "ElfImage.parse: W+X PT_LOAD segment is not supported"
      if !(perm.r || perm.w || perm.x) then
        .error "ElfImage.parse: PT_LOAD segment has no permissions"
      if pFilesz < pMemsz && !perm.w then
        .error "ElfImage.parse: non-writable PT_LOAD segment has p_filesz < p_memsz"
      let pageStart := pageAlignDown pVaddr
      let lead      := pVaddr - pageStart
      let pageEnd   := pageAlignUp (pVaddr + pMemsz)
      if pageEnd > 2 ^ 48 then
        .error "ElfImage.parse: PT_LOAD segment exceeds 48-bit user address space"
      let regionSize := pageEnd - pageStart
      let regBytes : List (BitVec 8) :=
        if pFilesz == pMemsz then
          let fileStart := pOffset - lead
          let avail     := Nat.min regionSize (fileSize - fileStart)
          let fileBytes := withForcedList (fastDrop fileStart bytes) (fastTake avail)
          let padLen    := regionSize - avail
          if padLen == 0 then fileBytes else fileBytes ++ List.replicate padLen 0#8
        else if pFilesz > 0 then
          let fileStart := pOffset - lead
          let fileLen   := (pOffset + pFilesz) - fileStart
          let fileBytes := withForcedList (fastDrop fileStart bytes) (fastTake fileLen)
          let tailLen   := pageEnd - (pVaddr + pFilesz)
          if tailLen == 0 then fileBytes else fileBytes ++ List.replicate tailLen 0#8
        else
          List.replicate regionSize 0#8
      let nonAnonLen := if pFilesz > 0 then pageAlignUp (pVaddr + pFilesz) - pageStart else 0
      let reg : Snapshot.Region :=
        { start      := BitVec.ofNat 64 pageStart
          perm       := perm
          bytes      := regBytes
          nonAnonLen := nonAnonLen }
      let fileMapStart := if pOffset ≥ lead && pFilesz > 0 then pOffset - lead else pOffset
      let fileMapEnd   := pOffset + pFilesz
      let phdrVaddr' :=
        if accPhdrVaddr != 0#64 then accPhdrVaddr
        else if fileMapStart ≤ ePhoff && ePhoff + ePhBytes ≤ fileMapEnd then
          BitVec.ofNat 64 (pageStart + (ePhoff - fileMapStart) +
            (if fileMapStart == pOffset then lead else 0))
        else 0#64
      pure (insertRegionSorted reg accRegions, phdrVaddr', Nat.max accMaxEnd pageEnd)
  else
    .error s!"ElfImage.parse: unsupported program header type {pType}"

@[simp] theorem fastParseProgramHeader_eq (bytes : List (BitVec 8)) (fileSize : Nat)
    (ph : List (BitVec 8)) (ePhoff ePhBytes : Nat) (accRegions : List Snapshot.Region)
    (accPhdrVaddr : BitVec 64) (accMaxEnd : Nat) :
    fastParseProgramHeader bytes fileSize ph ePhoff ePhBytes accRegions accPhdrVaddr accMaxEnd =
      parseProgramHeader bytes fileSize ph ePhoff ePhBytes accRegions accPhdrVaddr accMaxEnd := by
  simp only [fastParseProgramHeader, parseProgramHeader, withForcedList_eq, fastTake_eq_take,
    fastDrop_eq_drop]

def fastParseProgramHeaders (bytes : List (BitVec 8)) (fileSize ePhoff ePhBytes : Nat) :
    Nat → List (BitVec 8) → List Snapshot.Region → BitVec 64 → Nat →
    Except String (List Snapshot.Region × BitVec 64 × Nat)
  | 0, _, regs, phdr, mx => pure (regs, phdr, mx)
  | n + 1, phTable, regs, phdr, mx => do
    let (regs', phdr', mx') ←
      fastParseProgramHeader bytes fileSize phTable ePhoff ePhBytes regs phdr mx
    withForcedList (drop56 phTable) fun nextPhTable =>
      fastParseProgramHeaders bytes fileSize ePhoff ePhBytes n nextPhTable regs' phdr' mx'

@[simp] theorem fastParseProgramHeaders_eq (bytes : List (BitVec 8)) (fileSize ePhoff ePhBytes : Nat)
    (n : Nat) (phTable : List (BitVec 8)) (regs : List Snapshot.Region)
    (phdr : BitVec 64) (mx : Nat) :
    fastParseProgramHeaders bytes fileSize ePhoff ePhBytes n phTable regs phdr mx =
      parseProgramHeaders bytes fileSize ePhoff ePhBytes n phTable regs phdr mx := by
  induction n generalizing phTable regs phdr mx with
  | zero => rfl
  | succ n ih =>
    simp only [fastParseProgramHeaders, parseProgramHeaders, fastParseProgramHeader_eq,
      withForcedList_eq, drop56_eq_drop, ih]

def fastFindSymtabShdr : Nat → List (BitVec 8) → Option (Nat × Nat × Nat × Nat × Nat)
  | 0, _ => none
  | n + 1, sh =>
    if listReadU32LE sh 4 == 2 then
      some (listReadU64LE sh 24, listReadU64LE sh 32, listReadU32LE sh 40,
            listReadU32LE sh 44, listReadU64LE sh 56)
    else
      withForcedList (drop64 sh) (fastFindSymtabShdr n)

@[simp] theorem fastFindSymtabShdr_eq (n : Nat) (sh : List (BitVec 8)) :
    fastFindSymtabShdr n sh = findSymtabShdr n sh := by
  induction n generalizing sh with
  | zero => rfl
  | succ n ih =>
    simp only [fastFindSymtabShdr, findSymtabShdr, withForcedList_eq, drop64_eq_drop, ih]

/-- Binary search tree of pre-dropped `(offset, strtab.drop offset)` checkpoints. -/
inductive StrtabTree where
  | leaf (off : Nat) (tail : List (BitVec 8))
  | node (midOff : Nat) (left right : StrtabTree)

/-- Build a `StrtabTree` of depth `d` covering `[off, off + span)` from `tail = strtab.drop off`. -/
def buildStrtabTree : Nat → Nat → Nat → List (BitVec 8) → StrtabTree
  | 0, off, _, tail => .leaf off tail
  | d + 1, off, span, tail =>
    let half := span / 2
    let midOff := off + half
    withForcedList (fastDrop half tail) fun midTail =>
      .node midOff (buildStrtabTree d off half tail) (buildStrtabTree d midOff (span - half) midTail)

/-- Look up `stName` in a `StrtabTree`, returning `strtab.drop stName`. -/
def lookupStrtabTree (strtab : List (BitVec 8)) (stName : Nat) : StrtabTree → List (BitVec 8)
  | .leaf off tail =>
    if stName ≥ off then fastDrop (stName - off) tail else fastDrop stName strtab
  | .node midOff left right =>
    if stName < midOff then lookupStrtabTree strtab stName left
    else lookupStrtabTree strtab stName right

/-- Invariant that every leaf `(off, tail)` in a `StrtabTree` equals `strtab.drop off`. -/
def StrtabTree.Valid (strtab : List (BitVec 8)) : StrtabTree → Prop
  | .leaf off tail => tail = strtab.drop off
  | .node _ left right => Valid strtab left ∧ Valid strtab right

theorem buildStrtabTree_valid (strtab : List (BitVec 8)) :
    ∀ (d off span : Nat) (tail : List (BitVec 8)),
      tail = strtab.drop off → (buildStrtabTree d off span tail).Valid strtab
  | 0, off, _, tail, h => h
  | d + 1, off, span, tail, h => by
    simp only [buildStrtabTree, withForcedList_eq]
    refine ⟨buildStrtabTree_valid strtab d off (span / 2) tail h,
      buildStrtabTree_valid strtab d (off + span / 2) (span - span / 2) _ ?_⟩
    rw [fastDrop_eq_drop, h, List.drop_drop, Nat.add_comm]

theorem lookupStrtabTree_eq_drop (strtab : List (BitVec 8)) (stName : Nat) :
    ∀ (t : StrtabTree), t.Valid strtab → lookupStrtabTree strtab stName t = strtab.drop stName
  | .leaf off tail, h => by
    simp only [lookupStrtabTree, StrtabTree.Valid] at h ⊢
    subst h
    split <;> simp [List.drop_drop] <;> omega
  | .node midOff left right, ⟨hl, hr⟩ => by
    simp only [lookupStrtabTree]
    split
    · exact lookupStrtabTree_eq_drop strtab stName left hl
    · exact lookupStrtabTree_eq_drop strtab stName right hr

/-- Equivalent to `parseSymtabEntries`, using a `StrtabTree` of pre-dropped `.strtab`
    checkpoints so symbol lookups avoid re-dropping from offset `0`. -/
def fastParseSymtabEntries (strtab : List (BitVec 8)) (strSize : Nat) (tree : StrtabTree) :
    Nat → List (BitVec 8) → List (String × BitVec 64) →
    Except String (List (String × BitVec 64))
  | 0, _, acc => .ok acc.reverse
  | n + 1, sym, acc =>
    withForcedList (drop24 sym) fun nextSym =>
      if (listGetByte sym 4 &&& 0xf) == 2 && listReadU16LE sym 6 != 0 then
        let stName := listReadU32LE sym 0
        if stName == 0 then
          fastParseSymtabEntries strtab strSize tree n nextSym acc
        else if stName ≥ strSize then
          .error "ElfImage.parse: symbol st_name out of bounds in .strtab"
        else
          match readStrtabCString (strSize - stName) (lookupStrtabTree strtab stName tree) [] with
          | none => .error "ElfImage.parse: unterminated symbol name in .strtab"
          | some name =>
            let stValue := listReadU64LE sym 8
            fastParseSymtabEntries strtab strSize tree n nextSym
              ((name, BitVec.ofNat 64 stValue) :: acc)
      else
        fastParseSymtabEntries strtab strSize tree n nextSym acc

theorem fastParseSymtabEntries_eq_aux (strtab : List (BitVec 8)) (strSize : Nat)
    (tree : StrtabTree) (htree : tree.Valid strtab)
    (n : Nat) (sym : List (BitVec 8)) (acc : List (String × BitVec 64)) :
    fastParseSymtabEntries strtab strSize tree n sym acc =
      parseSymtabEntries strtab strSize n sym acc := by
  induction n generalizing sym acc with
  | zero => rfl
  | succ n ih =>
    simp only [fastParseSymtabEntries, parseSymtabEntries, withForcedList_eq, drop24_eq_drop,
      lookupStrtabTree_eq_drop strtab _ tree htree]
    split
    · split
      · exact ih (sym.drop 24) acc
      · split
        · rfl
        · cases readStrtabCString (strSize - listReadU32LE sym 0) (strtab.drop (listReadU32LE sym 0)) [] with
          | none => rfl
          | some name =>
            exact ih (sym.drop 24) _
    · exact ih (sym.drop 24) acc

@[simp] theorem fastParseSymtabEntries_eq (strtab : List (BitVec 8)) (strSize d : Nat)
    (n : Nat) (sym : List (BitVec 8)) (acc : List (String × BitVec 64)) :
    fastParseSymtabEntries strtab strSize (buildStrtabTree d 0 strSize strtab) n sym acc =
      parseSymtabEntries strtab strSize n sym acc :=
  fastParseSymtabEntries_eq_aux strtab strSize _
    (buildStrtabTree_valid strtab d 0 strSize strtab rfl) n sym acc

def fastParseSymtab (bytes : List (BitVec 8)) (fileSize eShoff eShentsize eShnum : Nat) :
    Except String (List (String × BitVec 64)) := do
  if eShnum == 0 then
    pure []
  else
    if eShentsize != 64 then
      .error s!"ElfImage.parse: expected e_shentsize=64, got {eShentsize}"
    let eShBytes := eShnum * 64
    if eShoff + eShBytes > fileSize then
      .error "ElfImage.parse: section header table exceeds file size"
    withForcedList (fastDrop eShoff bytes) fun shTable => do
      match fastFindSymtabShdr eShnum shTable with
      | none => pure []
      | some (shOffset, shSize, shLink, shInfo, shEntsize) =>
        if shEntsize != 24 then
          .error s!"ElfImage.parse: expected SHT_SYMTAB sh_entsize=24, got {shEntsize}"
        if shOffset + shSize > fileSize then
          .error "ElfImage.parse: SHT_SYMTAB section exceeds file size"
        if shSize % 24 != 0 then
          .error "ElfImage.parse: SHT_SYMTAB sh_size is not a multiple of 24"
        let totalEntries := shSize / 24
        if shInfo > totalEntries then
          .error "ElfImage.parse: SHT_SYMTAB sh_info exceeds symbol count"
        if shLink ≥ eShnum then
          .error "ElfImage.parse: SHT_SYMTAB sh_link out of bounds"
        let strSh     := drop64Blocks shLink shTable
        let strType   := listReadU32LE strSh 4
        let strOffset := listReadU64LE strSh 24
        let strSize   := listReadU64LE strSh 32
        if strType != 3 then
          .error "ElfImage.parse: SHT_SYMTAB sh_link is not SHT_STRTAB (3)"
        if strOffset + strSize > fileSize then
          .error "ElfImage.parse: SHT_STRTAB section exceeds file size"
        let symStart := shOffset + shInfo * 24
        withForcedList (fastDrop symStart bytes) fun symtab =>
          withForcedList (fastDrop strOffset bytes) fun strtab =>
            let tree := buildStrtabTree 6 0 strSize strtab
            fastParseSymtabEntries strtab strSize tree (totalEntries - shInfo) symtab []

@[simp] theorem fastParseSymtab_eq (bytes : List (BitVec 8)) (fileSize eShoff eShentsize eShnum : Nat) :
    fastParseSymtab bytes fileSize eShoff eShentsize eShnum =
      parseSymtab bytes fileSize eShoff eShentsize eShnum := by
  simp only [fastParseSymtab, parseSymtab, withForcedList_eq, fastDrop_eq_drop,
    fastFindSymtabShdr_eq, drop64Blocks_eq_drop, fastParseSymtabEntries_eq]
  cases findSymtabShdr eShnum (bytes.drop eShoff) <;> rfl

/-- Fast ELF64 `ET_EXEC` parser over `List (BitVec 8)`, equal to `ElfImage.parse`
    by `fastParse_eq_parse`. -/
def fastParse (bytes : List (BitVec 8)) : Except String ElfImage :=
  withForcedNat (fastFileSize bytes (listReadU64LE bytes 40)) fun fileSize => do
    if fileSize < 64 then
      .error "ElfImage.parse: file shorter than 64-byte ELF64 header"
    if listGetByte bytes 0 != 0x7f || listGetByte bytes 1 != 0x45 ||
       listGetByte bytes 2 != 0x4c || listGetByte bytes 3 != 0x46 then
      .error "ElfImage.parse: bad ELF magic"
    if listGetByte bytes 4 != 2 then
      .error "ElfImage.parse: expected ELFCLASS64 (2)"
    if listGetByte bytes 5 != 1 then
      .error "ElfImage.parse: expected ELFDATA2LSB (1, little-endian)"
    if listGetByte bytes 6 != 1 then
      .error "ElfImage.parse: expected EV_CURRENT (1)"
    let eType      := listReadU16LE bytes 16
    let eMachine   := listReadU16LE bytes 18
    let eEntry     := listReadU64LE bytes 24
    let ePhoff     := listReadU64LE bytes 32
    let eShoff     := listReadU64LE bytes 40
    let ePhentsize := listReadU16LE bytes 54
    let ePhnum     := listReadU16LE bytes 56
    let eShentsize := listReadU16LE bytes 58
    let eShnum     := listReadU16LE bytes 60
    if eType != 2 then
      .error s!"ElfImage.parse: expected static ET_EXEC (2), got e_type={eType}"
    if eMachine != 183 then
      .error s!"ElfImage.parse: expected EM_AARCH64 (183), got e_machine={eMachine}"
    if ePhentsize != 56 then
      .error s!"ElfImage.parse: expected e_phentsize=56, got {ePhentsize}"
    if ePhnum == 0 then
      .error "ElfImage.parse: e_phnum is 0"
    let ePhBytes := ePhnum * 56
    if ePhoff + ePhBytes > fileSize then
      .error "ElfImage.parse: program header table exceeds file size"
    let (regions, phdrVaddr, maxEnd) ←
      withForcedList (fastDrop ePhoff bytes) fun phTable =>
        fastParseProgramHeaders bytes fileSize ePhoff ePhBytes ePhnum phTable [] 0#64 0
    let symbols ← fastParseSymtab bytes fileSize eShoff eShentsize eShnum
    let img : ElfImage :=
      { entry     := BitVec.ofNat 64 eEntry
        phdrVaddr := phdrVaddr
        phent     := 56
        phnum     := ePhnum
        segments  := regions
        brkStart  := BitVec.ofNat 64 maxEnd
        symbols   := symbols }
    if !fastWellFormed img then
      .error "ElfImage.parse: resulting segment layout failed WellFormed check (overlapping segments or invalid entry)"
    pure img

/-- Equivalence between `fastParse` and `ElfImage.parse`. -/
theorem fastParse_eq_parse (bytes : List (BitVec 8)) :
    fastParse bytes = ElfImage.parse bytes := by
  simp only [fastParse, ElfImage.parse, withForcedNat_eq, fastFileSize_eq_length, withForcedList_eq,
    fastDrop_eq_drop, fastParseProgramHeaders_eq, fastParseSymtab_eq, fastWellFormed_eq]

/-- Derive `ElfImage.parse bytes = .ok img` from `fastParse bytes = .ok img`. -/
theorem ElfImage.parse_of_fastParse {bytes : List (BitVec 8)} {img : ElfImage}
    (h : fastParse bytes = .ok img) :
    ElfImage.parse bytes = .ok img :=
  (fastParse_eq_parse bytes).symm.trans h

/-- Equivalent to `img.loadState inputs` using `fastWellFormed` for fast kernel reduction. -/
def ElfImage.fastLoadState (img : ElfImage) (inputs : ProcessInputs := {}) : Except String State := do
  if !fastWellFormed img then
    .error "ElfImage.loadState: image is not WellFormed"
  if inputs.dirs.any (fun d => hasLeadingSlash d || hasDotDot d) then
    .error "ElfImage.loadState: inputs.dirs paths must be relative without '..'"
  if inputs.files.any (fun (p, bs) =>
      hasLeadingSlash p || hasDotDot p || !decide (bs.length ≤ MAX_LFS_FILESIZE)) then
    .error "ElfImage.loadState: inputs.files paths must be relative without '..' and size <= MAX_LFS_FILESIZE"
  let (sp, stackRegion) ← buildInitialStack img inputs
  let stackBase := BitVec.ofNat 64 (inputs.init.stackTop.toNat - inputs.init.stackSize)
  let baseMem : Memory := ⟨Snapshot.loadCellAt (img.segments ++ [stackRegion])⟩
  let mem := baseMem.mapZero stackBase inputs.init.stackSize
  let symtab : String → String → Option (BitVec 64) :=
    fun _ name => (img.symbols.find? (·.1 == name)).map (·.2)
  pure {
    regs      := RegFile.empty
    vregs     := VRegFile.empty
    sp        := sp
    pc        := img.entry
    pstate    := PState.zero
    mem       := mem
    tpidrEl0  := 0#64
    brkStart  := img.brkStart
    brk       := img.brkStart
    fs        := initFsState inputs
    oracle    := inputs.init.oracle
    oracleIdx := 0
    exclFails    := inputs.init.oracle.exclFails
    trace        := []
    status       := .Running
    symtab       := symtab
    physMemAvail := inputs.init.physMemAvail }

@[simp] theorem ElfImage.fastLoadState_eq (img : ElfImage) (inputs : ProcessInputs) :
    img.fastLoadState inputs = img.loadState inputs := by
  simp only [ElfImage.fastLoadState, ElfImage.loadState, fastWellFormed_eq]

/-- When `(img.fastLoadState inputs).toOption.isSome = true`, `img.loadState inputs` equals
    `.ok (img.rawState inputs)`. -/
theorem ElfImage.loadState_eq_rawState_fast {img : ElfImage} {inputs : ProcessInputs}
    (h : (img.fastLoadState inputs).toOption.isSome = true) :
    img.loadState inputs = .ok (img.rawState inputs) := by
  rw [ElfImage.fastLoadState_eq] at h
  exact ElfImage.loadState_eq_rawState h

end Arm64.Process
