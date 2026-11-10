/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Arm64.Trusted.ISA.State
public import Arm64.Trusted.ISA.Memory
public import Arm64.Trusted.Process.Loader
public import ProofLib.Invariant
public import LibsignalBinary.Specifications.LibsignalE2E.HooksCommon
public import LibsignalBinary.Specifications.SignalSession.CliRun
public import Symbolic.BugInjection.Proofs.CliExec.RadixMem

/-!
# Closure-Free File-System, Allocator, and String Helpers

Defines computable, closure-free counterparts and soundness lemmas for the noncomputable
operations used by CLI extern hooks. `FastFs` backs `Arm64.FsState` with association lists and
decides `fsView fs = filesOf expected` via `fastFsMatchesFilesOf`. `fastBumpAlloc` computes
`CryptoVerification.E2E.bumpAddr?` over sorted mapped heap intervals (`HeapIntervalsAgree`), while
`fastStrlenScan` and `fastCheckUtf8` compute `strlenHook` and `Utf8Ok`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.BugInjection.Proofs.CliExec.FastHooksAux

open Arm64 Arm64.Process ProofLib
open CryptoVerification.RustHeap
open CryptoVerification.E2E (heapBase heapSize HeapBlockFitsAt bumpAddr?)
open CryptoVerification.SignalSession (PathOk ancestors blockingAncestor? fsView filesOf
  stdioPaths Utf8Ok)
open Symbolic.BugInjection.Proofs.CliExec.RadixMemAux (sub_lt_iff_range)
open Symbolic.BugInjection.Proofs.CliExec.RadixMem

def assocLookup {α β : Type} [BEq α] (k : α) : List (α × β) → Option β
  | [] => none
  | (k', v) :: rest => if k == k' then some v else assocLookup k rest

def assocSet {α β : Type} [BEq α] (k : α) (v : β) : List (α × β) → List (α × β)
  | [] => [(k, v)]
  | (k', v') :: rest =>
    if k == k' then (k, v) :: rest
    else (k', v') :: assocSet k v rest

theorem assocLookup_assocSet {α β : Type} [BEq α] [LawfulBEq α]
    (k q : α) (v : β) (xs : List (α × β)) :
    assocLookup q (assocSet k v xs) = if q == k then some v else assocLookup q xs := by
  induction xs with
  | nil =>
    simp only [assocSet, assocLookup]
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    simp only [assocSet]
    by_cases hkk : (k == k') = true
    · have hk_eq : k = k' := eq_of_beq hkk
      subst hk_eq
      simp only [beq_self_eq_true, ↓reduceIte, assocLookup]
      cases (q == k) <;> rfl
    · simp only [Bool.not_eq_true] at hkk
      simp only [hkk, Bool.false_eq_true, ↓reduceIte, assocLookup, ih]
      by_cases hqk' : (q == k') = true
      · have hq_eq : q = k' := eq_of_beq hqk'
        subst hq_eq
        have hqk : (q == k) = false :=
          Bool.eq_false_iff.mpr fun h => by
            have h1 : q = k := eq_of_beq h
            subst h1
            simp at hkk
        simp [hqk]
      · simp only [Bool.not_eq_true] at hqk'
        simp [hqk']

theorem assocLookup_eq_none_of_not_mem {α β : Type} [BEq α] [LawfulBEq α]
    {q : α} {xs : List (α × β)} (h : q ∉ xs.map Prod.fst) :
    assocLookup q xs = none := by
  induction xs with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k', v'⟩
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have hqk' : (q == k') = false :=
      Bool.eq_false_iff.mpr fun hb => h.1 (eq_of_beq hb)
    simp only [assocLookup, hqk', Bool.false_eq_true, ↓reduceIte]
    exact ih h.2

/-- Structural `List.splitOn` exposed for kernel reduction. -/
def fastSplitOn {α : Type} [BEq α] (a : α) : List α → List (List α)
  | [] => [[]]
  | x :: xs =>
    if x == a then [] :: fastSplitOn a xs
    else
      match fastSplitOn a xs with
      | [] => []
      | h :: t => (x :: h) :: t

theorem fastSplitOn_eq {α : Type} [BEq α] (a : α) :
    ∀ xs : List α, fastSplitOn a xs = List.splitOn a xs
  | [] => (List.splitOn_nil a).symm
  | x :: xs => by
    simp only [fastSplitOn, List.splitOn_cons_eq_ite_modifyHead, fastSplitOn_eq a xs]
    cases List.splitOn a xs <;> rfl

def fastPathComps (p : String) : List (List Char) :=
  fastSplitOn '/' p.toList

theorem fastPathComps_eq (p : String) :
    fastPathComps p = CryptoVerification.SignalSession.pathComps p := by
  simp only [fastPathComps, CryptoVerification.SignalSession.pathComps, fastSplitOn_eq]

def fastPathOk (p : String) : Bool :=
  (fastPathComps p).all fun c =>
    !CryptoVerification.SignalSession.isUnmodelledPathComponent c &&
      !c.contains '\x00' && !(stdioPaths.contains (String.ofList c))

theorem fastPathOk_eq (p : String) : fastPathOk p = PathOk p := by
  simp only [fastPathOk, PathOk, fastPathComps_eq]

def fastAncestors (p : String) : List String :=
  let cs := fastPathComps p
  (List.range (cs.length - 1)).map fun i => String.ofList (['/'].intercalate (cs.take (i + 1)))

theorem fastAncestors_eq (p : String) : fastAncestors p = ancestors p := by
  simp only [fastAncestors, ancestors, fastPathComps_eq]

/-- Proof-term-free UTF-8 byte extraction from `String`. -/
@[inline] def strUtf8Bytes : String → List UInt8
  | ⟨⟨⟨bs⟩⟩, _⟩ => bs

/-- Pure `Bool` byte-list equality (avoids `Decidable` proof terms in kernel WHNF). -/
def listUInt8Eq : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | a :: as, b :: bs => Nat.beq a.toNat b.toNat && listUInt8Eq as bs
  | _, _ => false

/-- Pure `Bool` byte-list prefix test (avoids `Decidable` proof terms in kernel WHNF). -/
def listUInt8IsPrefix : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => Nat.beq a.toNat b.toNat && listUInt8IsPrefix as bs

/-- Fast `List.lookup` keyed on pre-extracted UTF-8 bytes `bs = strUtf8Bytes name`. -/
def lookupStrUtf8 {β : Type} (bs : List UInt8) : List (String × β) → Option β
  | [] => none
  | (k, v) :: rest => if listUInt8Eq bs (strUtf8Bytes k) then some v else lookupStrUtf8 bs rest

private theorem listUInt8Eq_iff : ∀ (xs ys : List UInt8), listUInt8Eq xs ys = true ↔ xs = ys
  | [], [] => by simp [listUInt8Eq]
  | [], _ :: _ => by simp [listUInt8Eq]
  | _ :: _, [] => by simp [listUInt8Eq]
  | a :: as, b :: bs => by
    simp only [listUInt8Eq, Bool.and_eq_true, Nat.beq_eq, UInt8.toNat_inj,
      listUInt8Eq_iff as bs, List.cons.injEq]

private theorem listUInt8IsPrefix_iff :
    ∀ (xs ys : List UInt8), listUInt8IsPrefix xs ys = true ↔ xs <+: ys
  | [], _ => by simp [listUInt8IsPrefix]
  | _ :: _, [] => by simp [listUInt8IsPrefix]
  | a :: as, b :: bs => by
    simp only [listUInt8IsPrefix, Bool.and_eq_true, Nat.beq_eq, UInt8.toNat_inj,
      listUInt8IsPrefix_iff as bs, List.cons_prefix_cons]

theorem listUInt8Eq_strUtf8Bytes (a b : String) :
    listUInt8Eq (strUtf8Bytes a) (strUtf8Bytes b) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  rw [listUInt8Eq_iff, beq_iff_eq]
  rcases a with ⟨⟨⟨as⟩⟩, ha⟩; rcases b with ⟨⟨⟨bs⟩⟩, hb⟩
  exact ⟨fun h => by simp only [strUtf8Bytes] at h; subst h; rfl, congrArg strUtf8Bytes⟩

theorem lookupStrUtf8_eq_lookup {β : Type} (name : String) (tbl : List (String × β)) :
    lookupStrUtf8 (strUtf8Bytes name) tbl = tbl.lookup name := by
  induction tbl with
  | nil => rfl
  | cons kv rest ih =>
    rcases kv with ⟨k, v⟩
    simp only [lookupStrUtf8, List.lookup, listUInt8Eq_strUtf8Bytes, ih]
    cases name == k <;> rfl

private theorem strUtf8Bytes_eq_flatMap (s : String) :
    strUtf8Bytes s = s.toList.flatMap String.utf8EncodeChar := by
  have h1 : s.toByteArray = (s.toList.flatMap String.utf8EncodeChar).toByteArray := by
    rw [← List.utf8Encode.eq_1, String.utf8Encode_toList]
  have h2 := congrArg (fun b : ByteArray => b.data.toList) h1
  rw [List.data_toByteArray] at h2
  rcases s with ⟨⟨⟨bs⟩⟩, _⟩
  exact h2

private theorem utf8EncodeChar_ascii_cons_iff {a c : Char} (ha : a.toNat ≤ 127)
    {rest tail : List UInt8} :
    String.utf8EncodeChar c ++ rest = UInt8.ofNat a.toNat :: tail ↔ c = a ∧ rest = tail := by
  constructor
  · intro h
    rw [String.utf8EncodeChar.eq_def] at h
    dsimp only [Char.toNat] at h ha
    split_ifs at h with h1 h2 h3
    · simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
      rcases h with ⟨hhd, rfl⟩
      have hnat := congrArg UInt8.toNat hhd
      simp only [UInt8.toNat_ofNat'] at hnat
      rcases c with ⟨⟨⟨cv, _⟩⟩, _⟩; rcases a with ⟨⟨⟨av, _⟩⟩, _⟩
      simp at ha h1 hnat
      have heq : cv = av := by omega
      subst heq; exact ⟨rfl, rfl⟩
    all_goals
      simp only [List.cons_append, List.cons.injEq] at h
      have hnat := congrArg UInt8.toNat h.1
      simp only [UInt8.toNat_ofNat'] at hnat
      omega
  · rintro ⟨rfl, rfl⟩
    rw [String.utf8EncodeChar.eq_def]
    simp [ha]

private theorem ascii_prefix_flatMap_iff :
    ∀ (ps cs : List Char), (∀ a ∈ ps, a.toNat ≤ 127) →
      (ps.flatMap String.utf8EncodeChar <+: cs.flatMap String.utf8EncodeChar ↔ ps <+: cs)
  | [], _, _ => by simp
  | a :: as, [], hps => by
    have ha : a.toNat ≤ 127 := hps a (.head _)
    simp [String.utf8EncodeChar.eq_def, ha]
  | a :: as, c :: cs, hps => by
    have ha : a.toNat ≤ 127 := hps a (.head _)
    have has : ∀ x ∈ as, x.toNat ≤ 127 := fun x hx => hps x (.tail _ hx)
    have ha_enc : String.utf8EncodeChar a = [UInt8.ofNat a.toNat] := by
      rw [String.utf8EncodeChar.eq_def]; simp [ha]
    simp only [List.flatMap_cons, ha_enc, List.singleton_append, List.cons_prefix_cons]
    constructor
    · rintro ⟨k, hk⟩
      have hsym := utf8EncodeChar_ascii_cons_iff ha |>.mp hk.symm
      exact ⟨hsym.1.symm, (ascii_prefix_flatMap_iff as cs has).mp ⟨k, hsym.2.symm⟩⟩
    · rintro ⟨rfl, hpre⟩
      rcases (ascii_prefix_flatMap_iff as cs has).mpr hpre with ⟨k, hk⟩
      exact ⟨k, by rw [ha_enc, List.singleton_append, List.cons_append, hk]⟩

private theorem any_strUtf8Bytes_eq_contains (name : String) :
    ∀ (xs : List String),
      (xs.map strUtf8Bytes).any (fun p => listUInt8Eq (strUtf8Bytes name) p) = xs.contains name
  | [] => rfl
  | k :: rest => by
    simp only [List.map_cons, List.any_cons, List.contains_cons, listUInt8Eq_strUtf8Bytes,
      any_strUtf8Bytes_eq_contains name rest]

def panicPrefixBs : List UInt8 := strUtf8Bytes "core::panicking::"

def panicExactNames : List String :=
  ["core::result::unwrap_failed",
   "core::option::unwrap_failed",
   "core::option::expect_failed",
   "core::slice::index::slice_start_index_len_fail",
   "core::slice::index::slice_end_index_len_fail",
   "core::slice::index::slice_index_order_fail",
   "core::slice::index::slice_index_fail",
   "alloc::raw_vec::handle_error",
   "alloc::raw_vec::capacity_overflow",
   "alloc::alloc::handle_alloc_error"]

def panicAllExactNamesBs : List (List UInt8) :=
  (panicExactNames ++ CryptoVerification.E2E.extraImagePanicNames).map strUtf8Bytes

/-- Checks `isImagePanicSymbol` on UTF-8 bytes without `String.startsWith` or `BEq String` proof terms. -/
def fastIsImagePanicSymbolBs (bs : List UInt8) : Bool :=
  listUInt8IsPrefix panicPrefixBs bs || panicAllExactNamesBs.any (fun p => listUInt8Eq bs p)

def fastIsImagePanicSymbol (name : String) : Bool :=
  fastIsImagePanicSymbolBs (strUtf8Bytes name)

theorem fastIsImagePanicSymbol_eq (name : String) :
    fastIsImagePanicSymbol name = CryptoVerification.E2E.isImagePanicSymbol name := by
  unfold fastIsImagePanicSymbol fastIsImagePanicSymbolBs panicAllExactNamesBs panicPrefixBs
    CryptoVerification.E2E.isImagePanicSymbol Rust.isPanicSymbol
  rw [any_strUtf8Bytes_eq_contains, List.contains_append, ← Bool.or_assoc]
  congr 2
  have hascii : ∀ a ∈ "core::panicking::".toList, a.toNat ≤ 127 := by decide
  apply Bool.eq_iff_iff.mpr
  rw [listUInt8IsPrefix_iff, strUtf8Bytes_eq_flatMap, strUtf8Bytes_eq_flatMap,
    ascii_prefix_flatMap_iff _ _ hascii, String.startsWith_string_iff]

/-- Closure-free file-system and file-descriptor state corresponding to `Arm64.FsState`. -/
structure FastFs where
  entries : List (FsPath × Option FsEntry) := []
  stdin   : List (BitVec 8) := []
  fds     : List (BitVec 64 × Option FdEntry) := []

@[inline] def withForcedFastFs {α : Type} (ffs : FastFs) (k : FastFs → α) : α :=
  match ffs with
  | ⟨es, si, fds⟩ =>
    withForcedListSpine es fun es' =>
    withForcedListSpine si fun si' =>
    withForcedListSpine fds fun fds' =>
      k ⟨es', si', fds'⟩

@[simp] theorem withForcedFastFs_eq {α : Type} (ffs : FastFs) (k : FastFs → α) :
    withForcedFastFs ffs k = k ffs := by
  rcases ffs with ⟨es, si, fds⟩
  simp [withForcedFastFs]

namespace FastFs

def getEntry (ffs : FastFs) (p : FsPath) : Option FsEntry :=
  if p.isEmpty then some .dir else (assocLookup p ffs.entries).join

def setEntry (ffs : FastFs) (p : FsPath) (e : Option FsEntry) : FastFs :=
  match ffs with
  | ⟨es, si, fds⟩ =>
    withForcedListSpine (assocSet p e es) fun es' => ⟨es', si, fds⟩

def files (ffs : FastFs) (path : String) : Option FsEntry :=
  ffs.getEntry (normalizePath path)

def setFile (ffs : FastFs) (path : String) (e : Option FsEntry) : FastFs :=
  ffs.setEntry (normalizePath path) e

def getFd (ffs : FastFs) (fd : BitVec 64) : Option FdEntry :=
  (assocLookup fd ffs.fds).join

def setFd (ffs : FastFs) (fd : BitVec 64) (e : Option FdEntry) : FastFs :=
  match ffs with
  | ⟨es, si, fds⟩ =>
    withForcedListSpine (assocSet fd e fds) fun fds' => ⟨es, si, fds'⟩

def blockingAncestor? (ffs : FastFs) (p : String) : Option (Option FsEntry) :=
  ((fastAncestors p).find? fun q => match ffs.files q with | some .dir => false | _ => true).map
    ffs.files

/-- Extensional agreement between `ffs : FastFs` and `fs : Arm64.FsState`. -/
def Agrees (ffs : FastFs) (fs : FsState) : Prop :=
  (∀ q : FsPath, q.isEmpty = false → (assocLookup q ffs.entries).join = fs.entries q) ∧
  ffs.stdin = fs.stdin ∧
  (∀ fd : BitVec 64, (assocLookup fd ffs.fds).join = fs.fds fd)

theorem empty_agrees : ({} : FastFs).Agrees ({} : FsState) := by
  refine ⟨fun q hq => ?_, rfl, fun _ => rfl⟩
  simp [assocLookup, hq]

theorem getEntry_eq {ffs : FastFs} {fs : FsState} (h : ffs.Agrees fs) (p : FsPath) :
    ffs.getEntry p = fs.getEntry p := by
  simp only [getEntry, FsState.getEntry]
  cases hp : p.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h.1 p hp
  · simp only [↓reduceIte]

theorem files_eq {ffs : FastFs} {fs : FsState} (h : ffs.Agrees fs) (path : String) :
    ffs.files path = fs.files path :=
  getEntry_eq h (normalizePath path)

theorem blockingAncestor?_eq {ffs : FastFs} {fs : FsState} (h : ffs.Agrees fs) (p : String) :
    ffs.blockingAncestor? p = CryptoVerification.SignalSession.blockingAncestor? fs p := by
  simp only [blockingAncestor?, CryptoVerification.SignalSession.blockingAncestor?,
    fastAncestors_eq]
  have hf : ffs.files = fs.files := funext (files_eq h)
  rw [hf]
  congr 1

theorem getFd_eq {ffs : FastFs} {fs : FsState} (h : ffs.Agrees fs) (fd : BitVec 64) :
    ffs.getFd fd = fs.fds fd :=
  h.2.2 fd

theorem setEntry_agrees {ffs : FastFs} {fs : FsState} (h : ffs.Agrees fs)
    (p : FsPath) (e : Option FsEntry) :
    (ffs.setEntry p e).Agrees (fs.setEntry p e) := by
  rcases ffs with ⟨es, si, fds⟩
  simp only [setEntry, withForcedListSpine_eq]
  refine ⟨fun q hq => ?_, h.2.1, h.2.2⟩
  simp only [FsState.setEntry, assocLookup_assocSet]
  cases hqp : (q == p)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h.1 q hq
  · simp only [↓reduceIte, Option.join_some]

theorem setFile_agrees {ffs : FastFs} {fs : FsState} (h : ffs.Agrees fs)
    (path : String) (e : Option FsEntry) :
    (ffs.setFile path e).Agrees (fs.setFile path e) :=
  setEntry_agrees h (normalizePath path) e

theorem setFd_agrees {ffs : FastFs} {fs : FsState} (h : ffs.Agrees fs)
    (fd : BitVec 64) (e : Option FdEntry) :
    (ffs.setFd fd e).Agrees (fs.setFd fd e) := by
  rcases ffs with ⟨es, si, fds⟩
  simp only [setFd, withForcedListSpine_eq]
  refine ⟨h.1, h.2.1, fun k => ?_⟩
  simp only [FsState.setFd, assocLookup_assocSet]
  cases hkf : (k == fd)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h.2.2 k
  · simp only [↓reduceIte, Option.join_some]

end FastFs

private theorem foldl_rel {α β γ : Type} (R : α → β → Prop)
    (f : α → γ → α) (g : β → γ → β)
    (hstep : ∀ a b x, R a b → R (f a x) (g b x)) :
    ∀ (xs : List γ) {a : α} {b : β}, R a b → R (xs.foldl f a) (xs.foldl g b)
  | [], _, _, h => h
  | x :: xs, _, _, h => foldl_rel R f g hstep xs (hstep _ _ x h)

/-- Closure-free counterpart of `Arm64.Process.initFsState`. -/
def initFastFs (inputs : ProcessInputs) : FastFs :=
  let withDirs := inputs.dirs.foldl
    (fun fs d => (FsPath.nonEmptyPrefixes (normalizePath d)).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs) ({} : FastFs)
  let withFiles := inputs.files.foldl
    (fun fs (p, bs) =>
      let withAnc := ((FsPath.nonEmptyPrefixes (normalizePath p)).dropLast).foldl
        (fun acc pref => acc.setEntry pref (some .dir)) fs
      withAnc.setFile p (some (.file bs))) withDirs
  let fs1 := withFiles.setFd 0#64 (some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio })
  let fs2 := fs1.setFd 1#64 (some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio })
  { (fs2.setFd 2#64 (some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio })) with
    stdin := inputs.stdin }

theorem initFastFs_agrees (inputs : ProcessInputs) :
    (initFastFs inputs).Agrees (initFsState inputs) := by
  unfold initFastFs initFsState
  dsimp only
  let stepDirF := fun (fs : FastFs) (d : String) =>
    (FsPath.nonEmptyPrefixes (normalizePath d)).foldl (fun acc pref => acc.setEntry pref (some .dir)) fs
  let stepDirS := fun (fs : FsState) (d : String) =>
    (FsPath.nonEmptyPrefixes (normalizePath d)).foldl (fun acc pref => acc.setEntry pref (some .dir)) fs
  have hdirs : FastFs.Agrees (inputs.dirs.foldl stepDirF {}) (inputs.dirs.foldl stepDirS {}) := by
    refine foldl_rel FastFs.Agrees stepDirF stepDirS (fun a b d hab => ?_) inputs.dirs FastFs.empty_agrees
    exact foldl_rel FastFs.Agrees _ _ (fun a' b' pref h' => FastFs.setEntry_agrees h' pref _)
      (FsPath.nonEmptyPrefixes (normalizePath d)) hab
  let stepFileF := fun (fs : FastFs) (pbs : String × List (BitVec 8)) =>
    (((FsPath.nonEmptyPrefixes (normalizePath pbs.1)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile pbs.1 (some (.file pbs.2))
  let stepFileS := fun (fs : FsState) (pbs : String × List (BitVec 8)) =>
    (((FsPath.nonEmptyPrefixes (normalizePath pbs.1)).dropLast).foldl
      (fun acc pref => acc.setEntry pref (some .dir)) fs).setFile pbs.1 (some (.file pbs.2))
  have hfiles : FastFs.Agrees
      (inputs.files.foldl stepFileF (inputs.dirs.foldl stepDirF {}))
      (inputs.files.foldl stepFileS (inputs.dirs.foldl stepDirS {})) := by
    refine foldl_rel FastFs.Agrees stepFileF stepFileS (fun a b pbs hab => ?_) inputs.files hdirs
    apply FastFs.setFile_agrees
    exact foldl_rel FastFs.Agrees _ _ (fun a' b' pref h' => FastFs.setEntry_agrees h' pref _)
      ((FsPath.nonEmptyPrefixes (normalizePath pbs.1)).dropLast) hab
  let fd0 : Option FdEntry :=
    some { path := "", accMode := .rdonly, append := false, offset := 0, kind := .stdio }
  let fd12 : Option FdEntry :=
    some { path := "", accMode := .wronly, append := true, offset := 0, kind := .stdio }
  have hfd2 := FastFs.setFd_agrees
    (FastFs.setFd_agrees (FastFs.setFd_agrees hfiles 0#64 fd0) 1#64 fd12) 2#64 fd12
  exact ⟨hfd2.1, rfl, hfd2.2.2⟩

/-- Regular-file contents at normalized path `q` (`none` on `stdioPaths` and directories). -/
def FastFs.fileBytesAt (ffs : FastFs) (q : FsPath) : Option (List (BitVec 8)) :=
  if (stdioPaths.map normalizePath).contains q then none
  else match ffs.getEntry q with
    | some (.file bs) => some bs
    | _ => none

private theorem fsView_eq_fileBytesAt {ffs : FastFs} {fs : FsState} (h : ffs.Agrees fs)
    (p : String) :
    fsView fs p = ffs.fileBytesAt (normalizePath p) := by
  simp only [fsView, FastFs.fileBytesAt, ← FastFs.files_eq h p, FastFs.files, List.contains_iff_mem]
  by_cases hm : normalizePath p ∈ stdioPaths.map normalizePath
  · simp [hm]
  · simp only [hm, ↓reduceIte]
    rcases ffs.getEntry (normalizePath p) with _ | ⟨_ | _⟩ <;> rfl

private theorem fileBytesAt_eq_none_of_not_mem {ffs : FastFs} {q : FsPath}
    (h : q ∉ ffs.entries.map Prod.fst) :
    ffs.fileBytesAt q = none := by
  simp only [FastFs.fileBytesAt]
  cases hc : (stdioPaths.map normalizePath).contains q
  · simp only [Bool.false_eq_true, ↓reduceIte, FastFs.getEntry]
    cases hq : q.isEmpty
    · simp only [Bool.false_eq_true, ↓reduceIte, assocLookup_eq_none_of_not_mem h, Option.join_none]
    · simp only [↓reduceIte]
  · simp only [↓reduceIte]

/-- Decides whether `ffs` has the same observable regular files as `filesOf expected`. -/
def fastFsMatchesFilesOf (ffs : FastFs) (expected : List (String × List (BitVec 8))) : Bool :=
  let ffsExp := initFastFs { files := expected }
  let keys := ffs.entries.map Prod.fst ++ ffsExp.entries.map Prod.fst
  keys.all fun q => ffs.fileBytesAt q == ffsExp.fileBytesAt q

theorem fastFsMatchesFilesOf_sound {ffs : FastFs} {fs : FsState}
    {expected : List (String × List (BitVec 8))}
    (hag : ffs.Agrees fs) (hm : fastFsMatchesFilesOf ffs expected = true) :
    fsView fs = filesOf expected := by
  funext p
  unfold filesOf
  have hexp := initFastFs_agrees { files := expected }
  rw [fsView_eq_fileBytesAt hag p, fsView_eq_fileBytesAt hexp p]
  set ffsExp := initFastFs { files := expected }
  set q := normalizePath p
  unfold fastFsMatchesFilesOf at hm
  simp only [List.all_eq_true] at hm
  by_cases hmem : q ∈ ffs.entries.map Prod.fst ++ ffsExp.entries.map Prod.fst
  · exact eq_of_beq (hm q hmem)
  · simp only [List.mem_append, not_or] at hmem
    rw [fileBytesAt_eq_none_of_not_mem hmem.1, fileBytesAt_eq_none_of_not_mem hmem.2]

/-- Sorted, non-empty, pairwise disjoint intervals `(lo, hi)` within `[bound, heapSize)`. -/
def HeapIvsWFFrom : Nat → List (Nat × Nat) → Prop
  | _, [] => True
  | bound, (lo, hi) :: rest => bound ≤ lo ∧ lo < hi ∧ hi ≤ heapSize ∧ HeapIvsWFFrom hi rest

def inHeapIvs (k : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | (lo, hi) :: rest => (decide (lo ≤ k) && decide (k < hi)) || inHeapIvs k rest

private theorem inHeapIvs_false_of_lt {k bound : Nat} {ivs : List (Nat × Nat)}
    (hwf : HeapIvsWFFrom bound ivs) (hlt : k < bound) :
    inHeapIvs k ivs = false := by
  induction ivs generalizing bound with
  | nil => rfl
  | cons iv rest ih =>
    rcases iv with ⟨lo, hi⟩
    rcases hwf with ⟨hblo, hlohi, _, hrest⟩
    have h1 : ¬ (lo ≤ k) := by omega
    simp [inHeapIvs, h1, ih hrest (by omega)]

/-- `ivs` tracks the exact mapped offsets of `m` in `[heapBase, heapBase + heapSize)`. -/
def HeapIntervalsAgree (ivs : List (Nat × Nat)) (m : Memory) : Prop :=
  HeapIvsWFFrom 0 ivs ∧
  ∀ k, k < heapSize → (m.perm (heapBase + BitVec.ofNat 64 k)).mapped = inHeapIvs k ivs

theorem HeapIntervalsAgree.of_perm_eq {ivs : List (Nat × Nat)} {m1 m2 : Memory}
    (h : HeapIntervalsAgree ivs m1) (hp : ∀ a, m2.perm a = m1.perm a) :
    HeapIntervalsAgree ivs m2 :=
  ⟨h.1, fun k hk => by rw [hp]; exact h.2 k hk⟩

theorem perm_write8_eq (m : Memory) (addr : BitVec 64) (val : BitVec 8) (a : BitVec 64) :
    (m.write8 addr val).perm a = m.perm a := by
  simp only [Memory.perm, Memory.write8]
  by_cases heq : a = addr
  · subst heq
    simp only [↓reduceIte, Memory.rawPerm]
    rcases m.cells a with _ | ⟨_ | p, _⟩ <;> rfl
  · simp only [heq, ↓reduceIte]

theorem perm_write16_eq (m : Memory) (addr : BitVec 64) (val : BitVec 16) (a : BitVec 64) :
    (m.write16 addr val).perm a = m.perm a := by
  simp only [Memory.write16, perm_write8_eq]

theorem perm_write32_eq (m : Memory) (addr : BitVec 64) (val : BitVec 32) (a : BitVec 64) :
    (m.write32 addr val).perm a = m.perm a := by
  simp only [Memory.write32, perm_write8_eq]

theorem perm_write64_eq (m : Memory) (addr : BitVec 64) (val : BitVec 64) (a : BitVec 64) :
    (m.write64 addr val).perm a = m.perm a := by
  simp only [Memory.write64, perm_write8_eq]

theorem perm_write128_eq (m : Memory) (addr : BitVec 64) (val : BitVec 128) (a : BitVec 64) :
    (m.write128 addr val).perm a = m.perm a := by
  simp only [Memory.write128, perm_write64_eq]

theorem perm_writeBytes_eq (m : Memory) (addr : BitVec 64) (bs : List (BitVec 8)) (a : BitVec 64) :
    (m.writeBytes addr bs).perm a = m.perm a := by
  induction bs generalizing m addr with
  | nil => rfl
  | cons b rest ih =>
    simp only [Memory.writeBytes]
    rw [ih, perm_write8_eq]

theorem heapBase_toNat : heapBase.toNat = 2 ^ 60 := by
  simp [heapBase]

theorem heapSize_eq : heapSize = 2 ^ 60 := rfl

theorem heapAddr_toNat {k : Nat} (hk : k ≤ heapSize) :
    (heapBase + BitVec.ofNat 64 k).toNat = 2 ^ 60 + k := by
  have hb : heapBase.toNat = 2 ^ 60 := heapBase_toNat
  have hs : heapSize = 2 ^ 60 := heapSize_eq
  rw [BitVec.toNat_add, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

/-- Smallest offset `k ≥ cur` such that `(2 ^ 60 + k) % align = 0`. -/
def alignOffsetFrom (cur align : Nat) : Nat :=
  let rem := (2 ^ 60 + cur) % align
  if rem == 0 then cur else cur + (align - rem)

private theorem alignOffsetFrom_le (cur align : Nat) :
    cur ≤ alignOffsetFrom cur align := by
  unfold alignOffsetFrom
  dsimp only
  split <;> omega

private theorem alignOffsetFrom_mod {cur align : Nat} (hpos : 0 < align) :
    (2 ^ 60 + alignOffsetFrom cur align) % align = 0 := by
  unfold alignOffsetFrom
  dsimp only
  set rem := (2 ^ 60 + cur) % align
  by_cases hrem : (rem == 0) = true
  · simp only [hrem, ↓reduceIte]
    exact eq_of_beq hrem
  · simp only [Bool.not_eq_true] at hrem
    simp only [hrem, Bool.false_eq_true, ↓reduceIte]
    have hlt : rem < align := Nat.mod_lt _ hpos
    have hdiv := Nat.div_add_mod (2 ^ 60 + cur) align
    have heq : 2 ^ 60 + (cur + (align - rem)) = align * ((2 ^ 60 + cur) / align + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    rw [heq, Nat.mul_mod_right]

private theorem alignOffsetFrom_min {cur align k : Nat} (hpos : 0 < align)
    (hcur : cur ≤ k) (hlt : k < alignOffsetFrom cur align) :
    (2 ^ 60 + k) % align ≠ 0 := by
  unfold alignOffsetFrom at hlt
  dsimp only at hlt
  set rem := (2 ^ 60 + cur) % align
  by_cases hrem : (rem == 0) = true
  · simp only [hrem, ↓reduceIte] at hlt
    omega
  · simp only [Bool.not_eq_true] at hrem
    simp only [hrem, Bool.false_eq_true, ↓reduceIte] at hlt
    have hr0 : rem ≠ 0 := fun h0 => by simp [h0] at hrem
    have hrlt : rem < align := Nat.mod_lt _ hpos
    have hdiv := Nat.div_add_mod (2 ^ 60 + cur) align
    have heq : 2 ^ 60 + k = (rem + (k - cur)) + align * ((2 ^ 60 + cur) / align) := by omega
    rw [heq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
    omega

/-- Scans sorted intervals from `cur` for the first `align`-aligned gap of `size` bytes,
and returns `(k, ivs')` with `(k, k + size)` inserted into `ivs'`. -/
def findAndInsertGapPos (cur size align : Nat) :
    List (Nat × Nat) → Option (Nat × List (Nat × Nat))
  | [] =>
    let k0 := alignOffsetFrom cur align
    if k0 + size ≤ heapSize then some (k0, [(k0, k0 + size)]) else none
  | (lo, hi) :: rest =>
    let k0 := alignOffsetFrom cur align
    if k0 + size ≤ lo then some (k0, (k0, k0 + size) :: (lo, hi) :: rest)
    else
      match findAndInsertGapPos hi size align rest with
      | some (k, rest') => some (k, (lo, hi) :: rest')
      | none => none

private theorem unmapped_of_inHeapIvs_false {cur : Nat} {ivs : List (Nat × Nat)} {m : Memory}
    (hmap : ∀ j, cur ≤ j → j < heapSize → (m.perm (heapBase + BitVec.ofNat 64 j)).mapped = inHeapIvs j ivs)
    {k size : Nat} (hcur_le : cur ≤ k) (hk_end : k + size ≤ heapSize)
    (hunm : ∀ j, k ≤ j → j < k + size → inHeapIvs j ivs = false) :
    Unmapped m (heapBase + BitVec.ofNat 64 k) size := by
  intro a ha
  unfold InRegion at ha
  have hp_nat : (heapBase + BitVec.ofNat 64 k).toNat = 2 ^ 60 + k := heapAddr_toNat (by omega)
  have hwrap : (heapBase + BitVec.ofNat 64 k).toNat + size ≤ 2 ^ 64 := by
    rw [hp_nat]; have := heapSize_eq; omega
  have hrng := (sub_lt_iff_range hwrap).mp ha
  rw [hp_nat] at hrng
  set j := a.toNat - 2 ^ 60
  have hj_lt : j < heapSize := by have := heapSize_eq; omega
  have ha_eq : a = heapBase + BitVec.ofNat 64 j := by
    apply BitVec.eq_of_toNat_eq
    rw [heapAddr_toNat (by omega)]
    omega
  rw [ha_eq, hmap j (by omega) hj_lt]
  exact hunm j (by omega) (by omega)

private theorem not_unmapped_of_inHeapIvs_true {cur : Nat} {ivs : List (Nat × Nat)} {m : Memory}
    (hmap : ∀ j, cur ≤ j → j < heapSize → (m.perm (heapBase + BitVec.ofNat 64 j)).mapped = inHeapIvs j ivs)
    {k size j : Nat} (hk_end : k + size ≤ heapSize) (hcur_j : cur ≤ j)
    (hkj : k ≤ j) (hj_end : j < k + size) (hin : inHeapIvs j ivs = true) :
    ¬ Unmapped m (heapBase + BitVec.ofNat 64 k) size := by
  intro hunm
  let a := heapBase + BitVec.ofNat 64 j
  have ha_in : InRegion (heapBase + BitVec.ofNat 64 k) size a := by
    unfold InRegion
    have hp_nat : (heapBase + BitVec.ofNat 64 k).toNat = 2 ^ 60 + k := heapAddr_toNat (by omega)
    have ha_nat : a.toNat = 2 ^ 60 + j := heapAddr_toNat (by omega)
    have hwrap : (heapBase + BitVec.ofNat 64 k).toNat + size ≤ 2 ^ 64 := by
      rw [hp_nat]; have := heapSize_eq; omega
    exact (sub_lt_iff_range hwrap).mpr (by omega)
  have hm_false := hunm a ha_in
  rw [hmap j hcur_j (by omega), hin] at hm_false
  nomatch hm_false

private theorem findAndInsertGapPos_none_sound {cur size align : Nat}
    {ivs : List (Nat × Nat)} {m : Memory}
    (hsize : 0 < size) (halign : 0 < align)
    (hwf : HeapIvsWFFrom cur ivs)
    (hmap : ∀ j, cur ≤ j → j < heapSize → (m.perm (heapBase + BitVec.ofNat 64 j)).mapped = inHeapIvs j ivs)
    (hnone : findAndInsertGapPos cur size align ivs = none) :
    ∀ k, cur ≤ k → ¬ HeapBlockFitsAt m size align k := by
  induction ivs generalizing cur with
  | nil =>
    simp only [findAndInsertGapPos] at hnone
    set k0 := alignOffsetFrom cur align
    by_cases hk0 : k0 + size ≤ heapSize
    · simp [hk0] at hnone
    · intro k hcur ⟨_, hmod, hkend, _⟩
      have hk_lt : k < k0 := by omega
      rw [heapAddr_toNat (by omega)] at hmod
      exact alignOffsetFrom_min halign hcur hk_lt hmod
  | cons iv rest ih =>
    rcases iv with ⟨lo, hi⟩
    rcases hwf with ⟨hcur_lo, hlo_hi, hhi_end, hwf_rest⟩
    simp only [findAndInsertGapPos] at hnone
    set k0 := alignOffsetFrom cur align
    by_cases hk0 : k0 + size ≤ lo
    · simp [hk0] at hnone
    · simp only [hk0, ↓reduceIte] at hnone
      cases hrec : findAndInsertGapPos hi size align rest with
      | some _ => rw [hrec] at hnone; nomatch hnone
      | none =>
        have hmap_rest : ∀ j, hi ≤ j → j < heapSize →
            (m.perm (heapBase + BitVec.ofNat 64 j)).mapped = inHeapIvs j rest := by
          intro j hhi_j hj_lt
          rw [hmap j (by omega) hj_lt]
          have hnot : ¬ (j < hi) := by omega
          simp [inHeapIvs, hnot]
        intro k hcur hfits
        rcases hfits with ⟨_, hmod, hkend, hunm⟩
        rw [heapAddr_toNat (by omega)] at hmod
        have hk_ge_k0 : k0 ≤ k := by
          by_contra hlt
          exact alignOffsetFrom_min halign hcur (by omega) hmod
        by_cases hk_lt_hi : k < hi
        · let j := max k lo
          have hj_in : inHeapIvs j ((lo, hi) :: rest) = true := by
            have h1 : lo ≤ j := Nat.le_max_right k lo
            have h2 : j < hi := by omega
            simp [inHeapIvs, h1, h2]
          exact not_unmapped_of_inHeapIvs_true hmap hkend (by omega) (Nat.le_max_left k lo) (by omega)
            hj_in hunm
        · exact ih hwf_rest hmap_rest hrec k (by omega)
            ⟨halign, by rw [heapAddr_toNat (by omega)]; exact hmod, hkend, hunm⟩

private theorem findAndInsertGapPos_some_sound {cur size align k : Nat}
    {ivs ivs' : List (Nat × Nat)} {m : Memory}
    (hsize : 0 < size) (halign : 0 < align)
    (hwf : HeapIvsWFFrom cur ivs)
    (hmap : ∀ j, cur ≤ j → j < heapSize → (m.perm (heapBase + BitVec.ofNat 64 j)).mapped = inHeapIvs j ivs)
    (hsome : findAndInsertGapPos cur size align ivs = some (k, ivs')) :
    cur ≤ k ∧ HeapBlockFitsAt m size align k ∧
    (∀ k', cur ≤ k' → k' < k → ¬ HeapBlockFitsAt m size align k') ∧
    HeapIvsWFFrom cur ivs' ∧
    (∀ j, inHeapIvs j ivs' = ((decide (k ≤ j) && decide (j < k + size)) || inHeapIvs j ivs)) := by
  induction ivs generalizing cur ivs' with
  | nil =>
    simp only [findAndInsertGapPos] at hsome
    set k0 := alignOffsetFrom cur align
    by_cases hk0 : k0 + size ≤ heapSize
    · simp only [hk0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hsome
      rcases hsome with ⟨rfl, rfl⟩
      have hcur_le : cur ≤ k0 := alignOffsetFrom_le cur align
      refine ⟨hcur_le, ?_, ?_, ?_, ?_⟩
      · refine ⟨halign, ?_, hk0, ?_⟩
        · rw [heapAddr_toNat (by omega)]; exact alignOffsetFrom_mod halign
        · exact unmapped_of_inHeapIvs_false hmap hcur_le hk0 (fun _ _ _ => rfl)
      · intro k' hcur' hlt ⟨_, hmod, hkend, _⟩
        rw [heapAddr_toNat (by omega)] at hmod
        exact alignOffsetFrom_min halign hcur' hlt hmod
      · exact ⟨hcur_le, by omega, hk0, trivial⟩
      · intro j; simp [inHeapIvs]
    · simp [hk0] at hsome
  | cons iv rest ih =>
    rcases iv with ⟨lo, hi⟩
    rcases hwf with ⟨hcur_lo, hlo_hi, hhi_end, hwf_rest⟩
    simp only [findAndInsertGapPos] at hsome
    set k0 := alignOffsetFrom cur align
    by_cases hk0 : k0 + size ≤ lo
    · simp only [hk0, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hsome
      rcases hsome with ⟨rfl, rfl⟩
      have hcur_le : cur ≤ k0 := alignOffsetFrom_le cur align
      refine ⟨hcur_le, ?_, ?_, ?_, ?_⟩
      · refine ⟨halign, ?_, by omega, ?_⟩
        · rw [heapAddr_toNat (by omega)]; exact alignOffsetFrom_mod halign
        · exact unmapped_of_inHeapIvs_false hmap hcur_le (by omega) fun j _ hj_lt =>
            inHeapIvs_false_of_lt ⟨Nat.le_refl lo, hlo_hi, hhi_end, hwf_rest⟩ (by omega)
      · intro k' hcur' hlt ⟨_, hmod, hkend, _⟩
        rw [heapAddr_toNat (by omega)] at hmod
        exact alignOffsetFrom_min halign hcur' hlt hmod
      · exact ⟨hcur_le, by omega, by omega, ⟨hk0, hlo_hi, hhi_end, hwf_rest⟩⟩
      · intro j; simp [inHeapIvs]
    · simp only [hk0, ↓reduceIte] at hsome
      cases hrec : findAndInsertGapPos hi size align rest with
      | none => rw [hrec] at hsome; nomatch hsome
      | some kr =>
        rw [hrec] at hsome
        rcases kr with ⟨k1, rest'⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        rcases hsome with ⟨rfl, rfl⟩
        have hmap_rest : ∀ j, hi ≤ j → j < heapSize →
            (m.perm (heapBase + BitVec.ofNat 64 j)).mapped = inHeapIvs j rest := by
          intro j hhi_j hj_lt
          rw [hmap j (by omega) hj_lt]
          have hnot : ¬ (j < hi) := by omega
          simp [inHeapIvs, hnot]
        obtain ⟨hhi_k, hfits_k, hmin_rest, hwf_rest', hin_rest'⟩ :=
          ih hwf_rest hmap_rest hrec
        refine ⟨by omega, hfits_k, ?_, ⟨hcur_lo, hlo_hi, hhi_end, hwf_rest'⟩, ?_⟩
        · intro k' hcur' hlt hfits'
          by_cases hk'_ge_hi : hi ≤ k'
          · exact hmin_rest k' hk'_ge_hi hlt hfits'
          · rcases hfits' with ⟨_, hmod', hkend', hunm'⟩
            rw [heapAddr_toNat (by omega)] at hmod'
            have hk'_ge_k0 : k0 ≤ k' := by
              by_contra hlt0
              exact alignOffsetFrom_min halign hcur' (by omega) hmod'
            let j := max k' lo
            have hj_in : inHeapIvs j ((lo, hi) :: rest) = true := by
              have h1 : lo ≤ j := Nat.le_max_right k' lo
              have h2 : j < hi := by omega
              simp [inHeapIvs, h1, h2]
            exact not_unmapped_of_inHeapIvs_true hmap hkend' (by omega) (Nat.le_max_left k' lo) (by omega)
              hj_in hunm'
        · intro j
          simp only [inHeapIvs, hin_rest' j, Bool.or_left_comm]

/-- Computes `bumpAddr?` over `ivs` and returns the allocated address with the updated interval list. -/
def fastBumpAlloc (ivs : List (Nat × Nat)) (size align : Nat) :
    Option (BitVec 64 × List (Nat × Nat)) :=
  if align == 0 then none
  else if size == 0 then
    let k0 := alignOffsetFrom 0 align
    if k0 ≤ heapSize then some (heapBase + BitVec.ofNat 64 k0, ivs) else none
  else
    match findAndInsertGapPos 0 size align ivs with
    | some (k, ivs') => some (heapBase + BitVec.ofNat 64 k, ivs')
    | none => none

open Classical in
theorem fastBumpAlloc_none_sound {ivs : List (Nat × Nat)} {m : Memory} {size align : Nat}
    (hag : HeapIntervalsAgree ivs m)
    (hnone : fastBumpAlloc ivs size align = none) :
    bumpAddr? m size align = none := by
  unfold fastBumpAlloc at hnone
  by_cases ha0 : align = 0
  · subst ha0
    simp only [bumpAddr?]
    rw [dite_eq_right_of_eq_false (eq_false fun ⟨_, h0, _, _⟩ => Nat.lt_irrefl 0 h0)]
  · have halign : 0 < align := Nat.pos_of_ne_zero ha0
    have ha_beq : (align == 0) = false := beq_eq_false_iff_ne.mpr ha0
    simp only [ha_beq, Bool.false_eq_true, ↓reduceIte] at hnone
    by_cases hs0 : size = 0
    · subst hs0
      simp only [beq_self_eq_true, ↓reduceIte] at hnone
      set k0 := alignOffsetFrom 0 align
      by_cases hk0 : k0 ≤ heapSize
      · simp [hk0] at hnone
      · simp only [bumpAddr?]
        refine dite_eq_right_of_eq_false (eq_false fun ⟨k, _, hmod, hkend, _⟩ => ?_)
        rw [heapAddr_toNat (by omega)] at hmod
        exact alignOffsetFrom_min halign (Nat.zero_le k) (by omega) hmod
    · have hsize : 0 < size := Nat.pos_of_ne_zero hs0
      have hs_beq : (size == 0) = false := beq_eq_false_iff_ne.mpr hs0
      simp only [hs_beq, Bool.false_eq_true, ↓reduceIte] at hnone
      cases hfind : findAndInsertGapPos 0 size align ivs with
      | some _ => rw [hfind] at hnone; nomatch hnone
      | none =>
        have hno := findAndInsertGapPos_none_sound hsize halign hag.1 (fun j _ hj => hag.2 j hj) hfind
        simp only [bumpAddr?]
        exact dite_eq_right_of_eq_false (eq_false fun ⟨k, hk⟩ => hno k (Nat.zero_le k) hk)

open Classical in
theorem fastBumpAlloc_some_sound {ivs ivs' : List (Nat × Nat)} {m : Memory}
    {size align : Nat} {p : BitVec 64}
    (hag : HeapIntervalsAgree ivs m)
    (hsome : fastBumpAlloc ivs size align = some (p, ivs')) :
    bumpAddr? m size align = some p ∧
    HeapIntervalsAgree ivs' (m.mapFresh p size Perm.rw) := by
  unfold fastBumpAlloc at hsome
  by_cases ha0 : align = 0
  · subst ha0; simp at hsome
  · have halign : 0 < align := Nat.pos_of_ne_zero ha0
    have ha_beq : (align == 0) = false := beq_eq_false_iff_ne.mpr ha0
    simp only [ha_beq, Bool.false_eq_true, ↓reduceIte] at hsome
    by_cases hs0 : size = 0
    · subst hs0
      simp only [beq_self_eq_true, ↓reduceIte] at hsome
      set k0 := alignOffsetFrom 0 align
      by_cases hk0 : k0 ≤ heapSize
      · simp only [hk0, ↓reduceIte] at hsome
        injection hsome with hsome
        injection hsome with hp hivs
        subst hp hivs
        have hfits0 : HeapBlockFitsAt m 0 align k0 := by
          refine ⟨halign, ?_, by omega, fun a ha => absurd ha (Nat.not_lt_zero _)⟩
          rw [heapAddr_toNat hk0]
          exact alignOffsetFrom_mod halign
        have hex : ∃ k, HeapBlockFitsAt m 0 align k := ⟨k0, hfits0⟩
        have hfind_eq : Nat.find hex = k0 := by
          rw [Nat.find_eq_iff]
          refine ⟨hfits0, fun k' hlt ⟨_, hmod', hkend', _⟩ => ?_⟩
          rw [heapAddr_toNat (by omega)] at hmod'
          exact alignOffsetFrom_min halign (Nat.zero_le k') hlt hmod'
        refine ⟨?_, ?_⟩
        · simp only [bumpAddr?, dite_eq_left_of_eq_true (eq_true hex), hfind_eq]
        · refine hag.of_perm_eq (fun a => ?_)
          simp [Memory.perm, Memory.mapFresh]
      · simp [hk0] at hsome
    · have hsize : 0 < size := Nat.pos_of_ne_zero hs0
      have hs_beq : (size == 0) = false := beq_eq_false_iff_ne.mpr hs0
      simp only [hs_beq, Bool.false_eq_true, ↓reduceIte] at hsome
      cases hfind : findAndInsertGapPos 0 size align ivs with
      | none => rw [hfind] at hsome; nomatch hsome
      | some ki =>
        rw [hfind] at hsome
        rcases ki with ⟨k, ivs1⟩
        simp only [Option.some.injEq, Prod.mk.injEq] at hsome
        rcases hsome with ⟨rfl, rfl⟩
        obtain ⟨_, hfits, hmin, hwf', hin'⟩ :=
          findAndInsertGapPos_some_sound hsize halign hag.1 (fun j _ hj => hag.2 j hj) hfind
        have hex : ∃ k', HeapBlockFitsAt m size align k' := ⟨k, hfits⟩
        have hfind_eq : Nat.find hex = k := by
          rw [Nat.find_eq_iff]
          exact ⟨hfits, fun k' hlt => hmin k' (Nat.zero_le k') hlt⟩
        refine ⟨?_, hwf', ?_⟩
        · simp only [bumpAddr?, dite_eq_left_of_eq_true (eq_true hex), hfind_eq]
        · intro j hj_lt
          rw [hin' j]
          have hkend : k + size ≤ heapSize := hfits.2.2.1
          have hp_nat : (heapBase + BitVec.ofNat 64 k).toNat = 2 ^ 60 + k :=
            heapAddr_toNat (by omega)
          have hj_nat : (heapBase + BitVec.ofNat 64 j).toNat = 2 ^ 60 + j :=
            heapAddr_toNat (by omega)
          have hwrap : (heapBase + BitVec.ofNat 64 k).toNat + size ≤ 2 ^ 64 := by
            rw [hp_nat]; have := heapSize_eq; omega
          have hrng_iff := sub_lt_iff_range hwrap (a := heapBase + BitVec.ofNat 64 j)
          rw [hp_nat, hj_nat] at hrng_iff
          by_cases hrng : k ≤ j ∧ j < k + size
          · have hlt_sub : ((heapBase + BitVec.ofNat 64 j) - (heapBase + BitVec.ofNat 64 k)).toNat < size :=
              hrng_iff.mpr (by omega)
            simp only [hrng.1, hrng.2, decide_true, Bool.true_and, Bool.true_or]
            simp only [Memory.perm, Memory.mapFresh, hlt_sub, decide_true, Bool.true_and]
            rcases m.cells (heapBase + BitVec.ofNat 64 j) with _ | ⟨_ | _, _⟩ <;> rfl
          · have hnot_sub : ¬ (((heapBase + BitVec.ofNat 64 j) - (heapBase + BitVec.ofNat 64 k)).toNat < size) :=
              fun hl => hrng (by have := hrng_iff.mp hl; omega)
            have hdec : (decide (k ≤ j) && decide (j < k + size)) = false := by
              by_cases h1 : k ≤ j
              · have h2 : ¬ (j < k + size) := fun h2 => hrng ⟨h1, h2⟩
                simp [h1, h2]
              · simp [h1]
            rw [hdec, Bool.false_or]
            simp only [Memory.perm, Memory.mapFresh, hnot_sub, decide_false, Bool.false_and,
              Bool.false_eq_true, ↓reduceIte]
            exact hag.2 j hj_lt

private theorem bv_add_one_add_ofNat (p : BitVec 64) (n : Nat) :
    (p + 1#64) + BitVec.ofNat 64 n = p + BitVec.ofNat 64 (n + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

private theorem allPerm_succ (m : Memory) (pred : Option Perm → Bool) :
    ∀ (n : Nat) (p : BitVec 64),
      m.allPerm pred p (n + 1) = (m.allPerm pred p n && pred (m.perm (p + BitVec.ofNat 64 n)))
  | 0, p => by simp [Memory.allPerm]
  | n + 1, p => by
    change (pred (m.perm p) && m.allPerm pred (p + 1#64) (n + 1)) =
      ((pred (m.perm p) && m.allPerm pred (p + 1#64) n) && pred (m.perm (p + BitVec.ofNat 64 (n + 1))))
    rw [allPerm_succ m pred n (p + 1#64), bv_add_one_add_ofNat, Bool.and_assoc]

private theorem allNoLazyFree_succ (m : Memory) :
    ∀ (n : Nat) (p : BitVec 64),
      m.allNoLazyFree p (n + 1) = (m.allNoLazyFree p n && !m.isLazyFree (p + BitVec.ofNat 64 n))
  | 0, p => by simp [Memory.allNoLazyFree]
  | n + 1, p => by
    change (!m.isLazyFree p && m.allNoLazyFree (p + 1#64) (n + 1)) =
      ((!m.isLazyFree p && m.allNoLazyFree (p + 1#64) n) && !m.isLazyFree (p + BitVec.ofNat 64 (n + 1)))
    rw [allNoLazyFree_succ m n (p + 1#64), bv_add_one_add_ofNat, Bool.and_assoc]

theorem canRead_succ (m : Memory) (p : BitVec 64) (n : Nat) :
    m.canRead p (n + 1) = (m.canRead p n && m.canRead (p + BitVec.ofNat 64 n) 1) := by
  unfold Memory.canRead
  rw [allPerm_succ, allNoLazyFree_succ]
  simp only [Memory.allPerm, Memory.allNoLazyFree, Bool.and_true]
  cases m.allPerm (·.r) p n <;> cases (m.perm (p + BitVec.ofNat 64 n)).r <;>
    cases m.allNoLazyFree p n <;> cases m.isLazyFree (p + BitVec.ofNat 64 n) <;> rfl

private theorem canRead_mono_le {m : Memory} {p : BitVec 64} {k n : Nat}
    (hle : k ≤ n) (hcr : m.canRead p n = true) :
    m.canRead p k = true := by
  induction n with
  | zero =>
    have hk0 : k = 0 := by omega
    subst hk0; exact hcr
  | succ n ih =>
    by_cases hkn : k = n + 1
    · subst hkn; exact hcr
    · rw [canRead_succ, Bool.and_eq_true] at hcr
      exact ih (by omega) hcr.1

/-- Fuel-bounded readable NUL scan from `p + off`:
- `some (some off')` at the first readable NUL byte `p + off'`;
- `some none` when an unreadable byte precedes any NUL byte;
- `none` when `fuel` is exhausted before a NUL or unreadable byte. -/
def fastStrlenScan (fm : FastMem) (p : BitVec 64) (off : Nat) : Nat → Option (Option Nat)
  | 0 => none
  | fuel + 1 =>
    let a := p + BitVec.ofNat 64 off
    if !fm.canRead a 1 then some none
    else if fm.read8 a == 0#8 then some (some off)
    else fastStrlenScan fm p (off + 1) fuel

def strlenFuel : Nat := 2 ^ 20

open Classical in
private def StrlenScanPost (m : Memory) (p : BitVec 64) : Option Nat → Prop
  | some len =>
    ∃ h : ∃ n, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8,
      Nat.find h = len
  | none =>
    ¬ ∃ n, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8

open Classical in
private theorem fastStrlenScan_sound_aux {fm : FastMem} {m : Memory} (hmem : fm.Agrees m)
    (p : BitVec 64) :
    ∀ (fuel off : Nat) (res : Option Nat),
      m.canRead p off = true →
      (∀ i < off, m.read8 (p + BitVec.ofNat 64 i) ≠ 0#8) →
      fastStrlenScan fm p off fuel = some res →
      StrlenScanPost m p res
  | 0, _, _, _, _, hscan => nomatch hscan
  | fuel + 1, off, res, hcr_off, hnonul, hscan => by
    simp only [fastStrlenScan] at hscan
    set a := p + BitVec.ofNat 64 off
    cases hcr1 : fm.canRead a 1
    · rw [hcr1] at hscan
      simp only [Bool.not_false, ↓reduceIte, Option.some.injEq] at hscan
      subst hscan
      dsimp only [StrlenScanPost]
      rintro ⟨n, hcr_n, hnul_n⟩
      by_cases hlt : n < off
      · exact hnonul n hlt hnul_n
      · have hcr_s : m.canRead p (off + 1) = true :=
          canRead_mono_le (by omega) hcr_n
        rw [canRead_succ, Bool.and_eq_true, ← FastMem.canRead_eq hmem a 1, hcr1] at hcr_s
        nomatch hcr_s.2
    · rw [hcr1] at hscan
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hscan
      have hm_cr1 : m.canRead a 1 = true := by rw [← FastMem.canRead_eq hmem a 1]; exact hcr1
      have hcr_succ : m.canRead p (off + 1) = true := by
        rw [canRead_succ]; exact Bool.and_eq_true_iff.mpr ⟨hcr_off, hm_cr1⟩
      cases hzero : (fm.read8 a == 0#8)
      · rw [hzero] at hscan
        simp only [Bool.false_eq_true, ↓reduceIte] at hscan
        have hne0 : m.read8 a ≠ 0#8 := by
          rw [← FastMem.read8_eq hmem a]
          intro hz; simp [hz] at hzero
        exact fastStrlenScan_sound_aux hmem p fuel (off + 1) res hcr_succ
          (fun i hi => by
            by_cases hieq : i = off
            · subst hieq; exact hne0
            · exact hnonul i (by omega))
          hscan
      · rw [hzero] at hscan
        simp only [↓reduceIte, Option.some.injEq] at hscan
        subst hscan
        dsimp only [StrlenScanPost]
        have heq0 : m.read8 a = 0#8 := by
          rw [← FastMem.read8_eq hmem a]; exact eq_of_beq hzero
        have hex : ∃ n, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8 :=
          ⟨off, hcr_succ, heq0⟩
        refine ⟨hex, ?_⟩
        rw [Nat.find_eq_iff]
        exact ⟨⟨hcr_succ, heq0⟩, fun i hi ⟨_, hi0⟩ => hnonul i hi hi0⟩

open Classical in
theorem fastStrlenScan_some_sound {fm : FastMem} {m : Memory} (hmem : fm.Agrees m)
    {p : BitVec 64} {len : Nat}
    (hscan : fastStrlenScan fm p 0 strlenFuel = some (some len)) :
    ∃ h : ∃ n, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8,
      Nat.find h = len :=
  fastStrlenScan_sound_aux hmem p strlenFuel 0 (some len) rfl
    (fun _ hi => absurd hi (Nat.not_lt_zero _)) hscan

open Classical in
theorem fastStrlenScan_none_sound {fm : FastMem} {m : Memory} (hmem : fm.Agrees m)
    {p : BitVec 64}
    (hscan : fastStrlenScan fm p 0 strlenFuel = some none) :
    ¬ ∃ n, m.canRead p (n + 1) = true ∧ m.read8 (p + BitVec.ofNat 64 n) = 0#8 :=
  fastStrlenScan_sound_aux hmem p strlenFuel 0 none rfl
    (fun _ hi => absurd hi (Nat.not_lt_zero _)) hscan

/-- Decides `Utf8Ok bs` via `ByteArray.validateUTF8`. -/
def fastCheckUtf8 (bs : List (BitVec 8)) : Bool :=
  ByteArray.validateUTF8 (bs.map UInt8.ofBitVec).toByteArray

private theorem map_toBitVec_ofBitVec (bs : List (BitVec 8)) :
    (bs.map UInt8.ofBitVec).map UInt8.toBitVec = bs := by
  induction bs with
  | nil => rfl
  | cons b rest ih => simp [ih]

private theorem map_ofBitVec_toBitVec (us : List UInt8) :
    (us.map UInt8.toBitVec).map UInt8.ofBitVec = us := by
  induction us with
  | nil => rfl
  | cons u rest ih => simp [ih]

theorem fastCheckUtf8_iff (bs : List (BitVec 8)) :
    fastCheckUtf8 bs = true ↔ Utf8Ok bs := by
  unfold fastCheckUtf8 Utf8Ok
  rw [ByteArray.validateUTF8_eq_true_iff]
  constructor
  · rintro ⟨cs, hba⟩
    refine ⟨cs, ?_⟩
    have hlist : bs.map UInt8.ofBitVec = cs.flatMap String.utf8EncodeChar := by
      have h1 := congrArg (fun b => b.data.toList) hba
      simpa only [List.utf8Encode, List.toList_data_toByteArray] using h1
    rw [← hlist, map_toBitVec_ofBitVec]
  · rintro ⟨cs, hbs⟩
    refine ⟨cs, ?_⟩
    simp only [List.utf8Encode]
    rw [← hbs, map_ofBitVec_toBitVec]

theorem fastCheckUtf8_eq_false_iff (bs : List (BitVec 8)) :
    fastCheckUtf8 bs = false ↔ ¬ Utf8Ok bs := by
  rw [← Bool.not_eq_true, fastCheckUtf8_iff]

end Symbolic.BugInjection.Proofs.CliExec.FastHooksAux
