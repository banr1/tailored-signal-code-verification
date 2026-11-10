/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public meta import LibsignalBinary.Proofs.SignalSession.Cli.DirSpecs -- shake: keep
import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.SignalSession.Cli.Kits
public import LibsignalBinary.Specifications.SignalSession.Run
public import LibsignalBinary.Proofs.SpecLemmas.SignalSession.RunProofDefs

/-!
# Pure Specification Model for `signal-session` `main`

Machine-free models of CLI argument parsing (`parseUnsigned`, `rsplitDot`, `addrParse`, `parseArgs`),
run inputs (`coinsOf`, `inputOf`), and sequential store commits (`WriteRule`, `commitFiles`),
with `#guard` edge-case checks.
-/

@[expose] public section

set_option warningAsError false

namespace CryptoVerification.SignalSession.Cli.MainHops

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open Arm64.Process
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## Argument Parsing -/

def isDigit (b : BitVec 8) : Bool := decide (48 ≤ b.toNat ∧ b.toNat ≤ 57)

/-- Unsigned base-10 integer parser (`<uN as FromStr>::from_str`): optional leading `'+'` followed by
one or more ASCII digits with value `≤ bound`. -/
def parseUnsigned (bound : Nat) (bs : List (BitVec 8)) : Option Nat :=
  let ds := match bs with
    | b :: rest => if b = 43#8 then rest else bs
    | [] => []
  if ds = [] ∨ ds.any (fun b => !isDigit b) then none
  else
    let v := ds.foldl (fun acc b => 10 * acc + (b.toNat - 48)) 0
    if v ≤ bound then some v else none

/-- Splits `bs` around its last `'.'` byte (`str::rsplit_once('.')`). -/
def rsplitDot (bs : List (BitVec 8)) : Option (List (BitVec 8) × List (BitVec 8)) :=
  match bs.reverse.span (fun b => b != 46#8) with
  | (_, []) => none
  | (devR, _ :: nameR) => some (nameR.reverse, devR.reverse)

/-- Parsed `ProtocolAddress` consisting of service-ID name bytes and device ID byte. -/
structure AddrV where
  name : List (BitVec 8)
  device : BitVec 8

/-- Parses `<service-id>.<device>` with `serviceIdParse uuidParse` and `u8` device ID in `1..=127`. -/
def addrParse (uuidParse : UuidParser) (bs : List (BitVec 8)) : Option AddrV :=
  match rsplitDot bs with
  | none => none
  | some (name, dev) =>
    match serviceIdParse uuidParse name, parseUnsigned 255 dev with
    | some _, some d => if 1 ≤ d ∧ d ≤ 127 then some ⟨name, BitVec.ofNat 8 d⟩ else none
    | _, _ => none

/-- Parsed CLI command (`enum Call`). -/
inductive CallV where
  | keygen (me : AddrV) (n : Nat)
  | init (peer : AddrV) (bundle : List (BitVec 8))
  | send (peer : AddrV)
  | recv (peer : AddrV)

/-- Numeric command tag (`0` keygen, `1` init, `2` send, `3` recv). -/
def CallV.tag : CallV → Nat
  | .keygen .. => 0
  | .init .. => 1
  | .send _ => 2
  | .recv _ => 3

/-- Parses `argv[1..]` (for ASCII arguments) into `Option CallV`, requiring `n ≤ 100` for `keygen`. -/
def parseArgs (uuidParse : UuidParser) : List (List (BitVec 8)) → Option CallV
  | [c, a, x] =>
    if c = utf8 "keygen" then
      match addrParse uuidParse a, parseUnsigned (2 ^ 32 - 1) x with
      | some me, some n => if n ≤ 100 then some (.keygen me n) else none
      | _, _ => none
    else if c = utf8 "init" then (addrParse uuidParse a).map fun p => CallV.init p x
    else none
  | [c, a] =>
    if c = utf8 "send" then (addrParse uuidParse a).map CallV.send
    else if c = utf8 "recv" then (addrParse uuidParse a).map CallV.recv
    else none
  | _ => none

namespace ParseArgsInline

private theorem char_eq_of_ascii_byte {c₁ c₂ : Char}
    (h₁ : c₁.toNat < 128) (h₂ : c₂.toNat < 128)
    (hb : BitVec.ofNat 8 c₁.toNat = BitVec.ofNat 8 c₂.toNat) :
    c₁ = c₂ := by
  have hn : c₁.toNat = c₂.toNat := by
    have hmod := congrArg BitVec.toNat hb
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat] at hmod
    omega
  rw [← Char.ofNat_toNat c₁, ← Char.ofNat_toNat c₂, hn]

private theorem chars_eq_of_bytes {l₁ l₂ : List Char}
    (h₁ : ∀ c ∈ l₁, c.toNat < 128) (h₂ : ∀ c ∈ l₂, c.toNat < 128)
    (hm : (l₁.map fun c => BitVec.ofNat 8 c.toNat) =
          (l₂.map fun c => BitVec.ofNat 8 c.toNat)) :
    l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons _ _ => cases hm
  | cons x₁ xs₁ ih =>
    cases l₂ with
    | nil => cases hm
    | cons x₂ xs₂ =>
      obtain ⟨hm₁, hm₂⟩ := List.cons.inj hm
      have hx : x₁ = x₂ :=
        char_eq_of_ascii_byte (h₁ x₁ (.head _)) (h₂ x₂ (.head _)) hm₁
      have hxs : xs₁ = xs₂ :=
        ih (fun c hc => h₁ c (.tail _ hc)) (fun c hc => h₂ c (.tail _ hc)) hm₂
      rw [hx, hxs]

private theorem eq_of_bytesOfString_eq_utf8 {s lit : String}
    (hs : PrintableAsciiArg s)
    (hlit_ascii : ∀ c ∈ lit.toList, c.toNat < 128)
    (hlit_utf8 : utf8 lit = bytesOfString lit)
    (heq : bytesOfString s = utf8 lit) :
    s = lit :=
  String.toList_injective <|
    chars_eq_of_bytes (fun c hc => (hs.2 c hc).2) hlit_ascii (heq.trans hlit_utf8)

end ParseArgsInline

open ParseArgsInline in
/-- Any ASCII `argv` failing `ArgvShapeOk` evaluates to `parseArgs uuidParse _ = none`. -/
theorem parseArgs_none_of_shape (uuidParse : UuidParser) {argv : List String}
    (hascii : ∀ a ∈ argv, PrintableAsciiArg a) (hshape : ArgvShapeOk argv = false) :
    parseArgs uuidParse (argv.map bytesOfString) = none := by
  rcases argv with _ | ⟨c, _ | ⟨a, _ | ⟨x, _ | ⟨_, _⟩⟩⟩⟩
  · rfl
  · rfl
  · have hc : PrintableAsciiArg c := hascii c (.head _)
    have hne_send : bytesOfString c ≠ utf8 "send" := by
      intro h
      have hceq : c = "send" :=
        eq_of_bytesOfString_eq_utf8 hc (by decide +kernel) (by decide +kernel) h
      rw [hceq] at hshape
      exact Bool.noConfusion hshape
    have hne_recv : bytesOfString c ≠ utf8 "recv" := by
      intro h
      have hceq : c = "recv" :=
        eq_of_bytesOfString_eq_utf8 hc (by decide +kernel) (by decide +kernel) h
      rw [hceq] at hshape
      exact Bool.noConfusion hshape
    change (if bytesOfString c = utf8 "send" then _
      else if bytesOfString c = utf8 "recv" then _ else none) = none
    split
    · exact absurd ‹_› hne_send
    · rfl
  · have hc : PrintableAsciiArg c := hascii c (.head _)
    have hne_keygen : bytesOfString c ≠ utf8 "keygen" := by
      intro h
      have hceq : c = "keygen" :=
        eq_of_bytesOfString_eq_utf8 hc (by decide +kernel) (by decide +kernel) h
      rw [hceq] at hshape
      exact Bool.noConfusion hshape
    have hne_init : bytesOfString c ≠ utf8 "init" := by
      intro h
      have hceq : c = "init" :=
        eq_of_bytesOfString_eq_utf8 hc (by decide +kernel) (by decide +kernel) h
      rw [hceq] at hshape
      exact Bool.noConfusion hshape
    change (if bytesOfString c = utf8 "keygen" then _
      else if bytesOfString c = utf8 "init" then _ else none) = none
    split
    · exact absurd ‹_› hne_keygen
    · rfl
  · rfl

/-! ## Read Inputs -/

/-- Bytes returned by `read_file("coins")` on `i` (defaulting to `[]` if absent). -/
def coinsOf (i : Inputs) : List (BitVec 8) := (filesOf i.files "coins").getD []

/-- Input byte slice passed to `run`: `i.stdin` for `send`/`recv`, `[]` for `keygen`/`init`. -/
def inputOf (i : Inputs) (c : CallV) : List (BitVec 8) := if 1 < c.tag then i.stdin else []

/-! ## `Stores::commit` -/

/-- Abstract single-file write transition `FsFiles → path → bytes → Option FsFiles`. -/
abbrev WriteRule : Type := FsFiles → List (BitVec 8) → List (BitVec 8) → Option FsFiles

/-- Sequential `Stores::commit` fold over `wr`, short-circuiting on the first `none` (`Err`). -/
def commitFiles (wr : WriteRule) : FsFiles → List (List (BitVec 8) × List (BitVec 8)) → Option FsFiles
  | F, [] => some F
  | F, (p, bs) :: ws => match wr F p bs with
    | some F' => commitFiles wr F' ws
    | none => none

/-! ## Regressions -/

private def u (s : String) : List (BitVec 8) := utf8 s

#guard ["7", "+7", "+", "", "-1", "007", "255", "256", "1a", "++1"].map
    (fun s => parseUnsigned 255 (u s)) =
  [some 7, some 7, none, none, none, some 7, some 255, none, none, none]

#guard parseUnsigned (2 ^ 32 - 1) (u "4294967295") = some 4294967295
#guard parseUnsigned (2 ^ 32 - 1) (u "4294967296") = none

#guard ["a.b.3", "abc", ".5", "x."].map
    (fun s => (rsplitDot (u s)).map fun (n, d) => (n.length, d.length)) =
  [some (3, 1), none, some (0, 1), some (1, 0)]

private def anyUuid : UuidParser := fun _ => some (List.Vector.replicate 16 0#8)

private def aci : String := "00000000-0000-0000-0000-000000000000"

private def addrShape (s : String) : Option (Nat × Nat) :=
  (addrParse anyUuid (u s)).map fun a => (a.name.length, a.device.toNat)

#guard addrShape (aci ++ ".1") = some (36, 1)
#guard addrShape (aci ++ ".127") = some (36, 127)
#guard addrShape (aci ++ ".+7") = some (36, 7)
#guard addrShape ("PNI:" ++ aci ++ ".2") = some (40, 2)
#guard addrShape (aci ++ ".0") = none
#guard addrShape (aci ++ ".128") = none
#guard addrShape (aci ++ ".256") = none
#guard addrShape (aci ++ ".") = none
#guard addrShape aci = none
#guard addrShape ("x." ++ aci ++ ".1") = none
#guard (addrParse (fun _ => none) (u (aci ++ ".1"))).isNone

private def callShape (args : List String) : Option (Nat × Nat) :=
  (parseArgs anyUuid (args.map u)).map fun c => (c.tag, match c with | .keygen _ n => n | _ => 0)

#guard callShape ["keygen", aci ++ ".1", "100"] = some (0, 100)
#guard callShape ["keygen", aci ++ ".1", "101"] = none
#guard callShape ["keygen", aci ++ ".1", "-1"] = none
#guard callShape ["init", aci ++ ".1", "anything"] = some (1, 0)
#guard callShape ["send", aci ++ ".3"] = some (2, 0)
#guard callShape ["recv", aci ++ ".3"] = some (3, 0)
#guard callShape ["send", aci ++ ".3", "x"] = none
#guard callShape ["recv"] = none
#guard callShape ["Send", aci ++ ".3"] = none
#guard callShape [] = none

end CryptoVerification.SignalSession.Cli.MainHops
