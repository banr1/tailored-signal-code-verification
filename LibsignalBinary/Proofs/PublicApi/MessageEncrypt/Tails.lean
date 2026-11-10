/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.CmDrop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrPreKeyEncrypt
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrSignalEncrypt
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.ProtocolErrStoreHook
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailDropRecord
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFreePrevSessions
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailFromSessionStateErr
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteErr
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Tail.TailWriteResult

/-!
# Shared Error and Result Tails for `session_message_encrypt_with_stores`

**Checked by Lean.** Statements and staged-result algebra for the shared exit tails of
`session_message_encrypt_with_stores` (`0x3caf4`, frame base `sp = s0.sp - 0xbe0`):

* **T1 (`+0x46c..+0x5b4`)**: frees the `OutgoingTripleRatchet`'s `pqr_state` buffer when the drop
  flag `[sp + 0x469]` is `1`, drops `SessionRecord.current_session` when present
  (`drop_glue<SessionStructure>`), and frees the empty `previous_sessions` buffer before falling
  into `T2` (`+0x49c` first stages an error from `from_session_state`; `+0x564` enters directly at
  the `previous_sessions` free).
* **T2 + T3 (`+0x5b4..+0x660`)**: copies staged error payload bytes `sp + 0x9d0 → sp + 0x4a0` with
  `x22 = errTag` (`+0x5b4`), writes the 248-byte `apiEncResultAt` to `x19` (`+0x5f8`), and executes
  the frame epilogue (`+0x640..+0x660`).
* **T5 (`+0xc14..+0xc78`, `+0xd40..+0xd50`)**: stages `SignalProtocolError` words `w3..w5` into
  `sp + 0x9d0..0x9e8`, frees any live Kyber box (`+0xc38`) or `CiphertextMessage` (`+0xd40`), and
  branches to `T1`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.MessageEncrypt

/-! ## Staged Results -/

def words64At : BitVec 64 → List (BitVec 64) → SepProp
  | _, [] => emp
  | a, w :: ws => (a ↦₆₄ w) ∗ words64At (a + 8#64) ws

/-- 48-byte `encrypt` error layout at `a` (`speAt` with function name `"encrypt"` for protocol
errors, `apiErrAt` otherwise). -/
def encErrAt (A : RustAlloc) (a : BitVec 64) : ApiError AddrVal Unit → SepProp
  | .protocol p => speAt A (utf8 "encrypt") a p
  | e => apiErrAt A a e

theorem apiEncResultAt_error (A : RustAlloc) (r : BitVec 64) (e : ApiError AddrVal Unit) :
    apiEncResultAt A r (.error e) =
      ((r ↦₆₄ errTag) ∗ encErrAt A (r + 8#64) e ∗ memRegion (r + 56#64) 192) := by
  cases e <;> rfl

/-- `speAt` is independent of the function-name string except on `.invalidState`. -/
theorem speAt_fnName_eq (A : RustAlloc) (f f' : List (BitVec 8)) (a : BitVec 64)
    (p : SignalProtocolError) (hp : p ≠ .invalidState) : speAt A f a p = speAt A f' a p := by
  cases p <;> first | rfl | exact absurd rfl hp

/-- Relocatable staged `SignalProtocolError`: six 64-bit words `ws` (`w0..w2` in `x27, x21, x23`
and `w3..w5` at `sp + 0x9d0`) plus owned heap resources `H` that entail `encErrAt A (ret + 8) e`. -/
def SpeStaged (A : RustAlloc) (ret : BitVec 64) (e : ApiError AddrVal Unit) (ws : List (BitVec 64))
    (H : SepProp) : Prop :=
  e ≠ .panic ∧ ws.length = 6 ∧ (words64At (ret + 8#64) ws ∗ H ⊢ encErrAt A (ret + 8#64) e)

/-- Relocatable staged 248-byte `apiEncResultAt`: four 64-bit words `ws` (`x22, x27, x21, x23`),
`0xd8` bytes `bs` (`sp + 0x4a0 .. sp + 0x578`), and owned heap resources `H`. -/
def ResStaged (A : RustAlloc) (ret : BitVec 64) (res : Except (ApiError AddrVal Unit) CiphertextMessage)
    (ws : List (BitVec 64)) (bs : List (BitVec 8)) (H : SepProp) : Prop :=
  res ≠ .error .panic ∧ ws.length = 4 ∧ bs.length = 0xd8 ∧
    (words64At ret ws ∗ ((ret + 0x20#64) ↦ₛ bs) ∗ H ⊢ apiEncResultAt A ret res)

/-- Heap body of a `Vec<u8>` (`vecU8At` without its 24-byte `(cap, ptr, len)` header). -/
def vecU8Body (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8)) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
    (if cap = 0 then emp
     else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
       memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length))

/-! ### Relocating `SignalProtocolError` Payloads -/

/-- `n` inline bytes at `f b` paired with a base-independent heap assertion `F bs`. -/
def RelocBytes (f : BitVec 64 → BitVec 64) (n : Nat) (F : List (BitVec 8) → SepProp)
    (b : BitVec 64) : SepProp :=
  ∃∗ bs : List (BitVec 8), ⌜bs.length = n⌝ ∗ (f b ↦ₛ bs) ∗ F bs

/-- Two-way equivalence between `P b` and `RelocBytes f n F b` for all `b`. -/
def Reloc (f : BitVec 64 → BitVec 64) (n : Nat) (P : BitVec 64 → SepProp) : Prop :=
  ∃ F : List (BitVec 8) → SepProp, ∀ b, (P b ⊢ RelocBytes f n F b) ∧ (RelocBytes f n F b ⊢ P b)

namespace Reloc

theorem of_eq {f : BitVec 64 → BitVec 64} {n : Nat} {P Q : BitVec 64 → SepProp}
    (h : Reloc f n P) (e : ∀ b, Q b = P b) : Reloc f n Q := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, fun b => by rw [e b]; exact hF b⟩

theorem pFalse (f : BitVec 64 → BitVec 64) (n : Nat) : Reloc f n (fun _ => ⌜False⌝) := by
  refine ⟨fun _ => ⌜False⌝, fun b => ⟨Entails.pure_left_only False.elim, ?_⟩⟩
  unfold RelocBytes
  refine Entails.sepExists_elim fun bs => ?_
  simp only [sepConj_pure_false]
  exact Entails.refl _

theorem bytes (f : BitVec 64 → BitVec 64) (cs : List (BitVec 8)) :
    Reloc f cs.length (fun b => f b ↦ₛ cs) := by
  refine ⟨fun bs => ⌜bs = cs⌝, fun b => ⟨?_, ?_⟩⟩
  · unfold RelocBytes
    exact Entails.sepExists_right cs (Entails.pure_right rfl
      (Entails.trans (Entails.of_eq (sepConj_emp _).symm)
        (sepConj_mono_right (Entails.pure_right_only rfl (Entails.refl _)))))
  · unfold RelocBytes
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun _ => ?_
    refine Entails.trans (Entails.of_eq (sepConj_comm _ _)) (Entails.pure_left fun h => ?_)
    subst h
    exact Entails.refl _

theorem pt64 (f : BitVec 64 → BitVec 64) (v : BitVec 64) : Reloc f 8 (fun b => f b ↦₆₄ v) :=
  (bytes f (unpack64 v)).of_eq fun _ => pointsTo64_eq_pointsToBytes _ v

theorem pt32 (f : BitVec 64 → BitVec 64) (v : BitVec 32) : Reloc f 4 (fun b => f b ↦₃₂ v) :=
  (bytes f (unpack32 v)).of_eq fun _ => pointsTo32_eq_pointsToBytes _ v

theorem pt8 (f : BitVec 64 → BitVec 64) (v : BitVec 8) : Reloc f 1 (fun b => f b ↦₈ v) :=
  (bytes f [v]).of_eq fun _ => (pointsToBytes_singleton _ v).symm

theorem region (f : BitVec 64 → BitVec 64) (k : Nat) (hk : k ≤ 2 ^ 64 := by decide) :
    Reloc f k (fun b => memRegion (f b) k) := by
  refine ⟨fun _ => emp, fun b => ?_⟩
  unfold RelocBytes
  simp only [memRegion_eq_exists_bytes _ _ hk, sepConj_emp]
  exact ⟨Entails.refl _, Entails.refl _⟩

theorem frameR {f : BitVec 64 → BitVec 64} {n : Nat} {P : BitVec 64 → SepProp}
    (h : Reloc f n P) (K : SepProp) : Reloc f n (fun b => P b ∗ K) := by
  obtain ⟨F, hF⟩ := h
  refine ⟨fun bs => F bs ∗ K, fun b => ⟨?_, ?_⟩⟩
  · refine Entails.trans (sepConj_mono_left (hF b).1) ?_
    unfold RelocBytes
    simp only [sepExists_sepConj_left, sepConj_assoc]
    exact Entails.refl _
  · refine Entails.trans ?_ (sepConj_mono_left (hF b).2)
    unfold RelocBytes
    simp only [sepExists_sepConj_left, sepConj_assoc]
    exact Entails.refl _

theorem frameL {f : BitVec 64 → BitVec 64} {n : Nat} {P : BitVec 64 → SepProp}
    (h : Reloc f n P) (K : SepProp) : Reloc f n (fun b => K ∗ P b) :=
  (h.frameR K).of_eq fun _ => sepConj_comm _ _

theorem sepEx {α : Type} {f : BitVec 64 → BitVec 64} {n : Nat} {P : α → BitVec 64 → SepProp}
    (h : ∀ x, Reloc f n (P x)) : Reloc f n (fun b => ∃∗ x, P x b) := by
  have hF := fun x => Classical.choose_spec (h x)
  refine ⟨fun bs => ∃∗ x, Classical.choose (h x) bs, fun b => ⟨?_, ?_⟩⟩
  · refine Entails.sepExists_elim fun x => Entails.trans (hF x b).1 ?_
    unfold RelocBytes
    refine Entails.sepExists_elim fun bs => Entails.sepExists_right bs ?_
    exact sepConj_mono_right (sepConj_mono_right
      (Entails.sepExists_intro (P := fun y => Classical.choose (h y) bs) x))
  · unfold RelocBytes
    refine Entails.sepExists_elim fun bs => ?_
    simp only [sepExists_sepConj_right]
    refine Entails.sepExists_elim fun x => Entails.trans ?_
      (Entails.trans (hF x b).2 (Entails.sepExists_intro (P := fun y => P y b) x))
    unfold RelocBytes
    exact Entails.sepExists_intro
      (P := fun bs => ⌜bs.length = n⌝ ∗ (f b ↦ₛ bs) ∗ Classical.choose (h x) bs) bs

theorem sep {f g : BitVec 64 → BitVec 64} {n m : Nat} {P Q : BitVec 64 → SepProp}
    (hP : Reloc f n P) (hQ : Reloc g m Q)
    (hg : ∀ b, g b = f b + BitVec.ofNat 64 n := by intro b; (try dsimp only) <;> bv_arith) :
    Reloc f (n + m) (fun b => P b ∗ Q b) := by
  obtain ⟨F, hF⟩ := hP
  obtain ⟨G, hG⟩ := hQ
  refine ⟨fun bs => F (bs.take n) ∗ G (bs.drop n), fun b => ⟨?_, ?_⟩⟩
  · refine Entails.trans (sepConj_mono (hF b).1 (hG b).1) ?_
    unfold RelocBytes
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs2 => Entails.sepExists_elim fun bs1 => ?_
    refine Entails.trans (Entails.of_eq (Q := ⌜bs1.length = n⌝ ∗ ⌜bs2.length = m⌝ ∗
      (f b ↦ₛ bs1) ∗ (g b ↦ₛ bs2) ∗ F bs1 ∗ G bs2)) ?_
    refine Entails.pure_left fun h1 => Entails.pure_left fun h2 => ?_
    refine Entails.sepExists_right (bs1 ++ bs2)
      (Entails.pure_right (by rw [List.length_append, h1, h2]) ?_)
    rw [List.take_left' h1, List.drop_left' h1, pointsToBytes_append, h1, ← hg b]
    exact Entails.of_eq
  · unfold RelocBytes
    refine Entails.sepExists_elim fun bs => Entails.pure_left fun hl => ?_
    refine Entails.trans ?_ (sepConj_mono (hF b).2 (hG b).2)
    unfold RelocBytes
    have e : (f b ↦ₛ bs) = (f b ↦ₛ bs.take n) ∗ (g b ↦ₛ bs.drop n) := by
      conv_lhs => rw [← List.take_append_drop n bs]
      rw [pointsToBytes_append, List.length_take, Nat.min_eq_left (by omega), hg b]
    rw [e]
    dsimp only
    refine Entails.trans (Entails.of_eq (Q := ((f b ↦ₛ bs.take n) ∗ F (bs.take n)) ∗
      ((g b ↦ₛ bs.drop n) ∗ G (bs.drop n)))) ?_
    exact sepConj_mono
      (Entails.sepExists_right (bs.take n)
        (Entails.pure_right (by rw [List.length_take]; omega) (Entails.refl _)))
      (Entails.sepExists_right (bs.drop n)
        (Entails.pure_right (by rw [List.length_drop]; omega) (Entails.refl _)))

theorem strRefR (f : BitVec 64 → BitVec 64) (lit : List (BitVec 8)) :
    Reloc f 16 (fun b => strRefAt (f b) lit) := by
  unfold strRefAt
  exact sepEx fun p => sep (pt64 f p) ((pt64 (fun b => f b + 8#64) _).frameR (p ↦ᵣ lit))

theorem vecU8R (A : RustAlloc) (f : BitVec 64 → BitVec 64) (bs : List (BitVec 8)) :
    Reloc f 24 (fun b => vecU8 A (f b) bs) := by
  have h := sepEx fun cap => sepEx fun ptr =>
    sep (pt64 f cap) (sep (pt64 (fun b => f b + 8#64) ptr)
      ((pt64 (fun b => f b + 16#64) (BitVec.ofNat 64 bs.length)).frameR (vecU8Body A cap ptr bs)))
  refine h.of_eq fun b => ?_
  simp only [vecU8, vecU8At, vecHeader, vecU8Body, sepConj_assoc]

theorem addrCloneR (A : RustAlloc) (f : BitVec 64 → BitVec 64) (v : AddrVal) :
    Reloc f 32 (fun b => addrCloneAt A (f b) v) := by
  unfold addrCloneAt
  exact sep (vecU8R A f v.name) (sep (pt8 (fun b => f b + 0x18#64) v.device)
    (region (fun b => f b + 0x19#64) 7))

theorem invalidMessageStrR (A : RustAlloc) (f : BitVec 64 → BitVec 64) (r : InvalidMessageReason) :
    Reloc f 24 (fun b => invalidMessageStrAt A (f b) r) := by
  cases r <;> first
    | exact vecU8R A f _
    | exact sepEx fun bs => vecU8R A f bs
    | exact pFalse f 24

theorem encErrR (A : RustAlloc) (e : ApiError AddrVal Unit) :
    Reloc (fun b => b) 48 (fun b => encErrAt A b e) := by
  rcases e with _ | p | ⟨addr, op⟩ | addr | ⟨⟩
  · exact pFalse _ 48
  · cases p
    case invalidSessionStructure r =>
      exact sep (pt64 (fun b => b) _) (sep (strRefR (fun b => b + 8#64) _)
        (region (fun b => b + 24#64) 24))
    case invalidKeyAgreement =>
      exact sep (pt64 (fun b => b) _) (region (fun b => b + 8#64) 40)
    case duplicatedMessage i c =>
      exact sep (pt64 (fun b => b) _) (sep (pt32 (fun b => b + 8#64) _)
        (sep (pt32 (fun b => b + 12#64) _) (region (fun b => b + 16#64) 32)))
    case invalidMessage t r =>
      exact sep (pt64 (fun b => b) _) (sep (invalidMessageStrR A (fun b => b + 8#64) r)
        (sep (pt8 (fun b => b + 32#64) _) (region (fun b => b + 33#64) 15)))
    case invalidState =>
      exact sep (pt64 (fun b => b) _)
        (sep (sepEx fun bs => vecU8R A (fun b => b + 8#64) bs) (strRefR (fun b => b + 32#64) _))
    case ciphertextMessageTooShort n =>
      exact sep (pt64 (fun b => b) _) (sep (pt64 (fun b => b + 8#64) _)
        (region (fun b => b + 16#64) 32))
    case legacyCiphertextVersion v =>
      exact sep (pt64 (fun b => b) _) (sep (pt8 (fun b => b + 8#64) _)
        (region (fun b => b + 9#64) 39))
    case unrecognizedCiphertextVersion v =>
      exact sep (pt64 (fun b => b) _) (sep (pt8 (fun b => b + 8#64) _)
        (region (fun b => b + 9#64) 39))
    case invalidProtobufEncoding =>
      exact sep (pt64 (fun b => b) _) (region (fun b => b + 8#64) 40)
    case noKeyTypeIdentifier =>
      exact sep (pt64 (fun b => b) _) (region (fun b => b + 8#64) 40)
    case badKeyType t =>
      exact sep (pt64 (fun b => b) _) (sep (pt8 (fun b => b + 8#64) _)
        (region (fun b => b + 9#64) 39))
    case badKeyLength n =>
      exact sep (pt64 (fun b => b) _) (sep (pt64 (fun b => b + 8#64) _)
        (region (fun b => b + 16#64) 32))
    case panic => exact pFalse _ 48
  · exact sep (addrCloneR A (fun b => b) addr) (strRefR (fun b => b + 0x20#64) _)
  · exact sep (pt64 (fun b => b) _) (sep (addrCloneR A (fun b => b + 8#64) addr)
      (region (fun b => b + 0x28#64) 8))
  · exact sep (pt64 (fun b => b) _) (sep (strRefR (fun b => b + 8#64) _)
      (sep (sepEx fun d => (pt64 (fun b => b + 0x18#64) d).frameL ⌜d ≠ 0⌝)
        (sep (sepEx fun vt => pt64 (fun b => b + 0x20#64) vt) (region (fun b => b + 0x28#64) 8))))

end Reloc

theorem words64At_eq_bytes (a : BitVec 64) (ws : List (BitVec 64)) :
    words64At a ws = (a ↦ₛ unpackL ws) := by
  induction ws generalizing a with
  | nil => simp only [words64At, unpackL, List.flatMap_nil, pointsToBytes_nil]
  | cons w ws ih =>
    simp only [words64At, unpackL, List.flatMap_cons] at ih ⊢
    rw [pointsToBytes_append, unpack64_length, ← ih, pointsTo64_eq_pointsToBytes]

/-- Relocates any non-panic `encErrAt A a e` from callee `sret + 8` address `a` into a
`SpeStaged` witness targeting `ret + 8`. -/
theorem speStaged_of_encErrAt (A : RustAlloc) (a ret : BitVec 64) (e : ApiError AddrVal Unit)
    (he : e ≠ .panic) :
    encErrAt A a e ⊢ ∃∗ ws : List (BitVec 64), ∃∗ H : SepProp,
      ⌜SpeStaged A ret e ws H⌝ ∗ words64At a ws ∗ H := by
  obtain ⟨F, hF⟩ := Reloc.encErrR A e
  refine Entails.trans (hF a).1 ?_
  unfold RelocBytes
  refine Entails.sepExists_elim fun bs => Entails.pure_left fun hl => ?_
  obtain ⟨ws, hws, rfl⟩ := exists_unpackL 6 bs hl
  have hS : SpeStaged A ret e ws (F (unpackL ws)) := by
    refine ⟨he, hws, ?_⟩
    rw [words64At_eq_bytes]
    refine Entails.trans ?_ (hF (ret + 8#64)).2
    unfold RelocBytes
    exact Entails.sepExists_right (unpackL ws) (Entails.pure_right hl (Entails.refl _))
  refine Entails.sepExists_right ws (Entails.sepExists_right (F (unpackL ws))
    (Entails.pure_right hS ?_))
  rw [words64At_eq_bytes]
  exact Entails.refl _

theorem vecU8_of_body (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecHeader v cap ptr (BitVec.ofNat 64 bs.length) ∗ vecU8Body A cap ptr bs ⊢ vecU8 A v bs :=
  Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem pointsTo64_lowByte (a w : BitVec 64) (d : BitVec 8) (hd : w.setWidth 8 = d) :
    (a ↦₆₄ w) ⊢ (a ↦₈ d) ∗ memRegion (a + 1#64) 7 := by
  rw [pointsTo64_eq_pointsToBytes]
  unfold unpack64
  rw [pointsToBytes_cons]
  have h0 : w.extractLsb' 0 8 = d := by rw [← hd, BitVec.setWidth_eq_extractLsb' (by decide)]
  rw [h0]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion _ _)

/-- Stages an in-place `SessionNotFound` error from a cloned address `Vec` `(cap, ptr, len)`,
device byte `devWord`, and operation string `(opPtr, opLen)`. -/
theorem speStaged_sessionNotFound (A : RustAlloc) (ret : BitVec 64) (addr : AddrVal) (op : String)
    (cap ptr len devWord opPtr opLen : BitVec 64) (hlen : len = BitVec.ofNat 64 addr.name.length)
    (hdev : devWord.setWidth 8 = addr.device) (hop : opLen = BitVec.ofNat 64 (utf8 op).length) :
    SpeStaged A ret (.sessionNotFound addr op) [cap, ptr, len, devWord, opPtr, opLen]
      (vecU8Body A cap ptr addr.name ∗ (opPtr ↦ᵣ utf8 op)) := by
  refine ⟨(by intro h; cases h), rfl, ?_⟩
  subst hlen hop
  show words64At (ret + 8#64) _ ∗ _ ⊢ apiErrAt A (ret + 8#64) (.sessionNotFound addr op)
  simp only [apiErrAt, addrCloneAt, strRefAt, words64At, sepConj_emp, BitVec.add_assoc,
    BitVec.reduceAdd]
  refine Entails.trans ?_
    (sepConj_mono (sepConj_mono_left (vecU8_of_body A _ cap ptr _)) (Entails.sepExists_intro opPtr))
  simp only [vecHeader, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_left (pointsTo64_lowByte _ _ _ hdev)))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq

/-- Stages an in-place `UntrustedIdentity` error from `speWord 12`, a cloned address `Vec`
`(cap, ptr, len)`, and device byte `devWord`. -/
theorem speStaged_untrusted (A : RustAlloc) (ret : BitVec 64) (addr : AddrVal)
    (cap ptr len devWord w5 : BitVec 64) (hlen : len = BitVec.ofNat 64 addr.name.length)
    (hdev : devWord.setWidth 8 = addr.device) :
    SpeStaged A ret (.untrustedIdentity addr) [speWord 12, cap, ptr, len, devWord, w5]
      (vecU8Body A cap ptr addr.name) := by
  refine ⟨(by intro h; cases h), rfl, ?_⟩
  subst hlen
  show words64At (ret + 8#64) _ ∗ _ ⊢ apiErrAt A (ret + 8#64) (.untrustedIdentity addr)
  simp only [apiErrAt, addrCloneAt, speUntrustedIdentity, words64At, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_left
    (sepConj_mono_left (vecU8_of_body A _ cap ptr _))))
  simp only [vecHeader, BitVec.add_assoc, BitVec.reduceAdd]
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_lowByte _ _ _ hdev)
      (pointsTo64_entails_memRegion _ _))))))) ?_
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq

/-! ## Tail Frame Predicates -/

/-- Poll and staging region `sp + 0x46a .. sp + 0xb80` with `ws` at `sp + off` and `memRegion`
elsewhere. -/
def pollWith (sp : BitVec 64) (off : Nat) (ws : List (BitVec 64)) : SepProp :=
  memRegion (sp + 0x46a#64) (off - 0x46a) ∗ words64At (sp + BitVec.ofNat 64 off) ws ∗
    memRegion (sp + BitVec.ofNat 64 (off + 8 * ws.length)) (0xb80 - (off + 8 * ws.length))

/-- `OutgoingTripleRatchet` slot `sp + 0x288 .. sp + 0x350` and its drop flag at `sp + 0x469`
(`some` when live with flag `1`, `none` when already consumed with flag `0`). -/
def otrSlotAt (A : RustAlloc) (sp : BitVec 64) :
    Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))) → SepProp
  | some (pqCap, pqPtr, ot) => otrAt A (sp + 0x288#64) pqCap pqPtr ot ∗ ((sp + 0x469#64) ↦₈ 1#8)
  | none => memRegion (sp + 0x288#64) 200 ∗ ((sp + 0x469#64) ↦₈ 0#8)

/-- Key and `CiphertextMessage` slots `sp + 0x350 .. sp + 0x469`. -/
def cmSlotAt (A : RustAlloc) (sp : BitVec 64) : Option CiphertextMessage → SepProp
  | some m => memRegion (sp + 0x350#64) 0x20 ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      memRegion (sp + 0x468#64) 1
  | none => memRegion (sp + 0x350#64) 0x119

/-- Stack frame layout at a `T1`-family record-drop entry (`+0x46c`, `+0xc14`, `+0xc38`,
`+0xd40`, and store-error stubs). -/
def dropRecordSlots (A : RustAlloc) (sp : BitVec 64) (scratch : BitVec 64 → SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (cm : Option CiphertextMessage) (poll : SepProp) : SepProp :=
  scratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗ memRegion (sp + 0x280#64) 8 ∗
    otrSlotAt A sp ot ∗ cmSlotAt A sp cm ∗ poll

/-- Register pins at a staged-error tail entry (`x26 = sp + 0x9d0`, `x28 = sp + 0x4a0`, and
`w0..w2` in `x27, x21, x23`). -/
def tailRegs (w0 w1 w2 : BitVec 64) (sp : BitVec 64) (s : State) : Prop :=
  s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x27 = w0 ∧
    s.readReg64 .x21 = w1 ∧ s.readReg64 .x23 = w2

open CryptoVerification.LibsignalPublicApi.StoreKit

/-- Machine and memory state at an `encrypt` tail entry `pc`. -/
def EncTailV {img : Obj.Image} {A : RustAlloc} (kit : SessionStoreSpec A img.base)
    (st0 : kit.StoreState) (ikit : IdentityStoreSpec A img.base) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit) (pc : BitVec 64)
    (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp) (s0 s : State) :
    Prop :=
  let sp := s0.sp - 0xbe0#64
  s.pc = pc ∧ encMidMeta img x s0 s ∧ regs sp s ∧ withStoresEncStack ≤ s0.sp.toNat ∧
    (s.mem ⊨ slots sp ∗ encSpillsAtV kit.ss_vt ikit.id_vt sp x ∗ memRegion x.ret 248 ∗
      encCommon A ctl img x (x.draws S answers) s0 ∗
      (encStoreExtra kit (kit.storeFinal st0 answers (x.model C S parse answers).2)
        ikit (ikit.idFinal ist0 answers (x.model C S parse answers).2) x s0 ∗ R))

abbrev EncTail (A : RustAlloc) (C : Crypto) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel)
    (img : Obj.Image)
    (x : WithStoresEncGhost) (answers : StoreAnswers (List (BitVec 8)) Unit) (pc : BitVec 64)
    (regs : BitVec 64 → State → Prop) (slots : BitVec 64 → SepProp) (R : SepProp) (s0 s : State) :
    Prop :=
  EncTailV (hookSessionStoreSpec A img.base) () (hookIdentityStoreSpec A img.base) () C ctl parse S
    x answers pc regs slots R s0 s

/-- Pure model and trace relation at an `encrypt` tail entry. -/
def TailModel {A : RustAlloc} {base : BitVec 64} (kit : SessionStoreSpec A base)
    (st0 : kit.StoreState) (ikit : IdentityStoreSpec A base) (ist0 : ikit.IdState)
    (C : Crypto) (S : SpqrModel) (parse : UuidParser)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) (x : WithStoresEncGhost)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (s0 s : State) : Prop :=
  ((x.model C S parse answers).1 = res ∧
    kit.callsRel st0 answers (x.model C S parse answers).2 ∧
    ikit.idCallsRel ist0 answers (x.model C S parse answers).2) ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2

/-- Weakens a `sessionRecordAt` with `rec.currentSession = none` to the `previous_sessions`
header plus 344 uninitialized bytes for `tailFreePrevSessions_ok`. -/
theorem sessionRecordAt_noCur_weaken (A : RustAlloc) (sp : BitVec 64) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8))) (hrec : rec.currentSession = none) :
    sessionRecordAt A (sp + 0x110#64) g rec ⊢
      vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 := by
  unfold sessionRecordAt
  rw [hrec]
  rcases g with ⟨pc, pp, _ | G⟩
  · refine sepConj_mono_right ?_
    show ((sp + 0x110#64 + 0x18#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x110#64 + 0x20#64) 336 ⊢ _
    have e1 : sp + 0x110#64 + 0x18#64 = sp + 0x128#64 := by bv_arith
    have e2 : sp + 0x110#64 + 0x20#64 = sp + 0x128#64 + BitVec.ofNat 64 8 := by bv_arith
    rw [e1, e2, show (0x158 : Nat) = 8 + 336 from rfl, memRegion_split _ 8 336 (by decide)]
    exact sepConj_mono_left (pointsTo64_entails_memRegion _ _)
  · show _ ∗ ⌜False⌝ ⊢ _
    rw [sepConj_pure_false]
    exact Entails.pure_left_only False.elim

/-! ## Tail Exit Theorems -/

variable {Scope : SessionRecord (List (BitVec 8)) → Prop} {Q : List (BitVec 8) → Prop}
  {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
  {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
  {abs : String → Option (State → State)} {kit : SessionStoreSpec A img.base} {st0 : kit.StoreState}
  {ikit : IdentityStoreSpec A img.base} {ist0 : ikit.IdState}

/-- `T2` result writer and `T3` epilogue (`+0x5f8..+0x660`): writes the staged 248-byte result to
`x19`, restores callee-saved registers, and returns. -/
theorem tailWriteResult_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit)
    (res : Except (ApiError AddrVal Unit) CiphertextMessage) (w0 w1 w2 w3 : BitVec 64)
    (bs : List (BitVec 8)) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers res s0 s)
    (hst : ResStaged A x.ret res [w0, w1, w2, w3] bs H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x5f8#64)
      (fun sp s => s.readReg64 .x28 = sp + 0x4a0#64 ∧ s.readReg64 .x22 = w0 ∧
        s.readReg64 .x27 = w1 ∧ s.readReg64 .x21 = w2 ∧ s.readReg64 .x23 = w3)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x390 ∗ ((sp + 0x4a0#64) ↦ₛ bs) ∗
        memRegion (sp + 0x578#64) 0x608 ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  exact Pf.TailWriteResult.tailWriteResult_ok env x R s0 s answers res w0 w1 w2 w3 bs H hm hst hs

/-- `T2` error staging, writer, and `T3` epilogue (`+0x5b4..+0x660`): copies `sp + 0x9d0..0xaa8`
to `sp + 0x4a0`, sets `x22 = errTag`, and exits via `tailWriteResult_ok`. -/
theorem tailWriteErr_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x5b4#64) (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗ memRegion (sp + 0x110#64) 0x35a ∗
        pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  exact Pf.TailWriteErr.tailWriteErr_ok env x R s0 s answers e w0 w1 w2 w3 w4 w5 H hm hst hs

/-- `T1` `previous_sessions` free + `T2` + `T3` (`+0x564..+0x660`): frees the empty
`previous_sessions` buffer and exits via `tailWriteErr_ok`. -/
theorem tailFreePrevSessions_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (prevCap prevPtr : BitVec 64)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x564#64) (tailRegs w0 w1 w2)
      (fun sp => memRegion sp 0x58 ∗
        vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) prevCap prevPtr [] ∗
        memRegion (sp + 0x128#64) 0x158 ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x9d0 [w3, w4, w5] ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  exact Pf.TailFreePrevSessions.tailFreePrevSessions_ok env x R s0 s answers e w0 w1 w2 w3 w4 w5 H prevCap prevPtr hm hst hs

/-- `T1` `from_session_state` error tail + `T2` + `T3` (`+0x49c..+0x660`): stages the protocol
error from `sp + 0x588..0x5b8` into `x27, x21, x23` and `sp + 0x9d0`, drops `current_session` if
present, and exits via `tailFreePrevSessions_ok`. -/
theorem tailFromSessionStateErr_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x49c#64)
      (fun sp s => s.readReg64 .x21 = sp + 0x580#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
        s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
      (fun sp => curScratch sp ∗ sessionRecordAt A (sp + 0x110#64) g rec ∗
        memRegion (sp + 0x280#64) 0x1ea ∗ pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  exact Pf.TailFromSessionStateErr.tailFromSessionStateErr_ok env x R s0 s answers e w0 w1 w2 w3 w4 w5 H g rec hm hst hs

/-- `T1` record drop + `T2` + `T3` (`+0x46c..+0x660`): frees the `OutgoingTripleRatchet`
`pqr_state` buffer when flagged, drops `current_session` if present, and exits via
`tailFreePrevSessions_ok`. -/
theorem tailDropRecord_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0x46c#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  exact Pf.TailDropRecord.tailDropRecord_ok env x R s0 s answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot hm hst hs

/-- `T5` Signal `OTR::encrypt` error tail (`+0xc14..+0xc20`, `+0xc6c..+0xc78`): stages `w3..w5`
from `sp + 0xb00` to `sp + 0x9d0` and exits via `tailDropRecord_ok`. -/
theorem tailSignalEncryptErr_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0xc14#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none (pollWith sp 0xb00 [w3, w4, w5]) ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  exact ProtocolErr.tailSignalEncryptErr env.loads hm hs fun s' hm' hs' =>
    tailDropRecord_ok env x R s0 s' answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot hm' hst hs'

/-- `T5` PreKey `OTR::encrypt` error tail (`+0xc38..+0xc64`): stages `w3..w5` from `sp + 0xb00`
to `sp + 0x9d0`, frees any non-empty Kyber ciphertext box at `sp + 0x8a0`, and exits via
`tailDropRecord_ok`. -/
theorem tailPreKeyEncryptErr_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (kyPtr : BitVec 64) (kp : Option KyberPayload)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0xc38#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot none
          (memRegion (sp + 0x46a#64) 0x436 ∗ optKyberAt A (sp + 0x8a0#64) kyPtr kp ∗
            memRegion (sp + 0x8b8#64) 0x248 ∗ words64At (sp + 0xb00#64) [w3, w4, w5] ∗
            memRegion (sp + 0xb18#64) 0x68) ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  exact ProtocolErr.tailPreKeyEncryptErr env.loads env.hooks.alloc hm hs fun s' hm' hs' =>
    tailDropRecord_ok env x R s0 s' answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot hm' hst hs'

/-- `CiphertextMessage` drop tail (`+0xd40..+0xd50`): drops the `CiphertextMessage` at
`sp + 0x370` and exits via `tailDropRecord_ok`. -/
theorem tailCmDrop_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (m : CiphertextMessage)
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + 0xd40#64) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot (some m) (pollWith sp 0x9d0 [w3, w4, w5]) ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  exact ProtocolErr.tailCmDrop env.loads env.callees.cmDrop hm hs fun s' hm' hs' =>
    tailDropRecord_ok env x R s0 s' answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot hm' hst hs'

/-- `T5` store-hook error tail (`+0xc20..+0xc38` with stubs `+0xe28` and `+0xf2c`): stages
`w3..w5` from `sp + src` to `sp + 0x9d0` and exits via `tailCmDrop_ok`. -/
theorem tailStoreHookErr_ok (env : EncEnv kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord abs)
    (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (answers : StoreAnswers (List (BitVec 8)) Unit) (e : ApiError AddrVal Unit)
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (H : SepProp) (scratch : BitVec 64 → SepProp)
    (hscr : scratch = curScratch ∨ scratch = cmScratch) (g : RecordGhost)
    (rec : SessionRecord (List (BitVec 8)))
    (ot : Option (BitVec 64 × BitVec 64 × OutgoingTripleRatchet (List (BitVec 8))))
    (m : CiphertextMessage) (pcOff src : Nat)
    (hpc : (pcOff, src) = (0xc20, 0x970) ∨ (pcOff, src) = (0xe28, 0x990) ∨
      (pcOff, src) = (0xf2c, 0x9b0))
    (hm : TailModel kit st0 ikit ist0 C S uuidTryParse encRecord x answers (.error e) s0 s)
    (hst : SpeStaged A x.ret e [w0, w1, w2, w3, w4, w5] H)
    (hs : EncTailV kit st0 ikit ist0 C ctl uuidTryParse S x answers (encEntry img + BitVec.ofNat 64 pcOff) (tailRegs w0 w1 w2)
      (fun sp => dropRecordSlots A sp scratch g rec ot (some m) (pollWith sp src [w3, w4, w5]) ∗ H)
      R s0 s) :
    SegExit kit st0 ikit ist0 C ctl uuidTryParse S encRecord abs x R s0 s (fun _ => False) := by
  exact ProtocolErr.tailStoreHookErr env.loads hpc hm hs fun s' hm' hs' =>
    tailCmDrop_ok env x R s0 s' answers e w0 w1 w2 w3 w4 w5 H scratch hscr g rec ot m hm' hst hs'

end CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails
