/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Main.Callees
public import LibsignalBinary.Proofs.SignalSession.Cli.PublicSpecs

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunCompose

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops

/-! ## Read-Only `.rodata` Borrowing, Slice Extraction, and Spatial Dropping -/

theorem r1b_sepWPp_with_ro {img : Obj.Image} {ext : String → Option (State → State)}
    {ret : BitVec 64} {s : State} {ro P : SepProp} {Q Qp : State → SepProp → Prop}
    {oom : State → SepProp}
    (hinv : ImgCallInv img s)
    (hro : ∀ {m : Memory} {R : SepProp}, img.RoDataLoaded m → (m ⊨ R) → (m ⊨ ro ∗ R))
    (hk : SepWPp (mProg img ext) ret s (ro ∗ P) Q Qp oom) :
    SepWPp (mProg img ext) ret s P Q Qp oom := by
  intro R hm hL
  exact hk R (by simpa only [sepConj_assoc] using hro hinv.1.roData hm) hL

theorem r1b_sepWPp_drop_left {prog : Program} {ret : BitVec 64} {s : State}
    {D P : SepProp} {Q Qp : State → SepProp → Prop} {oom : State → SepProp}
    (hk : SepWPp prog ret s P Q Qp oom) :
    SepWPp prog ret s (D ∗ P) Q Qp oom := by
  intro R hm hL
  have hm' : s.mem ⊨ emp ∗ D ∗ (P ∗ R) := by
    simpa only [emp_sepConj, sepConj_assoc] using hm
  exact hk R (by simpa only [emp_sepConj] using Satisfies.drop_mid hm') hL

def r1b_pairMem (p : Nat × Nat) : List (Nat × Nat) → Bool
  | [] => false
  | q :: qs => (Nat.beq p.1 q.1 && Nat.beq p.2 q.2) || r1b_pairMem p qs

theorem r1b_pairMem_sound {p : Nat × Nat} {l : List (Nat × Nat)}
    (h : r1b_pairMem p l = true) : p ∈ l := by
  rcases p with ⟨p1, p2⟩
  induction l with
  | nil => cases h
  | cons q qs ih =>
    rcases q with ⟨q1, q2⟩
    simp only [r1b_pairMem, Bool.or_eq_true, Bool.and_eq_true, Nat.beq_eq] at h
    rcases h with ⟨rfl, rfl⟩ | htl
    · exact List.Mem.head _
    · exact List.Mem.tail _ (ih htl)

noncomputable def r1b_roSec (xref : Nat) : Nat × Nat :=
  (libsignalSessionImage.roData.find? (fun p => Nat.ble p.1 xref && Nat.blt xref (p.1 + p.2))).getD (0, 0)

theorem r1b_ro_xref {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    (xref : Nat) (lit : String)
    (hsec : r1b_pairMem (r1b_roSec xref) libsignalSessionImage.roData = true)
    (hoff : Nat.ble libsignalSessionImage.dataOff (r1b_roSec xref).1 = true)
    (hlen : Nat.ble ((r1b_roSec xref).2 + 1) (2 ^ 32) = true)
    (hdlen : Nat.ble ((r1b_roSec xref).1 - libsignalSessionImage.dataOff + (r1b_roSec xref).2)
        libsignalSessionImage.data.length = true)
    (hrel : libsignalSessionImage.relocs.all
        (fun r => decide
          (r.off + r.width ≤ (r1b_roSec xref).1 - libsignalSessionImage.dataOff ∨
            (r1b_roSec xref).1 - libsignalSessionImage.dataOff + (r1b_roSec xref).2 ≤ r.off)) =
        true)
    (hle : Nat.ble (r1b_roSec xref).1 xref = true)
    (hfit : Nat.ble ((xref - (r1b_roSec xref).1) + (utf8 lit).length) (r1b_roSec xref).2 = true)
    (heq :
      (libsignalSessionImage.data.drop
          ((r1b_roSec xref).1 - libsignalSessionImage.dataOff)).take (r1b_roSec xref).2 =
        (libsignalSessionImage.data.drop
            ((r1b_roSec xref).1 - libsignalSessionImage.dataOff)).take
            (xref - (r1b_roSec xref).1) ++
          utf8 lit ++
          (libsignalSessionImage.data.drop
            ((r1b_roSec xref).1 - libsignalSessionImage.dataOff +
              (xref - (r1b_roSec xref).1) + (utf8 lit).length)).take
            ((r1b_roSec xref).2 - (xref - (r1b_roSec xref).1) - (utf8 lit).length))
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + BitVec.ofNat 64 xref) ↦ᵣ utf8 lit) ∗ P := by
  let secOff := (r1b_roSec xref).1
  let secLen := (r1b_roSec xref).2
  let preLen := xref - secOff
  have hsec' : (secOff, secLen) ∈ libsignalSessionImage.roData := r1b_pairMem_sound hsec
  have hoff' : libsignalSessionImage.dataOff ≤ secOff := Nat.le_of_ble_eq_true hoff
  have hlen' : secLen < 2 ^ 32 := Nat.lt_of_succ_le (Nat.le_of_ble_eq_true hlen)
  have hdlen' : secOff - libsignalSessionImage.dataOff + secLen ≤
      libsignalSessionImage.data.length := Nat.le_of_ble_eq_true hdlen
  have hle' : secOff ≤ xref := Nat.le_of_ble_eq_true hle
  have hfit' : preLen + (utf8 lit).length ≤ secLen := Nat.le_of_ble_eq_true hfit
  have hfull := ProofLib.Satisfies.of_rodata_loads himg rfl
    (secOff := secOff) (secLen := secLen)
    hsec' hoff' hlen' hdlen' hrel hro hP
  rw [heq, List.append_assoc, pointsToBytesRO_append] at hfull
  have hpre_len :
      ((libsignalSessionImage.data.drop (secOff - libsignalSessionImage.dataOff)).take
        preLen).length = preLen :=
    List.length_take_of_le (by rw [List.length_drop]; omega)
  have hxref : secOff + preLen = xref := by omega
  rw [hpre_len, pointsToBytesRO_append, BitVec.add_assoc, ← BitVec.ofNat_add, hxref] at hfull
  have h1 : m ⊨ emp ∗
      ((img.base + BitVec.ofNat 64 secOff) ↦ᵣ
        (libsignalSessionImage.data.drop (secOff - libsignalSessionImage.dataOff)).take preLen) ∗
      (((img.base + BitVec.ofNat 64 xref) ↦ᵣ utf8 lit) ∗
        (((img.base + BitVec.ofNat 64 xref + BitVec.ofNat 64 (utf8 lit).length) ↦ᵣ
          (libsignalSessionImage.data.drop
            (secOff - libsignalSessionImage.dataOff + preLen + (utf8 lit).length)).take
            (secLen - preLen - (utf8 lit).length)) ∗ P)) := by
    simpa only [emp_sepConj, sepConj_assoc] using hfull
  have h2 : m ⊨ ((img.base + BitVec.ofNat 64 xref) ↦ᵣ utf8 lit) ∗
      (((img.base + BitVec.ofNat 64 xref + BitVec.ofNat 64 (utf8 lit).length) ↦ᵣ
        (libsignalSessionImage.data.drop
          (secOff - libsignalSessionImage.dataOff + preLen + (utf8 lit).length)).take
          (secLen - preLen - (utf8 lit).length)) ∗ P) := by
    simpa only [emp_sepConj] using Satisfies.drop_mid h1
  exact Satisfies.drop_mid h2

/-! ## `ownedBytes` Borrow/Rejoin and Subslice Splitting Lemmas -/

def r1b_ownedRest (A : RustAlloc) (cap ptr : BitVec 64) (lenNat : Nat) : SepProp :=
  if cap = 0 then emp
  else A.live ptr cap.toNat 1 ∗
    memRegion (ptr + BitVec.ofNat 64 lenNat) (cap.toNat - lenNat)

theorem r1b_ownedBytes_borrow (A : RustAlloc) (cap ptr len : BitVec 64) (bs : List (BitVec 8)) :
    ownedBytes A cap ptr len bs =
      ⌜len = BitVec.ofNat 64 bs.length ∧ bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (ptr ↦ₛ bs) ∗ r1b_ownedRest A cap ptr bs.length := by
  dsimp only [ownedBytes, r1b_ownedRest]
  apply sepProp_eq_of_entails
  · apply Entails.pure_left
    rintro ⟨hlen, hle, hlt, hne⟩
    refine Entails.pure_right ⟨hlen, hle, hlt, hne⟩ ?_
    by_cases hc : cap = 0
    · subst hc
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
      subst hbs
      simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
      exact Entails.refl _
    · simp only [hc, ↓reduceIte]
      exact Entails.of_eq (by ac_rfl)
  · apply Entails.pure_left
    rintro ⟨hlen, hle, hlt, hne⟩
    refine Entails.pure_right ⟨hlen, hle, hlt, hne⟩ ?_
    by_cases hc : cap = 0
    · subst hc
      have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hle)
      subst hbs
      simp only [↓reduceIte, pointsToBytes_nil, emp_sepConj]
      exact Entails.refl _
    · simp only [hc, ↓reduceIte]
      exact Entails.of_eq (by ac_rfl)

theorem r1b_ownedBytes_rejoin (A : RustAlloc) (cap ptr : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hlt : cap.toNat < 2 ^ 63) (hne : ptr ≠ 0) :
    ((ptr ↦ₛ bs) ∗ r1b_ownedRest A cap ptr bs.length) ⊢
      ownedBytes A cap ptr (BitVec.ofNat 64 bs.length) bs := by
  rw [r1b_ownedBytes_borrow]
  exact Entails.pure_right ⟨rfl, hle, hlt, hne⟩ (Entails.refl _)

theorem r1b_splitSigned_bytes {file : List (BitVec 8)} {id : BitVec 32}
    {key sig : List (BitVec 8)}
    (h : splitSigned file = some (id, key, sig)) :
    file = file.take 4 ++ key ++ sig ∧
      (file.take 4).length = 4 ∧
      sig.length = 64 ∧
      file.length = 4 + key.length + 64 := by
  unfold splitSigned at h
  cases file with
  | nil => simp [splitId] at h
  | cons b0 r0 =>
    cases r0 with
    | nil => simp [splitId] at h
    | cons b1 r1 =>
      cases r1 with
      | nil => simp [splitId] at h
      | cons b2 r2 =>
        cases r2 with
        | nil => simp [splitId] at h
        | cons b3 rest =>
          simp only [splitId] at h
          split at h
          · rename_i hge
            injection h with htuple
            rcases Prod.mk.inj htuple with ⟨rfl, hpair⟩
            rcases Prod.mk.inj hpair with ⟨rfl, rfl⟩
            have hcat : rest.take (rest.length - 64) ++ rest.drop (rest.length - 64) = rest :=
              List.take_append_drop (rest.length - 64) rest
            have hsig : (rest.drop (rest.length - 64)).length = 64 := by
              rw [List.length_drop]; omega
            have hkey : (rest.take (rest.length - 64)).length = rest.length - 64 :=
              List.length_take_of_le (by omega)
            refine ⟨?_, rfl, hsig, ?_⟩
            · simp only [List.take, List.append_assoc, hcat]; rfl
            · simp only [List.length_cons, hkey]; omega
          · simp at h

theorem r1b_splitSigned_slice_eq {ptr : BitVec 64} {file key sig : List (BitVec 8)}
    (heq : file = file.take 4 ++ key ++ sig)
    (ht4 : (file.take 4).length = 4) :
    (ptr ↦ₛ file) =
      (ptr ↦ₛ file.take 4) ∗
        ((ptr + 4#64) ↦ₛ key) ∗
        ((ptr + 4#64 + BitVec.ofNat 64 key.length) ↦ₛ sig) := by
  conv_lhs => rw [heq]
  rw [List.append_assoc, pointsToBytes_append, ht4, pointsToBytes_append]

theorem r1b_splitId_bytes {file : List (BitVec 8)} {id : BitVec 32} {key : List (BitVec 8)}
    (h : splitId file = some (id, key)) :
    file = file.take 4 ++ key ∧
      (file.take 4).length = 4 ∧
      file.length = 4 + key.length := by
  cases file with
  | nil => simp [splitId] at h
  | cons b0 r0 =>
    cases r0 with
    | nil => simp [splitId] at h
    | cons b1 r1 =>
      cases r1 with
      | nil => simp [splitId] at h
      | cons b2 r2 =>
        cases r2 with
        | nil => simp [splitId] at h
        | cons b3 rest =>
          simp only [splitId, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, by simp only [List.length_cons]; omega⟩

theorem r1b_splitId_slice_eq {ptr : BitVec 64} {file key : List (BitVec 8)}
    (heq : file = file.take 4 ++ key)
    (ht4 : (file.take 4).length = 4) :
    (ptr ↦ₛ file) =
      (ptr ↦ₛ file.take 4) ∗ ((ptr + 4#64) ↦ₛ key) := by
  conv_lhs => rw [heq]
  rw [pointsToBytes_append, ht4]

theorem r1b_u32_of_4bytes (ptr : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    (ptr ↦ₛ [b0, b1, b2, b3]) = (ptr ↦₃₂ ofLe32 b0 b1 b2 b3) := by
  rw [pointsTo32_eq_pointsToBytes]
  congr 1
  unfold unpack32 ofLe32
  have h0 : (b3 ++ b2 ++ b1 ++ b0).extractLsb' 0 8 = b0 := by bv_bits
  have h1 : (b3 ++ b2 ++ b1 ++ b0).extractLsb' 8 8 = b1 := by bv_bits
  have h2 : (b3 ++ b2 ++ b1 ++ b0).extractLsb' 16 8 = b2 := by bv_bits
  have h3 : (b3 ++ b2 ++ b1 ++ b0).extractLsb' 24 8 = b3 := by bv_bits
  rw [h0, h1, h2, h3]

end CryptoVerification.SignalSession.Cli.RunCompose
