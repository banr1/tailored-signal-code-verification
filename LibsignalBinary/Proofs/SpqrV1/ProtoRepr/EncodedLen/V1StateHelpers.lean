/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.LeavesChunked
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.FetchChunkedV1
import ProofLib.SepLogic.WPp

/-!
# Prologue, Shared Tails, and Single-Callee Branches for `V1State::encoded_len`

Proves option-niche splits, the shared epilogue tails (`+524` and `+1580`), single-callee variant
branches (`keysUnsampled`, `headerSent`, `ct1Sampled`), and jump-table prologue stepping for
`V1State::encoded_len [local#1, #2]` (`0x3902c`, `0x67df8`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.ProtoRepr

open Arm64 Arm64.Obj ProofLib CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 EncodedLen

local notation "tripleRatchetProgAtExt" => CryptoVerification.LibsignalTripleRatchet.contractProg

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## 1. Entry Membership and Instruction Fetch Macro -/

/-- Entry-point membership for the two copies of `V1State::encoded_len` (`0x3902c`, `0x67df8`). -/
def IsV1StateEntry (b : BitVec 64) (abs : String → Option (State → State))
    (entry : BitVec 64) : Prop :=
  (tripleRatchetProgAtExt b abs).fnAddr v1StateEncodedLenLocal1Name = entry ∨
  (tripleRatchetProgAtExt b abs).fnAddr v1StateEncodedLenLocal2Name = entry

open Lean Elab Tactic in
elab "v1State_fetches_range " hfn:ident kStart:num kEnd:num : tactic => do
  let offs := #[0x39110, 0x62a00]
  let fnOffs := #[
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x39110,
    mkIdent `CryptoVerification.libsignalSessionCode_fnOff_0x62a00
  ]
  let skip : Array Nat := #[
    56, 60,
    124, 188, 260, 324, 376, 408, 472, 520, 600, 664,
    756, 820, 912, 976, 1024, 1076, 1140, 1192, 1256,
    1332, 1336, 1340, 1372, 1376, 1380, 1412, 1416, 1420,
    1452, 1456, 1460, 1492, 1496, 1500, 1532, 1536, 1540,
    1556, 1560, 1564, 1620, 1624, 1628, 1632, 1636, 1640
  ]
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  for i in [kStart / 4 : kEnd / 4] do
    let k := 4 * i
    if !skip.contains k then
      let decs := offs.map fun off =>
        mkIdent (`CryptoVerification.SpqrV1.ProtoRepr |>.str
          s!"spqrV1StateBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
      let d0 := decs[0]!; let d1 := decs[1]!
      let f0 := fnOffs[0]!; let f1 := fnOffs[1]!
      let kq := Syntax.mkNumLit (toString k)
      if k == 0 then
        let pf0 := mkIdent (`CryptoVerification.blkPC_177_rebase_fetch_base)
        let pf1 := mkIdent (`CryptoVerification.blkPC_405_rebase_fetch_base)
        evalTactic (← `(tactic|
          have := dualBlockP2_fetch_entry $hfn
            (fun b H => $fetchEntry (b := b) (H := H) $f0 (by decide) $d0)
            (fun b H => $fetchEntry (b := b) (H := H) $f1 (by decide) $d1)
            (fun [LibsignalPlacement] H => $pf0 _ H)
            (fun [LibsignalPlacement] H => $pf1 _ H)))
      else
        let kHex := String.ofList (Nat.toDigits 16 k)
        let pf0 := mkIdent (`CryptoVerification |>.str s!"blkPC_177_rebase_fetch_0x{kHex}")
        let pf1 := mkIdent (`CryptoVerification |>.str s!"blkPC_405_rebase_fetch_0x{kHex}")
        evalTactic (← `(tactic|
          have := dualBlockP2_fetch_add $hfn (k := $kq)
            (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f0 (by decide) $d0)
            (fun b H => $fetchAdd (b := b) (H := H) (k := $kq) $f1 (by decide) $d1)
            (fun [LibsignalPlacement] H => $pf0 _ H)
            (fun [LibsignalPlacement] H => $pf1 _ H)))

/-! ## 2. Niche Arithmetic & Stack Split Helpers -/

@[simp] theorem noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := by decide

@[simp] theorem noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := by decide

@[simp] theorem noneCap_add_two_beq_zero :
    (0xffffffffffffffff#64 + 2#64 == 0#64) = false := by decide

@[simp] theorem noneCap_add_two_bne_zero :
    (0xffffffffffffffff#64 + 2#64 != 0#64) = true := by decide

theorem cap_add_two_beq_zero_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 == 0#64) = false := by
  have h1 : cap < 0x8000000000000000#64 := (BitVec.lt_def).2 h
  clear h; bv_bits

theorem cap_add_two_bne_zero_true {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    (cap + 2#64 != 0#64) = true := by
  rw [bne_iff_ne, ne_eq, ← beq_iff_eq, cap_add_two_beq_zero_false h]
  decide

theorem ult_of_lt_of_fit {vlen tot : Nat} (hlt : vlen < tot) (htot : tot < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 vlen) (BitVec.ofNat 64 tot) = true := by
  rw [BitVec.ult_eq_decide, decide_eq_true_eq]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : vlen < 2 ^ 64), Nat.mod_eq_of_lt htot]
  omega

theorem stackAt_v1StateEncodedLen_eq (sp : BitVec 64) :
    stackAt sp v1StateEncodedLenStack =
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
        stackAt (sp - 32#64) chunkedEncodedLenStack := by
  change memRegion (sp - BitVec.ofNat 64 80) 80 =
    ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
      ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) ∗
      memRegion (sp - 32#64 - BitVec.ofNat 64 48) 48
  have hsplit := ProofLib.memRegion_split_le (sp - BitVec.ofNat 64 80) 48 80
    (by decide) (by decide)
  have haddr1 : sp - BitVec.ofNat 64 80 = sp - 32#64 - BitVec.ofNat 64 48 := by bv_bits
  have haddr2 : sp - BitVec.ofNat 64 80 + BitVec.ofNat 64 48 = sp - 32#64 := by bv_bits
  rw [hsplit, haddr2, haddr1]
  have hcells : memRegion (sp - 32#64) (80 - 48) =
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64, ∃∗ v8 : BitVec 64,
        ((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
        ((sp - 16#64) ↦₆₄ v16) ∗ ((sp - 8#64) ↦₆₄ v8) := by
    change memRegion (sp - 32#64) (8 * 4) = _
    rw [memRegion_cells (sp - 32#64) 4 (by decide)]
    cells_unfold
  rw [hcells]
  simp only [sepExists_sepConj_right]
  apply sepProp_eq_of_entails
  · exact Entails.sepExists_elim fun v32 => Entails.sepExists_elim fun v24 =>
      Entails.sepExists_elim fun v16 => Entails.sepExists_elim fun v8 =>
      Entails.sepExists_right v32 (Entails.sepExists_right v24
        (Entails.sepExists_right v16 (Entails.sepExists_right v8 (Entails.of_eq (by ac_rfl)))))
  · exact Entails.sepExists_elim fun v32 => Entails.sepExists_elim fun v24 =>
      Entails.sepExists_elim fun v16 => Entails.sepExists_elim fun v8 =>
      Entails.sepExists_right v32 (Entails.sepExists_right v24
        (Entails.sepExists_right v16 (Entails.sepExists_right v8 (Entails.of_eq (by ac_rfl)))))

theorem stackAt_chunked_eq_poly (sp : BitVec 64) :
    stackAt sp chunkedEncodedLenStack =
      stackAt sp polyEncodedLenStack ∗ memRegion (sp - 48#64) 32 := by
  change memRegion (sp - BitVec.ofNat 64 48) 48 =
    memRegion (sp - BitVec.ofNat 64 16) 16 ∗ memRegion (sp - 48#64) 32
  have hsplit := ProofLib.memRegion_split_le (sp - BitVec.ofNat 64 48) 32 48
    (by decide) (by decide)
  have haddr1 : sp - BitVec.ofNat 64 48 = sp - 48#64 := rfl
  have haddr2 : sp - 48#64 + BitVec.ofNat 64 32 = sp - BitVec.ofNat 64 16 := by bv_bits
  rw [hsplit, haddr1, haddr2]
  ac_rfl

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  zeroExtend64_beq_zero32 ofNat_countLeadingZeros_64 ofNat_countLeadingZeros_32
  ProofLib.truncate32_ofNat64 hwVarintLen_eq_ofNat_varintLen_norm
  hwVarintLen_bvShift_eq_ofNat_varintLen_norm
  noneCap_add_one_beq_zero noneCap_add_one_bne_zero
  noneCap2_add_two_beq_zero noneCap2_add_two_bne_zero
  noneCap_add_two_beq_zero noneCap_add_two_bne_zero
  zext64_truncate32 ule_zero_64 ult_zero_64 ule_self_64 ult_self_64

/-! ## 3. Option Cap / Rest Splits for `Unchunked` Sub-Messages -/

/-- First word (`[p]`) of `optKeysUnsampledPBPinnedAt` / `optNoHeaderReceivedPBPinnedAt` / `optCt2SentPBPinnedAt`:
    `noneCap2` when `none`, `optAuthCap g auth` when `some`. -/
def optUnchunked2Cap (g : Unchunked2PBGhost) : Option (Option AuthenticatorPB) → BitVec 64
  | none => noneCap2
  | some auth => optAuthCap g auth

def optUnchunked2Rest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64) :
    Option (BitVec 64 × Option AuthenticatorPB) → SepProp
  | none => memRegion (p + 8#64) 48
  | some (epoch, auth) =>
    optAuthPayload A g p auth ∗ ((p + 48#64) ↦₆₄ epoch)

theorem optUnchunked2Rest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option (BitVec 64 × Option AuthenticatorPB)} {R : SepProp} {m : Memory}
    (hm : m ⊨ optUnchunked2Rest A g p opt ∗ R) :
    (optUnchunked2Cap g (opt.map Prod.snd) + 2#64 == 0#64) = !opt.isSome ∧
      (optUnchunked2Cap g (opt.map Prod.snd) + 2#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optUnchunked2Cap, noneCap2, arm64_norm]
  | some pair =>
    rcases pair with ⟨epoch, auth⟩
    cases auth with
    | none =>
      simp only [Option.map_some, Option.isSome_some, Bool.not_true, optUnchunked2Cap, optAuthCap]
      exact ⟨by decide, by decide⟩
    | some a =>
      simp only [optUnchunked2Rest, optAuthPayload] at hm
      have hbuf : m ⊨ vecU8Buf A g.rootKey.cap g.rootKey.ptr a.rootKey ∗
          (((p + 8#64) ↦₆₄ g.rootKey.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 a.rootKey.length) ∗
           ((p + 24#64) ↦₆₄ g.macKey.cap) ∗ ((p + 32#64) ↦₆₄ g.macKey.ptr) ∗
           ((p + 40#64) ↦₆₄ BitVec.ofNat 64 a.macKey.length) ∗
           vecU8Buf A g.macKey.cap g.macKey.ptr a.macKey ∗
           ((p + 48#64) ↦₆₄ epoch) ∗ R) := by
        convert hm using 1; ac_rfl
      have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
      simp only [Option.map_some, Option.isSome_some, Bool.not_true, optUnchunked2Cap, optAuthCap]
      exact ⟨cap_add_two_beq_zero_false hcap, cap_add_two_bne_zero_true hcap⟩

def optKeysUnsampledCap (g : Unchunked2PBGhost) (opt : Option V1State.Unchunked.KeysUnsampled) : BitVec 64 :=
  optUnchunked2Cap g (opt.map fun u => u.auth)

def optKeysUnsampledRest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) : SepProp :=
  optUnchunked2Rest A g p (opt.map fun u => (u.epoch, u.auth))

theorem optKeysUnsampledPBPinnedAt_eq (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.KeysUnsampled) :
    optKeysUnsampledPBPinnedAt A g p opt =
      (p ↦₆₄ optKeysUnsampledCap g opt) ∗ optKeysUnsampledRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optKeysUnsampledPBPinnedAt, keysUnsampledPBPinnedAt,
      unchunked2PinnedAt_eq_unpacked, unchunked2Unpacked,
      optKeysUnsampledCap, optKeysUnsampledRest, optUnchunked2Cap, optUnchunked2Rest,
      Option.map_some, sepConj_assoc]

theorem optKeysUnsampledRest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.KeysUnsampled} {R : SepProp} {m : Memory}
    (hm : m ⊨ optKeysUnsampledRest A g p opt ∗ R) :
    (optKeysUnsampledCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optKeysUnsampledCap g opt + 2#64 != 0#64) = opt.isSome := by
  have h := optUnchunked2Rest_cap_bounds hm
  cases opt <;> simpa [optKeysUnsampledCap] using h

def optNoHeaderReceivedCap (g : Unchunked2PBGhost) (opt : Option V1State.Unchunked.NoHeaderReceived) : BitVec 64 :=
  optUnchunked2Cap g (opt.map fun u => u.auth)

def optNoHeaderReceivedRest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) : SepProp :=
  optUnchunked2Rest A g p (opt.map fun u => (u.epoch, u.auth))

theorem optNoHeaderReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.NoHeaderReceived) :
    optNoHeaderReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optNoHeaderReceivedCap g opt) ∗ optNoHeaderReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optNoHeaderReceivedPBPinnedAt, noHeaderReceivedPBPinnedAt,
      unchunked2PinnedAt_eq_unpacked, unchunked2Unpacked,
      optNoHeaderReceivedCap, optNoHeaderReceivedRest, optUnchunked2Cap, optUnchunked2Rest,
      Option.map_some, sepConj_assoc]

theorem optNoHeaderReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.NoHeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optNoHeaderReceivedRest A g p opt ∗ R) :
    (optNoHeaderReceivedCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optNoHeaderReceivedCap g opt + 2#64 != 0#64) = opt.isSome := by
  have h := optUnchunked2Rest_cap_bounds hm
  cases opt <;> simpa [optNoHeaderReceivedCap] using h

def optCt2SentCap (g : Unchunked2PBGhost) (opt : Option V1State.Unchunked.Ct2Sent) : BitVec 64 :=
  optUnchunked2Cap g (opt.map fun u => u.auth)

def optCt2SentRest (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) : SepProp :=
  optUnchunked2Rest A g p (opt.map fun u => (u.epoch, u.auth))

theorem optCt2SentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked2PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct2Sent) :
    optCt2SentPBPinnedAt A g p opt =
      (p ↦₆₄ optCt2SentCap g opt) ∗ optCt2SentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optCt2SentPBPinnedAt, ct2SentPBPinnedAt,
      unchunked2PinnedAt_eq_unpacked, unchunked2Unpacked,
      optCt2SentCap, optCt2SentRest, optUnchunked2Cap, optUnchunked2Rest,
      Option.map_some, sepConj_assoc]

theorem optCt2SentRest_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct2Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt2SentRest A g p opt ∗ R) :
    (optCt2SentCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optCt2SentCap g opt + 2#64 != 0#64) = opt.isSome := by
  have h := optUnchunked2Rest_cap_bounds hm
  cases opt <;> simpa [optCt2SentCap] using h

/-- First word (`[p]`) of `optHeaderReceivedPBPinnedAt`: `noneCap` when `none`, `g.f3.cap` when `some`. -/
def optHeaderReceivedCap (g : Unchunked3PBGhost) : Option V1State.Unchunked.HeaderReceived → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optHeaderReceivedRest (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.HeaderReceived → SepProp
  | none => memRegion (p + 8#64) 72
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
      ((p + 0x48#64) ↦₆₄ u.epoch)

theorem optHeaderReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked3PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderReceived) :
    optHeaderReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optHeaderReceivedCap g opt) ∗ optHeaderReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optHeaderReceivedPBPinnedAt, headerReceivedPBPinnedAt, unchunked3PinnedAt,
      optHeaderReceivedCap, optHeaderReceivedRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optHeaderReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderReceivedRest A g p opt ∗ R) :
    (optHeaderReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optHeaderReceivedCap, arm64_norm]
  | some u =>
    simp only [optHeaderReceivedRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x18#64) u.auth ∗
         ((p + 0x48#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

/-- First word (`[p]`) of `optHeaderSentPBPinnedAt`: `noneCap` when `none`, `g.f3.cap` when `some`. -/
def optHeaderSentCap (g : Unchunked4PBGhost) : Option V1State.Unchunked.HeaderSent → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optHeaderSentRest (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.HeaderSent → SepProp
  | none => memRegion (p + 8#64) 96
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.ek.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.ek ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.dk ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
      ((p + 0x60#64) ↦₆₄ u.epoch)

theorem optHeaderSentPBPinnedAt_eq (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.HeaderSent) :
    optHeaderSentPBPinnedAt A g p opt =
      (p ↦₆₄ optHeaderSentCap g opt) ∗ optHeaderSentRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optHeaderSentPBPinnedAt, headerSentPBPinnedAt, unchunked4PinnedAt,
      optHeaderSentCap, optHeaderSentRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optHeaderSentRest_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderSentRest A g p opt ∗ R) :
    (optHeaderSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optHeaderSentCap, arm64_norm]
  | some u =>
    simp only [optHeaderSentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.ek ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.ek.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.dk ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
         ((p + 0x60#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

/-- First word (`[p]`) of `optEkSentCt1ReceivedPBPinnedAt`: `noneCap` when `none`, `g.f3.cap` when `some`. -/
def optEkSentCt1ReceivedCap (g : Unchunked4PBGhost) : Option V1State.Unchunked.EkSentCt1Received → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optEkSentCt1ReceivedRest (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.EkSentCt1Received → SepProp
  | none => memRegion (p + 8#64) 96
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ct1 ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
      ((p + 0x60#64) ↦₆₄ u.epoch)

theorem optEkSentCt1ReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked4PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.EkSentCt1Received) :
    optEkSentCt1ReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optEkSentCt1ReceivedCap g opt) ∗ optEkSentCt1ReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optEkSentCt1ReceivedPBPinnedAt, ekSentCt1ReceivedPBPinnedAt, unchunked4PinnedAt,
      optEkSentCt1ReceivedCap, optEkSentCt1ReceivedRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optEkSentCt1ReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSentCt1Received} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentCt1ReceivedRest A g p opt ∗ R) :
    (optEkSentCt1ReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEkSentCt1ReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optEkSentCt1ReceivedCap, arm64_norm]
  | some u =>
    simp only [optEkSentCt1ReceivedRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.dk ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.dk.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x30#64) u.auth ∗
         ((p + 0x60#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

/-- First word (`[p]`) of `optCt1SentEkReceivedPBPinnedAt`: `noneCap` when `none`, `g.f3.cap` when `some`. -/
def optCt1SentEkReceivedCap (g : Unchunked5PBGhost) : Option V1State.Unchunked.Ct1SentEkReceived → BitVec 64
  | none => noneCap
  | some _ => g.f3.cap

def optCt1SentEkReceivedRest (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64) :
    Option V1State.Unchunked.Ct1SentEkReceived → SepProp
  | none => memRegion (p + 8#64) 120
  | some u =>
    ((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.es.length) ∗
      vecU8Buf A g.f3.cap g.f3.ptr u.es ∗
      vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ek ∗
      vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
      optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
      ((p + 0x78#64) ↦₆₄ u.epoch)

theorem optCt1SentEkReceivedPBPinnedAt_eq (A : RustAlloc) (g : Unchunked5PBGhost) (p : BitVec 64)
    (opt : Option V1State.Unchunked.Ct1SentEkReceived) :
    optCt1SentEkReceivedPBPinnedAt A g p opt =
      (p ↦₆₄ optCt1SentEkReceivedCap g opt) ∗ optCt1SentEkReceivedRest A g p opt := by
  cases opt with
  | none => rfl
  | some u =>
    simp only [optCt1SentEkReceivedPBPinnedAt, ct1SentEkReceivedPBPinnedAt, unchunked5PinnedAt,
      optCt1SentEkReceivedCap, optCt1SentEkReceivedRest, vecU8At_eq_header_sep_buf A p, vecHeader, sepConj_assoc]

theorem optCt1SentEkReceivedRest_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1SentEkReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentEkReceivedRest A g p opt ∗ R) :
    (optCt1SentEkReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentEkReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  cases opt with
  | none => simp [optCt1SentEkReceivedCap, arm64_norm]
  | some u =>
    simp only [optCt1SentEkReceivedRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.es ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.es.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.ek ∗
         vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
         ((p + 0x78#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_one_beq_zero_false hcap, cap_add_one_bne_zero_true hcap⟩

theorem cap_xor_top_ult_11_false {cap : BitVec 64} (h : cap.toNat < 2 ^ 63) :
    ((cap ^^^ 0x8000000000000000#64).ult 11#64) = false := by
  have hlt : cap < 0x8000000000000000#64 := (BitVec.lt_def).2 h
  clear h; bv_bits

theorem optCt1SentRest_disc_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentRest A g p opt ∗ R) :
    (optCt1SentCap g opt + 2#64 == 0#64) = false ∧
      (optCt1SentCap g opt + 2#64 != 0#64) = true ∧
      ((optCt1SentCap g opt ^^^ 0x8000000000000000#64).ult 11#64) = false := by
  cases opt with
  | none => simp [optCt1SentCap, noneCap, arm64_norm]
  | some u =>
    simp only [optCt1SentRest] at hm
    have hbuf : m ⊨ vecU8Buf A g.f3.cap g.f3.ptr u.hdr ∗
        (((p + 8#64) ↦₆₄ g.f3.ptr) ∗ ((p + 16#64) ↦₆₄ BitVec.ofNat 64 u.hdr.length) ∗
         vecU8At A (p + 0x18#64) g.f4.cap g.f4.ptr u.es ∗
         vecU8At A (p + 0x30#64) g.f5.cap g.f5.ptr u.ct1 ∗
         optAuthenticatorPBPinnedAt A g.auth (p + 0x48#64) u.auth ∗
         ((p + 0x78#64) ↦₆₄ u.epoch) ∗ R) := by
      convert hm using 1; ac_rfl
    have ⟨_, hcap⟩ := vecU8Buf_bounds hbuf
    exact ⟨cap_add_two_beq_zero_false hcap, cap_add_two_bne_zero_true hcap,
      cap_xor_top_ult_11_false hcap⟩

/-! ## 4. Shared Tails (`+524..+572` and `+1580..+1616 -> +564..+572`) -/

/-- Direct epilogue at `+524` (`0x20c`): given `X0 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)`
    and `v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64`, computes `1 + varintLen + len` in `X0`,
    restores `x19, fp, lr`, and returns to `s0.readReg64 .lr`. -/
theorem step_v1State_tail_524 (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (sp : BitVec 64) (is : V1State.InnerState)
    (hfit : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 524#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some is⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 524 576
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have houter_eq := bv_optMsgField_some (inner := v1StateInnerPayloadEncodedLen is)
    (tot := v1StatePBEncodedLen ⟨some is⟩) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)) <
      v1StatePBEncodedLen ⟨some is⟩ := by
    simp only [v1StatePBEncodedLen]; omega
  have ⟨hule_out, hule_out_rev, hult_out, hsub_out, hbeq_out⟩ :=
    cmp_ls_false_of_lt hvlen_lt hfit
  have hult_out_fwd := ult_of_lt_of_fit hvlen_lt hfit
  apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpF.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-- Shared outer-varint + epilogue tail at `+1580` (`0x62c`): given
    `X8 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)` and
    `v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64`, computes `1 + varintLen + len` in `X0`,
    branches `HI` to `+564`, restores `x19, fp, lr`, and returns to `s0.readReg64 .lr`. -/
theorem step_v1State_tail_1580 (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (sp : BitVec 64) (is : V1State.InnerState)
    (hfit : v1StatePBEncodedLen ⟨some is⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 1580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is))
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some is⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 1580 1620
  v1State_fetches_range hfn 564 576
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have houter_eq := bv_optMsgField_some (inner := v1StateInnerPayloadEncodedLen is)
    (tot := v1StatePBEncodedLen ⟨some is⟩) rfl
  have hvlen_lt : varintLen (BitVec.ofNat 64 (v1StateInnerPayloadEncodedLen is)) <
      v1StatePBEncodedLen ⟨some is⟩ := by
    simp only [v1StatePBEncodedLen]; omega
  have ⟨hule_out, hule_out_rev, hult_out, hsub_out, hbeq_out⟩ :=
    cmp_ls_false_of_lt hvlen_lt hfit
  have hult_out_fwd := ult_of_lt_of_fit hvlen_lt hfit
  apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpF.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-! ## 5. Single-Callee Variant Branches (`k = 0, 2, 7`) -/

/-- Branch `k = 0` (`keysUnsampled`, `+80`): steps from `entry + 80#64` through `+1580` to `s0.readReg64 .lr`. -/
theorem step_v1State_keysUnsampled (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl : CallPinnedEncLenAtF Φ prog entry 1024
      (keysUnsampledPBPinnedAt A) keysUnsampledPBEncodedLen polyEncodedLenStack)
    (g : Unchunked2PBGhost) (a sp : BitVec 64) (v : V1State.Chunked.KeysUnsampled)
    (hfit : v1StatePBEncodedLen ⟨some (.keysUnsampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 80#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hcap : (optKeysUnsampledCap g v.uc + 2#64 == 0#64) = !v.uc.isSome ∧
            (optKeysUnsampledCap g v.uc + 2#64 != 0#64) = v.uc.isSome)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      optKeysUnsampledPBPinnedAt A g (a + 8#64) v.uc ∗
      stackAt (sp - 32#64) polyEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.keysUnsampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 80 100
  v1State_fetches_range hfn 1028 1072
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  rcases hcap with ⟨hcap_beq, hcap_bne⟩
  subst hP
  cases huc : v.uc with
  | none =>
    simp only [huc, Option.isSome_none, Bool.not_false] at hcap_beq hcap_bne
    rw [optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) none]
    apply SepWPpF.of_sepWP (mid := entry + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) none, ← huc]
    refine step_v1State_tail_1580 Φ prog entry hfn sp (.keysUnsampled v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun]) (by simp [arm64_norm, hsp]) halign
      (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, optKeysUnsampledPBFieldEncodedLen])
      ⟨by simp [arm64_norm, h20], by simp [arm64_norm, h21], by simp [arm64_norm, h22],
       by simp [arm64_norm, h23], by simp [arm64_norm, h24], by simp [arm64_norm, h25],
       by simp [arm64_norm, h26], by simp [arm64_norm, h27], by simp [arm64_norm, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf]) hx0f hcsf
  | some u =>
    simp only [huc, Option.isSome_some, Bool.not_true] at hcap_beq hcap_bne
    have hu_fit : keysUnsampledPBEncodedLen u < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc,
        optKeysUnsampledPBFieldEncodedLen] at hfit
      omega
    have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
      clear *- halign; bv_bits
    rw [optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) (some u)]
    apply SepWPpF.of_sepWP (mid := entry + 1024#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    rw [← optKeysUnsampledPBPinnedAt_eq A g (a + 8#64) (some u), ← huc]
    have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
        optKeysUnsampledPBPinnedAt A g (a + 8#64) v.uc ∗
        stackAt (sp - 32#64) polyEncodedLenStack ∗ F) =
      ((keysUnsampledPBPinnedAt A g (a + 8#64) u ∗
        stackAt (sp - 32#64) polyEncodedLenStack) ∗
        (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
          ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F)) := by
      simp only [huc, optKeysUnsampledPBPinnedAt]; ac_rfl
    apply SepWPpF.congr_pre hP_bl
    refine hbl (s0.readReg64 .lr) g (a + 8#64) (sp - 32#64) u _ _ Q Qp
      (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hu_fit ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
    apply SepWPpF.congr_pre hP_bl.symm
    rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
    have hf_eq := bv_optMsgField_some (inner := keysUnsampledPBEncodedLen u)
      (tot := optKeysUnsampledPBFieldEncodedLen (some u)) rfl
    have htot_fit : optKeysUnsampledPBFieldEncodedLen (some u) < 2 ^ 64 := by
      simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen, huc] at hfit; omega
    have hvlen_lt : varintLen (BitVec.ofNat 64 (keysUnsampledPBEncodedLen u)) <
        optKeysUnsampledPBFieldEncodedLen (some u) := by
      simp only [optKeysUnsampledPBFieldEncodedLen]; omega
    have ⟨hule_f, hule_f_rev, hult_f, hsub_f, hbeq_f⟩ :=
      cmp_ls_false_of_lt hvlen_lt htot_fit
    have hult_f_fwd := ult_of_lt_of_fit hvlen_lt htot_fit
    apply SepWPpF.of_sepWP (mid := entry + 1580#64)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)
    refine step_v1State_tail_1580 Φ prog entry hfn sp (.keysUnsampled v) hfit
      (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
      (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, huc, hf_eq, hx0_1])
      ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
       by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
       by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
       by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
       by simp [arm64_norm, h28_1, h28]⟩
      rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
        hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 2` (`headerSent`, `+372`): steps `ADD X0, X0, #8; BL Chunked.HeaderSent; B +524`
    through `+524..+572` to `s0.readReg64 .lr`. -/
theorem step_v1State_headerSent (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl : CallPinnedEncLenAtF Φ prog entry 376
      (chunkedHeaderSentPBPinnedAt A) chunkedHeaderSentPBEncodedLen chunkedEncodedLenStack)
    (g : ChunkedHeaderSentPBGhost) (a sp : BitVec 64) (v : V1State.Chunked.HeaderSent)
    (hfit : v1StatePBEncodedLen ⟨some (.headerSent v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 372#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedHeaderSentPBPinnedAt A g (a + 8#64) v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.headerSent v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  v1State_fetches_range hfn 372 384
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hv_fit : chunkedHeaderSentPBEncodedLen v < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  apply SepWPpF.of_sepWP (mid := entry + 376#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedHeaderSentPBPinnedAt A g (a + 8#64) v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F) =
    ((chunkedHeaderSentPBPinnedAt A g (a + 8#64) v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F)) := by ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl (s0.readReg64 .lr) g (a + 8#64) (sp - 32#64) v _ _ Q Qp
    (by simp_all) (by simp_all) (by simp_all) hsp_sub_align (by simp_all) hv_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  apply SepWPpF.of_sepWP (mid := entry + 524#64)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  refine step_v1State_tail_524 Φ prog entry hfn sp (.headerSent v) hfit
    (by simp [arm64_norm]) (by simp [arm64_norm, hrun1]) (by simp [arm64_norm, hsp1]) halign
    (by simp [arm64_norm, v1StateInnerPayloadEncodedLen, hx0_1])
    ⟨by simp [arm64_norm, h20_1, h20], by simp [arm64_norm, h21_1, h21],
     by simp [arm64_norm, h22_1, h22], by simp [arm64_norm, h23_1, h23],
     by simp [arm64_norm, h24_1, h24], by simp [arm64_norm, h25_1, h25],
     by simp [arm64_norm, h26_1, h26], by simp [arm64_norm, h27_1, h27],
     by simp [arm64_norm, h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by simp [arm64_norm, htrf, htr1]) hx0f hcsf

/-- Branch `k = 7` (`ct1Sampled`, `+520`): steps `BL Chunked.Ct1Sampled` and falls through
    to `+524..+572`, returning to `s0.readReg64 .lr`. -/
theorem step_v1State_ct1Sampled (Φ : Memory → Prop) [FrozenInv Φ] (prog : Program) (A : RustAlloc)
    (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hbl : CallPinnedEncLenAtF Φ prog entry 520
      (chunkedCt1SampledPBPinnedAt A) chunkedCt1SampledPBEncodedLen chunkedEncodedLenStack)
    (g : ChunkedCt1SampledPBGhost) (a sp : BitVec 64) (v : V1State.Chunked.Ct1Sampled)
    (hfit : v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩ < 2 ^ 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = entry + 520#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp - 32#64)
    (halign : sp &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = a)
    (hcs : s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
           s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
           s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
           s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
           s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedCt1SampledPBPinnedAt A g a v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = sp →
      sf.trace = s.trace →
      sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen ⟨some (.ct1Sampled v)⟩) →
      CalleeSavedPreserved s0 sf →
      Q sf P) :
    SepWPpF Φ prog (s0.readReg64 .lr) s P Q Qp := by
  rcases hcs with ⟨h20, h21, h22, h23, h24, h25, h26, h27, h28⟩
  subst hP
  have hv_fit : chunkedCt1SampledPBEncodedLen v < 2 ^ 64 := by
    simp only [v1StatePBEncodedLen, v1StateInnerPayloadEncodedLen] at hfit; omega
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_bits
  have hP_bl : (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
      ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗
      chunkedCt1SampledPBPinnedAt A g a v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack ∗ F) =
    ((chunkedCt1SampledPBPinnedAt A g a v ∗
      stackAt (sp - 32#64) chunkedEncodedLenStack) ∗
      (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ F)) := by ac_rfl
  apply SepWPpF.congr_pre hP_bl
  refine hbl (s0.readReg64 .lr) g a (sp - 32#64) v s _ Q Qp
    hpc hrun hsp hsp_sub_align hx0 hv_fit ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx0_1 hcs1 hfp1
  apply SepWPpF.congr_pre hP_bl.symm
  rcases hcs1 with ⟨h19_1, h20_1, h21_1, h22_1, h23_1, h24_1, h25_1, h26_1, h27_1, h28_1⟩
  refine step_v1State_tail_524 Φ prog entry hfn sp (.ct1Sampled v) hfit
    hpc1 hrun1 hsp1 halign (by simpa [v1StateInnerPayloadEncodedLen] using hx0_1)
    ⟨by simp [h20_1, h20], by simp [h21_1, h21], by simp [h22_1, h22],
     by simp [h23_1, h23], by simp [h24_1, h24], by simp [h25_1, h25],
     by simp [h26_1, h26], by simp [h27_1, h27], by simp [h28_1, h28]⟩
    rfl fun sf hpcf hrunf hspf htrf hx0f hcsf =>
      hnext sf hpcf hrunf hspf (by rw [htrf, htr1]) hx0f hcsf

/-! ## 6. Jump-Table Decomposition & Option-Cap Bounds -/

def v1StateJumpTableBytesAt (roBase : BitVec 64) : SepProp :=
  (roBase ↦₈ᵣ 0x00#8) ∗ ((roBase + 1#64) ↦₈ᵣ 0x7c#8) ∗
    ((roBase + 2#64) ↦₈ᵣ 0x49#8) ∗ ((roBase + 3#64) ↦₈ᵣ 0x4c#8) ∗
    ((roBase + 4#64) ↦₈ᵣ 0x05#8) ∗ ((roBase + 5#64) ↦₈ᵣ 0x9e#8) ∗
    ((roBase + 6#64) ↦₈ᵣ 0xa3#8) ∗ ((roBase + 7#64) ↦₈ᵣ 0x6e#8) ∗
    ((roBase + 8#64) ↦₈ᵣ 0xca#8) ∗ ((roBase + 9#64) ↦₈ᵣ 0x27#8) ∗
    ((roBase + 10#64) ↦₈ᵣ 0xc5#8)

theorem v1StateJumpTableBytes_eq (roBase : BitVec 64) :
    (roBase ↦ᵣ v1StateJumpTableBytes) = v1StateJumpTableBytesAt roBase := by
  unfold v1StateJumpTableBytes v1StateJumpTableBytesAt
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd]

theorem optKeysUnsampledPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.KeysUnsampled} {R : SepProp} {m : Memory}
    (hm : m ⊨ optKeysUnsampledPBPinnedAt A g p opt ∗ R) :
    (optKeysUnsampledCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optKeysUnsampledCap g opt + 2#64 != 0#64) = opt.isSome := by
  rw [optKeysUnsampledPBPinnedAt_eq, sepConj_assoc] at hm
  exact optKeysUnsampledRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optNoHeaderReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.NoHeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optNoHeaderReceivedPBPinnedAt A g p opt ∗ R) :
    (optNoHeaderReceivedCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optNoHeaderReceivedCap g opt + 2#64 != 0#64) = opt.isSome := by
  rw [optNoHeaderReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optNoHeaderReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optCt2SentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked2PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct2Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt2SentPBPinnedAt A g p opt ∗ R) :
    (optCt2SentCap g opt + 2#64 == 0#64) = !opt.isSome ∧
      (optCt2SentCap g opt + 2#64 != 0#64) = opt.isSome := by
  rw [optCt2SentPBPinnedAt_eq, sepConj_assoc] at hm
  exact optCt2SentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optHeaderReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked3PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderReceivedPBPinnedAt A g p opt ∗ R) :
    (optHeaderReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optHeaderReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optHeaderReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optHeaderSentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.HeaderSent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optHeaderSentPBPinnedAt A g p opt ∗ R) :
    (optHeaderSentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optHeaderSentCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optHeaderSentPBPinnedAt_eq, sepConj_assoc] at hm
  exact optHeaderSentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optEkSentCt1ReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked4PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.EkSentCt1Received} {R : SepProp} {m : Memory}
    (hm : m ⊨ optEkSentCt1ReceivedPBPinnedAt A g p opt ∗ R) :
    (optEkSentCt1ReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optEkSentCt1ReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optEkSentCt1ReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optEkSentCt1ReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optCt1SentEkReceivedPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1SentEkReceived} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentEkReceivedPBPinnedAt A g p opt ∗ R) :
    (optCt1SentEkReceivedCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentEkReceivedCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optCt1SentEkReceivedPBPinnedAt_eq, sepConj_assoc] at hm
  exact optCt1SentEkReceivedRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optCt1SentPBPinnedAt_cap_bounds {A : RustAlloc} {g : Unchunked5PBGhost} {p : BitVec 64}
    {opt : Option V1State.Unchunked.Ct1Sent} {R : SepProp} {m : Memory}
    (hm : m ⊨ optCt1SentPBPinnedAt A g p opt ∗ R) :
    (optCt1SentCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optCt1SentCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optCt1SentPBPinnedAt_eq, sepConj_assoc] at hm
  exact optCt1SentRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optPolynomialEncoderPBPinnedAt_cap_bounds {A : RustAlloc} {g : PolynomialEncoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialEncoderPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolynomialEncoderPBPinnedAt A g p opt ∗ R) :
    (optPolyEncCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyEncCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optPolynomialEncoderPBPinnedAt_eq, sepConj_assoc] at hm
  exact optPolyEncRest_cap_bounds (Satisfies.of_sep_right hm)

theorem optPolynomialDecoderPBPinnedAt_cap_bounds {A : RustAlloc} {g : PolynomialDecoderPBGhost} {p : BitVec 64}
    {opt : Option PolynomialDecoderPB} {R : SepProp} {m : Memory}
    (hm : m ⊨ optPolynomialDecoderPBPinnedAt A g p opt ∗ R) :
    (optPolyDecCap g opt + 1#64 == 0#64) = !opt.isSome ∧
      (optPolyDecCap g opt + 1#64 != 0#64) = opt.isSome := by
  rw [optPolynomialDecoderPBPinnedAt_eq, sepConj_assoc] at hm
  exact optPolyDecRest_cap_bounds (Satisfies.of_sep_right hm)

/-! ## 7. Prologue Symbolic Execution (`none` Path `+0..+36` and `some` Path `+0..+64`) & Post Helpers -/

abbrev V1CalleeSaved20To28 (s s0 : State) : Prop :=
  s.readReg64 .x20 = s0.readReg64 .x20 ∧ s.readReg64 .x21 = s0.readReg64 .x21 ∧
  s.readReg64 .x22 = s0.readReg64 .x22 ∧ s.readReg64 .x23 = s0.readReg64 .x23 ∧
  s.readReg64 .x24 = s0.readReg64 .x24 ∧ s.readReg64 .x25 = s0.readReg64 .x25 ∧
  s.readReg64 .x26 = s0.readReg64 .x26 ∧ s.readReg64 .x27 = s0.readReg64 .x27 ∧
  s.readReg64 .x28 = s0.readReg64 .x28 ∧ calleeSavedVRegs s = calleeSavedVRegs s0

/-- Steps the `none` path (`+0..+36`) from `entry` to `s0.readReg64 .lr`, returning `X0 = 0`. -/
theorem step_v1State_none (Φ : Memory → Prop) [FrozenInv Φ]
    (prog : Program) (entry : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (a sp v32 v24 v16 : BitVec 64)
    {s0 : State} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = a)
    (hmem : P = (((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ Rest ∗ (a ↦₆₄ noneCap2)))
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr → sf.status = .Running → sf.sp = sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ Rest ∗ (a ↦₆₄ noneCap2))) :
    SepWPpF Φ prog (s0.readReg64 .lr) s0 P Q Qp := by
  v1State_fetches_range hfn 0 40
  subst hmem
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by rw [hsp]; exact halign
  have hsp_sub_align : (sp - 32#64) &&& 15#64 = 0#64 := by
    clear *- halign; bv_kernel
  apply SepWPpF.of_sepWP (mid := s0.readReg64 .lr)
  wp_steps
  apply SepWP.done (by simp_all) (by simp_all)
  apply SepWPpF.done (by simp_all) (by simp_all)
  exact hnext _ (by simp_all) (by simp_all) (by simp_all) (by simp_all)
    (by simp_all) (by epochEncLen_cc_close)

/-- Steps the `some` prologue (`+0..+64`) up to the jump-table `ADR X10, #16` instruction,
    storing `X29, X30, X19` on the stack, computing the jump-table index in `X8`, and loading
    `roBase` into `X9`. -/
theorem step_v1State_prologue_to_64 (Φ : Memory → Prop) [FrozenInv Φ]
    (prog : Program) (entry roBase : BitVec 64)
    (hfn : IsV1StateEntryP2 prog entry)
    (hjt : HasJumpTableStepP2 prog entry roBase)
    (a sp w v32 v24 v16 : BitVec 64)
    {s0 : State} {P Rest : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s0.pc = entry) (hrun : s0.status = .Running)
    (hsp : s0.sp = sp) (halign : sp &&& 15#64 = 0#64)
    (hx0 : s0.readReg64 .x0 = a)
    (hw_beq : (w + 2#64 == 0#64) = false)
    (hw_bne : (w + 2#64 != 0#64) = true)
    (hmem : P = (((sp - 32#64) ↦₆₄ v32) ∗ ((sp - 24#64) ↦₆₄ v24) ∗
      ((sp - 16#64) ↦₆₄ v16) ∗ Rest ∗ (a ↦₆₄ w)))
    (hnext : ∀ (s1 : State) (P1 : SepProp),
      s1.pc = entry + 64#64 → s1.status = .Running → s1.sp = sp - 32#64 →
      s1.trace = s0.trace →
      s1.readReg64 .x0 = a →
      s1.readReg64 .x8 =
        (if BitVec.ult (w ^^^ 0x8000000000000000#64) 11#64
         then w ^^^ 0x8000000000000000#64 else 7#64) →
      s1.readReg64 .x9 = roBase →
      (s1.readReg64 .x19 = s0.readReg64 .x19 ∧ V1CalleeSaved20To28 s1 s0) →
      P1 = (((sp - 32#64) ↦₆₄ s0.readReg64 .fp) ∗ ((sp - 24#64) ↦₆₄ s0.readReg64 .lr) ∗
        ((sp - 16#64) ↦₆₄ s0.readReg64 .x19) ∗ Rest ∗ (a ↦₆₄ w)) →
      SepWPpF Φ prog (s0.readReg64 .lr) s1 P1 Q Qp) :
    SepWPpF Φ prog (s0.readReg64 .lr) s0 P Q Qp := by
  v1State_fetches_range hfn 0 56
  subst hmem
  have hsp_align : s0.sp &&& 15#64 = 0#64 := by rw [hsp]; exact halign
  have hsp_sub_align : (s0.sp - 32#64) &&& 15#64 = 0#64 := by
    rw [hsp]; clear *- halign; bv_kernel
  apply SepWPpF.of_sepWP (mid := entry + 64#64)
  wp_steps
  apply hjt _ _ _ _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
  apply SepWP.done (by simp_all) (by simp_all)
  exact hnext _ _ (by simp [arm64_norm]) (by simp [arm64_norm, hrun])
    (by simp [arm64_norm, hsp]) (by simp [arm64_norm])
    (by simp [arm64_norm, hx0])
    (by simp [arm64_norm])
    (by simp [arm64_norm])
    ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
     by simp [arm64_norm], by simp [arm64_norm]⟩
    rfl

/-- Reconstructs `(v1StateEncodedLenRoPinnedSpec A roBase).post` from the unpacked post-state. -/
theorem v1State_post_of_body (A : RustAlloc) (roBase a : BitVec 64)
    (g : V1StatePBGhost) (m : V1State) (R : SepProp) (s0 sf : State)
    (v32 v24 v16 v8 : BitVec 64)
    (hx0 : sf.readReg64 .x0 = BitVec.ofNat 64 (v1StatePBEncodedLen m))
    (htr : sf.trace = s0.trace)
    (hm : sf.mem ⊨ (((s0.sp - 32#64) ↦₆₄ v32) ∗ ((s0.sp - 24#64) ↦₆₄ v24) ∗
      ((s0.sp - 16#64) ↦₆₄ v16) ∗ ((s0.sp - 8#64) ↦₆₄ v8) ∗
      stackAt (s0.sp - 32#64) chunkedEncodedLenStack ∗
      v1StateJumpTableBytesAt roBase ∗
      v1StatePBPinnedAt A g a m ∗ R) ∗ emp) :
    sf.mem ⊨ (v1StateEncodedLenRoPinnedSpec A roBase).post ⟨a, g, m⟩ s0 sf ∗ R := by
  rw [sepConj_emp] at hm
  simp only [v1StateEncodedLenRoPinnedSpec, v1StateJumpTableBytes_eq,
    stackAt_v1StateEncodedLen_eq,
    sepExists_sepConj_left, sepExists_sepConj_right,
    satisfies_sepExists, sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨v32, v24, v16, v8, ⟨hx0, htr⟩, ?_⟩
  convert hm using 1; ac_rfl

theorem fold_v1StateJumpTableBytesAt (roBase : BitVec 64) :
    ((roBase ↦₈ᵣ 0x00#8) ∗ ((roBase + 1#64) ↦₈ᵣ 0x7c#8) ∗
      ((roBase + 2#64) ↦₈ᵣ 0x49#8) ∗ ((roBase + 3#64) ↦₈ᵣ 0x4c#8) ∗
      ((roBase + 4#64) ↦₈ᵣ 0x05#8) ∗ ((roBase + 5#64) ↦₈ᵣ 0x9e#8) ∗
      ((roBase + 6#64) ↦₈ᵣ 0xa3#8) ∗ ((roBase + 7#64) ↦₈ᵣ 0x6e#8) ∗
      ((roBase + 8#64) ↦₈ᵣ 0xca#8) ∗ ((roBase + 9#64) ↦₈ᵣ 0x27#8) ∗
      ((roBase + 10#64) ↦₈ᵣ 0xc5#8)) = v1StateJumpTableBytesAt roBase := rfl

macro "step_v1State_jump_to " entry:term:max off:num s1:term:max idx:term:max hx8:term:max : tactic =>
  `(tactic| (
    have _hx8 : ($s1).readReg64 .x8 = $idx := $hx8
    dsimp only [v1StateJumpTableBytesAt]
    apply SepWPp.of_sepWP (mid := $entry + BitVec.ofNat 64 $off)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)))

macro "step_v1State_jump_to_F " entry:term:max off:num s1:term:max idx:term:max hx8:term:max : tactic =>
  `(tactic| (
    have _hx8 : ($s1).readReg64 .x8 = $idx := $hx8
    dsimp only [v1StateJumpTableBytesAt]
    apply SepWPpF.of_sepWP (mid := $entry + BitVec.ofNat 64 $off)
    wp_steps
    apply SepWP.done (by simp_all) (by simp_all)))

theorem v1StateEncodedLen_ro_ok_of_pinned {prog : Program} {entry roBase : BitVec 64} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (v1StateEncodedLenRoPinnedSpec A roBase)) :
    subroutine_ok prog entry (v1StateEncodedLenRoSpec A roBase) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, m⟩ R s0 hpc hrun hpre hsp
  simp only [v1StateEncodedLenRoSpec, v1StatePBAt,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [v1StateEncodedLenRoSpec, v1StatePBAt,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

theorem v1StateEncodedLen_ro_lscl_ok_of_pinned {prog : Program} {entry roBase : BitVec 64}
    {pl : MultiPlacement} {A : RustAlloc}
    (hpinned : subroutine_ok prog entry (withLsCodeLoaded pl (v1StateEncodedLenRoPinnedSpec A roBase))) :
    subroutine_ok prog entry (withLsCodeLoaded pl (v1StateEncodedLenRoSpec A roBase)) := by
  apply subroutine_ok_outcome_intro
  intro ⟨a, m⟩ R s0 hpc hrun hpre hsp
  simp only [withLsCodeLoaded, v1StateEncodedLenRoSpec, v1StatePBAt,
    sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpre
  rcases hpre with ⟨g, hpre⟩
  refine (hpinned.to_outcome ⟨a, g, m⟩ R s0 hpc hrun hpre hsp).mono_outcome fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex
  · refine Or.inl ⟨hret, hcc, ?_⟩
    simp only [withLsCodeLoaded, v1StateEncodedLenRoSpec, v1StatePBAt,
      sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists]
    exact ⟨g, hpost⟩
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr hex)

end CryptoVerification.SpqrV1.ProtoRepr
