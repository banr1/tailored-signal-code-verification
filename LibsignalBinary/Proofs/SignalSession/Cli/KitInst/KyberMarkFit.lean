/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.KpkMark
public import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.PreKeyVtables
public import LibsignalBinary.Proofs.PublicApi.StoreKit.KyberPreKeyStoreKit
public import LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced
import LibsignalBinary.Proofs.SignalSession.Cli.KitInst.SessionSpec
import LibsignalBinary.Proofs.SignalSession.Cli.Store.KpkMarkPoll.Pure

/-!
# CLI `KyberPreKeyFiles` Mark-Side Store Specification

Defines the `KyberPreKeyFiles` invariant `CliKpkInv` (closed under `mark_kyber_pre_key_used`),
the 48-byte `SignalProtocolError` layout `cliKpkMarkErrSpec` for mark errors, the parameterized
`KyberPreKeyStoreSpec` instance `cliKpkStoreSpec`, and the poll bridge `cliKpkStoreSpec_markPoll`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.SignalSession.Cli.KitInst

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApi.StoreKit CryptoVerification.RecordCodecs
open CryptoVerification.SignalSession.Cli
open LibsignalBinary.Proofs.SignalSession.Cli.F3.HRead.ReadFileBudgetPlaced (FdsGe3Closed)

/-! ## Offsets -/

/-- The `get_kyber_pre_key` shim. -/
abbrev cliKpkGetShimOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key")

/-- The `get_kyber_pre_key` future's poll. -/
abbrev cliKpkGetPollOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::get_kyber_pre_key::{closure#0}")

/-- The `mark_kyber_pre_key_used` shim. -/
abbrev cliKpkMarkShimOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used")

/-- The `mark_kyber_pre_key_used` future's poll. -/
abbrev cliKpkMarkPollOff : BitVec 64 :=
  bv% (ls_off% "<libsignal_cli::stores::KyberPreKeyFiles as libsignal_protocol::storage::traits::KyberPreKeyStore>::mark_kyber_pre_key_used::{closure#0}")

/-! ## Store invariant -/

/-- Pure invariant of `KyberPreKeyFiles` at mark call `(kid, ksid, kbk)` and initial files `F0`:
name and base-key bounds (`PkNameOk`, `KpkBaseKeysOk`), well-formedness of seen entries
(`KpkSeenOk`), and capacity in `oneTime.changed` and `lastResort.changed` for one `put`. -/
structure CliKpkInv (rd : ReadRule) (F0 : FsFiles) (pathOk : List (BitVec 8) → Prop)
    (kid ksid : BitVec 32) (kbk : PublicKey) (g : KyberGhost) : Prop where
  nameOk : PkNameOk pathOk g.oneTime kid
  baseOk : KpkBaseKeysOk pathOk g.lastResort kid
  seenOk : KpkSeenOk rd F0 g.lastResort kid ksid kbk
  oneLt : g.oneTime.changed.length < 2 ^ 32 ∧
    (g.oneTime.changed.length + 1 < 2 ^ 32 ∨ keyName kid ∈ g.oneTime.changed.map Prod.fst)
  lastLt : g.lastResort.changed.length < 2 ^ 32 ∧
    (g.lastResort.changed.length + 1 < 2 ^ 32 ∨
      baseKeysName kid ∈ g.lastResort.changed.map Prod.fst)

/-- `kpkMarkOf`'s directory update preserves `CliKpkInv`. -/
theorem CliKpkInv.mark {rd : ReadRule} {F0 : FsFiles} {pathOk : List (BitVec 8) → Prop}
    {kid ksid : BitVec 32} {kbk : PublicKey} {g : KyberGhost}
    (h : CliKpkInv rd F0 pathOk kid ksid kbk g) :
    CliKpkInv rd F0 pathOk kid ksid kbk (kpkMarkOf rd F0 g kid ksid kbk).2 := by
  unfold kpkMarkOf
  rcases g.oneTime.get rd F0 (keyName kid) with _ | _ | ⟨_, _⟩
  · exact h
  · rcases g.lastResort.get rd F0 (baseKeysName kid) with _ | seen
    · exact h
    · dsimp only
      split
      · exact h
      · rename_i hmod
        have hmod0 : seen.length % 37 = 0 := by
          rw [Store.KpkMarkPoll.Helpers.baseKeyEntry_length] at hmod
          omega
        split
        · exact h
        · refine ⟨h.nameOk, h.baseOk, ?_, h.oneLt, ?_⟩
          · intro bs hget _ hfalse
            rw [DirGhost.get_put_self] at hget
            cases hget
            have htrue :
                hasChunk (seen ++ baseKeyEntry ksid kbk) (baseKeyEntry ksid kbk) = true :=
              Store.KpkMarkPoll.Helpers.hasChunk_true_of_match
                (seen := seen ++ baseKeyEntry ksid kbk)
                (pre := seen) (suf := baseKeyEntry ksid kbk)
                (used := baseKeyEntry ksid kbk)
                (idx := seen.length / 37) (rem := 0)
                (Store.KpkMarkPoll.Helpers.baseKeyEntry_length ksid kbk)
                rfl
                (by omega)
                (by rw [Store.KpkMarkPoll.Helpers.baseKeyEntry_length])
                (List.take_of_length_le (by rw [Store.KpkMarkPoll.Helpers.baseKeyEntry_length]))
            rw [htrue] at hfalse
            cases hfalse
          · obtain ⟨hlt, hroom⟩ := h.lastLt
            refine ⟨?_, Or.inr (mem_setOrPush_self _ _ _)⟩
            show (DirGhost.setOrPush _ _ g.lastResort.changed).length < 2 ^ 32
            rcases hroom with hroom | hmem
            · exact Nat.lt_of_le_of_lt (setOrPush_length_le _ _ _) hroom
            · rw [setOrPush_length_of_mem hmem]; exact hlt
  · refine ⟨h.nameOk, h.baseOk, h.seenOk, ?_, h.lastLt⟩
    obtain ⟨hlt, hroom⟩ := h.oneLt
    refine ⟨?_, Or.inr (mem_setOrPush_self _ _ _)⟩
    show (DirGhost.setOrPush _ _ g.oneTime.changed).length < 2 ^ 32
    rcases hroom with hroom | hmem
    · exact Nat.lt_of_le_of_lt (setOrPush_length_le _ _ _) hroom
    · rw [setOrPush_length_of_mem hmem]; exact hlt

/-- `KyberPreKeyFiles` layout at `self`: `one_time` at `+0x00`, `last_resort` at `+0x28`, and
`CliKpkInv`. -/
def cliKpkStoreAt (A : RustAlloc) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (self : BitVec 64) (g : KyberGhost) : SepProp :=
  ⌜CliKpkInv rd F0 pathOk kid ksid kbk g⌝ ∗ dirAt A self g.oneTime ∗
    dirAt A (self + 0x28#64) g.lastResort

/-! ## Mark error layout -/

/-- Error witness for `mark_kyber_pre_key_used`: non-`.ok` `KpkMarkAns` plus five inline payload
words. -/
structure CliKpkMarkErr where
  ans : KpkMarkAns
  ne_ok : ans ≠ .ok
  cap : BitVec 64
  ptr : BitVec 64
  len : BitVec 64
  w4 : BitVec 64
  w5 : BitVec 64

/-- 48-byte `SignalProtocolError` layout for `CliKpkMarkErr`: tag word (`speWord 24` on `.reused`,
`speWord 1` otherwise), `String` header words `1..3` with owned heap buffer, and `"read"` slice
words `4..5` on `.readErr`. -/
def cliKpkMarkErrSpec (A : RustAlloc) : SpeErrSpec CliKpkMarkErr where
  w0 := fun e => match e.ans with
    | .reused => speWord 24
    | _ => speWord 1
  w1 := fun e => e.cap
  w2 := fun e => e.ptr
  w3 := fun e => e.len
  w4 := fun e => e.w4
  w5 := fun e => e.w5
  heap := fun e =>
    (∃∗ bs : List (BitVec 8),
      ⌜BitVec.ofNat 64 bs.length = e.len ∧ bs.length ≤ e.cap.toNat ∧ e.cap.toNat < 2 ^ 63 ∧
        e.ptr ≠ 0⌝ ∗
      (if e.cap = 0 then emp
       else A.live e.ptr e.cap.toNat 1 ∗ (e.ptr ↦ₛ bs) ∗
         memRegion (e.ptr + BitVec.ofNat 64 bs.length) (e.cap.toNat - bs.length))) ∗
    (match e.ans with
     | .readErr => ⌜e.w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗ (e.w4 ↦ᵣ utf8 "read")
     | _ => emp)
  w0_ne_err := by
    intro e
    cases e.ans <;> decide
  w0_ne_ok := by
    intro e
    cases e.ans <;> decide
  w0_ne_pending := by
    intro e
    cases e.ans <;> decide

private theorem cliMarkErr_of_parts (A : RustAlloc) (out : BitVec 64)
    (ans : KpkMarkAns)
    (bs : List (BitVec 8)) (w4 w5 : BitVec 64) (tail : SepProp)
    (htail : tail ⊢ match ans with
      | .readErr => ⌜w5 = BitVec.ofNat 64 (utf8 "read").length⌝ ∗ (w4 ↦ᵣ utf8 "read")
      | _ => emp)
    (hne : ans ≠ .ok) :
    ((out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1) ∗
      vecU8 A (out + 8#64) bs ∗
      ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5) ∗ tail) ⊢
    ∃∗ r : Except CliKpkMarkErr Unit,
      ⌜(match r with | .ok () => ans = .ok | .error e => ans = e.ans)⌝ ∗
        unitSpePollOutAt (cliKpkMarkErrSpec A) out r := by
  unfold vecU8 vecU8At vecHeader
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun cap => ?_
  rw [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun ptr => ?_
  let e : CliKpkMarkErr :=
    { ans := ans
      ne_ok := hne
      cap := cap
      ptr := ptr
      len := BitVec.ofNat 64 bs.length
      w4 := w4
      w5 := w5 }
  refine Entails.sepExists_right (.error e) (Entails.pure_right rfl ?_)
  dsimp only [unitSpePollOutAt, speErrAt, speWordsAt, cliKpkMarkErrSpec, e]
  have h10 : out + 8#64 + 8#64 = out + 0x10#64 := by bv_omega
  have h18 : out + 8#64 + 16#64 = out + 0x18#64 := by bv_omega
  rw [h10, h18]
  set bufHeap : SepProp :=
    if cap = 0 then emp
    else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
      memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)
  set w0Term : SepProp :=
    out ↦₆₄ match ans with | .reused => speWord 24 | _ => speWord 1
  have hvec :
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ bufHeap ⊢
        ∃∗ bs' : List (BitVec 8),
          ⌜BitVec.ofNat 64 bs'.length = BitVec.ofNat 64 bs.length ∧
            bs'.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
          (if cap = 0 then emp
           else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs') ∗
             memRegion (ptr + BitVec.ofNat 64 bs'.length) (cap.toNat - bs'.length)) := by
    refine Entails.pure_left fun ⟨hlen, hcap, hptr⟩ => ?_
    refine Entails.sepExists_right bs ?_
    exact Entails.pure_right ⟨rfl, hlen, hcap, hptr⟩ (Entails.refl _)
  refine Entails.trans (Entails.of_eq (show _ =
    ((w0Term ∗ ((out + 0x08#64) ↦₆₄ cap) ∗ ((out + 0x10#64) ↦₆₄ ptr) ∗
        ((out + 0x18#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ((out + 0x20#64) ↦₆₄ w4) ∗ ((out + 0x28#64) ↦₆₄ w5)) ∗
      ((⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗ bufHeap) ∗ tail)) by ac_rfl)) ?_
  cases ans <;> exact sepConj_mono_right (sepConj_mono hvec htail)

private theorem cliKpkMarkOut_entails (A : RustAlloc) (out : BitVec 64) (a : KpkMarkAns) :
    kpkMarkOutAt A out a ⊢
      ∃∗ ans : Except CliKpkMarkErr Unit,
        ⌜(match ans with | .ok () => a = .ok | .error e => a = e.ans)⌝ ∗
          unitSpePollOutAt (cliKpkMarkErrSpec A) out ans := by
  rcases a with _ | _ | _ | _
  · exact Entails.sepExists_right (.ok ()) (Entails.pure_right rfl (Entails.refl _))
  · dsimp only [kpkMarkOutAt, speAt, strRefAt]
    have e1 : out + asm64% spePayloadOff = out + 8#64 := by bv_omega
    have e2 : out + asm64% speInvalidStateFnOff = out + 0x20#64 := by bv_omega
    have e3 : out + 0x20#64 + asm64% boxSliceLenOff = out + 0x28#64 := by bv_omega
    rw [e1, e2, e3, sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun p => ?_
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts A out .readErr bs p
        (BitVec.ofNat 64 (utf8 "read").length) (p ↦ᵣ utf8 "read")
        (Entails.pure_right rfl (Entails.refl _)) (by nofun))
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
          (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 0x28#64) ↦₆₄ w5)]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts A out .malformed bs w4 w5 emp (Entails.refl _) (by nofun))
  · dsimp only [kpkMarkOutAt, strSpeAt]
    rw [sepExists_sepConj_left, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun bs => ?_
    rw [ProofLib.memRegion_split' (b := out + 0x20#64) (n := 8) (k := 8)
          (b' := out + 0x28#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_eight, ProofLib.memRegion_eight,
        sepExists_sepConj_left, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w4 => ?_
    rw [sepExists_sepConj_right, sepExists_sepConj_right, sepExists_sepConj_right]
    refine Entails.sepExists_elim fun w5 => ?_
    rw [← sepConj_emp ((out + 0x28#64) ↦₆₄ w5)]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (cliMarkErr_of_parts A out .reused bs w4 w5 emp (Entails.refl _) (by nofun))

/-! ## Store kit specification -/

/-- Parameters for the `get_kyber_pre_key` half of `cliKpkStoreSpec` (instantiated in
`PreKeySpecs.lean`). -/
structure CliKpkGetSide where
  RecOk : KyberPreKeyRecord → Prop
  getIdOk : BitVec 32 → Prop
  GetErr : Type
  getErr : SpeErrSpec GetErr
  getRel : KyberGhost → BitVec 32 → Except GetErr KyberPreKeyRecord → Prop

/-- Concrete `KyberPreKeyStoreSpec` for CLI `KyberPreKeyFiles` at mark call `(kid, ksid, kbk)`,
parameterized by `G : CliKpkGetSide`. -/
def cliKpkStoreSpec (A : RustAlloc) (b : BitVec 64) (rd : ReadRule) (F0 : FsFiles)
    (pathOk : List (BitVec 8) → Prop) (kid ksid : BitVec 32) (kbk : PublicKey)
    (G : CliKpkGetSide) (getShimStk getPollStk markShimStk markPollStk : Nat)
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32) :
    KyberPreKeyStoreSpec A b where
  kpk_vt := b + cliKpkVtOff
  KpkState := KyberGhost
  storeAt := cliKpkStoreAt A rd F0 pathOk kid ksid kbk
  RecOk := G.RecOk
  getIdOk := G.getIdOk
  markOk := fun id sid bk => id = kid ∧ sid = ksid ∧ bk = kbk
  envOk := fun f => f = F0
  fdsOk := fun fs => FdsGe3Closed fs
  GetErr := G.GetErr
  MarkErr := CliKpkMarkErr
  getErr := G.getErr
  markErr := cliKpkMarkErrSpec A
  markUpdate := fun g id sid bk _ => (kpkMarkOf rd F0 g id sid bk).2
  getRel := G.getRel
  markRel := fun g id sid bk ans =>
    match ans with
    | .ok () => (kpkMarkOf rd F0 g id sid bk).1 = .ok
    | .error e => (kpkMarkOf rd F0 g id sid bk).1 = e.ans
  getShimOff := cliKpkGetShimOff
  getFutVtOff := cliKpkGetFutVtOff
  getPollOff := cliKpkGetPollOff
  getFutDropOff := cliIdFutDropOff
  getBoxSize := 16
  markShimOff := cliKpkMarkShimOff
  markFutVtOff := cliKpkMarkFutVtOff
  markPollOff := cliKpkMarkPollOff
  markFutDropOff := cliIdFutDropOff
  markBoxSize := 32
  getShimStack := getShimStk
  getPollStack := getPollStk
  markShimStack := markShimStk
  markPollStack := markPollStk
  getBoxAt := pkBoxAt
  markBoxAt := kpkMarkBoxAt
  getBoxAt_memRegion := hGetBox
  markBoxAt_memRegion := hMarkBox
  getBoxSize_ne_zero := by decide
  markBoxSize_ne_zero := by decide
  getBoxSize_lt := by decide
  markBoxSize_lt := by decide
  getFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)
  markFutDrop_ne_zero := fun hb h => by
    rw [show b = 0#64 - cliIdFutDropOff by rw [← h, BitVec.add_sub_cancel]] at hb
    exact absurd hb (by decide)

/-! ## Poll contract bridge -/

theorem cliKpkMarkPoll_fnAddr {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).fnAddr kpkMarkPollName = b + cliKpkMarkPollOff := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase, kpkMarkPoll_fnOff, cliKpkMarkPollOff]

/-- Lift `kpkMarkPollSpec` at `fnAddr kpkMarkPollName` to `KyberPreKeyStoreKitOkImg.markPoll`. -/
theorem cliKpkStoreSpec_markPoll {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (hhop : subroutine_ok (tripleRatchetProgAtExt img.base (tripleRatchetExterns C ctl abs))
      ((tripleRatchetProgAtExt img.base (tripleRatchetExterns C ctl abs)).fnAddr kpkMarkPollName)
      (kpkMarkPollSpec rd pathOk A img s4)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (img.base + (cliKpkStoreSpec A img.base rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
        hGetBox hMarkBox).markPollOff)
      ((kitKpkMarkPollSpecE (cliKpkStoreSpec A img.base rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
        hGetBox hMarkBox)).inImage img) := by
  let kit := cliKpkStoreSpec A img.base rd F0 pathOk kid ksid kbk G s1 s2 s3 s4 hGetBox hMarkBox
  have hhop' :
      subroutine_ok (tripleRatchetProgAt img.base C ctl abs) (img.base + kit.markPollOff)
        (kpkMarkPollSpec rd pathOk A img s4) :=
    cliSess_kitProg (@cliKpkMarkPoll_fnAddr img.base) hhop
  refine subroutine_ok.of_codeLoaded
    fun ⟨⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0⟩ R s0 hpc hrun hpre hsp _ => ?_
  have hpre1 :
      s0.mem ⊨ ⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
        (⌜s0.fs.files = F0⌝ ∗ ((kitKpkMarkPollSpec kit).pre
          (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0) s0 ∗ R)) := by
    change s0.mem ⊨ (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.fs.files = F0⌝ ∗ (kitKpkMarkPollSpec kit).pre
        (⟨fut, out, self, baseKeyA, kid', ksid', kbk'⟩, st0) s0)) ∗ R at hpre
    simpa only [sepConj_assoc] using hpre
  rw [satisfies_pure_sepConj] at hpre1
  obtain ⟨himgInv, hpre2⟩ := hpre1
  rw [satisfies_pure_sepConj] at hpre2
  obtain ⟨hfiles, hpre3⟩ := hpre2
  change s0.mem ⊨
    (⌜(img.base &&& 0xfff#64) = 0#64 ∧ s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
        (kid' = kid ∧ ksid' = ksid ∧ kbk' = kbk)⌝ ∗
      kpkMarkBoxAt fut self baseKeyA kid' ksid' 0#8 ∗
      (⌜CliKpkInv rd F0 pathOk kid ksid kbk st0⌝ ∗ dirAt A self st0.oneTime ∗
        dirAt A (self + 0x28#64) st0.lastResort) ∗
      memRegion out 48 ∗
      (baseKeyA ↦ₛ kbk'.bytes.toList) ∗
      A.pool ∗ stackAt s0.sp s4) ∗ R at hpre3
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre3
  obtain ⟨⟨_, hx0, hx8, hxid, hxsid, hxbk⟩, hpre4⟩ := hpre3
  rw [hxid, hxsid, hxbk] at hpre4 ⊢
  have hpre5 :
      s0.mem ⊨ ⌜CliKpkInv rd F0 pathOk kid ksid kbk st0⌝ ∗
        (kpkMarkBoxAt fut self baseKeyA kid ksid 0#8 ∗
          dirAt A self st0.oneTime ∗ dirAt A (self + 0x28#64) st0.lastResort ∗
          (baseKeyA ↦ₛ kbk.bytes.toList) ∗ memRegion out 48 ∗
          A.pool ∗ stackAt s0.sp s4 ∗ R) :=
    Satisfies.mono (Entails.of_eq (by ac_rfl)) hpre4
  rw [satisfies_pure_sepConj] at hpre5
  obtain ⟨hinv, hspatial⟩ := hpre5
  let xg : KpkMarkPollGhost := ⟨fut, out, self, baseKeyA, kid, ksid, kbk, st0⟩
  have hpre_hop : s0.mem ⊨ (kpkMarkPollSpec rd pathOk A img s4).pre xg s0 ∗ R := by
    show s0.mem ⊨ (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
      (⌜s0.readReg64 .x0 = fut ∧ s0.readReg64 .x8 = out ∧
          PkNameOk pathOk st0.oneTime kid ∧ KpkBaseKeysOk pathOk st0.lastResort kid ∧
          KpkSeenOk rd s0.fs.files st0.lastResort kid ksid kbk ∧
          st0.oneTime.changed.length < 2 ^ 32 ∧ st0.lastResort.changed.length < 2 ^ 32⌝ ∗
        kpkMarkBoxAt fut self baseKeyA kid ksid 0#8 ∗
        dirAt A self st0.oneTime ∗ dirAt A (self + 0x28#64) st0.lastResort ∗
        (baseKeyA ↦ₛ kbk.bytes.toList) ∗ memRegion out 48 ∗
        A.pool ∗ stackAt s0.sp s4)) ∗ R
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨himgInv, ?_⟩
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hx8, hinv.nameOk, hinv.baseOk, hfiles ▸ hinv.seenOk,
      hinv.oneLt.1, hinv.lastLt.1⟩, ?_⟩
    simpa only [sepConj_assoc] using hspatial
  refine subroutine_ok.mono_outcome hhop' xg R s0 hpc hrun hpre_hop hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | hpan | hex | hoom
  · refine Or.inl ⟨hret, hcc, ?_⟩
    refine Satisfies.mono (sepConj_mono_left ?_) hpost
    show (kpkMarkPollSpec rd pathOk A img s4).post xg s0 sf ⊢
      (kitKpkMarkPollSpec kit).post (⟨fut, out, self, baseKeyA, kid, ksid, kbk⟩, st0) s0 sf
    dsimp only [kpkMarkPollSpec, Spec.inImage, kitKpkMarkPollSpec, kit, cliKpkStoreSpec,
      cliKpkStoreAt, kpkMarkPollOutAt, xg]
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun res => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun ⟨hres, htr⟩ => ?_
    rw [hfiles] at hres
    subst hres
    set m := kpkMarkOf rd F0 st0 kid ksid kbk
    refine Entails.trans
      (Entails.of_eq (show _ =
        kpkMarkOutAt A out m.1 ∗
          (dirAt A self m.2.oneTime ∗ dirAt A (self + 0x28#64) m.2.lastResort ∗
            kpkMarkBoxAt fut self baseKeyA kid ksid 1#8 ∗
            (baseKeyA ↦ₛ kbk.bytes.toList) ∗ A.pool ∗ stackAt s0.sp s4) by ac_rfl)) ?_
    refine Entails.trans (sepConj_mono_left (cliKpkMarkOut_entails A out m.1)) ?_
    rw [sepExists_sepConj_left]
    refine Entails.sepExists_elim fun ans => ?_
    rw [sepConj_assoc]
    refine Entails.pure_left fun hrel => ?_
    refine Entails.sepExists_right ans ?_
    refine Entails.pure_right ⟨hrel, by rw [List.append_nil]; exact htr⟩ ?_
    exact Entails.trans (Entails.pure_right hinv.mark (Entails.refl _)) (Entails.of_eq (by ac_rfl))
  · exact Or.inr (Or.inl hpan)
  · exact Or.inr (Or.inr (Or.inl hex))
  · exact Or.inr (Or.inr (Or.inr hoom))

example {A : RustAlloc} {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)} {rd : ReadRule} {F0 : FsFiles}
    {pathOk : List (BitVec 8) → Prop} {kid ksid : BitVec 32} {kbk : PublicKey}
    (G : CliKpkGetSide) {s1 s2 s3 s4 : Nat}
    (hGetBox : ∀ box self id st, pkBoxAt box self id st ⊢ memRegion box 16)
    (hMarkBox : ∀ box self baseKeyA id signedId st,
      kpkMarkBoxAt box self baseKeyA id signedId st ⊢ memRegion box 32)
    (hhop : subroutine_ok (tripleRatchetProgAtExt img.base (tripleRatchetExterns C ctl abs))
      ((tripleRatchetProgAtExt img.base (tripleRatchetExterns C ctl abs)).fnAddr kpkMarkPollName)
      (kpkMarkPollSpec rd pathOk A img s4)) :
    subroutine_ok (tripleRatchetProgAt img.base C ctl abs)
      (img.base + (cliKpkStoreSpec A img.base rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
        hGetBox hMarkBox).markPollOff)
      ((kitKpkMarkPollSpecE (cliKpkStoreSpec A img.base rd F0 pathOk kid ksid kbk G s1 s2 s3 s4
        hGetBox hMarkBox)).inImage img) :=
  cliKpkStoreSpec_markPoll G hGetBox hMarkBox hhop

end CryptoVerification.SignalSession.Cli.KitInst
