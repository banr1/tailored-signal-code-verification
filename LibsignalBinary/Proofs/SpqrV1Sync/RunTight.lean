/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncParty
public import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.DecoderCodec
public import LibsignalBinary.Proofs.SpqrV1Sync.Erasure.EncoderCodec
public import LibsignalBinary.Proofs.SpqrV1Sync.ErasureDefs
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncCalib
public import LibsignalBinary.Proofs.SpqrV1Sync.InSyncEpoch
public import LibsignalBinary.Specifications.AsmConstants
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDecDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.CBCDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EffSalt
public import LibsignalBinary.Specifications.CryptoGames.AEAD.EtMDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HKDFDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.HMACDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.LibsignalAead
public import LibsignalBinary.Specifications.CryptoGames.AEAD.MacPrecompDefs
public import LibsignalBinary.Specifications.CryptoGames.AEAD.WireAeadDefs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Construction
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Defs
public import LibsignalBinary.Specifications.CryptoGames.FSAEAD.Security
public import LibsignalBinary.Specifications.CryptoGames.PRNG.Defs
public import LibsignalBinary.Specifications.CryptoGames.Primitives
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.ChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.CreateChainDefs
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.LibsignalSession
public import LibsignalBinary.Specifications.CryptoGames.Ratchet.RootKdfDefs
public import LibsignalBinary.Specifications.HkdfSalt
public import LibsignalBinary.Specifications.LibsignalAesCbc
public import LibsignalBinary.Specifications.LibsignalHmac
public import LibsignalBinary.Specifications.LibsignalProtoCodec
public import LibsignalBinary.Specifications.LibsignalSession
public import LibsignalBinary.Specifications.LibsignalSessionRepr
public import LibsignalBinary.Specifications.LibsignalSignalMessage
public import LibsignalBinary.Specifications.LibsignalSpqr
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Assemble
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Auth
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Chain
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Core
public import LibsignalBinary.Specifications.LibsignalSpqrV1.GF16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Interface
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Kdf
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKem
public import LibsignalBinary.Specifications.LibsignalSpqrV1.MlKemCorrect
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Poly
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Proto
public import LibsignalBinary.Specifications.LibsignalSpqrV1.ProtoPB
public import LibsignalBinary.Specifications.LibsignalSpqrV1.States
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Top
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Wire
public import LibsignalBinary.Specifications.LibsignalTripleRatchet
public import LibsignalBinary.Specifications.LibsignalTripleRatchetProst
public import LibsignalBinary.Specifications.LibsignalTripleRatchetRepr
public import LibsignalBinary.Specifications.RustHeap.Alloc
public import LibsignalBinary.Specifications.RustHeap.Vec

/-!
# Tight Honest Braid Runs (`DrawsEnc` and `RunT`)

Refines `InSyncParty.Run` so that the ML-KEM good event `KemOk K s r` is required **only** at the
single CT-side send per epoch that actually draws encapsulation randomness (`DrawsEnc`: ghost coins
`.seed s` and sender in `.headerReceived`), rather than on earlier `.noHeaderReceived` sends that
consume no coins.

Because `MlKem.CorrectWith δ` bounds failure probability averaged over a uniform seed `s`, an
adaptive adversary who learns `s` could otherwise trigger multiple no-op CT sends at `.seed s` and
inflate a naive union bound to `q² · δ`. Restricting `KemOk` to `DrawsEnc` ensures each epoch draws
`(s, r)` at most once (transitioning immediately to `.both s r`), giving an `O(q · δ)` union bound.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.Braid

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.Erasure
open CryptoVerification.SpqrV1Sync.InSync
open CryptoGames.LibsignalSession (ShaCompress)
/-- Sending on `Y_e` at `.seed s` prior to `.headerReceived` emits `noneMsg e`, leaves coins
unchanged, and preserves `InSyncE` without requiring `KemOk`. -/
theorem inSyncE_sendY_nodraw (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (s : Seed) (x y : St F) (toY toX : List Msg) (h : InSyncE F K e auth (.seed s) x y toY toX)
    (hnhr : ∀ hr, y ≠ .headerReceived hr) (tape : Bytes) :
    y.send K tape = .ok ({ msg := noneMsg e, key := none, state := y }, tape) ∧
      InSyncE F K e auth (.seed s) x y toY (toX ++ [noneMsg e]) := by
  refine ⟨InSync.ySend_noHeader F K e auth (some s) y h.hy hnhr tape, ?_⟩
  refine
    { hepoch := h.hepoch
      hauth := h.hauth
      hx := h.hx
      hy := h.hy
      hkem := fun _ _ hc => nomatch hc
      hcausal := fun _ _ hc => nomatch hc
      hlag := h.hlag
      htoY := h.htoY
      htoX := ?_ }
  intro m hm
  rcases List.mem_append.mp hm with hm0 | hm1
  · exact h.htoX m hm0
  · rw [List.mem_singleton.mp hm1]
    exact Or.inr (Or.inl rfl)

/-- `nextCoins` leaves `.seed s` unchanged when the sender is not in `.headerReceived`. -/
theorem nextCoins_seed_of_not_hr (F : ShaCompress) (s : Seed) (st : St F)
    (hnhr : ∀ hr, st ≠ .headerReceived hr) (tape : Bytes) :
    nextCoins F (.seed s) st tape = .seed s := by
  cases st with
  | headerReceived hr => exact absurd rfl (hnhr hr)
  | _ => rfl

/-- Predicate characterizing the unique send step that draws encapsulation coins: `c = .seed s`
and `st` is `.headerReceived`. -/
def DrawsEnc (F : ShaCompress) (c : Coins) (st : St F) (s : Seed) : Prop :=
  c = .seed s ∧ ∃ hr, st = .headerReceived hr

/-- Party `A` send step requiring `KemOk` only when `DrawsEnc F c stA s` holds. -/
theorem inSync_sendA_tight (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (tape : Bytes) (htape : 64 ≤ tape.length)
    (hkem : ekSide e = .b → ∀ (s : Seed) (r : EncRand), DrawsEnc F c stA s →
      r.toList = tape.take 32 → KemOk K s r) :
    ∃ (m : Msg) (key : Option EpochSecret) (stA' : St F) (tape' : Bytes),
      stA.send K tape = .ok ({ msg := m, key := key, state := stA' }, tape') ∧
      CoinStep F K e tape c (nextCoins F c stA tape) key ∧
      InSync F K e auth (nextCoins F c stA tape) stA' stB toA (toB ++ [m]) := by
  cases hs : ekSide e
  · exact inSync_sendA_det F K e auth c stA stB toA toB h tape htape
      (fun hb => by rw [hs] at hb; nomatch hb)
  · cases c with
    | init =>
        exact inSync_sendA_det F K e auth .init stA stB toA toB h tape htape
          (fun _ _ _ hc => nomatch hc)
    | both s0 r0 =>
        exact inSync_sendA_det F K e auth (.both s0 r0) stA stB toA toB h tape htape
          (fun _ _ _ hc => nomatch hc)
    | seed s =>
        by_cases hhr : ∃ hr, stA = .headerReceived hr
        · exact inSync_sendA_det F K e auth (.seed s) stA stB toA toB h tape htape
            (fun hb s' r' hc hrList => hkem hb s' r' ⟨hc, hhr⟩ hrList)
        · have hnhr : ∀ hr, stA ≠ .headerReceived hr := fun hr hEq => hhr ⟨hr, hEq⟩
          have hE := (inSync_of_b hs).mp h
          rcases inSyncE_sendY_nodraw F K e auth s stB stA toA toB hE hnhr tape with
            ⟨hsend, hE'⟩
          have hnc := nextCoins_seed_of_not_hr F s stA hnhr tape
          rw [hnc]
          exact ⟨noneMsg e, none, stA, tape, hsend, Or.inl ⟨rfl, rfl⟩, (inSync_of_b hs).mpr hE'⟩

/-- Party `B` send step requiring `KemOk` only when `DrawsEnc F c stB s` holds. -/
theorem inSync_sendB_tight (F : ShaCompress) (K : MlKem) (e : Epoch) (auth : Authenticator)
    (c : Coins) (stA stB : St F) (toA toB : List Msg) (h : InSync F K e auth c stA stB toA toB)
    (tape : Bytes) (htape : 64 ≤ tape.length)
    (hkem : ekSide e = .a → ∀ (s : Seed) (r : EncRand), DrawsEnc F c stB s →
      r.toList = tape.take 32 → KemOk K s r) :
    ∃ (m : Msg) (key : Option EpochSecret) (stB' : St F) (tape' : Bytes),
      stB.send K tape = .ok ({ msg := m, key := key, state := stB' }, tape') ∧
      CoinStep F K e tape c (nextCoins F c stB tape) key ∧
      InSync F K e auth (nextCoins F c stB tape) stA stB' (toA ++ [m]) toB := by
  cases hs : ekSide e
  · cases c with
    | init =>
        exact inSync_sendB_det F K e auth .init stA stB toA toB h tape htape
          (fun _ _ _ hc => nomatch hc)
    | both s0 r0 =>
        exact inSync_sendB_det F K e auth (.both s0 r0) stA stB toA toB h tape htape
          (fun _ _ _ hc => nomatch hc)
    | seed s =>
        by_cases hhr : ∃ hr, stB = .headerReceived hr
        · exact inSync_sendB_det F K e auth (.seed s) stA stB toA toB h tape htape
            (fun ha s' r' hc hrList => hkem ha s' r' ⟨hc, hhr⟩ hrList)
        · have hnhr : ∀ hr, stB ≠ .headerReceived hr := fun hr hEq => hhr ⟨hr, hEq⟩
          have hE := (inSync_of_a hs).mp h
          rcases inSyncE_sendY_nodraw F K e auth s stA stB toB toA hE hnhr tape with
            ⟨hsend, hE'⟩
          have hnc := nextCoins_seed_of_not_hr F s stB hnhr tape
          rw [hnc]
          exact ⟨noneMsg e, none, stB, tape, hsend, Or.inl ⟨rfl, rfl⟩, (inSync_of_a hs).mpr hE'⟩
  · exact inSync_sendB_det F K e auth c stA stB toA toB h tape htape
      (fun ha => by rw [hs] at ha; nomatch ha)

/-- Honest two-party braid runs requiring `KemOk` only at `DrawsEnc` steps. -/
inductive RunT (F : ShaCompress) (K : MlKem) (authKey : Bytes) :
    Epoch → Authenticator → Coins → St F → St F → List Msg → List Msg → Prop
  | init (stA stB : St F)
      (hA : States.init_a spqrPolyApi (spqrAuthApi F) authKey = .ok stA)
      (hB : States.init_b spqrPolyApi (spqrAuthApi F) authKey = .ok stB) :
      RunT F K authKey 1#64 (Authenticator.new F authKey 1#64) .init stA stB [] []
  | sendA {e : Epoch} {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
      (hr : RunT F K authKey e auth c stA stB toA toB) (tape : Bytes) (htape : 64 ≤ tape.length)
      (hkem : ekSide e = .b → ∀ (s : Seed) (r : EncRand), DrawsEnc F c stA s →
        r.toList = tape.take 32 → KemOk K s r)
      (m : Msg) (key : Option EpochSecret) (stA' : St F) (tape' : Bytes)
      (hsend : stA.send K tape = .ok ({ msg := m, key := key, state := stA' }, tape')) :
      RunT F K authKey e auth (nextCoins F c stA tape) stA' stB toA (toB ++ [m])
  | sendB {e : Epoch} {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
      (hr : RunT F K authKey e auth c stA stB toA toB) (tape : Bytes) (htape : 64 ≤ tape.length)
      (hkem : ekSide e = .a → ∀ (s : Seed) (r : EncRand), DrawsEnc F c stB s →
        r.toList = tape.take 32 → KemOk K s r)
      (m : Msg) (key : Option EpochSecret) (stB' : St F) (tape' : Bytes)
      (hsend : stB.send K tape = .ok ({ msg := m, key := key, state := stB' }, tape')) :
      RunT F K authKey e auth (nextCoins F c stB tape) stA stB' (toA ++ [m]) toB
  | recvA {e : Epoch} {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
      (hr : RunT F K authKey e auth c stA stB toA toB) (m : Msg) (hm : m ∈ toA)
      (hne : m ≠ noneMsg (e + 1#64)) (key : Option EpochSecret) (stA' : St F)
      (hrecv : stA.recv K m = .ok { key := key, state := stA' }) :
      RunT F K authKey e auth c stA' stB toA toB
  | recvB {e : Epoch} {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
      (hr : RunT F K authKey e auth c stA stB toA toB) (m : Msg) (hm : m ∈ toB)
      (hne : m ≠ noneMsg (e + 1#64)) (key : Option EpochSecret) (stB' : St F)
      (hrecv : stB.recv K m = .ok { key := key, state := stB' }) :
      RunT F K authKey e auth c stA stB' toA toB
  | advanceA {e : Epoch} {auth : Authenticator} {s : Seed} {r : EncRand} {stA stB : St F}
      {toA toB : List Msg} (hr : RunT F K authKey e auth (.both s r) stA stB toA toB)
      (hm : noneMsg (e + 1#64) ∈ toA) (hnext : e.toNat + 2 < 2 ^ 64) (stA' : St F)
      (hrecv : stA.recv K (noneMsg (e + 1#64)) = .ok { key := none, state := stA' }) :
      RunT F K authKey (e + 1#64) (authNext F K e auth s r) .init stA' stB toA toB
  | advanceB {e : Epoch} {auth : Authenticator} {s : Seed} {r : EncRand} {stA stB : St F}
      {toA toB : List Msg} (hr : RunT F K authKey e auth (.both s r) stA stB toA toB)
      (hm : noneMsg (e + 1#64) ∈ toB) (hnext : e.toNat + 2 < 2 ^ 64) (stB' : St F)
      (hrecv : stB.recv K (noneMsg (e + 1#64)) = .ok { key := none, state := stB' }) :
      RunT F K authKey (e + 1#64) (authNext F K e auth s r) .init stA stB' toA toB

private theorem ok_eq_impT {ε α : Type} {a b : α} (h : (Except.ok a : Except ε α) = Except.ok b) :
    a = b := by
  cases h; rfl

private theorem coins_both_injT {s s0 : Seed} {r r0 : EncRand}
    (h : Coins.both s r = Coins.both s0 r0) : s = s0 ∧ r = r0 := by
  cases h; exact ⟨rfl, rfl⟩

/-- Every tight honest braid run `RunT` satisfies `InSync`. -/
theorem runT_inSync (F : ShaCompress) (K : MlKem) (authKey : Bytes) {e : Epoch}
    {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
    (hr : RunT F K authKey e auth c stA stB toA toB) : InSync F K e auth c stA stB toA toB := by
  induction hr with
  | init stA stB hA hB =>
    rcases inSync_init F K authKey with ⟨stA0, stB0, hA0, hB0, hIn⟩
    have hEqA : stA = stA0 := ok_eq_impT (hA.symm.trans hA0)
    have hEqB : stB = stB0 := ok_eq_impT (hB.symm.trans hB0)
    rw [← hEqA, ← hEqB] at hIn
    exact hIn
  | sendA _ tape htape hkem m key stA' tape' hsend ih =>
    rcases inSync_sendA_tight F K _ _ _ _ _ _ _ ih tape htape hkem with
      ⟨m0, key0, stA0, tape0, hsend0, _, hIn⟩
    have ho := congrArg Prod.fst (ok_eq_impT (hsend.symm.trans hsend0))
    have hmEq : m = m0 := congrArg (fun o => o.msg) ho
    have hstEq : stA' = stA0 := congrArg (fun o => o.state) ho
    rw [← hmEq, ← hstEq] at hIn
    exact hIn
  | sendB _ tape htape hkem m key stB' tape' hsend ih =>
    rcases inSync_sendB_tight F K _ _ _ _ _ _ _ ih tape htape hkem with
      ⟨m0, key0, stB0, tape0, hsend0, _, hIn⟩
    have ho := congrArg Prod.fst (ok_eq_impT (hsend.symm.trans hsend0))
    have hmEq : m = m0 := congrArg (fun o => o.msg) ho
    have hstEq : stB' = stB0 := congrArg (fun o => o.state) ho
    rw [← hmEq, ← hstEq] at hIn
    exact hIn
  | recvA _ m hm hne key stA' hrecv ih =>
    rcases inSync_recvA_stay F K _ _ _ _ _ _ _ ih m hm hne with ⟨key0, stA0, hrecv0, _, hIn⟩
    have ho := ok_eq_impT (hrecv.symm.trans hrecv0)
    have hstEq : stA' = stA0 := congrArg (fun o => o.state) ho
    rw [← hstEq] at hIn
    exact hIn
  | recvB _ m hm hne key stB' hrecv ih =>
    rcases inSync_recvB_stay F K _ _ _ _ _ _ _ ih m hm hne with ⟨key0, stB0, hrecv0, _, hIn⟩
    have ho := ok_eq_impT (hrecv.symm.trans hrecv0)
    have hstEq : stB' = stB0 := congrArg (fun o => o.state) ho
    rw [← hstEq] at hIn
    exact hIn
  | advanceA _ hm hnext stA' hrecv ih =>
    rcases inSync_advanceA F K _ _ _ _ _ _ _ ih hm hnext with ⟨s0, r0, hc, stA0, hrecv0, hIn⟩
    rcases coins_both_injT hc with ⟨hsEq, hrEq⟩
    have ho := ok_eq_impT (hrecv.symm.trans hrecv0)
    have hstEq : stA' = stA0 := congrArg (fun o => o.state) ho
    rw [← hsEq, ← hrEq, ← hstEq] at hIn
    exact hIn
  | advanceB _ hm hnext stB' hrecv ih =>
    rcases inSync_advanceB F K _ _ _ _ _ _ _ ih hm hnext with ⟨s0, r0, hc, stB0, hrecv0, hIn⟩
    rcases coins_both_injT hc with ⟨hsEq, hrEq⟩
    have ho := ok_eq_impT (hrecv.symm.trans hrecv0)
    have hstEq : stB' = stB0 := congrArg (fun o => o.state) ho
    rw [← hsEq, ← hrEq, ← hstEq] at hIn
    exact hIn

/-- Every `Run` trace is a `RunT` trace. -/
theorem runT_of_run (F : ShaCompress) (K : MlKem) (authKey : Bytes) {e : Epoch}
    {auth : Authenticator} {c : Coins} {stA stB : St F} {toA toB : List Msg}
    (hr : Run F K authKey e auth c stA stB toA toB) : RunT F K authKey e auth c stA stB toA toB := by
  induction hr with
  | init stA stB hA hB => exact .init stA stB hA hB
  | sendA _ tape htape hkem m key stA' tape' hsend ih =>
    exact .sendA ih tape htape (fun hb s r hd hrList => hkem hb s r hd.1 hrList) m key stA' tape' hsend
  | sendB _ tape htape hkem m key stB' tape' hsend ih =>
    exact .sendB ih tape htape (fun ha s r hd hrList => hkem ha s r hd.1 hrList) m key stB' tape' hsend
  | recvA _ m hm hne key stA' hrecv ih => exact .recvA ih m hm hne key stA' hrecv
  | recvB _ m hm hne key stB' hrecv ih => exact .recvB ih m hm hne key stB' hrecv
  | advanceA _ hm hnext stA' hrecv ih => exact .advanceA ih hm hnext stA' hrecv
  | advanceB _ hm hnext stB' hrecv ih => exact .advanceB ih hm hnext stB' hrecv

end CryptoVerification.SpqrV1Sync.Braid
