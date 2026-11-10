/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1Sync.SendTotal.Defs

set_option autoImplicit false

/-!
# Top-Level Invariant Preservation Under Adversarial Receives

Proves `TopRecvClosedStmt`: `(spqrV1 F K).recv` preserves `TopAdv F K n` across all incoming
protocol version branches (`< 1`, `= 1` via `TopRecvEqualStmt`, and `> 1` during version
negotiation).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1Sync.SendTotal

open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1Sync.ChainSync
open CryptoVerification.SpqrV1Sync.TopSync
open CryptoGames.LibsignalSession (ShaCompress)

private theorem tr_bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {b : β}
    (h : (m >>= f) = .ok b) : ∃ a, m = .ok a ∧ f a = .ok b := by
  cases m with
  | error _ => cases h
  | ok a => exact ⟨a, rfl, h⟩

private theorem tr_bv8_gt_one_of_not_lt_ne {v : BitVec 8} (h1 : ¬ v < 1#8) (h2 : v ≠ 1#8) :
    v > 1#8 := by
  have hne : v.toNat ≠ 1 := fun heq => h2 (BitVec.eq_of_toNat_eq heq)
  change (1#8).toNat < v.toNat
  change ¬ v.toNat < (1#8).toNat at h1
  simp only [BitVec.toNat_ofNat] at h1 ⊢
  omega

theorem st_chainFrom_ok (F : ShaCompress) (authKey : Bytes) (dir : Direction)
    (secret : ℕ → Bytes) (sendCtr : ℕ → ℕ) (recvSet : ℕ → Finset ℕ)
    (vn? : Option VersionNegotiationPB) (ch? : Option Chain) (chE : Chain)
    (hch : ch? = some chE ∨
      (ch? = none ∧ vn? = some (vnOf dir authKey) ∧
        chainFromVersionNegotiation (spqrHkdfWith F) (vnOf dir authKey) = .ok chE))
    (hok : ChainOk F authKey dir secret sendCtr recvSet chE) :
    chainFrom (spqrHkdfWith F) (ch?.map Chain.intoPb) vn? = .ok chE := by
  rcases hch with rfl | ⟨rfl, rfl, hvn⟩
  · simpa [chainFrom] using chain_fromPb_intoPb F authKey dir secret sendCtr recvSet chE hok
  · simpa [chainFrom] using hvn

theorem st_topRecv (F : ShaCompress) (K : MlKem) (hTS : TopSizeStmt F K)
    (hRE : TopRecvEqualStmt F K) (hCR : ChainRecvStmt F) : TopRecvClosedStmt F K := by
  intro n bytes msgBytes bytes' salt hadv hn hrecv
  have hsize : bytes.length < 2 ^ 64 := hTS n bytes hadv hn
  rcases hadv with ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet, vn?, ch?, chE, w⟩
  rw [spqrV1_eq] at hrecv
  dsimp only [toSpqrModel] at hrecv
  cases hr : LibsignalSpqrV1.recv (spqrDeps F K) (spqrHkdfWith F) bytes msgBytes with
  | error e =>
    cases e <;> simp [hr] at hrecv
  | ok r =>
    simp only [hr] at hrecv
    cases hs : recvKeyToSalt? r.key with
    | none => simp [hs] at hrecv
    | some _ =>
      simp only [hs, Except.ok.injEq, Prod.mk.injEq] at hrecv
      rcases hrecv with ⟨rfl, _⟩
      have hsize' : (topBytes F K st vn? ch?).length < 2 ^ 64 := w.htop.hbytes ▸ hsize
      cases hpre : msgPreamble msgBytes with
      | error _ =>
        simp [LibsignalSpqrV1.recv, hpre, SpqrApiResult.ofError, Bind.bind, Except.bind] at hr
      | ok pre =>
        by_cases hver : pre.version = 1#8
        · rw [w.htop.hbytes,
            recv_topBytes F K authKey dir st vn? ch? msgBytes pre hsize' w.htop.hvn hpre hver] at hr
          exact hRE n bytes authKey dir secret st sendEp sendCtr recvSet vn? ch? chE pre r w hn hr
        · have hdec := decodeState_topBytes F K st vn? ch? hsize'
          rw [w.htop.hbytes] at hr
          unfold LibsignalSpqrV1.recv at hr
          simp only [hpre, hdec, SpqrApiResult.ofError, Bind.bind, Except.bind, topPb,
            stateVersion] at hr
          have hv1 : Version.v1.toU8 = 1#8 := by decide
          rcases w.htop.hvn with hvn | hvn
          · subst hvn
            simp only [hv1] at hr
            by_cases hlt : pre.version < 1#8
            · simp [hlt] at hr
            · have hneB : (pre.version != 1#8) = true := bne_iff_ne.mpr hver
              simp [hlt, hneB] at hr
          · have hch0 := st_chainFrom_ok F authKey dir secret sendCtr recvSet vn? ch? chE
              w.htop.hch w.htop.hok
            subst hvn
            have hmin : (vnOf dir authKey).minVersion.truncate 8 = 1#8 := by
              change Version.v1.toI32.truncate 8 = 1#8
              decide
            simp only [hv1, hmin] at hr
            by_cases hlt : pre.version < 1#8
            · simp [hlt] at hr
            · have hgt : pre.version > 1#8 := tr_bv8_gt_one_of_not_lt_ne hlt hver
              simp only [hlt, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                show ¬ (1#8 == 0#8) = true by decide, hgt] at hr
              rw [hch0] at hr
              obtain ⟨⟨chain1, rawKey⟩, hck0, hret⟩ := tr_bind_ok hr
              have hck : chE.recvKey (spqrHkdfWith F) 0#64 pre.index = .ok (chain1, rawKey) :=
                SpqrApiResult.ofChainResult_eq_ok.mp hck0
              simp only [Except.ok.injEq] at hret
              subst hret
              obtain ⟨recvSet', hok', hsmall', hcurEq, hsendEpEq⟩ :=
                hCR authKey dir secret sendCtr recvSet chE chain1 0#64 pre.index rawKey
                  w.htop.hok w.hsmall hck
              have hsp' : SendPrevNil chain1 :=
                recvKey_sendPrevNil (spqrHkdfWith F) chE chain1 0#64 pre.index rawKey
                  w.htop.hsendPrev hck
              refine ⟨authKey, dir, secret, st, sendEp, sendCtr, recvSet',
                some (vnOf dir authKey), some chain1, chain1, ?_⟩
              exact
                { htop :=
                    { hbytes := rfl
                      hvn := Or.inr rfl
                      hch := Or.inl rfl
                      hok := hok'
                      hcur := by rw [hcurEq]; exact w.htop.hcur
                      hsendEp := by rw [hsendEpEq]; exact w.htop.hsendEp
                      hsendLe := w.htop.hsendLe
                      hsendPrev := hsp' }
                  hauth := w.hauth
                  hbok := w.hbok
                  hphi := w.hphi
                  hctr := w.hctr
                  hsmall := hsmall' }

end CryptoVerification.SpqrV1Sync.SendTotal
