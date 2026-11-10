/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedBase -- proof-setup: allow-public-import
public import Computational.Proofs.ReductionDsl.FSAEAD.HybridRedZero -- proof-setup: allow-public-import
import Computational.Proofs.ReductionDsl.Size
import Computational.Proofs.ReductionDsl.Tables

/-!
# Soundness and bounds for the costed ACD19 Theorem 5 reductions

Re-exports the two-stage simulation soundness and query bounds for `prgRedZeroProg` and
`multiRedProg`, and proves `OpsSizeHonest` and `SampSizeHonest` certificates.
-/

public section

set_option autoImplicit false

namespace CryptoGames.FSAEAD.Thm5.Costed

open ReductionDsl CryptoGames.FSAEAD.Costed CryptoGames.PRG.Costed CryptoGames.OTCCA.Costed
open OracleComp OracleSpec

variable {CK MK AD M C : Type}

local notation "HSig" => fsSig CK MK AD Unit M C
local notation "HT" => Ty HSig

local notation "HSamp" =>
  unifSamplers (S := HSig) fsStateSampleSort (fun _ => 1)

local notation "hybOps" ae:arg G:arg kPRG:arg kAEAD:arg =>
  Ops.sum
    (prgOps (S := HSig) (Ty.prod Ty.nat (bt FSort.ss)) (Ty.prod (bt FSort.ss) (bt FSort.rs))
      (fun pw => PRGScheme.gen (G (Prod.fst pw)) (Prod.snd pw)) kPRG)
    (otccaOps (S := HSig) (bt FSort.rs) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ad)
      (bt FSort.msg) (bt FSort.ct) ae kAEAD Ty.unit (fun _ => ()))

local notation "prgRedZeroIface" ideal:arg kIdeal:arg =>
  Iface.withSamp
    (Iface.withSamp (prgIface HSig)
      (idealSamplers (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.ct) ideal kIdeal))
    HSamp

local notation "multiRedIface" ideal:arg kIdeal:arg =>
  Iface.withSamp
    (otccaIface (S := HSig) (Ty.prod Ty.nat (bt FSort.ad)) (bt FSort.msg) (bt FSort.ct)
      ideal kIdeal)
    HSamp

local notation "recTy'" => recTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "kcTy'" => kcTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "slotTy'" => slotTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "hsTy'" => hsTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)
local notation "stTy'" => stTy (CK := CK) (MK := MK) (AD := AD) (M := M) (C := C)


section TopLevel

variable [DecidableEq AD] [DecidableEq M] [DecidableEq C]
  [SampleableType MK] [SampleableType CK]
  (ae : AEADScheme MK (ℕ × AD) M C) (G : ℕ → PRGScheme CK (CK × MK)) (kPRG kAEAD : ℕ)
  (ideal : ℕ × AD → ProbComp C) (kIdeal : ℕ)


omit [SampleableType MK] [SampleableType CK] in
theorem hybOps_sizeHonest (hPRG : 1 ≤ kPRG) (hAEAD : 1 ≤ kAEAD) :
    OpsSizeHonest (hybOps ae G kPRG kAEAD) :=
  OpsSizeHonest.sum
    (CryptoGames.prgOps_sizeHonest_pair (S := HSig) (.prod .nat (bt .ss)) .ss .rs
      (fun pw => (G pw.1).gen pw.2) kPRG (fun _ => hPRG) (fun _ => hPRG))
    (CryptoGames.otccaOps_sizeHonest (S := HSig) (bt .rs) (.prod .nat (bt .ad)) (bt .ad)
      (bt .msg) (bt .ct) ae kAEAD .unit (fun _ => ())
      (fun _ => hAEAD) (fun _ => hAEAD) (fun _ => trivial))

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem prgRedZeroIface_sampSizeHonest (hIdeal : 1 ≤ kIdeal) :
    SampSizeHonest (prgRedZeroIface ideal kIdeal).smp :=
  SampSizeHonest.sum
    (SampSizeHonest.sum SampSizeHonest.empty
      (CryptoGames.idealSamplers_sizeHonest (S := HSig) (.prod .nat (bt .ad)) (bt .ct)
        ideal kIdeal (fun _ _ _ => hIdeal)))
    (SampSizeHonest.unifSamplers (S := HSig) fsStateSampleSort (fun _ => 1))

omit [DecidableEq AD] [DecidableEq M] [DecidableEq C] in
theorem multiRedIface_sampSizeHonest (hIdeal : 1 ≤ kIdeal) :
    SampSizeHonest (multiRedIface ideal kIdeal).smp :=
  SampSizeHonest.sum
    (CryptoGames.idealSamplers_sizeHonest (S := HSig) (.prod .nat (bt .ad)) (bt .ct)
      ideal kIdeal (fun _ _ _ => hIdeal))
    (SampSizeHonest.unifSamplers (S := HSig) fsStateSampleSort (fun _ => 1))

end TopLevel

end CryptoGames.FSAEAD.Thm5.Costed
