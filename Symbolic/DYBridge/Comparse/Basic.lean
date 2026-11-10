/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Comparse.Basic
import all Comparse.Basic

public section

namespace Symbolic.DYBridge

theorem Comparse.concatPrefixes_eq_1 :
    ∀ {Bytes : Type} [Comparse.BytesLike Bytes] (prefixes : List Bytes)
      (suffix : Bytes),
      Comparse.concatPrefixes prefixes suffix = List.foldr Comparse.BytesLike.concat suffix prefixes :=
  @_root_.Comparse.concatPrefixes.eq_1

end Symbolic.DYBridge

end
