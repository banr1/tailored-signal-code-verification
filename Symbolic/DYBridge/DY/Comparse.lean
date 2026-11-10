/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import DY.Comparse
import all DY.Comparse

public section

namespace Symbolic.DYBridge

theorem DY.Comparse.serialize_eq_1 :
    ∀ [DY.BytesFunctor] [DY.BytesLength]
      [DY.BytesFunctor.Has DY.Literal.SubF] [DY.BytesLength.Has DY.Literal.SubF.length]
      [DY.BytesFunctor.Has DY.Concat.SubF] [DY.BytesLength.Has DY.Concat.SubF.length] {a : Type}
      [DY.Comparse.ParseableSerializeable a] (x : a),
      DY.Comparse.serialize x = DY.Comparse.ParseableSerializeable.mf.serialize x :=
  @_root_.DY.Comparse.serialize.eq_1

end Symbolic.DYBridge

end
