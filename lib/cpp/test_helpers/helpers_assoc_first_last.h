#pragma once

#include <utility>

#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

// Create string-keyed assoc array "aa" with entries
// {"cherry":3, "apple":1, "banana":2} and a 48-bit ref variable "s".
// Shared by the §7.9.4 first() and §7.9.5 last() string-key tests, which build
// this exact array and differ only in the method invoked.
inline std::pair<AssocArrayObject*, Variable*> MakeAssocWith3StringEntries(
    SimFixture& f) {
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  aa->str_data["cherry"] = MakeLogic4VecVal(f.arena, 32, 3);
  aa->str_data["apple"] = MakeLogic4VecVal(f.arena, 32, 1);
  aa->str_data["banana"] = MakeLogic4VecVal(f.arena, 32, 2);
  auto* ref = f.ctx.CreateVariable("s", 48);
  ref->value = MakeLogic4VecVal(f.arena, 48, 0);
  return {aa, ref};
}

// Build assoc array "aa" (index_width 32) holding a single int entry
// {42:value} plus a 32-bit ref variable "k", then evaluate aa.first(k),
// filling `out` with the method result and `*ref_out` with the ref variable.
// Returns whether the call evaluated. Shared by the §7.9.4 and §7.9.8 tests
// that assert first() over an equal-width key returns 1 and writes key 42; the
// stored value differs between sites but does not affect the traversal result.
inline bool EvalFirstSingleEntry42(SimFixture& f, uint64_t value,
                                   Variable** ref_out, Logic4Vec& out) {
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  aa->int_data[42] = MakeLogic4VecVal(f.arena, 32, value);
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, 0);
  auto* call = MkAssocCall(f.arena, "aa", "first", "k");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  *ref_out = ref;
  return ok;
}
