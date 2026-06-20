#pragma once

#include <cstdint>
#include <initializer_list>
#include <string>
#include <string_view>
#include <utility>

#include "common/arena.h"
#include "fixture_simulator.h"
#include "helpers_assoc.h"
#include "simulator/eval_array.h"

using namespace delta;

// Outcome of running a string-keyed next()/prev() traversal: the method's
// success return code, its output value, and the index variable read back
// after the call (so a test can assert either the return code, the rewritten
// key, or that the key was left untouched).
struct AssocTraversalResult {
  bool ok;
  Logic4Vec out;
  uint64_t ref_after;
};

// Build an integer-keyed assoc array "aa" populated with the given
// {key, value} entries and an index variable "k" initialised to ref_val.
// Used by §7.9.6 next() and §7.9.7 prev() traversal tests, which share this
// exact setup and differ only in the entry set, the starting index, and the
// method being exercised.
inline std::pair<AssocArrayObject*, Variable*> MakeAssocIntEntries(
    SimFixture& f, std::initializer_list<std::pair<int64_t, uint64_t>> entries,
    uint64_t ref_val) {
  auto* aa = f.ctx.CreateAssocArray("aa", 32, false);
  aa->index_width = 32;
  for (const auto& [key, val] : entries) {
    aa->int_data[key] = MakeLogic4VecVal(f.arena, 32, val);
  }
  auto* ref = f.ctx.CreateVariable("k", 32);
  ref->value = MakeLogic4VecVal(f.arena, 32, ref_val);
  return {aa, ref};
}

// Encode a short ASCII string (each character packed one byte per position,
// most-significant byte first) into a Logic4Vec whose width is one byte per
// character. This matches the string-key representation used by the assoc
// traversal tests.
inline Logic4Vec MakeAssocStringKeyVec(Arena& arena, std::string_view s) {
  auto v = MakeLogic4Vec(arena, static_cast<uint32_t>(s.size()) * 8);
  uint64_t packed = 0;
  for (char c : s) {
    packed = (packed << 8) | static_cast<uint64_t>(static_cast<uint8_t>(c));
  }
  v.words[0].aval = packed;
  return v;
}

// Build a string-keyed assoc array "aa" from the given keys (each mapped to a
// distinct nonzero value), seed an index variable "s" (48 bits wide) with
// start_key's packed encoding, then invoke method ("next" or "prev") on it.
// Returns the call's success flag, output value, and the index variable's
// value after the call. The §7.9.6/§7.9.7 string traversal tests share this
// exact setup and differ only in the key set, the start key, the method, and
// which part of the result they assert.
inline AssocTraversalResult RunAssocStringTraversal(
    SimFixture& f, std::initializer_list<std::string_view> keys,
    std::string_view start_key, std::string_view method) {
  auto* aa = f.ctx.CreateAssocArray("aa", 32, true);
  uint64_t val = 1;
  for (std::string_view key : keys) {
    aa->str_data[std::string(key)] = MakeLogic4VecVal(f.arena, 32, val++);
  }
  auto* ref = f.ctx.CreateVariable("s", 48);
  ref->value = MakeAssocStringKeyVec(f.arena, start_key);
  Logic4Vec out{};
  auto* call = MkAssocCall(f.arena, "aa", method, "s");
  bool ok = TryEvalAssocMethodCall(call, f.ctx, f.arena, out);
  return {ok, out, ref->value.ToUint64()};
}
