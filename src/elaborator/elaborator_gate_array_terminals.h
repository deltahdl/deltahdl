#pragma once

#include <cstdint>
#include <vector>

#include "elaborator/const_eval.h"

namespace delta {

class Arena;
struct Expr;
struct RtlirModule;

// Where the terminals of one array of gate, switch or UDP instances are read:
// the module and the scope that size them, and the arena the bit-selects are
// made in.
struct GateArraySite {
  const RtlirModule* mod;
  const ScopeMap& scope;
  Arena& arena;
};

// §28.3.6: the terminal list element `p` of an instance array of `array_len`
// elements connects to, counted from the element of the range's right-hand
// index. A terminal as wide as an array of more than one element gives element
// `p` its bit `p` above the least significant end (GateTerminalBit), and any
// other terminal, a one-bit one among them, is connected whole. The
// elaborator builds each element from it, and the VPI model reports what each
// element connects to from it.
std::vector<Expr*> InstanceArrayElementTerminals(
    const std::vector<Expr*>& terms, const GateArraySite& site,
    uint32_t array_len, uint32_t p);

}  // namespace delta
