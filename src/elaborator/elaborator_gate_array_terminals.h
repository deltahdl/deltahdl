#pragma once

#include <cstdint>
#include <vector>

#include "elaborator/const_eval.h"

namespace delta {

class Arena;
struct Expr;
struct RtlirModule;

struct GateArraySite {
  const RtlirModule* mod;
  const ScopeMap& scope;
  Arena& arena;
};

std::vector<Expr*> InstanceArrayElementTerminals(
    const std::vector<Expr*>& terms, const GateArraySite& site,
    uint32_t array_len, uint32_t p);

}  // namespace delta
