#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"

namespace delta {

struct RtlirModule;
struct Stmt;

struct ForceLhsNames {
  const std::unordered_set<std::string_view>& net_names;
  const std::unordered_set<std::string_view>& nettype_net_names;
  const RtlirModule& mod;
  const TypedefMap& typedefs;
  const ScopeMap& scope;
};

void CheckForceLhs(const Stmt* s, const ForceLhsNames& names, DiagEngine& diag);

}  // namespace delta
