#pragma once

#include <string_view>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/type_eval.h"

namespace delta {

struct RtlirModule;
struct Stmt;

// §10.6.2: what a force statement's target is judged against -- the nets, the
// nets of a user-defined nettype among them, the module whose variables the
// target may name, the typedefs their types are written with, and the scope a
// select's bounds fold in.
struct ForceLhsNames {
  const std::unordered_set<std::string_view>& net_names;
  const std::unordered_set<std::string_view>& nettype_net_names;
  const RtlirModule& mod;
  const TypedefMap& typedefs;
  const ScopeMap& scope;
};

// Reports §10.6.2's rule on what a force statement may name, at every statement
// position a force can stand in. Defined in elaborator_validate.cpp.
void CheckForceLhs(const Stmt* s, const ForceLhsNames& names, DiagEngine& diag);

}  // namespace delta
