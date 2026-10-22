#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/diagnostic.h"
#include "elaborator/const_eval.h"
#include "elaborator/elaborator_data.h"

namespace delta {

struct Stmt;

// §10.6.2: what a force statement's target is judged against -- the nets, the
// nets of a user-defined nettype among them, the variables declaring unpacked
// dimensions, and the scope a select's bounds fold in.
struct ForceLhsNames {
  const std::unordered_set<std::string_view>& net_names;
  const std::unordered_set<std::string_view>& nettype_net_names;
  const std::unordered_map<std::string_view, ElaboratorData::VarArrayInfo>&
      arrays;
  const ScopeMap& scope;
};

// Reports §10.6.2's rule on what a force statement may name, at every statement
// position a force can stand in. Defined in elaborator_validate.cpp.
void CheckForceLhs(const Stmt* s, const ForceLhsNames& names, DiagEngine& diag);

}  // namespace delta
