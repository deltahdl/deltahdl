#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

#include "common/source_loc.h"
#include "elaborator/elaborator_helpers.h"
#include "elaborator/uwire_drivers.h"
#include "parser/ast_type.h"

namespace delta {

// What a module's generate blocks are elaborated against, the module's own
// items having been elaborated and checked before them: the names it declares;
// the nets among them, by which an alias in a block tells the module's nets
// from its variables (§10.11 with §27.5); the variables its continuous and its
// procedural assignments write, which §6.5's and §10.3.2's one-driver rules
// weigh a block's assignments against; the variables declared with an
// initializer, which §10.3.2 bars a block's continuous assignment from; the
// bits of its uwire nets its drivers reach, which §6.6.2 weighs a block's
// drivers against; its interconnects, which §6.6.8 keeps out of a block's
// expressions; the variables its forces and releases are applied to, which
// §10.6.2 bars a block's assignments from making a variable of mixed
// continuous and procedural assignments; and the types of its variables and
// parameters, by which a block's items are held to the rules a module's own
// items are held to (§6.12, §6.14, §8, §11.5.1, §25.9).
struct ModuleScopeNames {
  std::unordered_set<std::string_view> declared;
  std::unordered_set<std::string_view> nets;
  std::unordered_map<std::string_view, SourceLoc> cont_targets;
  std::unordered_map<std::string_view, SourceLoc> proc_targets;
  std::unordered_set<std::string_view> initialized;
  UwireDrivers uwire_drivers;
  std::unordered_set<std::string_view> interconnects;
  std::unordered_map<std::string_view, SourceLoc> force_targets;
  std::unordered_map<std::string_view, DataTypeKind> var_types;
  std::unordered_map<std::string_view, std::string_view> class_var_types;
  std::unordered_set<std::string_view> scalar_vars;
  std::unordered_set<std::string_view> real_vars;
  std::unordered_set<std::string_view> real_params;
  std::unordered_map<std::string_view, VarSelectShape> select_shapes;
  std::unordered_set<std::string_view> class_vars;
};

}  // namespace delta
