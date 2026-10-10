#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "parser/ast_type.h"

namespace delta {

struct ModuleItem;

// §6.16 (printed pages 112-113): a string variable takes a string literal or a
// value of string type directly, and a value of an integral type only through
// a cast; the subclause's examples hold the other direction to the same rule,
// a string assigned to an integral variable, or to one character of a string,
// needing a cast too. Reports, among `items`, each procedural assignment and
// each declaration's initializer that writes a value of one side to a target
// of the other without a cast. `var_types` gives the declared kind of each of
// the module's variables, an array's being its element's, and `arrays` names
// those that are unpacked arrays.
void CheckStringNumericAssignments(
    const std::vector<ModuleItem*>& items,
    const std::unordered_map<std::string_view, DataTypeKind>& var_types,
    const std::unordered_set<std::string_view>& arrays, DiagEngine& diag);

}  // namespace delta
