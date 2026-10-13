#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>

namespace delta {

class DiagEngine;
struct TypeShapeTables;
struct ModuleDecl;
struct ModuleItem;

// §17.3 and §17.6: the rules on the actuals the instance `item` binds to the
// formals of the checker `checker`, by name, by position or by default:
//   - an output actual is a variable or net lvalue;
//   - a `$` actual binds an untyped formal the checker reads only as a range's
//     upper bound, an instance's actual or a nested checker's default;
//   - a formal bound to a `const` cast is used in no continuous assignment
//     and no procedural code of the checker, and is referenced by none of its
//     covergroups.
void ValidateCheckerActuals(const ModuleItem* item, const ModuleDecl* checker,
                            DiagEngine& diag);

// §17.3: for an instance standing in a procedure whose automatic variables
// are `automatics`, a formal bound to an actual holding one is used in no
// continuous assignment and no procedural code of the checker.
void ValidateProceduralCheckerActuals(
    const ModuleItem* item, const ModuleDecl* checker,
    const std::unordered_set<std::string_view>& automatics, DiagEngine& diag);

// §17.2: a checker the module `decl` declares references no member or
// element of a dynamic variable `decl` declares, an array of a dimension that
// is not fixed-size or a handle of a class, judged by `tables`, and no element
// of a fork-join block of `decl`'s procedures. §17.8: nor does it call, on the
// right-hand side of a checker variable assignment, one of the functions
// `funcs` that writes an argument back, keeps state or has a side effect.
void ValidateCheckerEnclosingRefs(
    const ModuleDecl* decl, const TypeShapeTables& tables,
    const std::unordered_map<std::string_view, const ModuleItem*>& funcs,
    DiagEngine& diag);

}  // namespace delta
