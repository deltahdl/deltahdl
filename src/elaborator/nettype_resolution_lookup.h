#pragma once

#include <string>
#include <string_view>
#include <unordered_map>

#include "elaborator/type_eval.h"

namespace delta {

struct CompilationUnit;
struct DataType;
struct ModuleItem;

// §6.6.7's Syntax 6-1 writes the with clause as `with [ package_scope |
// class_scope ] tf_identifier`, so the search for a resolution function ends in
// one of three places, and which one it was is part of the answer: §6.6.7 lets
// a class function method serve as a resolution function only if it is static,
// since the call happens with no class object involved (printed page 98 of IEEE
// 1800-2023), so whether the function is a class method decides which
// requirements it is held to.
//
// `scope_named_nothing` separates a qualifier that reaches neither a package
// nor a class from one that reaches a scope declaring no such function. They
// are different mistakes and get different reports.
struct NettypeResolutionTarget {
  const ModuleItem* fn = nullptr;
  bool is_class_method = false;
  bool is_static_method = false;
  bool scope_named_nothing = false;
};

// The function the with clause of the nettype declaration `item` names. An
// unqualified name is looked up among `func_decls`, the functions of the design
// element being elaborated. A scope is followed along every name A.2.2.1 lets
// it write: a package, `$unit` or a class, then the classes nested in it.
NettypeResolutionTarget FindNettypeResolutionFunction(
    const ModuleItem* item, const CompilationUnit* unit,
    const std::unordered_map<std::string_view, const ModuleItem*>& func_decls,
    const TypedefMap& typedefs);

// The names of the scope a with clause wrote, outermost first and joined by
// `::`, as a report or the function's qualified name spells it. A class's
// parameter values are left out.
std::string NettypeScopeText(const DataType& scope);

}  // namespace delta
