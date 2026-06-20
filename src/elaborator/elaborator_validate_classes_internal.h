#pragma once

// Internal declarations shared between the elaborator_validate_class_*.cpp
// translation units that were split out of elaborator_validate_classes.cpp.
// These helpers are file-local in spirit; the header exists only so that one
// translation unit can define a helper that another references, keeping a
// single definition of each symbol.

#include <string_view>
#include <unordered_map>

#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

// Defined in elaborator_validate_class_handles.cpp.
bool IsClassDerivedFrom(std::string_view a, std::string_view b,
                        const CompilationUnit* unit);

// Defined in elaborator_validate_class_array_assign.cpp.
bool IsSliceSelect(const Expr* e);
bool IsNonintegralIndex(const Expr* idx, const TypeMap& var_types);

}  // namespace delta
