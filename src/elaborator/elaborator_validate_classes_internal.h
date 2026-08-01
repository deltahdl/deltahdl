#pragma once

// Internal declarations shared between the elaborator_validate_class_*.cpp
// translation units that were split out of elaborator_validate_classes.cpp.
// These helpers are file-local in spirit; the header exists only so that one
// translation unit can define a helper that another references, keeping a
// single definition of each symbol.

#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/rtlir.h"
#include "parser/ast.h"

namespace delta {

using TypeMap = std::unordered_map<std::string_view, DataTypeKind>;

// One scope that declares classes, with the items it declares them among.
//
// §8.1 lets a class be declared wherever a data declaration may appear, so the
// classes of a design are spread across the compilation unit and every module,
// interface, program, checker and package in it. Rules that ask what order
// things were declared in, or what else the scope declares, are asking about
// one of these rather than about the design: a forward typedef in one module
// says nothing about a class in another, and neither does the order they were
// written in.
struct ClassScope {
  const CompilationUnit* unit = nullptr;
  const std::vector<ModuleItem*>* items = nullptr;
  std::vector<const ClassDecl*> classes;
};

// Defined in elaborator_validate_class_inheritance.cpp.
std::vector<ClassScope> DeclaredClassScopes(const CompilationUnit* unit);

// Defined in elaborator_validate_class_handles.cpp.
bool IsClassDerivedFrom(std::string_view a, std::string_view b,
                        const CompilationUnit* unit);

// Defined in elaborator_validate_class_array_assign.cpp.
bool IsSliceSelect(const Expr* e);
bool IsNonintegralIndex(const Expr* idx, const TypeMap& var_types);

}  // namespace delta
