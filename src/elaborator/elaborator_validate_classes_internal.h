#pragma once

// Internal declarations shared between the elaborator_validate_class_*.cpp
// translation units that were split out of elaborator_validate_classes.cpp.
// These helpers are file-local in spirit; the header exists only so that one
// translation unit can define a helper that another references, keeping a
// single definition of each symbol.

#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

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

// Defined in elaborator_validate_static_methods.cpp: the names a statement
// brings into scope for its own expressions and its child statements (§6.21),
// and the names in scope over the whole of a method body -- its formals, its
// result name where it is a function, and the declarations at the body's top
// level. A rule that asks whether a bare name in a method is a class member
// subtracts both, §8.10 for a static method and §8.23 for a nested class.
std::unordered_set<std::string_view> NamesDeclaredUnder(const Stmt* s);
std::unordered_set<std::string_view> CollectMethodLocalNames(
    const ModuleItem* method);

}  // namespace delta
