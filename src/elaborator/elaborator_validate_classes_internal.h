#pragma once

// Internal declarations shared between the elaborator_validate_class_*.cpp
// translation units that were split out of elaborator_validate_classes.cpp.
// These helpers are file-local in spirit; the header exists only so that one
// translation unit can define a helper that another references, keeping a
// single definition of each symbol.

#include <cstddef>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/type_eval.h"
#include "elaborator/value_kind.h"
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

// Defined in elaborator_validate_class_overrides.cpp: §8.25, the argument of
// the specialization `args` binding the class parameter `name`, the `index`th
// the class declares: by name where the specialization names its arguments,
// .Y(int), and by position otherwise; null where it binds none, which leaves
// the parameter its default.
const DataType* SpecializationArgument(const std::vector<DataType>& args,
                                       std::size_t index,
                                       std::string_view name);

// Defined in elaborator_validate_class_overrides.cpp: §8.20 with §8.25, the
// virtual overrides of the class the specialization `type` names whose
// argument types, written in that class's own type parameters, do not match
// the overridden method's under the types the specialization gives them,
// reported at `loc`, where the specialization is written. The generic
// declaration leaves such an argument to its specializations.
void ReportSpecializationOverrideMismatches(const DataType& type, SourceLoc loc,
                                            const CompilationUnit* unit,
                                            const TypedefMap& typedefs,
                                            DiagEngine& diag);

// §8.24: the declaration holding the body of the method `method` declares,
// the out-of-block declaration defining it where `method` is an `extern`
// prototype one defines, else `method` itself. The class rules read a method's
// body, and report at its declaration, through this.
inline const ModuleItem* MethodBody(const ModuleItem* method) {
  return method->out_of_block_body != nullptr ? method->out_of_block_body
                                              : method;
}

// Defined in elaborator_validate_class_handles.cpp.
bool IsClassDerivedFrom(std::string_view a, std::string_view b,
                        const CompilationUnit* unit);

// A subroutine body a scope declares, with the classes it stands inside,
// innermost first: the class it is a method of, or defines out of block
// (§8.24), and the classes that class is nested in (§8.23). Empty for a
// subroutine of a module, interface, program, package or the compilation unit.
struct SubroutineSite {
  const ModuleItem* sub = nullptr;
  std::vector<const ClassDecl*> inside;
};

// Defined in elaborator_validate_class_bodies.cpp: every subroutine body among
// `items`, a scope's own items, and the methods of the classes declared among
// them and in `classes` (the compilation unit's, which its items do not hold),
// nested classes' included.
std::vector<SubroutineSite> SubroutinesAmong(
    const std::vector<ModuleItem*>& items,
    const std::vector<const ClassDecl*>& classes = {});

// Defined in elaborator_validate_class_bodies.cpp: §8.4, whether `e` yields a
// class handle: a handle variable `names` holds; an element of an array of
// handles, a variable `types` holds but `names` does not, selected once
// (§7.4); a property of a class type selected from a handle, h.next (§8.5);
// or a call of a function the design declares returning a class handle
// (§13.4).
bool IsHandleOperand(
    const Expr* e, const std::unordered_set<std::string_view>& names,
    const std::unordered_map<std::string_view, std::string_view>& types,
    const CompilationUnit* unit);

// Defined in elaborator_validate_class_bodies.cpp: adds to `names` and `types`
// the handle variables the body of `site` sees besides its scope's: in a
// method, the properties of a class type of its class and the classes that
// class extends (§8.11, §8.13), its formal arguments of a class type, and a
// function's own name where it returns one (§13.4.1). A
// variable with an unpacked dimension is an array of handles (§7.4), so it
// enters `types` alone.
void AddSubroutineHandles(
    const SubroutineSite& site,
    const std::unordered_set<std::string_view>& class_names,
    const CompilationUnit* unit, std::unordered_set<std::string_view>& names,
    std::unordered_map<std::string_view, std::string_view>& types);

// Defined in elaborator_validate_class_array_assign.cpp.
bool IsSliceSelect(const Expr* e);
bool IsNonintegralIndex(const Expr* idx, const ValueScope& values);

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
