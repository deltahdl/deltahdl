#pragma once

#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/diagnostic.h"
#include "common/source_loc.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

// §6.20.3: a type parameter may prefix the class scope resolution operator in
// a typedef declaration, the type operator and a type parameter assignment,
// and it shall be an error where the prefix does not resolve to a class. Which
// type the parameter resolves to is the instance's to say, an override as much
// as the default, so the check runs as each instance elaborates the place the
// prefix is written in.

namespace delta {

// The names an instance's scope binds while it elaborates: its parameters, the
// type each typedef and type parameter stands for, and the classes it sees.
struct TypeParamPrefixScope {
  const std::vector<RtlirParamDecl>& params;
  const TypedefMap& typedefs;
  const std::unordered_set<std::string_view>& class_names;
};

// Reports, at `loc`, a scope prefix `prefix` that names one of the scope's type
// parameters bound to a type that is not a class. A prefix naming anything
// else, or a parameter bound to a name the scope cannot follow to a type, is
// left alone.
void ReportTypeParamPrefixNotAClass(std::string_view prefix, SourceLoc loc,
                                    const TypeParamPrefixScope& scope,
                                    DiagEngine& diag);

// ReportTypeParamPrefixNotAClass for the prefix of `ref`, the argument of a
// type operator, where it is a scope resolution of one name by another,
// `type(T::inner)`.
void ReportTypeRefPrefixNotAClass(const Expr* ref, SourceLoc loc,
                                  const TypeParamPrefixScope& scope,
                                  DiagEngine& diag);

// The typedef `type(prefix::name)` names where `prefix` is a type parameter or
// typedef `typedefs` binds to a class (ThroughBoundPrefix); null otherwise.
const DataType* TypeRefThroughBoundPrefix(std::string_view prefix,
                                          std::string_view name,
                                          const TypedefMap& typedefs);

// Reports, at `loc`, a specialization `written` of a parameterized class -- `P
// #(int)`, or `P` alone, the default specialization -- that binds a type
// parameter to a type that is not a class where the class's body selects a
// type through that parameter, `typedef C::T t;` or `localparam type t =
// C::T;`. A type parameter bound to a name is left alone, as above.
void ReportSpecializationPrefixNotAClass(const DataType& written, SourceLoc loc,
                                         const CompilationUnit* unit,
                                         DiagEngine& diag);

// ReportTypeParamPrefixNotAClass for each typedef and type parameter the body
// of the procedure or subroutine `item` declares, and each type operator its
// declarations write: a prefix naming a type parameter the body declares is
// judged by the type that declaration gives it, and one naming the instance's
// by `scope`. Where `item` declares a checker, the same for the checker's
// items, its type operators included, since the checker is elaborated as an
// instance of its own that does not see the parameters of `scope`.
void ReportItemPrefixesNotAClass(const ModuleItem& item,
                                 const TypeParamPrefixScope& scope,
                                 DiagEngine& diag);

// The same for each package and the compilation unit, whose own type
// parameters no instance overrides: the prefixes their typedefs, type
// parameters and variables write, and those of the subroutines they declare.
void ReportUnitScopePrefixesNotAClass(const CompilationUnit* unit,
                                      DiagEngine& diag);

// ReportSpecializationPrefixNotAClass for each specialization the compilation
// unit writes as the type of a typedef or variable of its own, or a class at
// its scope writes as the type of a property or a typedef.
void ReportUnitSpecializations(const CompilationUnit* unit, DiagEngine& diag);

}  // namespace delta
