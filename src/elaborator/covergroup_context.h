#ifndef DELTA_ELABORATOR_COVERGROUP_CONTEXT_H
#define DELTA_ELABORATOR_COVERGROUP_CONTEXT_H

#include <functional>
#include <optional>
#include <string_view>

#include "elaborator/coverpoint_bin_set_expression.h"
#include "elaborator/value_kind.h"
#include "parser/ast_type.h"

namespace delta {

struct CoverPointDecl;
struct CovergroupDecl;
struct Expr;
struct ModuleItem;

// The type of the variable a name a covergroup reads denotes, or nothing where
// it denotes none; and whether the name is visible where the covergroup is
// declared at all.
using CovergroupTypeOf =
    std::function<std::optional<DataTypeKind>(std::string_view)>;
using CovergroupDeclared = std::function<bool(std::string_view)>;

// The arrays a covergroup reads where it is declared: the kind of array a name
// denotes, or nothing where it denotes no unpacked array, and whether a name is
// a type, as the index of an associative array may be (§7.8).
struct CovergroupArrays {
  std::function<std::optional<SetExpressionArrayKind>(std::string_view)>
      kind_of;
  CovergroupDeclared is_type;
};

// The kind of value an expression a covergroup reads gives where the
// covergroup is declared, kUnknown where the declarations there do not tell.
using CovergroupValueKind = std::function<ValueKind(const Expr*)>;

// The function a name a covergroup calls denotes where the covergroup is
// declared, or null where it denotes none.
using CovergroupFunction = std::function<const ModuleItem*(std::string_view)>;

// What a covergroup reads where it is declared, a module or a class (§19.3,
// §19.4):
// - type_of, declared and arrays, for the names its expressions read;
// - value_kind, for the kind of value an expression gives;
// - non_constant, whether a name denotes a variable or property that is no
//   constant (§11.2.1, §8.19), which a covergroup_expression may not read
//   (§19.5);
// - function_named, for the functions its expressions call;
// - is_class, whether a name denotes a class type.
struct CovergroupContext {
  CovergroupTypeOf type_of;
  CovergroupDeclared declared;
  CovergroupArrays arrays;
  CovergroupValueKind value_kind;
  CovergroupDeclared non_constant;
  CovergroupFunction function_named;
  CovergroupDeclared is_class;
};

// The formal of `cg` named `name`, or null where it has none.
const FunctionArg* FindCovergroupFormal(const CovergroupDecl& cg,
                                        std::string_view name);

// Whether the formal of `cg` named `name` is a `ref` formal, a formal written
// without a direction taking the one before it (§13.3).
bool IsRefCovergroupFormal(const CovergroupDecl& cg, std::string_view name);

// §19.5: the kind of value a variable declared of type `type` gives: a string
// is kString; a chandle, an event and a handle of a class `is_class` names are
// kOther, no integral or real value; kUnknown for any type it cannot place.
ValueKind KindOfDeclaredType(const DataType& type,
                             const CovergroupDeclared& is_class);

// §19.5: the name a coverpoint goes by, its label or, unlabelled, the variable
// its expression names; empty for an unlabelled coverpoint of any other
// expression.
std::string_view CoverpointName(const CoverPointDecl& cp);

}  // namespace delta

#endif  // DELTA_ELABORATOR_COVERGROUP_CONTEXT_H
