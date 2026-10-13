#pragma once

#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

// Whether the value a return statement gives fits the type it is returned as.
// §12.8 asks it of a return in a nonvoid function and §18.17.7 of a return in a
// randsequence production that returns a value, each naming the other's rule as
// the one it follows, so the two checks read one type comparison.

// What the check reads besides the return statement: the typedefs and classes
// a type name may stand for, and the declared type of each name the subroutine
// or production declares, its formals and the variables its body declares,
// which no name outside it hides.
struct ReturnCtx {
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  std::unordered_map<std::string_view, const DataType*> locals;
};

// The type a return compares, as far as the check can see it: a class, or a
// type IsAssignmentCompatible answers for, or neither where the type is not
// one the check reads (`type.kind` is kImplicit and `cls` null).
struct CheckedType {
  DataType type;
  const ClassDecl* cls = nullptr;
  bool is_string_literal = false;
};

// The type `declared` stands for, followed through typedef names to the type
// it was declared with. A name the typedefs do not hold is a class or a type
// the check does not read.
CheckedType CheckedTypeOf(const DataType& declared, const ReturnCtx& ctx);

// §6.22.3: the type of a return expression as far as it is plain from the
// source: a literal's, or the declared type of a name `ctx.locals` holds,
// named whole. A member, a select, a call or an operation is not read.
CheckedType CheckedTypeOfValue(const Expr* e, const ReturnCtx& ctx);

// §6.22.3 with §8.4: whether a value of `value` may be returned where `ret` is
// the return type. A class handle fits a class it is or derives from (§8.13)
// and no other type, and no other value fits a class; two other types fit as
// IsAssignmentCompatible says of the value's type assigned to the return
// type, but for a string literal, which a string takes as it is (§6.16). A
// type the check does not read fits anything.
bool ReturnValueFits(const CheckedType& ret, const CheckedType& value,
                     const CompilationUnit* unit);

// The methods of the classes `items` declare and of the classes of `unit`. A
// method's type names are read in its class first, whose typedefs may hide the
// names of the module or the package around it, so the return check reads a
// method's names through no table of those outer names.
std::unordered_set<const ModuleItem*> ClassMethodsOf(
    const std::vector<ModuleItem*>& items, const CompilationUnit* unit);

}  // namespace delta
