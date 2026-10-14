#pragma once

#include <functional>
#include <string_view>
#include <unordered_map>
#include <vector>

#include "elaborator/type_eval.h"
#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

namespace delta {

// Whether the value a return statement gives fits the type it is returned as.
// §12.8 asks it of a return in a nonvoid function and §18.17.7 of a return in a
// randsequence production that returns a value, each naming the other's rule as
// the one it follows, so the two checks read one type comparison.

// A name in scope where a return stands: the type it was declared with and the
// unpacked dimensions written after it, none for a variable that is not an
// unpacked array. An unpacked array is a type the check does not read, but its
// dimensions tell the type of a foreach loop variable over it (§12.7.3).
struct DeclaredLocal {
  const DataType* type;
  const std::vector<Expr*>* unpacked;
};
using DeclaredLocals = std::unordered_map<std::string_view, DeclaredLocal>;

// What the check reads besides the return statement: the typedefs and classes
// a type name may stand for, and each name in scope the check knows the
// declaration of. A name it holds no entry for is one whose type it does not
// read.
struct ReturnCtx {
  const TypedefMap& typedefs;
  const CompilationUnit* unit;
  DeclaredLocals locals;
};

// Enters into `locals` the variables declared among `items`, the items of a
// subroutine body, of a randsequence code block or of a begin-end block, over
// the names already there: §23.9 makes a begin-end block a scope of its own,
// whose declarations hide the names of the same spelling around it.
void EnterDeclaredLocals(const std::vector<Stmt*>& items,
                         DeclaredLocals& locals);

// Calls `visit` on each statement directly under `s`, with the context the
// names there are read through. A begin-end block (§23.9), a for loop
// (§12.7.1) and a foreach loop (§12.7.3) are scopes whose declarations hide the
// names of the same spelling around them, so the statements under one get a
// copy of `ctx` with those declarations entered. A for loop's declared
// variable stands for its declared type. A foreach loop variable is an int over
// a fixed-size, dynamic or queue dimension and has the index type over an
// associative one, so where the dimension it walks is not plainly one of the
// first three in `ctx.locals`, it hides the outer name without standing for a
// type. A fork-join block is a scope too, but neither §12.8's nor §18.17.7's
// check reaches a return inside one, which §9.3.2 forbids.
void ForEachChildInScope(
    const Stmt* s, const ReturnCtx& ctx,
    const std::function<void(const Stmt*, const ReturnCtx&)>& visit);

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
// source: a literal's, or the declared type of a name `ctx.locals` holds that
// is not an unpacked array, named whole. A member, a select, a call or an
// operation is not read.
CheckedType CheckedTypeOfValue(const Expr* e, const ReturnCtx& ctx);

// §6.22.3 with §8.4: whether a value of `value` may be returned where `ret` is
// the return type. A class handle fits a class it is or derives from (§8.13)
// and no other type, and no other value fits a class; two other types fit as
// IsAssignmentCompatible says of the value's type assigned to the return
// type, but for a string literal, which a string takes as it is (§6.16). A
// type the check does not read fits anything.
bool ReturnValueFits(const CheckedType& ret, const CheckedType& value,
                     const CompilationUnit* unit);

// The methods of the classes `items` declare and of the classes of `unit`, each
// with the class whose body declares it. A method's type names are read in its
// class first, whose typedefs may hide the names of the module or the package
// around it, so the return check reads a method's names through no table of
// those outer names.
using ClassMethods = std::unordered_map<const ModuleItem*, const ClassDecl*>;
ClassMethods ClassMethodsOf(const std::vector<ModuleItem*>& items,
                            const CompilationUnit* unit);

// The properties a method of `cls` finds by a name it does not declare itself:
// those of `cls` and of each class it extends (§8.13), a class's own over the
// inherited ones of the same name, which it hides. None for a null `cls`.
DeclaredLocals ClassProperties(const ClassDecl* cls,
                               const CompilationUnit* unit);

// The variables `items` declare, those of a module, a package or a compilation
// unit, which §23.9's outward search finds for a name one of its subroutines
// uses without declaring it.
DeclaredLocals ScopeVariables(const std::vector<ModuleItem*>& items);

// Each class `items` declares and each class of `unit`, and each class nested
// in one (§8.23), with the names a method of it finds without declaring them:
// its ClassProperties, over the names of the scope around the class (§23.9).
// That scope is the variables of `items` or of the compilation unit, or, for a
// nested class, the names a method of the class enclosing it finds. A name the
// class or a class it extends declares hides the one of the scope around, so
// none of those is entered. Where a class of the chain extends one
// SoleClassIndex does not give, the names the chain declares are not known in
// full, and none of the scope around is entered.
using ClassScopes = std::unordered_map<const ClassDecl*, DeclaredLocals>;
ClassScopes ClassScopesOf(const std::vector<ModuleItem*>& items,
                          const CompilationUnit& unit);

}  // namespace delta
