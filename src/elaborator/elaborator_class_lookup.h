#pragma once

#include <string_view>
#include <vector>

#include "parser/ast_class.h"
#include "parser/ast_design.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"

namespace delta {

// Name lookups through the classes of a compilation unit, read from the parsed
// declarations alone: a member through a class and its bases, a class through
// a package, an enclosing class or a `::` chain, and the class a declared type
// names. The §8.18 visibility checks and the §18.5.4 inline uniqueness check
// both need the class a handle expression holds, and these are the steps they
// share.

// The member named `name` of `cls` or of a class it extends, the nearest
// declaration first. A method matches by the name its method item carries.
const ClassMember* FindMemberInClass(const ClassDecl* cls,
                                     std::string_view name,
                                     const CompilationUnit* unit);

// The class named `cls_name` among the items of the package named `pkg_name`,
// or null where there is no such package or it declares no such class.
const ClassDecl* FindClassInPackage(std::string_view pkg_name,
                                    std::string_view cls_name,
                                    const CompilationUnit* unit);

// The class named `name` among the classes declared directly inside `cls`,
// which §8.23 names from outside as `cls::name`.
const ClassDecl* FindNestedClass(const ClassDecl* cls, std::string_view name);

// The classes a `::` prefix walks through, outermost first, ending in the one
// it names, read along the chain §8.23 gives it: the leftmost identifier is a
// package §26.3 resolves the next one through, or a class by its bare name, and
// each identifier after that is a class nested in the class so far. `C`,
// `p::C`, `Outer::Inner` and `p::Outer::Inner` each resolve; a typedef or a
// parameterized class in the chain answers empty.
std::vector<const ClassDecl*> ClassChainOfScopePrefix(
    const Expr* prefix, const CompilationUnit* unit);

// The class a declaration of type `dt` holds a handle to, where `chain` is the
// classes enclosing the declaration, outermost first: `C h;` by the bare name,
// `p::C h;` through the package, `Outer::Inner h;` through the enclosing class.
// A bare name is read along the chain outward and then among the unit's
// classes; a scoped name's prefix is read the same way, then as a package, and
// the type is the class nested in whichever answers. Null for a type that is
// not a class.
const ClassDecl* ClassOfDeclaredType(const DataType& dt,
                                     const std::vector<const ClassDecl*>& chain,
                                     const CompilationUnit* unit);

}  // namespace delta
