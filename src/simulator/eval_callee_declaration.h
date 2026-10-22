#pragma once

#include <string_view>

namespace delta {

class Arena;
struct ClassTypeInfo;
struct DataType;
struct Expr;
class SimContext;

// §13.4: what the subroutine a call names declares its result to be, read
// without running the call, for those that type a call's result -- the
// enumeration a call answers (eval_enum.cpp), or whether it answers a handle to
// a process (eval_process_methods.cpp).
struct CalleeDeclaration {
  // The declared return type. DeclarationOfCallee never answers null: where
  // the callee names no subroutine the design declares, the type is an
  // implicit one, naming no type at all.
  const DataType* result = nullptr;
  // Where the names in that type are declared: the class declaring the method
  // (§8.23), or the package of a function named through its scope, `P::f`
  // (§26.3).
  const ClassTypeInfo* cls = nullptr;
  std::string_view package;
};

// §13.4 with §8.6, §8.9 and §26.3: the declaration of the subroutine `callee`,
// a call's callee, names -- a bare function or method, a static method or
// package function through a scope, `C::m` or `P::f`, or a method through a
// handle, `this` or `super`, `h.m`.
CalleeDeclaration DeclarationOfCallee(const Expr* callee, SimContext& ctx,
                                      Arena& arena);

// §8.3, §8.11 and §8.15: the class whose declarations a member select through
// `base` reads -- the object's own for a handle or a chain of them and for
// `this`, and the parent of the running method's class for `super` -- or
// null where `base` denotes no object.
const ClassTypeInfo* ClassBehindHandle(const Expr* base, SimContext& ctx,
                                       Arena& arena);

}  // namespace delta
