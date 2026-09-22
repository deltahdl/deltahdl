#pragma once

// §8.23 (printed pages 200-201 of IEEE 1800-2023): a class nested in
// another is named `Outer::Inner` from outside the containing class, the key
// LowerNestedClass (lowerer_class.cpp) registers it under, and §26.3 names a
// package's class `p::C`, which the run binds under its bare name as well.
// The parser keeps the two halves apart -- DataType::scope_name holds the
// `Outer`, DataType::type_name the `Inner` -- so a lookup by type_name alone
// finds no class for a nested one, and the declared variable becomes a plain
// vector whose method calls run nothing. The two sites that create a
// declared local from its DataType, TryExecClassVarDecl
// (statement_assign_decl.cpp) for a procedural block's declaration and
// CreateFuncLocalVar (eval_function_body.cpp) for a subroutine body's, resolve
// the class through here so that one spelling serves both.

#include <string_view>

namespace delta {

class Arena;
class SimContext;
struct ClassTypeInfo;
struct DataType;

// The key the run holds the declared class under: the scoped spelling where
// the declaration wrote a scope the run holds it by, else the bare name, else,
// for a bare name that is a type parameter of the running method's class,
// the key of the class its actual names (§8.25); empty where none names a
// class. A scoped spelling is built in the arena
// so that the key outlives the call, as the recorded class type and the
// constructor both read it later.
std::string_view DeclaredClassKey(const DataType& type, SimContext& ctx,
                                  Arena& arena);

// §8.23 (printed pages 200-201): a nested class's bare name is visible
// throughout the containing class, so a declaration written in class
// `declaring` -- a property of Outer, or of a class nested in Outer, declared
// `Inner h` or `Inner q[$]` -- names the class the run holds under
// `Outer::Inner`. The key for `type` as written in `declaring`: the scoped
// spelling where the declaration wrote one the run holds a class by, else the
// class of `type`'s bare name nested in `declaring` or in a class enclosing
// it, innermost first, else the bare name; empty where none names a class.
// The nested probe goes ahead of the bare one so that the key answered is
// the one the class is registered under whichever scope later reads it:
// SimContext::FindClassType resolves a bare nested name through the running
// method's class alone, so a property first referenced from a module's
// initial block, where no method runs, named no class by its bare name.
std::string_view DeclaredClassKeyInScope(const DataType& type,
                                         const ClassTypeInfo* declaring,
                                         SimContext& ctx, Arena& arena);

}  // namespace delta
