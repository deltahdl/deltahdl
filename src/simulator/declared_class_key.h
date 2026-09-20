#pragma once

// §8.23 (printed pages 200-201 of ~/LRM.pdf): a class nested in another is
// named `Outer::Inner` from outside the containing class, the key
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
struct DataType;

// The key the run holds the declared class under: the scoped spelling where
// the declaration wrote a scope the run holds it by, else the bare name;
// empty where neither names a class. A scoped spelling is built in the arena
// so that the key outlives the call, as the recorded class type and the
// constructor both read it later.
std::string_view DeclaredClassKey(const DataType& type, SimContext& ctx,
                                  Arena& arena);

}  // namespace delta
