#pragma once

#include <cstdint>
#include <string_view>

namespace delta {

class Arena;
struct ClassTypeInfo;
struct DataType;
struct Expr;
class SimContext;

// §8.25 through §23.10.2.2: the type an element of a `#(...)` list spells, at
// kImplicit where it spells none. A keyword type or a typedef name arrives as
// an identifier, each packed dimension hung off the node before it so the
// last one written is the outermost node; §7.4.1 orders them leftmost first,
// so they are put back in written order, ahead of any the named type carries.
// `int unsigned` and the like arrive as the type the parser read into a
// kTypeRef.
DataType TypeSpelledBy(const Expr* elem);

// §8.25.1: a static method called through an explicit specialization,
// `Box#(byte)::bits()` or `p::Box#(shortint)::bits()`, runs on no object, so
// the type the specialization gives each type parameter of the class -- which
// §8.25 binds throughout the class body -- has to reach the running body some
// other way than ClassObject::type_param_actuals. Binds it in the innermost
// scope, the one the call pushed, under the parameter's name, beside the
// value parameters BindClassParams in src/simulator/eval_function.cpp binds
// there. `base` is the class name the call wrote, whose `elements` and
// `arg_names` hold the `#(...)` list as Parser::ParseParamValueAssignment left
// it: a keyword type or a typedef name as an identifier, a packed dimension as
// a select on it, and a type an expression could not spell as a kTypeRef. An
// element that spells no type, and a parameter the list leaves at its
// default, bind nothing, so a reader falls to the class's defaults for them.
// Where `cls` is the specialization the list names, its own actuals are bound
// instead, resolved as the scope was read in the caller, so a list naming the
// caller's type parameter binds the type that parameter stands for.
void BindClassScopeTypeActuals(const ClassTypeInfo* cls, const Expr* base,
                               SimContext& ctx, Arena& arena);

// §8.25 with §20.6.2: the number of bits of the type the type parameter `name`
// of the running class stands for, where no object is running -- the type
// the innermost scope binds it to (BindClassScopeTypeActuals), else the
// default the class of the running method declares for it (§8.25.1). 0 for a
// name bound in no scope that is no type parameter of that class, for a call
// outside a method, or for a type nothing sizes.
uint32_t ScopedTypeParamWidth(std::string_view name, SimContext& ctx);

}  // namespace delta
