#pragma once

#include <string_view>

#include "elaborator/const_eval.h"

namespace delta {

struct ClassDecl;
struct DataType;
struct StructTypeInfo;
class SimContext;

// §8.25: whether the class declaration `decl` has a value parameter, in its
// header or its body, which makes the widths of its typedefs the
// specialization's.
bool ClassHasValueParams(const ClassDecl& decl);

// §8.23: the structure or union type the class declaration `decl` gives the
// typedef `name`, null where it declares no such typedef or one of another
// type.
const DataType* ClassAggregateTypedef(const ClassDecl& decl,
                                      std::string_view name);

// §8.25 with §8.23 and §7.2: registers, where none stands yet, the layout of
// the aggregate typedef `type` a class declares under `name`, its members'
// packed widths folded against `scope` -- the parameter values of the
// specialization `spelled` names -- under the key "<spelled>::<name>",
// `Box#(16)::S`, and answers the key. A method's local and a property of the
// specialization declared by the typedef share the one registration.
std::string_view RegisterSpecializationTypedefLayout(std::string_view spelled,
                                                     std::string_view name,
                                                     const DataType& type,
                                                     const ScopeMap& scope,
                                                     SimContext& ctx);

// §8.25 with §8.23 and §7.2 (printed pages 203, 200 and 146): a structure or
// union typedef a parameterized class declares, `typedef struct { bit [p-1:0]
// data; } S;`, named bare in a method of the class or of one extending it, is
// of the widths the specialization running the method binds: `data` is 32
// bits in a method of `B#(32)` and 8 under the default specialization, `p =
// 8`. The layout is folded with that specialization's parameter values and
// registered, the first time it is asked for, under a key naming the
// specialization, `B#(32)::S` or `B#()::S` for the default one, which
// `key` receives. Null where no class of the running method's chain with a
// value parameter declares an aggregate typedef named `name`.
const StructTypeInfo* MethodClassTypedefLayout(std::string_view name,
                                               SimContext& ctx,
                                               std::string_view* key);

}  // namespace delta
