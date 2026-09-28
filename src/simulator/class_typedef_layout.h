#pragma once

#include <string_view>

namespace delta {

struct StructTypeInfo;
class SimContext;

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
