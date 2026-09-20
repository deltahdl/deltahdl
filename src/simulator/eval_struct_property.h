#pragma once

#include <string_view>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;

// §8.11: inside a method, a property of the enclosing class may be named
// without a `this.` prefix -- the clause resolves an unqualified name by
// looking outward from the innermost scope, and notes that qualifying a member
// with `this` is usually unnecessary. So the base of a member access can be a
// property rather than a variable: `left.v` where `left` is a rand class handle
// of the object being randomized, or `p.f` where `p` holds a structure (§7.2)
// whose member `f` the access selects. Every other resolution of a member
// access starts from a variable of that name and finds none, so without this
// the whole access falls through to the unknown-name result and reads zero,
// silently, however the object's or the structure's member is set.
//
// Tried last by ResolveMemberByType, so it only claims a name nothing else
// resolved, and only when that name holds a live handle or a structure whose
// layout the property's declared type name registers.
bool TryImplicitThisHandleMember(std::string_view base_name,
                                 std::string_view field_name, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out);

}  // namespace delta
