#pragma once

#include <cstdint>
#include <optional>
#include <string_view>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct StructFieldInfo;
struct StructTypeInfo;

// §7.2.1: the member `field` (a dotted path through nested members) of the
// structure value `value`, whose layout is `info`, read as its declared
// type: a 2-state member of a packed union with its unknowns as zeros
// (§7.3.1), a real member as a real (§6.12), a signed member as signed
// (§6.11), and a string member as its text (§7.2 with §6.16). A one-bit zero
// where the path names no member.
Logic4Vec ExtractStructField(const Logic4Vec& value, const StructTypeInfo* info,
                             std::string_view field, Arena& arena);

// §7.2 with §8.7: the member `path` (a dotted path through nested members) of
// a structure whose layout is `info`, where that member is declared with a
// class type and so holds a handle, `h` of `typedef struct { int i; C h; }`;
// its offset in the structure goes to *bit_offset. Null where the path names
// no member, or a member of a type that names no class.
const StructFieldInfo* StructMemberOfClassType(const StructTypeInfo* info,
                                               std::string_view path,
                                               SimContext& ctx,
                                               uint32_t* bit_offset);

// §7.2 with §8.4: a structure's member declared with a class type holds a
// handle, not a structure, so in `s.k.v` and `s.n.h.v` the path past that
// member names a property of the object the handle refers to, which no
// member of the structure's layout does. That property's value where a member
// along `field` of the structure `value`, whose layout is `info`, is of a
// class type and refers to an object; none where no member is, or its handle
// is null, which leaves the read to the structure.
std::optional<Logic4Vec> StructMemberObjectRead(const Logic4Vec& value,
                                                const StructTypeInfo* info,
                                                std::string_view field,
                                                SimContext& ctx, Arena& arena);

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
