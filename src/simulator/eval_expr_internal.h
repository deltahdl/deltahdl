#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/types.h"

namespace delta {

class Arena;
class SimContext;
struct ClassObject;
struct ClassTypeInfo;

// Resolves a (possibly chained) field path against class object `obj`: a
// single field is read directly, a chained path `first.rest` follows `first`
// as a class handle into the referenced object, and a `first` that holds a
// structure rather than a handle answers the member of it the rest of the path
// selects (§7.2.1). Defined in eval_expr.cpp; also used by
// eval_struct_property.cpp for a property named bare inside a method.
Logic4Vec ResolveClassFieldChain(ClassObject* obj,
                                 const ClassTypeInfo* declared_type,
                                 std::string_view field_path, SimContext& ctx,
                                 Arena& arena);

// Internal helper shared between eval_expr.cpp and eval_streaming.cpp. Defined
// in eval_expr.cpp. Resolves a type name (built-in or user-defined) to its bit
// width, defaulting to 32 for unknown names.
uint32_t ResolveCastWidth(std::string_view type_name, SimContext& ctx);

// The position of the dot that parts a member access path into the variable
// on its left and the member path on its right: the first dot, unless the
// segment before it names no variable and a longer prefix of the path -- an
// instance path ending in a variable, `i.c` of `i.c.v` -- does, in which case
// the dot after that prefix. npos for a path with no dot. Defined in
// eval_member_path.cpp.
size_t MemberPathSplit(const std::string& path, SimContext& ctx);

// Strips a leading "$root.<top>." prefix from a hierarchical name, returning
// the remainder; names without the prefix are returned unchanged. Defined in
// eval_expr.cpp; also used by statement_assign.cpp.
std::string StripRootPrefix(const std::string& name);

}  // namespace delta
