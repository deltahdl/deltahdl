#pragma once

#include <string_view>

namespace delta {

struct StructTypeInfo;

// §7.3.2 (printed page 151): a tagged union holds the member's value beside a
// tag naming the member, and §11.9 (printed 304) builds such a value with a
// tagged union expression, `tagged M v`, whose `v` may be a §10.9.2 structure
// assignment pattern to be placed by the named member's own layout rather
// than the union's. The layout of the member `member` names within the union
// laid out by `sinfo`: the nested structure or union layout of the first
// field so named that has one, or null where the union declares no such
// member or the member is a scalar or void with no layout of its own. One
// helper for the three places a `tagged M '{...}` is placed by its member --
// the assignment statement (EvalRhsWithStructContext in
// statement_assign_core.cpp), a subroutine actual (TryEvalTaggedPatternActual
// in eval_function_args_tagged.cpp) and a body local's initializer
// (TaggedPatternMemberLayout in eval_function_body.cpp) -- which each walked
// the union's fields on their own. MemberPathSplit, StructLayoutOfName and
// TagKeyOfName, defined beside this in eval_member_path.cpp, are declared in
// eval_expr_internal.h.
const StructTypeInfo* TaggedMemberLayout(const StructTypeInfo& sinfo,
                                         std::string_view member);

}  // namespace delta
