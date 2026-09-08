#pragma once

#include <string_view>
#include <unordered_map>

namespace delta {

struct ArrayInfo;
struct AssocArrayObject;
struct QueueObject;
struct Variable;

// One frame of SimContext's scope stack: everything a scope declares, held for
// exactly as long as the scope is on the stack.
//
// §18.17 is why a frame carries an array shape and not only its variables:
// "The randsequence statement creates an automatic scope", and §18.17.7
// declares within a rule "a variable ... for each production (of the rule)
// that returns a value", whose type "is an array where the element type is the
// return type of the production" when the rule names that production more than
// once. A name that stands for an array is read through
// SimContext::FindArrayInfo, so the shape has to go out of scope with the
// variables it describes; recorded anywhere else it would still describe the
// name after the scope was gone, and §18.17.7's own Example 2 declares three
// rules of one production that name C once, twice and three times, each
// activation giving C a different shape from the last.
//
// ArrayInfo is held by pointer so that this header names it without its
// definition, keeping the frame available to a translation unit that only
// parks the stack. SimContext::RegisterLocalArray allocates the pointed-to
// value in the context's arena, which outlives every scope.
// §13.5.1 is why a frame carries a queue and an associative array as well:
// "This argument passing mechanism works by copying each argument into the
// subroutine area ... If the arguments are changed within the subroutine, the
// changes are not visible outside the subroutine." Their elements live in a
// QueueObject and an AssocArrayObject rather than in variables, so the copy a
// by-value bind makes is registered by name like any other declaration, and a
// formal named after a queue of the enclosing module answered to the module's
// until the name could be looked up here first. §23.9 gives the same answer for
// a declaration inside a begin-end block, which is local to that block.
struct Scope {
  std::unordered_map<std::string_view, Variable*> vars;
  std::unordered_map<std::string_view, ArrayInfo*> arrays;
  std::unordered_map<std::string_view, QueueObject*> queues;
  std::unordered_map<std::string_view, AssocArrayObject*> assoc_arrays;
};

}  // namespace delta
