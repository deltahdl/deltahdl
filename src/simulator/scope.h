#pragma once

#include <string_view>
#include <unordered_map>

namespace delta {

struct ArrayInfo;
struct AssocArrayObject;
struct DataType;
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
//
// §26.3 and §13.4 are why a frame names a package: a subroutine declared in a
// package reads the package's variables, and those the package imports, by
// their bare names, so the frame a package subroutine's call opens carries the
// package's name and SimContext::FindVariable reads the package's keys through
// it; every other frame carries none.
//
// §23.9 with §26.3 is why a frame records that it is a subroutine's: a task,
// function or method body is a scope nested in the module, package or class
// that declares it, never in the body that calls it, so the outward search
// for the package a bare name is read through ends at the innermost
// subroutine frame (SimContext::PackageFrame). A begin-end, fork or loop
// frame inside the body is not one, and still sees the body's package.
//
// §8.25.1 is why a frame binds a type to a type parameter's name: a static
// method called through an explicit specialization, `Box#(byte)::bits()`,
// runs on no object, and the type the specialization gives the class's type
// parameter -- which §8.25 binds throughout the class body -- is held by the
// frame the call pushed, for exactly as long as the call runs, as the value
// parameters it binds are (BindClassParams in src/simulator/eval_function.cpp).
// An object's specialization binds its own on the object instead
// (ClassObject::type_param_actuals).
//
// §13.4 with §8.3 is why a frame records the class of each handle it declares:
// a function's implicit result variable, its formals and its locals are the
// frame's own, and a call of a function of the same name made while the body
// runs -- uvm_registry_common#(...)::create reached again for another
// specialization while constructing the first one's object -- declares its own.
// Recorded only under the bare name for the whole run, the inner call's class
// replaced the outer's, and the outer's `$cast(create, obj)` was screened
// against the inner call's class.
struct Scope {
  std::unordered_map<std::string_view, Variable*> vars;
  std::unordered_map<std::string_view, ArrayInfo*> arrays;
  std::unordered_map<std::string_view, QueueObject*> queues;
  std::unordered_map<std::string_view, AssocArrayObject*> assoc_arrays;
  std::string_view package;
  std::unordered_map<std::string_view, const DataType*> type_actuals;
  bool is_subroutine = false;
  std::unordered_map<std::string_view, std::string_view> class_types;
};

}  // namespace delta
