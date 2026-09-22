#pragma once

#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/packed_range.h"
#include "common/types.h"
#include "simulator/stmt_result.h"

namespace delta {

struct Expr;
struct Stmt;
struct StructTypeInfo;
struct Variable;
struct ClassObject;
struct ClassTypeInfo;
struct QueueObject;
class SimContext;
class Arena;

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena);

// The two halves of that statement's store, reached by the subroutine body
// executor as well. §10.4 puts procedural assignments "within procedures such
// as always, initial, task, and function" and names one set of left-hand sides
// for all of them, so a body inside a subroutine reaches this dispatch rather
// than restating which forms count -- which is what left a class method
// dropping an array assignment, a streaming target, an associative copy, an
// event alias and a virtual interface bind in silence.
//
// The first answers the forms the target's own kind decides before any value is
// made: a virtual interface, a `new`, an associative array, a queue, an event,
// an unpacked slice or subarray, and a compound operator. It returns true when
// it stored.
bool TryDispatchSpecialBlockingAssign(const Stmt* stmt, SimContext& ctx,
                                      Arena& arena);
// The second stores a value the caller has already made: a concatenation or
// assignment-pattern target, a streaming target, §11.4.14's left-alignment, a
// bit or part select, a whole array, and the scalar write the rest fall to.
void ApplyGenericBlockingAssign(const Stmt* stmt, Logic4Vec rhs_val,
                                SimContext& ctx, Arena& arena);
StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);
StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena);
StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena);
StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);

void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena);

// §7.3.2 (printed page 151): a tagged union's value is its tag beside the
// member's bits, so a nonblocking update of a tagged union target carries the
// tag the right-hand side gave it and sets it when the bits land. `key` is
// what the target's tag stands under -- the key its storage was created by
// (TagKeyOfName) for a variable, that key followed by the member path for a
// member of one (TaggedUnionMemberKey) -- and `tag` the member the update
// sets it to; `tag` is empty where the update carries none. Both are resolved
// where the statement executed, as §10.4.2 (printed 253) resolves the target
// itself, and interned in the arena, since the update outlives the statement
// and the tag table keeps the views it is given.
struct NbaUpdateTag {
  std::string_view key;
  std::string_view tag;
  bool Carries() const { return !tag.empty(); }
};

// §10.4.2 (printed page 253): the right-hand side of a nonblocking assignment,
// evaluated when the statement executes and held until the update lands --
// the value, owning its words, and the tag it carries for a tagged union
// target.
struct NbaSample {
  Logic4Vec value;
  NbaUpdateTag tag;
};

// Evaluates the right-hand side of the nonblocking assignment `stmt` where the
// statement executes -- with the target as its context, a streaming source
// left-aligned in a wider target (§11.4.14), and copied into the arena so no
// later write reaches it through an alias -- and takes the tag a tagged union
// target's update carries: the member a `tagged M v` names, or the one a
// call's body returned. Shared by the statement executed at once and by the
// one an intra-assignment event control defers (§9.4.5), which sample the same
// statement at the same moment and differ only in when the update is placed.
NbaSample SampleNonblockingRhs(const Stmt* stmt, SimContext& ctx, Arena& arena);

// Places the update of `stmt` with the sampled right-hand side `sample` in
// the NBA region `delay_ticks` from now; a tag the sample carries lands in
// the same update as the bits.
void ScheduleNonblockingAssign(const Stmt* stmt, const NbaSample& sample,
                               uint64_t delay_ticks, SimContext& ctx,
                               Arena& arena);

void BuildLhsName(const Expr* expr, std::string& out);

// §7.3.2 (printed page 151) has a tagged union carry its tag wherever it
// stands, a variable or a member of one, and §11.9 (printed 304) makes an
// access of a member inconsistent with the current tag a run-time error, a
// read and a write alike. A member's tag stands under the variable's tag key
// (TagKeyOfName) followed by the member path, "s.u" for `s.u = tagged Valid
// 9`, so both sides walk `field_name` down from `info`, the layout of
// `base_name`, asking each tagged union on the way about the member the path
// enters next. `found` says the walk met a union holding a tag that is
// another member: `union_name` is that union as the access spelled it, "u"
// or "s.u", `member` the rest of the path, and `tag` the tag it holds. A
// member the layout does not declare ends the walk unfound: the window
// resolution after it answers for that. Defined in statement_assign.cpp and
// asked by the write side there and the read side in eval_expr.cpp, which
// checked the base variable's own layout alone and so let `y = s.u.Other`
// through after `s.u = tagged Valid 9`.
struct UnionTagMismatch {
  std::string union_name;
  std::string member;
  std::string tag;
  bool found = false;
};
UnionTagMismatch FindUnionTagMismatch(std::string_view base_name,
                                      const StructTypeInfo* info,
                                      std::string_view field_name,
                                      SimContext& ctx);

// The layout of the member `field_name` names within `base_name`'s layout
// `info`, walked as FindUnionTagMismatch walks, and, where that member is a
// tagged union, the tag it currently holds -- empty for one holding none, and
// for every other member. `layout` is null where the path names no member or
// a singular one. §21.2.1.6 (printed page 662) prints a tagged union under %p
// as its tag beside the valid member's value, and a member that is one,
// `s.u`, is printed by this rather than by the variable's own tag, which is
// what printed the member as a number.
struct MemberLayout {
  const StructTypeInfo* layout = nullptr;
  std::string tag;
};
MemberLayout ResolveMemberLayout(std::string_view base_name,
                                 const StructTypeInfo* info,
                                 std::string_view field_name, SimContext& ctx);
Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx);
bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name);
// The name of the identifier a compound indexed name stands on, `a` for
// `a[i][j]`, or empty where the chain does not stand on one.
std::string_view CompoundRootName(const Expr* e);

// The element a packed sub-select of an unpacked array element selects within
// -- `mem[0]` for `mem[0][3]` on a `logic [7:0] mem [0:3]`, and `y[0]` for
// `y[0][3][1]` on a `logic [3:0][7:0] y[1:0]` -- or the packed variable a chain
// of indices stands on where it has no unpacked dimension, `x` for `x[1][3]`
// on a `logic [1:0][7:0] x`; null where the name is of neither shape. §11.5.1
// makes the trailing indices bits of that object, so both assignment forms
// resolve it here before they ask TryResolveCompoundElement, which would
// answer for a further array dimension, and SelectStorageBits then resolves
// the window every index past the object names.
Variable* TryResolveCompoundElementBase(const Expr* lhs, SimContext& ctx,
                                        Arena& arena);

// The leaf variable a multidimensional indexed name such as `a[i][j]` stands
// for, or null. `absent_element`, when given, is set true where the name is one
// of this shape and no such leaf exists, which §7.4.5 makes a write that
// performs no operation: a caller reads it as "stop", since the fallback
// resolution walks such a name down to the array's base carrier and would write
// a bit of that instead.
Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena,
                                    bool* absent_element = nullptr);
Variable* ResolveLhsVariable(const Expr* lhs, SimContext& ctx);

// The storage a dotted member path names, resolved away from the expression
// that named it.
//
// §10.4.2 gives a nonblocking assignment the same `variable_lvalue` a blocking
// one takes, and A.8.5 makes a member path -- `s.field`, `h.prop`, `this.prop`
// -- the first production of variable_lvalue, so the same paths are targets of
// both forms. Where such a path "requires an evaluation, such as an index
// expression, class handle, or virtual interface reference", §10.4.2 has it
// "evaluated at the same time as the expression on the right-hand side": the
// path is resolved when the statement executes, and a nonblocking assignment
// defers only the deposit. That is why the resolution is an entity of its own
// rather than a step inside the write.
// §7.2.1: the run of bits of a class property's value that a member path names.
// A property declared with a packed struct or union type holds the whole
// structure in one value (§6.8), so `c.p.b` addresses a window of `p` rather
// than storage of its own. `valid` is false for a path that names no such
// window, which leaves the caller the answer it had.
struct PropertyFieldWindow {
  std::string_view property;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  // The width of the whole structure the window sits in, which is the width
  // the property's value has to have for the window to fit: a property
  // declared by a typedef name is sized by CollectClassMembers to a 32-bit
  // carrier, which holds a one-member structure and loses every member of a
  // wider one above its top.
  uint32_t total_width = 0;
  bool valid = false;
};

// The window `path` names in a property of `type`, resolved through the layout
// registered for the property's declared type name. Shared by the write side
// and the read side so one path answers the same window to both.
PropertyFieldWindow ResolveClassPropertyField(const ClassTypeInfo* type,
                                              std::string_view path,
                                              SimContext& ctx);

struct FieldTarget {
  enum class Kind : uint8_t {
    kNone,      // the path names no storage; the caller declines
    kNoOp,      // storage that takes no value -- a write to a member of a
                // tagged union carrying another tag (§11.9), already reported
    kBits,      // a window of bits inside a packed struct or union variable
    kVariable,  // a whole variable of its own: a component of the interface
                // instance a virtual interface is bound to (§25.9)
    kProperty,  // a property of one class object (§8.5)
    kPropertyBits,  // a window of bits inside one property's value: the member
                    // §7.2.1 selects of a packed structure the property holds
    kStatic,        // a static property of one class type (§8.9)
  };
  Kind kind = Kind::kNone;

  // kBits: the variable holding the packed object, and the window of it the
  // member occupies. kPropertyBits: the same window, of the value the property
  // named below holds rather than of a variable, so `var` says nothing about
  // it. kVariable: the whole variable the path named, which owns every bit of
  // its own storage, so the window fields say nothing about it.
  Variable* var = nullptr;
  uint32_t bit_offset = 0;
  uint32_t width = 0;
  // kPropertyBits: the width of the whole value the window sits in, which the
  // held value is widened to before the deposit where it is narrower.
  uint32_t holder_width = 0;

  // kProperty: the object holding the field. A class object is arena-allocated
  // and the class garbage collector only unregisters it, so the pointer stays
  // good for the run; holding it is what lets a deferred write reach the object
  // resolved when the statement executed rather than re-reading `this` or the
  // base handle in the update region, where the running process is another one.
  ClassObject* obj = nullptr;
  // kProperty: the declared type that scopes the write (§8.15), null when the
  // object's own type governs. kStatic: the class type whose declaration the
  // value is coerced to.
  const ClassTypeInfo* type = nullptr;
  // kProperty: the variable the handle was read from, notified after the write;
  // null where the path went through `this` or `super`, neither of which is
  // read from a variable.
  Variable* notify = nullptr;

  // kStatic: the entry in the class type's shared static-property map.
  Logic4Vec* slot = nullptr;

  // kProperty, kPropertyBits and kStatic: the property's name, or the part of a
  // dotted path that is stored under one key.
  std::string field;

  // Whether a value is to be deposited: kNone found no storage and kNoOp
  // resolved storage that takes none.
  bool HasDeposit() const { return kind != Kind::kNone && kind != Kind::kNoOp; }
};

// Resolves the member path `lhs` to the storage it names, evaluating the base
// -- `this`, `super`, a class type, or a variable holding a packed object or a
// handle -- as §10.4.2 requires of the moment the statement executes.
FieldTarget ResolveFieldTarget(const Expr* lhs, SimContext& ctx);

// §8.6: the property `name` of the object the running method runs on, named
// bare inside the method, as the method's class declares it, or (§8.10) the
// static property of the running method's class, or of a class enclosing it
// (§8.23), that a static method names bare; kNone where no method is running
// or its class declares no such property, which leaves the name to whatever
// else it may denote.
FieldTarget ResolveBarePropertyTarget(std::string_view name, SimContext& ctx);

// Deposits `rhs_val` in already-resolved storage. Nothing is re-resolved here,
// so this is what a nonblocking assignment runs in the update region.
void WriteResolvedField(const FieldTarget& target, const Logic4Vec& rhs_val,
                        SimContext& ctx, Arena& arena);

// §11.5.1: writes the window `lhs` names of the class property its base selects
// from, e.g. `c.p[7:0] = 8'h00`. Answers false for anything that is not a
// select over a member access naming a property of a declared width, so a
// caller goes on to the writers that name a context variable. Defined in
// statement_assign.cpp; the definition's comment gives the reason it exists.
bool TryWriteClassPropertyBits(const Expr* lhs, const Logic4Vec& rhs_val,
                               SimContext& ctx, Arena& arena);

// Resolve-then-write for a blocking assignment, which does both when the
// statement executes. Returns false when the path names no storage.
// Writes `rhs_val` through the member access `lhs` names. `written_width`, when
// given, receives the declared width of the storage the target named, which
// §11.3.6 makes the data type of the value an assignment expression returns; it
// is left alone where the target has no declared width to report.
bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx, uint32_t* written_width = nullptr);

// §7.4.1: how many selects within `var` stand between `sel` and `var`'s own
// name -- one for `y[0][3]` under `y[0][3][1]` with the element `y[0]` the
// storage and for `x[1]` under `x[1][3]` with `x` the storage, two for
// `z[1][0]` under `z[1][0][3]` -- which is the packed dimension `sel`'s own
// index addresses (§7.4.4, Variable::PackedLevelWithin) rather than an element
// of the whole object. Zero where the base names `var` itself, `y[0]` under
// `y[0][3]`, is no select at all, or stands on no name that resolves to `var`,
// which leaves a variable built for one write, as the associative-array and
// class-property writers build, addressed as it was. Defined in
// statement_assign_select.cpp; SelectStorageBits resolves the chain by it, and
// SelectExprWidth (statement_assign_core.cpp) sizes the select by it.
size_t SelectDepthWithin(const Variable& var, const Expr* sel, SimContext& ctx,
                         Arena& arena);

// §11.5.1: the storage bits of `var` that the select `sel` addresses, resolved
// against the declaration, since "the actual bit that is accessed by an address
// is, in part, determined by the declaration". A width of zero is the select
// that addresses no bit of the object -- an index carrying x or z, which
// §11.5.1 has "return x" when read and have "no effect on the data stored when
// written", and an index or a range wholly outside the declared bounds, which
// the same sentence covers.
//
// One index of a packed multidimensional array addresses an element rather than
// a bit (§7.4.1), and the window is that element's; a further index or range on
// that select addresses bits within the element, so a chain of selects is
// resolved from the inside out and `sel` may stand on a select within `var`
// (SelectDepthWithin) as well as on `var`'s own name, each index one packed
// dimension further in (§7.4.4).
//
// Three callers ask it: the concatenation lvalue walk, which needs an element's
// own width rather than its variable's; the streaming-concatenation unpack,
// which needs the same of a target element that is a select, since §11.4.14.1
// makes a stream_expression's contribution the expression's and not that of the
// object a sub-expression of it names; and the continuous-assignment lowering,
// which needs the bits a select-targeted driver drives. The first two asked it
// separately and of the same clause, which is what the copy-paste gate found.
PartSelectBits SelectStorageBits(const Variable& var, const Expr* sel,
                                 SimContext& ctx, Arena& arena);

void WriteBitSelect(Variable* var, const Expr* lhs, const Logic4Vec& rhs_val,
                    SimContext& ctx, Arena& arena);
Logic4Vec ResizeToWidth(Logic4Vec val, uint32_t target_width, Arena& arena);
// §10.7 with §7.10.1: a value stored as an element of a queue, or of the
// dynamic array a queue backs, takes the element's width, `d[0] = 1` on
// `byte d[]` holding an 8-bit 1 and not the 32-bit literal; a string, a real
// and a class handle keep their own. Defined in statement_assign_select.cpp.
Logic4Vec SizedForQueueElement(const QueueObject& q, Logic4Vec val,
                               Arena& arena);

// §8.5 puts no restriction on a class property's data type, so a property is an
// object of the type its declaration gave it, and §10.4 makes every write to
// one a procedural assignment. Answers what the property `name` declared on
// `type`
// -- or on one of its bases, which is where the walk goes -- can hold of `val`:
// §10.7 truncates or extends into its width, §6.12.1 converts a value crossing
// the real boundary, and §6.11.2 clears the unknowns a 2-state one has no room
// for.
//
// The value is answered unchanged where the declaration gave no width this can
// trust. CollectClassMembers substitutes a 32-bit carrier for a type it could
// not size -- a name, a string, a class handle -- and truncating to a carrier
// would cut a handle in half and a string down to four characters, so
// PropertyInfo::width_is_declared is what gates all three.
Logic4Vec CoerceToPropertyType(const ClassTypeInfo* type, std::string_view name,
                               Logic4Vec val, Arena& arena);
bool TryArrayBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);
// §7.10.1: the element of `q` an index expression names, with `$` standing for
// the last element as the clause writes it. Signed, because §7.10.1 gives an
// out-of-range index its own answer -- "a read ... shall return the value of
// the element type's default", a write "shall be ignored" -- and a negative
// index is one of the ways to be out of range. `has_xz` reports an index
// carrying an unknown bit, which §7.10.1 makes invalid whatever its value.
int64_t QueueElementIndex(const Expr* index, QueueObject* q, SimContext& ctx,
                          Arena& arena, bool* has_xz);

bool TryAssocIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueIndexedWrite(const Expr* lhs, const Logic4Vec& rhs_val,
                          SimContext& ctx, Arena& arena);
bool TryQueueBlockingAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// §8.4: handle a blocking assignment whose right-hand side is a `new` call and
// whose left-hand side names a variable of a class type -- the two-step form
// `P p; p = new;` by which an object is created and its handle stored. `new`
// names a construction rather than a value to be read, so an assignment of
// this shape cannot be served by evaluating the right-hand side; it is
// recognized here, the object is created, and the handle is written to the
// target. Declines (returning false) for any other assignment, including one
// to a variable with no known class type, leaving it to the ordinary paths.
bool TryClassNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
