#pragma once

#include <cstdint>
#include <string>

#include "common/packed_range.h"
#include "common/types.h"
#include "simulator/stmt_result.h"

namespace delta {

struct Expr;
struct Stmt;
struct Variable;
struct ClassObject;
struct ClassTypeInfo;
class SimContext;
class Arena;

StmtResult ExecBlockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                  Arena& arena);
StmtResult ExecNonblockingAssignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);
StmtResult ExecVarDeclImpl(const Stmt* stmt, SimContext& ctx, Arena& arena);
StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena);
StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena);

void PerformBlockingAssign(const Expr* lhs, const Logic4Vec& rhs_val,
                           SimContext& ctx, Arena& arena);

void ScheduleNonblockingAssign(const Stmt* stmt, const Logic4Vec& rhs_val,
                               uint64_t delay_ticks, SimContext& ctx,
                               Arena& arena);

void BuildLhsName(const Expr* expr, std::string& out);
Variable* TryResolveArrayElement(const Expr* lhs, SimContext& ctx);
bool BuildCompoundLhsName(const Expr* expr, SimContext& ctx, Arena& arena,
                          std::string& name);
Variable* TryResolveCompoundElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena);
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
struct FieldTarget {
  enum class Kind : uint8_t {
    kNone,      // the path names no storage; the caller declines
    kNoOp,      // storage that takes no value -- a write to a member of a
                // tagged union carrying another tag (§11.9), already reported
    kBits,      // a window of bits inside a packed struct or union variable
    kVariable,  // a whole variable of its own: a component of the interface
                // instance a virtual interface is bound to (§25.9)
    kProperty,  // a property of one class object (§8.5)
    kStatic,    // a static property of one class type (§8.9)
  };
  Kind kind = Kind::kNone;

  // kBits: the variable holding the packed object, and the window of it the
  // member occupies. kVariable: the whole variable the path named, which owns
  // every bit of its own storage, so the window fields say nothing about it.
  Variable* var = nullptr;
  uint32_t bit_offset = 0;
  uint32_t width = 0;

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

  // kProperty and kStatic: the property's name, or the part of a dotted path
  // that is stored under one key.
  std::string field;

  // Whether a value is to be deposited: kNone found no storage and kNoOp
  // resolved storage that takes none.
  bool HasDeposit() const { return kind != Kind::kNone && kind != Kind::kNoOp; }
};

// Resolves the member path `lhs` to the storage it names, evaluating the base
// -- `this`, `super`, a class type, or a variable holding a packed object or a
// handle -- as §10.4.2 requires of the moment the statement executes.
FieldTarget ResolveFieldTarget(const Expr* lhs, SimContext& ctx);

// Deposits `rhs_val` in already-resolved storage. Nothing is re-resolved here,
// so this is what a nonblocking assignment runs in the update region.
void WriteResolvedField(const FieldTarget& target, const Logic4Vec& rhs_val,
                        Arena& arena);

// Resolve-then-write for a blocking assignment, which does both when the
// statement executes. Returns false when the path names no storage.
bool WriteStructField(const Expr* lhs, const Logic4Vec& rhs_val,
                      SimContext& ctx);

// §11.5.1: the storage bits of `var` that the select `sel` addresses, resolved
// against the declaration, since "the actual bit that is accessed by an address
// is, in part, determined by the declaration". A width of zero is the select
// that addresses no bit of the object -- an index carrying x or z, which
// §11.5.1 has "return x" when read and have "no effect on the data stored when
// written", and an index or a range wholly outside the declared bounds, which
// the same sentence covers.
//
// One index of a packed multidimensional array addresses an element rather than
// a bit (§7.4.1), and the window is that element's.
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
