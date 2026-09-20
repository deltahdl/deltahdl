#pragma once

#include <cstdint>
#include <string>
#include <string_view>

#include "common/source_loc.h"

namespace delta {

struct ClassMember;
struct ClassObject;
struct ClassTypeInfo;
struct DataType;
struct Expr;
struct MailboxObject;
struct SemaphoreObject;
class Arena;
class SimContext;

// §15.3 and §15.4 with §8.5: a class property may be declared of either
// built-in synchronization class, `semaphore s` or `mailbox mb`, the latter
// with or without a `#(T)`, and §8.7 has the declaration's initializer -- its
// `new(keyCount)` (§15.3.1) or `new(bound)` (§15.4.1) -- evaluated when each
// object is constructed, so every object holds a bucket or a queue of its own
// (§8.4), which the object keeps in ClassObject::semaphore_properties and
// ClassObject::mailbox_properties. A method on such a property, `s.get()` in
// a method of the class, `this.mb.put(v)` and `c.mb.num()` through a handle,
// names the running or the referenced object's own; the run's tables, which
// SimContext::FindSemaphore and FindMailbox answer by name, hold a module's,
// a package's and an instance's and never an object's.

// Which of the two classes a declaration's type names: a named type spelled
// `semaphore` or `mailbox` (the spelling CreateSemaphoreForVar and
// CreateMailboxForVar in lowerer_var.cpp recognize a module's variable by),
// or a typedef name standing for one -- §15.4.9's `typedef mailbox #(string)
// s_mbox`, a package's `p::mb_t` (§26.3) and a typedef of a typedef (§6.18)
// -- followed through the chain the run records (SimContext::FindTypeTarget),
// bounded by the table's size. kNone for any other type.
enum class SyncKind : uint8_t { kNone, kSemaphore, kMailbox };
SyncKind SyncKindOfType(const DataType& type, const SimContext& ctx);

// The property a receiver names, where it names a semaphore or mailbox
// property: `kind` says which, kNone where the receiver names no such
// property -- a variable, a property of another type, a static one, an array
// of them -- and the caller then resolves the receiver as it did. `obj` is
// the object holding the property: the running method's for a bare name
// (§8.11) or the one the handle side refers to; null through a null handle
// or in a static method, where §8.4 makes the access illegal. `member` is the
// declaration, whose `mailbox #(T)` parameters IsParameterizedMailbox reads.
// `spelling` is the null handle a report names, the receiver as written or,
// with `obj` null, its handle side.
struct SyncProperty {
  SyncKind kind = SyncKind::kNone;
  ClassObject* obj = nullptr;
  const ClassMember* member = nullptr;
  std::string spelling;
};

// The semaphore or mailbox property `recv` names: a bare name inside a method
// of the declaring class or of one derived from it, no local of the name
// shadowing it, and `this.name` or `h.name` through a handle path (§8.4); a
// scoped `p::name` or `C::name` and every other shape name none.
SyncProperty ResolveSyncProperty(const Expr* recv, SimContext& ctx,
                                 Arena& arena);

// The semaphore or the mailbox the property `prop` holds, for a call of
// `method` at `loc`, or null where `prop` is of the other kind. A property
// that holds none -- declared with no initializer and never assigned, or
// reached through a null handle or from a static method -- is §8.4's illegal
// access, reported as ResolveThroughNullHandle in eval_function.cpp reports a
// method called through a null handle.
SemaphoreObject* SemaphoreOfProperty(const SyncProperty& prop,
                                     std::string_view method, SourceLoc loc,
                                     SimContext& ctx);
MailboxObject* MailboxOfProperty(const SyncProperty& prop,
                                 std::string_view method, SourceLoc loc,
                                 SimContext& ctx);

// §15.3.1 and §15.4.1: `new_expr`, a `new(...)` call, builds the property's
// semaphore with the keys or its mailbox with the bound the argument names,
// each defaulting to 0. A property already holding one is rebuilt in place,
// as TrySemaphoreNewAssign and TryMailboxNewAssign rebuild a variable's, so
// a process waiting on it keeps its place. Reports under §8.4 where `prop`
// has no object.
void BuildSyncProperty(const SyncProperty& prop, const Expr* new_expr,
                       SimContext& ctx, Arena& arena);

// §8.7: the property `name` of the level `info` of the object `obj` under
// construction, where `info` declares it a semaphore or a mailbox: its
// initializer `init`, a `new(...)`, builds the object's own; any other
// initializer, or none, leaves the property the null handle a class-typed
// property without a `new` is. False, building nothing, for a property of
// any other type, which the caller then initializes as a value.
bool TryInitClassSyncProperty(ClassObject* obj, const ClassTypeInfo* info,
                              std::string_view name, const Expr* init,
                              SimContext& ctx);

}  // namespace delta
