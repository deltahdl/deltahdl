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
struct Stmt;
struct Variable;
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
// a package's and an instance's and never an object's. §8.9 gives a static
// property one copy shared by every object, created once, kept in
// ClassTypeInfo::static_semaphore_properties and static_mailbox_properties
// and reached by the bare name, from a static method (§8.10), by `C::mb`
// and through any handle.

// Which of the two classes a declaration's type names: a named type spelled
// `semaphore` or `mailbox` (the spelling CreateSyncObjectForVar in
// sync_variable.cpp recognizes a module's variable by),
// or a typedef name standing for one -- §15.4.9's `typedef mailbox #(string)
// s_mbox`, a package's `p::mb_t` (§26.3) and a typedef of a typedef (§6.18)
// -- followed through the chain the run records (SimContext::FindTypeTarget),
// bounded by the table's size. kNone for any other type. `package` is the
// package the declaration stands in, empty for a module's or none: §26.2
// (printed page 808) has the package's typedefs visible bare throughout it,
// so a bare name of the chain is looked up under "package::name" before its
// own, the key the run records a package's typedef by; a formal's type,
// declared in no package the run names, is followed with none.
enum class SyncKind : uint8_t { kNone, kSemaphore, kMailbox };
SyncKind SyncKindOfType(const DataType& type, std::string_view package,
                        const SimContext& ctx);
SyncKind SyncKindOfType(const DataType& type, const SimContext& ctx);

// The property a receiver names, where it names a semaphore or mailbox
// property: `kind` says which, kNone where the receiver names no such
// property -- a variable, a property of another type, an array of them --
// and the caller then resolves the receiver as it did. `obj` is the object
// holding the property: the running method's for a bare name (§8.11) or the
// one the handle side refers to; null through a null handle or in a static
// method, where §8.4 makes the access to an instance property illegal.
// `member` is the declaration, whose `mailbox #(T)` parameters
// IsParameterizedMailbox reads, and `declaring` the class that declares it,
// whose static maps hold a static property's object (§8.9), `obj` then
// beside the point. `spelling` is the null handle a report names, the
// receiver as written or, with `obj` null, its handle side.
struct SyncProperty {
  SyncKind kind = SyncKind::kNone;
  ClassObject* obj = nullptr;
  const ClassMember* member = nullptr;
  const ClassTypeInfo* declaring = nullptr;
  std::string spelling;
};

// The semaphore or mailbox property `recv` names: a bare name inside a method
// of the declaring class or of one derived from it, or, for a static
// property, of a class nested in it (§8.23), no local of the name shadowing
// it, `this.name` or `h.name` through a handle path (§8.4), and `C::name`
// for a static property of the class C (§8.9); a package's `p::name` and
// every other shape name none.
SyncProperty ResolveSyncProperty(const Expr* recv, SimContext& ctx,
                                 Arena& arena);

// The semaphore or the mailbox the property `prop` holds, for a call of
// `method` at `loc`, or null where `prop` is of the other kind. A property
// that holds none -- declared with no initializer and never assigned, or an
// instance property reached through a null handle or from a static method
// -- is §8.4's illegal access, reported as ResolveThroughNullHandle in
// eval_function.cpp reports a method called through a null handle. A static
// property declared through a typedef was built here on the first
// reference, the run's typedef table being filled after the packages' and
// the unit's classes were lowered; filled ahead of every class
// (RegisterTypeTargets in lowerer_register.cpp), the class's static
// initialization builds it (TryInitStaticSyncProperty).
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
// is an instance property with no object.
void BuildSyncProperty(const SyncProperty& prop, const Expr* new_expr,
                       SimContext& ctx, Arena& arena);

// §8.7: the property `name` of the level `info` of the object `obj` under
// construction, where `info` declares it a semaphore or a mailbox: its
// initializer `init`, a `new(...)`, builds the object's own, and any other
// initializer that names a semaphore or mailbox -- a module's `mailbox mb =
// shared;` -- makes the property a handle to that object (§8.12, one object
// under two names); an initializer naming none, or no initializer, leaves
// the property the null handle a class-typed property without a `new` is.
// The value under the name is stored too, the handle's carrier §8.4
// (printed pages 181-182) compares with null -- nonzero for a property that
// holds an object, 0 for one that holds none -- so the caller stores none.
// False, building nothing, for a property of any other type, which the
// caller then initializes as a value.
bool TryInitClassSyncProperty(ClassObject* obj, const ClassTypeInfo* info,
                              std::string_view name, const Expr* init,
                              SimContext& ctx);

// §8.9 (printed page 186) with §6.21 (printed 132-133): a static property is
// created once, at the class's static initialization, and a static variable
// takes its declaration's initializer then, so the one copy of the static
// property `name` that `info` itself declares a semaphore or a mailbox is
// built by its `new(...)` into the class's static map at lowering
// (InitStaticProperties in lowerer_class.cpp), in the frame of the class's
// scope, the argument read as it stands then; any other initializer makes
// the property a handle to the object it names (§8.12), or null. The
// class's storage under the name takes the handle's carrier, as
// TryInitClassSyncProperty stores an object's. False, building nothing, for
// a property of any other type, an instance property, or a static one a base
// class declares, whose copy is the base's own. Built on the first reference
// instead, `new(K)` read K as a later assignment had left it.
bool TryInitStaticSyncProperty(const ClassTypeInfo* info, std::string_view name,
                               const Expr* init, SimContext& ctx);

// §15.4 (printed page 374 of IEEE 1800-2023) makes a mailbox variable a
// handle to the mailbox object, §15.3 a semaphore's alike, and §8.12 (printed
// 188) has a handle assigned to another variable leave one object under two
// names. A blocking assignment whose target ResolveSyncProperty answers takes
// the object its source is a handle to -- a module's, an instance's or a
// package's by name (SimContext::FindMailbox and FindSemaphore), another
// object's property, a formal bound to one (BindSyncFormal), or `null` --
// into the object's map, the same object and not a copy. Answers whether the
// assignment was one; an assignment to a property from a source that is no
// handle is left to the caller. Left to the generic store, `mb = m` in a
// constructor wrote the handle's carrier and the property stayed null.
bool TrySyncHandleAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

// The object an expression is a handle to: `kind` says which class, kNone
// where the expression is a handle to neither; the object may be null for a
// handle that holds none.
struct SyncHandle {
  SyncKind kind = SyncKind::kNone;
  SemaphoreObject* sem = nullptr;
  MailboxObject* mbx = nullptr;
};

// §13.5.1 (printed page 348) with §8.2 (printed 180): an object passed by
// value is passed as its handle, so a formal declared `semaphore s` or
// `mailbox m` -- `kind` says which, as SyncKindOfType answers for its
// declared type -- is a handle to the object the actual `actual` names: a
// module's, an instance's or a package's by name, another formal's, or an
// object's property. The actual is the caller's expression and is read in
// the caller's scope, which the binding sets the callee's aside for. The
// answer keeps `kind` and holds the object, or null where the actual is a
// handle to none or to the other class.
SyncHandle ResolveSyncActual(SyncKind kind, const Expr* actual, SimContext& ctx,
                             Arena& arena);

// The formal's variable `var`, which the binding just created, made a handle
// to the object `actual` holds (SimContext::BindMailboxHandle and
// BindSemaphoreHandle) for the body's `m.put(v)` (MailboxOfFormal) and for a
// property assignment `mb = m` (TrySyncHandleAssign) to find. Does nothing
// for a formal of any other type, whose `actual` is of kind kNone.
void BindSyncFormal(const SyncHandle& actual, Variable* var, SimContext& ctx);

// §13.5.1 with §15.3 and §15.4: the semaphore or the mailbox the receiver
// `recv`, a bare name, is a formal bound to (BindSyncFormal), or null where
// `recv` names no such formal; the call paths ask this after the property
// and before the run's tables, a formal's name shadowing a module's (§8.6).
SemaphoreObject* SemaphoreOfFormal(const Expr* recv, SimContext& ctx);
MailboxObject* MailboxOfFormal(const Expr* recv, SimContext& ctx);

}  // namespace delta
