#pragma once

#include <string_view>

namespace delta {

class Arena;
struct RtlirVariable;
class SimContext;
struct Stmt;
struct Variable;

// §15.3 (printed page 372 of IEEE 1800-2023) and §15.4 (printed 374): a
// module's, an instance's or a package's `semaphore s` or `mailbox mb` is a
// variable holding a handle to the bucket or the queue, which §15.3.1
// (printed 373) and §15.4.1 (printed 374) have new() create and return, and
// §8.4 (printed 181-182) sets the handle to null until then, an
// uninitialized one being detected by comparing it with null. The run keeps
// the object under the variable's name (SimContext::CreateSemaphore and
// CreateMailbox, found by FindSemaphore and FindMailbox), and the variable's
// own value is the handle's carrier, the value `mb == null`, `mb != null`,
// `a == b` and `if (mb)` read through the generic paths, as a class
// property's is (MirrorSyncCarrier in eval_class_sync.cpp): 0 while the
// handle is null and the object's identity (SyncObjectIdentity in
// sync_objects.h) while it refers to one, so that two handles compare equal
// exactly where they refer to one object (§8.4).

// Creates the bucket or the queue the variable `var`, created under `name`
// as `v`, is a handle to, and marks the handle held where the declaration's
// initializer is a `new(...)`, whose argument sizes the object; a
// declaration with no initializer, or with any other one, leaves the value
// the initializer stored, 0 for none. The object is made either way, so a
// later `mb = new(bound)` rebuilds it in place and a process waiting on it
// keeps its place. Does nothing for a variable of any other type.
void CreateSyncObjectForVar(std::string_view name, const RtlirVariable& var,
                            Variable* v, SimContext& ctx, Arena& arena);

// Marks the semaphore or mailbox variable under `key` -- a bare name, an
// instance's prefixed one or a package's "p.name" -- as holding the object
// the run keeps under that key, after a procedural or a package
// declaration's `new(...)` has built or rebuilt it; nothing where no
// variable stands under the key. Left at the 0 its declaration stored, the
// variable compared equal to null after the new.
void HoldSyncVariable(std::string_view key, SimContext& ctx);

// §15.3.1 and §15.4.1 with §6.21: a semaphore or mailbox declared by `stmt`
// as a local of a subroutine or a procedural block, just created as `v`, is a
// handle the frame binds to an object of its own (SimContext::
// BindSemaphoreHandle and BindMailboxHandle), which the body's `s.try_get()`
// and `m.put(v)` reach as a formal's (SemaphoreOfFormal and MailboxOfFormal);
// a `new(...)` initializer sizes the object and marks the handle held, and
// any other declaration leaves it null. Made for none, `s = new(keys)` and
// `semaphore s = new(keys)` in an automatic task filled no bucket. Does
// nothing for a local of any other type.
void CreateSyncObjectForLocal(const Stmt* stmt, Variable* v, SimContext& ctx,
                              Arena& arena);

// §15.3.1 and §15.4.1: `s = new(...)` where `s` is a local
// CreateSyncObjectForLocal bound, which binds it to a new object, sized by
// the argument, and marks the handle held. False, doing nothing, for any
// other target.
bool TryLocalSyncNewAssign(const Stmt* stmt, SimContext& ctx, Arena& arena);

}  // namespace delta
