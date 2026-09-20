#include "parser/ast_type.h"
#include "simulator/eval_class_sync.h"
#include "simulator/eval_function_args_internal.h"
#include "simulator/sim_context.h"

namespace delta {

// §13.5.1 (printed page 348) with §8.2 (printed 180): an object passed by
// value is passed as its handle, so the actual of a `mailbox m` or
// `semaphore s` formal is read for the object it is a handle to
// (ResolveSyncActual), in the caller's scope as ResolveArgValue reads its
// value -- an actual named after a formal bound just before it would read
// that formal. Of kind kNone, binding nothing, for a formal of any other
// type; the value copied in is the carrier alone, which names no object, so
// the body's `m.put(v)` and a constructor's `mb = m` reached no mailbox.
//
// §26.2 (printed page 808): a package's declarations are visible by their
// bare names throughout the package, its subroutines' formals included --
// the clause's own ComplexPkg declares `add(Complex a, b)` through the
// package's typedef written bare -- and §6.18 (printed 118) makes the
// typedef name stand for the type it renames, so `mb_t m` after the
// package's `typedef mailbox mb_t` is a mailbox formal. The run keys the
// package's typedef "p::mb_t" and a module's `import p::*` is what adds the
// bare key, so the formal's type is followed through the package the
// subroutine was declared in (SimContext::SubroutinePackage, "$unit" for
// the unit's own, empty for a module's), under which SyncKindOfType looks a
// bare name of the chain up first; followed with no package, `p::count(mb)`
// with no module importing p bound a plain 32-bit value and its `m.num()`
// found no mailbox.
SyncHandle SyncActualOf(const FunctionArg& param, const Expr* actual,
                        const ModuleItem* func, SimContext& ctx, Arena& arena) {
  SyncHandle handle;
  handle.kind =
      SyncKindOfType(param.data_type, ctx.SubroutinePackage(func), ctx);
  if (handle.kind == SyncKind::kNone || actual == nullptr) return handle;
  CalleeScopeAside aside(ctx);
  return ResolveSyncActual(handle.kind, actual, ctx, arena);
}

}  // namespace delta
