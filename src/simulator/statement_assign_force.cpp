#include <algorithm>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/scheduler.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_force_internal.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/stmt_result.h"
#include "simulator/variable.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_user.h"

namespace delta {

// Behavior of the watchers InstallRhsWatchers installs, and of the write each
// installer makes before installing them: `still_valid` gates the watcher
// (returning true to detach once its backing force/assign is no longer in
// effect); `forced` selects whether the value written also refreshes
// var->forced_value.
struct RhsWatcherSpec {
  std::function<bool()> still_valid;
  bool forced = false;
  // §10.6.2: the net the force is standing on, when the target is one. Its
  // reported strength is the force's while the force is in effect, so a
  // recomputed forced value re-resolves it; null when the target is a variable,
  // which carries no strength.
  Net* net = nullptr;
  // §11.4.12 treats a concatenation as a packed vector of bits, so an element
  // of one owns a window of the right-hand value and a window of its own
  // storage. Those five numbers are what Variable records beside an assign's
  // right-hand side, so they are the struct Variable records rather than five
  // fields of this one: a release has to reestablish through the window the
  // assign was installed with.
  ProcContAssignWindow window;
};

// Writes into `var` the part of `val` this installation owns. A singular target
// owns the whole value and takes it whole, sized to its own width. An element
// of a concatenation owns the two windows above instead, and the bits outside
// its destination window belong to the other elements or to nothing at all and
// have to be left standing, which is what DepositBitField does and what writing
// the variable whole did not: `force {w, bus[3]} = 2'b11;` gave `bus` the whole
// two-bit value.
//
// The deposit is made into a fresh copy of the target's current value rather
// than through the words it is holding. Copying a Logic4Vec copies its `words`
// pointer rather than the words (common/types.h), so a variable last written
// whole from another object shares that object's storage, and depositing
// through the pointer would write these bits into whatever else is holding it.
//
// WriteBitSelect resolves the same window for a select and is deliberately not
// the writer here: it declines every write to a forced variable, and the force
// whose bits these are has just set that flag, so the deposit would be dropped
// and the element would keep the value it had.
static void WriteOwnedBits(Variable* var, const Logic4Vec& val,
                           const RhsWatcherSpec& spec, Arena& arena) {
  if (spec.window.dst_width == 0) {
    // §10.6.2 gives the force and the assign a right-hand expression as an
    // assignment does, and §10.7 sizes an assigned value to its target: the
    // value takes the width the variable has, as WriteVar gives a blocking
    // assignment's. Taken as evaluated, `force w = 0;` on a scalar net left w
    // holding the literal's 32 bits as its value, width and all.
    Logic4Vec sized = ResizeToWidth(val, var->value.width, arena);
    if (spec.forced) var->forced_value = sized;
    var->value = sized;
  } else {
    // §10.7: a select's value is sized to the select as the whole one is to
    // the variable, a signed value sign-extended; deposited as evaluated,
    // `force bus[7:4] = 2'sb11` left bus[7:6] zero.
    Logic4Vec updated = ExtractBitField(arena, var->value, 0, var->value.width);
    DepositBitField(updated, spec.window.dst_lo,
                    spec.window.src_width == 0
                        ? ResizeToWidth(val, spec.window.dst_width, arena)
                        : ExtractBitField(arena, val, spec.window.src_lo,
                                          spec.window.src_width),
                    spec.window.dst_width);
    var->value = updated;
    if (spec.forced) var->forced_value = var->value;
  }
  if (!var->is_4state) CoerceTo2State(var->value);
}

// Recomputes `rhs` into the part of `var` the spec's windows name, also
// refreshing var->forced_value when the spec is a forced one.
static void RecomputeRhsInto(Variable* var, const Expr* rhs, SimContext& ctx,
                             Arena& arena, const RhsWatcherSpec& spec) {
  auto new_val = EvalExpr(rhs, ctx, arena, spec.window.rhs_width);
  WriteOwnedBits(var, new_val, spec, arena);
  var->NotifyWatchers();
}

// Installs, on each variable referenced by `rhs` (other than `var`), a watcher
// that re-evaluates `rhs` into `var` whenever a source changes.
static void InstallRhsWatchers(Variable* var, const Expr* rhs, SimContext& ctx,
                               Arena& arena, const RhsWatcherSpec& spec) {
  auto* ctx_ptr = &ctx;
  auto* arena_ptr = &arena;
  for (auto* rhs_var : CollectDistinctRhsVars(rhs, ctx, var)) {
    rhs_var->AddWatcher([var, rhs, ctx_ptr, arena_ptr, spec]() {
      if (!spec.still_valid()) return true;
      RecomputeRhsInto(var, rhs, *ctx_ptr, *arena_ptr, spec);
      if (spec.net != nullptr) spec.net->Resolve(*arena_ptr);
      return false;
    });
  }
}

// Whether two windows of one variable share a bit; the empty window is the
// whole object and shares every bit.
static bool WindowsOverlap(const ProcContAssignWindow& a,
                           const ProcContAssignWindow& b) {
  if (a.dst_width == 0 || b.dst_width == 0) return true;
  return a.dst_lo < b.dst_lo + b.dst_width && b.dst_lo < a.dst_lo + a.dst_width;
}

// Whether `var` still holds the part `window` names for the right-hand side
// `rhs`, which is what keeps that part's watchers recomputing it.
static bool HoldsPart(const Variable& var, const ProcContAssignWindow& window,
                      const Expr* rhs) {
  return std::ranges::any_of(var.held_parts, [&](const Variable::HeldPart& p) {
    return p.rhs == rhs && p.window.dst_lo == window.dst_lo &&
           p.window.dst_width == window.dst_width;
  });
}

// Applies a procedural continuous-assignment forced value to `var` from the
// expression `rhs`, then installs watchers on each variable appearing in `rhs`
// so the forced value is re-evaluated whenever those variables change. The spec
// carries the net the target stands on and, for an element of a concatenation
// target, the windows that element owns; this fills in the rest of it.
static void InstallForcedValueWatcher(Variable* var, const Expr* rhs,
                                      SimContext& ctx, Arena& arena,
                                      RhsWatcherSpec spec) {
  spec.forced = true;
  auto rhs_val = EvalExpr(rhs, ctx, arena, spec.window.rhs_width);
  var->is_forced = true;
  // §10.6.2 overrides every driver of the net that was named, and a constant
  // select of a vector net names some of its bits: the window travels onto the
  // variable so Net::Resolve can leave the drivers of the rest alone. A hold
  // of bits another part held takes them from it, and a part of other bits
  // goes on holding its own.
  std::erase_if(var->held_parts, [&spec](const Variable::HeldPart& part) {
    return WindowsOverlap(part.window, spec.window);
  });
  var->held_parts.push_back({spec.window, rhs});
  WriteOwnedBits(var, rhs_val, spec, arena);
  var->proc_cont_rhs = rhs;
  var->NotifyWatchers();

  // §10.6.2: the force overrides the net's drivers from here, so the strength
  // it reports is settled now rather than at the next driver update -- there
  // may be no further one, and a net forced before anything drove it has no
  // strength recorded at all.
  if (spec.net != nullptr) spec.net->Resolve(arena);

  spec.still_valid = [var, rhs, window = spec.window]() {
    return var->is_forced && HoldsPart(*var, window, rhs);
  };
  InstallRhsWatchers(var, rhs, ctx, arena, spec);
}

// §10.6.1 with §10.6.2: a release puts back in force the assign procedural
// continuous assignment the force overrode, through the window the assign was
// installed with, and the assign again overrides every procedural assignment
// until it is deassigned. It holds the variable as it did before the force, so
// every other writer goes on declining. §10.6.1 gives the assign statement a
// variable or a concatenation of variables as its target, so nothing it
// reestablishes stands on a net.
static void ReestablishAssign(Variable* var, SimContext& ctx, Arena& arena) {
  RhsWatcherSpec spec;
  spec.window = var->assign_cont_window;
  InstallForcedValueWatcher(var, var->assign_cont_rhs, ctx, arena, spec);
}

// §10.6.2: releasing a variable a continuous assignment drives reestablishes
// that assignment and schedules its reevaluation in the continuous
// assignment's own region, which for a variable driven no further is the
// Active region of the present time step. Waiting for an operand of the
// assignment to change left the forced value standing until one did.
static void ScheduleContAssignReevaluation(const Variable* var,
                                           SimContext& ctx) {
  auto* event = ctx.GetScheduler().GetEventPool().Acquire();
  event->callback = var->cont_assign_reevaluate;
  ctx.GetScheduler().ScheduleEvent(ctx.CurrentTime(), Region::kActive, event);
}

// Installs one of §10.6's two statements that hold a variable. An assign is
// recorded whatever else holds the variable, since a later release puts it
// back, but §10.6.2 has a force in effect override it, so while one is the
// assign drives nothing. A force overrides whatever held the variable before.
static void InstallProcContAssign(Variable* var, const Stmt* stmt,
                                  const RhsWatcherSpec& spec, SimContext& ctx,
                                  Arena& arena) {
  if (stmt->kind == StmtKind::kAssign) {
    var->assign_cont_rhs = stmt->rhs;
    var->assign_cont_window = spec.window;
    if (var->force_active) return;
  } else {
    var->force_active = true;
  }
  InstallForcedValueWatcher(var, stmt->rhs, ctx, arena, spec);
}

// Ends one of §10.6's two statements on a variable: a release when `release`
// says so, a deassign otherwise. A deassign ends the assign alone (§10.6.1),
// leaving a force in effect; a release ends the force alone (§10.6.2) and puts
// back whatever it overrode, an assign or a continuous assignment.
static void EndProcContAssign(Variable* var, bool release, SimContext& ctx,
                              Arena& arena) {
  if (!release) {
    var->assign_cont_rhs = nullptr;
    var->assign_cont_window = {};
    if (var->force_active) return;
  }
  var->is_forced = false;
  var->force_active = false;
  var->held_parts.clear();
  var->proc_cont_rhs = nullptr;
  if (!release) return;
  if (var->assign_cont_rhs) {
    ReestablishAssign(var, ctx, arena);
  } else if (var->cont_assign_reevaluate) {
    ScheduleContAssignReevaluation(var, ctx);
  }
}

// One element of a concatenation left-hand side, the window of the right-hand
// value it owns and the width that value is evaluated at. §11.4.12 makes the
// concatenation a packed vector of bits, so the rightmost element takes the
// least significant bits and each element to its left begins where the previous
// one ended: `src_lo` is where this one begins and `width` is what
// ConcatLhsElemWidth gave it.
struct ConcatElemSlot {
  const Expr* el = nullptr;
  Variable* var = nullptr;
  uint32_t src_lo = 0;
  uint32_t width = 0;
  uint32_t rhs_width = 0;
  // §7.4.2: whether the element's index names a whole element of an unpacked
  // array rather than bits of a packed object. Both are written `x[i]`, and the
  // variable resolved for them is a different one -- the element's own storage
  // against the object the index selects within -- so the window has to follow
  // the resolution: an element owns all of itself, where a select owns the bits
  // §11.5.1 gives its indices.
  bool names_whole_element = false;
};

// The window of the right-hand value `slot` owns and the window of its own
// storage that receives it. A whole-variable element takes its bits into the
// whole of itself; a select element takes them into the bits §11.5.1 says its
// indices address, as the declaration determines them.
//
// The two windows are two answers and not one: the element is as wide as
// ConcatLhsElemWidth makes it whether or not its address is in bounds, and it
// writes only the bits SelectStorageBits leaves it. They differ for a
// part-select that is partly out of range, which §11.5.1 has change only its
// in-range bits when written -- `a[9:6]` on `logic [7:0] a` is
// four bits of the concatenation landing on the two of them that exist. Which
// two of the four land is a third answer, and not always the low ones: `a[9:6]`
// runs off the high end and lands its bits [1:0], while `a[1 -: 4]` runs off
// the low end and lands its bits [3:2]. An empty window never reaches here:
// ApplyToConcatElement declines the element first, so the dst_width of zero
// below still means the whole variable.
static RhsWatcherSpec SpecForSlot(const ConcatElemSlot& slot, SimContext& ctx,
                                  Arena& arena) {
  PartSelectBits dst{0, slot.width};
  if (!slot.names_whole_element && slot.el->kind == ExprKind::kSelect &&
      slot.el->base != nullptr) {
    dst = SelectStorageBits(*slot.var, slot.el, ctx, arena);
  }
  // §10.6.2 makes force a statement on a net as well as on a variable, and the
  // net is what holds the strength the force settles, so only an element naming
  // a whole net is looked up. A select element is left standing on no net, as
  // the standalone `force bus[3] = 1'b1;` is: ctx.FindNet on the select's base
  // would hand Net::Resolve the whole of `bus`, which settles every bit of it
  // from the drivers and would undo the one bit this element forced.
  Net* net = slot.el->kind == ExprKind::kIdentifier ? ctx.FindNet(slot.el->text)
                                                    : nullptr;
  RhsWatcherSpec spec;
  spec.net = net;
  spec.window.rhs_width = slot.rhs_width;
  // §11.5.1's limit of such a write to the in-range bits is two answers:
  // dst.lo and dst.width are the bits of the object that are written, and
  // dst.src_lo is where among the element's own bits the ones that land begin.
  // The element's window of the right-hand value starts at slot.src_lo, so the
  // bits it deposits start that far in again. WriteOwnedBits gives
  // DepositBitField the extracted window's low dst_width bits, which for a
  // select running off the low end of its object are the wrong ones:
  // `force {w, a[1 -: 4]} = 5'b1_1101;` on a `logic [7:0] a` left `a` at 8'h01
  // where the clause reads the select as `a[1:-2]` and gives `a[1:0]` the
  // element's bits [3:2], which is 8'h03.
  spec.window.src_lo = slot.src_lo + dst.src_lo;
  spec.window.src_width = slot.width;
  spec.window.dst_lo = dst.lo;
  spec.window.dst_width = dst.width;
  return spec;
}

// Forces or assigns one element of a concatenation target. §10.6.1's assign and
// §10.6.2's force share this executor and differ here only in that the assign
// records its right-hand side, which a later deassign or release looks for.
//
// The window travels onto the variable with the force, so an element naming
// bits of a net holds those bits alone: §10.6.2's override of every driver of
// the net reaches the drivers of what was named, which for `force {w, bus[3]}`
// is bit 3 rather than every bit of `bus`.
// §10.6.1's reestablishment is of the assignment an assign installs, so the
// window it gave this element travels with the expression that will be
// re-evaluated through it, however the release that reestablishes it is
// written; InstallProcContAssign records the two together.
static void ForceOneElement(const ConcatElemSlot& slot, const Stmt* stmt,
                            SimContext& ctx, Arena& arena) {
  InstallProcContAssign(slot.var, stmt, SpecForSlot(slot, ctx, arena), ctx,
                        arena);
}

// Releases or deassigns one element of a concatenation target. §10.6.1: a
// deassign ends the assign procedural continuous assignment to a variable, and
// §10.6.2 ends a force on a release; each element was marked on its own and so
// is cleared on its own.
//
// §10.6.2: a released net at once takes the value its drivers determine, and
// an element naming bits of a net is released as the lone select would be:
// the net under the select is found as ForceTargetNet finds it for a select
// standing alone, where the element's own spec, made for the force, stands on
// no net for a select. Released without its net, `bus[3]` kept its forced
// value until a driver of the net happened to change.
static Net* ForceTargetNet(const Expr* lhs, SimContext& ctx);
static void ReleaseForcedBits(Variable* var, Net* net,
                              const ProcContAssignWindow& window,
                              SimContext& ctx, Arena& arena);

static void ReleaseOneElement(const ConcatElemSlot& slot, const Stmt* stmt,
                              SimContext& ctx, Arena& arena) {
  if (stmt->kind != StmtKind::kRelease) {
    EndProcContAssign(slot.var, /*release=*/false, ctx, arena);
    return;
  }
  ReleaseForcedBits(slot.var, ForceTargetNet(slot.el, ctx),
                    SpecForSlot(slot, ctx, arena).window, ctx, arena);
}

// Routes one element to the statement that named it: the two statements that
// install a procedural continuous assignment, and the two that end one.
//
// An element addressing no bit of its target is routed nowhere. §11.5.1 gives
// such a write no effect on the stored data, and for these four statements
// that has to mean the target is left exactly as it was found: is_forced is one
// flag on the whole Variable, so setting it for an element owning none of its
// bits would suppress every driver of every bit of it, and the watchers
// installed with it would go on recomputing a value into it. The element has
// already taken its own width of the right-hand value, which is what the caller
// advances past.
static void ApplyToConcatElement(const ConcatElemSlot& slot, const Stmt* stmt,
                                 SimContext& ctx, Arena& arena) {
  if (!ConcatLhsElemHasWritableBits(slot.el, *slot.var, ctx, arena)) return;
  if (stmt->kind == StmtKind::kRelease || stmt->kind == StmtKind::kDeassign) {
    ReleaseOneElement(slot, stmt, ctx, arena);
    return;
  }
  ForceOneElement(slot, stmt, ctx, arena);
}

// Distributes a force, an assign, a release or a deassign over the elements of
// a concatenation target. §10.6.2 admits a concatenation of its targets and
// §10.6.1 a concatenation of variables, so each element is a target of the
// statement in its own right and the elements divide the right-hand value the
// way §11.4.12 divides it for a blocking assignment: the walk runs in reverse
// so that the rightmost element takes the least significant bits. Returns the
// offset one past the elements it walked, which is where a nesting caller
// resumes. All four statements walk here, so a release draws the element
// boundaries exactly where the force drew them.
//
// An element ConcatLhsElemWidth cannot size is passed over without advancing
// the offset, which is what UnpackConcatLhs does with the same element on the
// blocking path. Nothing here knows its width to be anything else, so no other
// advance is available, and a force and an assignment to such a target misalign
// the elements to its left together rather than disagreeing.
//
// A select addressing no bit of its object is not that element: §11.5.1 gives
// it the width its indices name and no bits of its target to write, so the
// offset advances past it and ApplyToConcatElement declines it.
static uint32_t WalkConcatLhsElements(const Expr* lhs, const Stmt* stmt,
                                      uint32_t bit_offset, SimContext& ctx,
                                      Arena& arena) {
  uint32_t rhs_width = LhsContextWidth(stmt->lhs, ctx, arena);
  for (auto it = lhs->elements.rbegin(); it != lhs->elements.rend(); ++it) {
    const Expr* el = *it;
    uint32_t w = ConcatLhsElemWidth(el, ctx, arena);
    if (w == 0) {
      // §11.5.1 requires an indexed part-select's width to be a positive
      // constant, so an element written with a width of zero is illegal
      // rather than merely empty and is reported before being passed over,
      // the same way the blocking unpack reports it. The report gates itself
      // on the select carrying such a width, so the other causes of a zero
      // here -- an element this cannot size at all, a part-select whose bounds
      // carry x or z -- stay silent, as they were.
      ReportZeroWidthPartSelect(el, ctx, arena);
      continue;
    }
    // §11.4.12: a nested concatenation lvalue divides the slice it was given
    // among its own elements, so the walk continues into it at the offset it
    // has reached.
    if (IsConcatLhs(el)) {
      bit_offset = WalkConcatLhsElements(UnwrapTypedPattern(el), stmt,
                                         bit_offset, ctx, arena);
      continue;
    }
    // §7.4.2 makes `out[i]` on a `logic [7:0] out [0:3]` a whole element, and
    // §10.6.1 and §10.6.2 both admit a concatenation of the targets they name,
    // so an element of an unpacked array is one of them. ResolveLhsVariable
    // walks the select down to `out`, which is the one-element-wide carrier the
    // lowerer registers under the array's own name and which no read of the
    // array consults, and the window was then resolved against that: the force
    // settled one bit of a variable nothing reads. TryResolveArrayElement is
    // the resolution a lone target already takes, and what it answers owns all
    // of itself.
    // An element of a queue or of an associative array owns all of itself the
    // way an element of a fixed unpacked array does, and takes its own slice of
    // the right-hand value; it is answered here because no Variable stands for
    // it.
    if (TryContainerElementDrive(
            el, stmt, ElementDriveSource{nullptr, bit_offset, w, rhs_width},
            ctx, arena)) {
      bit_offset += w;
      continue;
    }
    Variable* var = TryResolveArrayElement(el, ctx);
    bool whole_element = var != nullptr;
    if (var == nullptr) var = ResolveLhsVariable(el, ctx);
    if (var != nullptr) {
      ApplyToConcatElement({el, var, bit_offset, w, rhs_width, whole_element},
                           stmt, ctx, arena);
    }
    bit_offset += w;
  }
  return bit_offset;
}

// The key of the unpacked array element `e` names, or empty where it names
// none.
static std::string ArrayElementKeyOf(const Expr* e, SimContext& ctx) {
  if (e->kind != ExprKind::kSelect || e->base == nullptr ||
      e->index == nullptr || e->index_end != nullptr) {
    return {};
  }
  std::string_view root = ArrayRootKey(e->base, ctx.GetArena());
  if (root.empty() || ctx.FindArrayInfo(root) == nullptr) return {};
  Logic4Vec idx = EvalExpr(e->index, ctx, ctx.GetArena());
  if (HasUnknownBits(idx)) return {};
  return std::string(root) + "[" + std::to_string(idx.ToUint64()) + "]";
}

// The key of the unpacked array element a force target stands on: the
// element `lhs` names whole, or the one a select of `lhs` is a select of.
static std::string ForceElementKey(const Expr* lhs, SimContext& ctx) {
  std::string key = ArrayElementKeyOf(lhs, ctx);
  if (key.empty() && lhs->kind == ExprKind::kSelect && lhs->base != nullptr) {
    key = ArrayElementKeyOf(lhs->base, ctx);
  }
  return key;
}

// §10.6.2 gives force and release the same targets, among them a net and a
// constant bit-select or part-select of a vector net: all three stand on one
// net, which is what holds the strength the force
// settles and what a release re-resolves from its drivers. A select is followed
// to its base for that reason -- one sentence names the three forms and says
// the same thing about them -- while a concatenation names no one net and
// answers none.
//
// §7.4.2 (printed page 154): an element of a net array is used as a scalar or
// vector net would be, so `force n[0] = 1;` on `wire n[0:1]`
// forces the net n[0] is, and `force n[1][2] = 1;` a bit of it. Each element
// of an unpacked array is held under its own key (CreateDeclaredNet in
// lowerer_register.cpp), and a select naming one stands on that element
// rather than on the array's name.
static Net* ForceTargetNet(const Expr* lhs, SimContext& ctx) {
  if (std::string key = ForceElementKey(lhs, ctx); !key.empty()) {
    return ctx.FindNet(key);
  }
  if (lhs->kind == ExprKind::kIdentifier) return ctx.FindNet(lhs->text);
  if (lhs->kind == ExprKind::kSelect && lhs->base != nullptr &&
      lhs->base->kind == ExprKind::kIdentifier) {
    return ctx.FindNet(lhs->base->text);
  }
  return nullptr;
}

// The target all four §10.6 statements resolve before they act, and whether the
// statement is already answered by the resolution.
//
// §10.6.2: the left-hand side may be a singular variable, a net, a constant
// bit-select or part-select of a vector net, or a concatenation of these, and
// §10.6.1 gives the assign statement a singular variable or a concatenation of
// variables. §10.6.1 and §10.6.2 give release and deassign the targets their
// installing statements take, so one resolution answers all four and a release
// draws the element boundaries exactly where the force drew them.
//
// A concatenation names no one object, so ResolveLhsVariable answers null for
// it and each of the four returned having marked nothing and written nothing:
// `force {a, b} = 16'h1234;` left `a` and `b` at their initial values with
// is_forced clear on both, and `release {a, b};` was the no-op that would have
// made such a force one no release could lift. An element of a queue or of an
// associative array is answered next: §6.4 makes it a singular variable, which
// both statements name among their targets, and it has no Variable for the
// resolution below to answer with.
static bool ProcContAssignTargetHandled(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena, Variable** var) {
  if (IsConcatLhs(stmt->lhs)) {
    WalkConcatLhsElements(UnwrapTypedPattern(stmt->lhs), stmt, 0, ctx, arena);
    return true;
  }
  if (TryContainerElementDrive(stmt->lhs, stmt, ElementDriveSource{}, ctx,
                               arena)) {
    return true;
  }
  std::string key = ForceElementKey(stmt->lhs, ctx);
  *var =
      key.empty() ? ResolveLhsVariable(stmt->lhs, ctx) : ctx.FindVariable(key);
  return *var == nullptr;
}

// The window of `var` a lone target of §10.6's statements names: empty for a
// whole object, and the bits §11.5.1 resolves for a select of a vector net.
// False for a select naming no bit of the object, which a statement leaves
// untouched.
static bool TargetWindow(const Expr* lhs, Variable& var, SimContext& ctx,
                         Arena& arena, ProcContAssignWindow& window) {
  if (lhs->kind != ExprKind::kSelect || !ArrayElementKeyOf(lhs, ctx).empty()) {
    return true;
  }
  PartSelectBits dst = SelectStorageBits(var, lhs, ctx, arena);
  window.src_lo = dst.src_lo;
  window.src_width = dst.width;
  window.dst_lo = dst.lo;
  window.dst_width = dst.width;
  return dst.width != 0;
}

StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  Variable* var = nullptr;
  if (ProcContAssignTargetHandled(stmt, ctx, arena, &var)) {
    return StmtResult::kDone;
  }

  // §10.6.2's constant bit-selects and part-selects of a vector net are targets
  // in their own right, and ResolveLhsVariable walks
  // a select down to its base and discards the index. Without the window,
  // `force bus[3] = 1'b1;` on a `wire [7:0] bus` marked all eight bits forced
  // and stored the one-bit value as the whole net's value -- the net's width
  // among what it overwrote, a Logic4Vec carrying its own. §11.5.1 resolves
  // which bits the select names, through the same call every writer of a select
  // makes; a select naming no bit of the object leaves the stored data
  // untouched, which here is a force that holds nothing and marks nothing.
  RhsWatcherSpec spec;
  if (!TargetWindow(stmt->lhs, *var, ctx, arena, spec.window)) {
    return StmtResult::kDone;
  }
  // §10.7 with §10.6: the target's width is the context the right-hand side is
  // evaluated in, as for any assignment, so `force w = a + b` keeps the carry
  // a sixteen-bit `w` has room for and a signed value is sign-extended into a
  // wider select. A concatenation target has its context width from
  // LhsContextWidth.
  spec.window.rhs_width =
      spec.window.dst_width != 0 ? spec.window.dst_width : var->value.width;

  // §10.6.1 gives the assign statement a singular variable or a concatenation
  // of variables as its target, and this is the singular one: it owns every
  // bit of the value and every bit of itself, which is the empty window with
  // the variable's width as the context. InstallProcContAssign records it
  // rather than leaving it alone, so that an earlier assign through a
  // concatenation leaves no window behind for this one's release to read.
  //
  // §10.6.2 makes force a statement on a net as well as on a variable, and the
  // net is what holds the strength the force settles. A select of a vector net
  // stands on that net as much as its name does -- the clause names both forms
  // in one sentence -- so the lookup follows the select to its base, which is
  // the name ResolveLhsVariable above resolved through.
  spec.net = ForceTargetNet(stmt->lhs, ctx);
  InstallProcContAssign(var, stmt, spec, ctx, arena);
  // §38.36.1: a cbForce callback is called after the force.
  if (stmt->kind == StmtKind::kForce) {
    GetGlobalVpiContext().NoteForce(cbForce, var, stmt,
                                    ctx.ActiveInstancePrefix());
  }

  return StmtResult::kDone;
}

// §10.6.2 (printed page 258): a released net at once takes the value its
// drivers determine, and §6.7.1 gives a net no driver reaches the value z.
// Resolution leaves such a net as it finds it -- a value written there by other
// means stands until they write again -- so `force a = 1; release a;` on an
// undriven `wire a` went on reading 1. The bits the force held are put back to
// z here, the drivers' answer when there are none; a trireg keeps them, as the
// charge it holds with every driver off, and a net type that resolves undriven,
// tri0 or supply1, is resolved over them.
static void ReleaseUndrivenBits(Net& net, const ProcContAssignWindow& window) {
  if (!net.drivers.empty() || !net.switch_drivers.empty() ||
      net.is_user_nettype || net.type == NetType::kTrireg) {
    return;
  }
  Logic4Vec& value = net.resolved->value;
  uint32_t lo = window.dst_width == 0 ? 0 : window.dst_lo;
  uint32_t width = window.dst_width == 0 ? value.width : window.dst_width;
  for (uint32_t bit = lo; bit < lo + width && bit < value.width; ++bit) {
    uint64_t mask = uint64_t{1} << (bit % 64);
    value.words[bit / 64].aval &= ~mask;
    value.words[bit / 64].bval |= mask;
  }
  net.resolved->NotifyWatchers();
}

// §10.6.2: ends the force on the bits of `var` that `window` names, the whole
// of it for the empty window. The parts it held on those bits go, a part
// holding other bits stays, and the variable is let go only when no part is
// left. A net released at once takes its drivers' value on the bits let go.
static void ReleaseForcedBits(Variable* var, Net* net,
                              const ProcContAssignWindow& window,
                              SimContext& ctx, Arena& arena) {
  auto released_by = [&window](const Variable::HeldPart& part) {
    return WindowsOverlap(part.window, window);
  };
  std::vector<ProcContAssignWindow> released;
  for (const auto& part : var->held_parts) {
    if (released_by(part)) released.push_back(part.window);
  }
  std::erase_if(var->held_parts, released_by);
  if (var->held_parts.empty())
    EndProcContAssign(var, /*release=*/true, ctx, arena);
  if (net == nullptr) return;
  for (const auto& bits : released) ReleaseUndrivenBits(*net, bits);
  net->Resolve(arena);
}

StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  Variable* var = nullptr;
  if (ProcContAssignTargetHandled(stmt, ctx, arena, &var)) {
    return StmtResult::kDone;
  }

  if (stmt->kind == StmtKind::kDeassign) {
    EndProcContAssign(var, /*release=*/false, ctx, arena);
    return StmtResult::kDone;
  }
  // §10.6.2: a released net at once takes the value its drivers determine,
  // which is as true of the bits a select named as of a whole net. The lookup
  // followed the identifier form alone, so `release bus[3];` cleared the flag
  // and left the net holding the forced value until some driver happened to
  // notify. The release ends the force on the bits it names and no other: a
  // force on other bits of the net goes on holding them.
  ProcContAssignWindow window;
  if (TargetWindow(stmt->lhs, *var, ctx, arena, window)) {
    ReleaseForcedBits(var, ForceTargetNet(stmt->lhs, ctx), window, ctx, arena);
  }
  // §38.36.1: a cbRelease callback is called after the release.
  GetGlobalVpiContext().NoteForce(cbRelease, var, stmt,
                                  ctx.ActiveInstancePrefix());
  return StmtResult::kDone;
}

void ReleaseForcedTarget(Variable* var, Net* net, SimContext& ctx,
                         Arena& arena) {
  ReleaseForcedBits(var, net, ProcContAssignWindow{}, ctx, arena);
}

}  // namespace delta
