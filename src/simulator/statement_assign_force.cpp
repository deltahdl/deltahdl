#include <algorithm>
#include <cstdint>
#include <functional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/packed_range.h"
#include "parser/ast.h"
#include "simulator/eval_array.h"
#include "simulator/evaluation.h"
#include "simulator/net.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/variable.h"

namespace delta {

static void CollectExprVars(const Expr* expr, SimContext& ctx,
                            std::vector<Variable*>& vars) {
  if (!expr) return;
  if (expr->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(expr->text);
    if (var) vars.push_back(var);
    return;
  }
  CollectExprVars(expr->lhs, ctx, vars);
  CollectExprVars(expr->rhs, ctx, vars);
  CollectExprVars(expr->condition, ctx, vars);
  CollectExprVars(expr->true_expr, ctx, vars);
  CollectExprVars(expr->false_expr, ctx, vars);
  CollectExprVars(expr->base, ctx, vars);
  CollectExprVars(expr->index, ctx, vars);
  CollectExprVars(expr->index_end, ctx, vars);
  CollectExprVars(expr->with_expr, ctx, vars);
  CollectExprVars(expr->repeat_count, ctx, vars);
  for (auto* e : expr->elements) CollectExprVars(e, ctx, vars);
  for (auto* a : expr->args) CollectExprVars(a, ctx, vars);
}

// Returns the distinct variables referenced by `rhs`, excluding `self`.
static std::vector<Variable*> CollectDistinctRhsVars(const Expr* rhs,
                                                     SimContext& ctx,
                                                     Variable* self) {
  std::vector<Variable*> rhs_vars;
  CollectExprVars(rhs, ctx, rhs_vars);
  std::sort(rhs_vars.begin(), rhs_vars.end());
  rhs_vars.erase(std::unique(rhs_vars.begin(), rhs_vars.end()), rhs_vars.end());
  rhs_vars.erase(std::remove(rhs_vars.begin(), rhs_vars.end(), self),
                 rhs_vars.end());
  return rhs_vars;
}

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
  // §11.4.12 treats a concatenation as "a packed vector of bits", so an element
  // of one owns a window of the right-hand value and a window of its own
  // storage. Those five numbers are what Variable records beside an assign's
  // right-hand side, so they are the struct Variable records rather than five
  // fields of this one: a release has to reestablish through the window the
  // assign was installed with.
  ProcContAssignWindow window;
};

// Writes into `var` the part of `val` this installation owns. A singular target
// owns the whole value and takes it whole, width and all. An element of a
// concatenation owns the two windows above instead, and the bits outside its
// destination window belong to the other elements or to nothing at all and have
// to be left standing, which is what DepositBitField does and what writing the
// variable whole did not: `force {w, bus[3]} = 2'b11;` gave `bus` the whole
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
    if (spec.forced) var->forced_value = val;
    var->value = val;
  } else {
    Logic4Vec updated = ExtractBitField(arena, var->value, 0, var->value.width);
    DepositBitField(updated, spec.window.dst_lo,
                    spec.window.src_width == 0
                        ? val
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
  // §10.6.2 overrides "all drivers of the net" that was named, and a constant
  // select of a vector net names some of its bits: the window travels onto the
  // variable so Net::Resolve can leave the drivers of the rest alone.
  var->forced_window = spec.window;
  WriteOwnedBits(var, rhs_val, spec, arena);
  var->proc_cont_rhs = rhs;
  var->NotifyWatchers();

  // §10.6.2: the force overrides the net's drivers from here, so the strength
  // it reports is settled now rather than at the next driver update -- there
  // may be no further one, and a net forced before anything drove it has no
  // strength recorded at all.
  if (spec.net != nullptr) spec.net->Resolve(arena);

  spec.still_valid = [var, rhs]() {
    return var->is_forced && var->proc_cont_rhs == rhs;
  };
  InstallRhsWatchers(var, rhs, ctx, arena, spec);
}

// Reestablishes a continuous assignment on `var` from expression `rhs` after
// a release statement. Similar to InstallForcedValueWatcher but for
// assignments: does not set is_forced, and watchers check assign_cont_rhs
// instead of is_forced to remain valid after release.
static void ReestablishContinuousAssignment(Variable* var, const Expr* rhs,
                                            SimContext& ctx, Arena& arena,
                                            RhsWatcherSpec spec) {
  // §10.6.1 gives the assign statement "a singular variable reference or a
  // concatenation of variables", so nothing it reestablishes stands on a net
  // and the force's net does not carry over into the assignment that outlives
  // it.
  spec.net = nullptr;
  spec.forced = false;
  auto rhs_val = EvalExpr(rhs, ctx, arena, spec.window.rhs_width);
  WriteOwnedBits(var, rhs_val, spec, arena);
  var->NotifyWatchers();

  spec.still_valid = [var, rhs]() {
    return var->assign_cont_rhs && var->assign_cont_rhs == rhs;
  };
  InstallRhsWatchers(var, rhs, ctx, arena, spec);
}

// One element of a concatenation left-hand side, the window of the right-hand
// value it owns and the width that value is evaluated at. §11.4.12 makes the
// concatenation "a packed vector of bits", so the rightmost element takes the
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
// indices address, "determined by the declaration".
//
// The two windows are two answers and not one: the element is as wide as
// ConcatLhsElemWidth makes it whether or not its address is in bounds, and it
// writes only the bits SelectStorageBits leaves it. They differ for a
// part-select that is partly out of range, which §11.5.1 has "when written,
// only affect the bits that are in range" -- `a[9:6]` on `logic [7:0] a` is
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
  // §11.5.1's "only affect the bits that are in range" is itself two answers:
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
// bits of a net holds those bits alone: §10.6.2's override of "all drivers of
// the net" reaches the drivers of what was named, which for `force {w, bus[3]}`
// is bit 3 rather than every bit of `bus`.
static void ForceOneElement(const ConcatElemSlot& slot, const Stmt* stmt,
                            SimContext& ctx, Arena& arena) {
  RhsWatcherSpec spec = SpecForSlot(slot, ctx, arena);
  if (stmt->kind == StmtKind::kAssign) {
    slot.var->assign_cont_rhs = stmt->rhs;
    // §10.6.1's reestablishment is of this assignment, so the window it gave
    // this element travels with the expression that will be re-evaluated
    // through it, however the release that reestablishes it is written.
    slot.var->assign_cont_window = spec.window;
  }
  InstallForcedValueWatcher(slot.var, stmt->rhs, ctx, arena, spec);
}

// Releases or deassigns one element of a concatenation target. §10.6.1: "The
// deassign procedural statement shall end an assign procedural continuous
// assignment to a variable", and §10.6.2 ends a force on a release; each
// element was marked on its own and so is cleared on its own.
static void ReleaseOneElement(const ConcatElemSlot& slot, const Stmt* stmt,
                              SimContext& ctx, Arena& arena) {
  Variable* var = slot.var;
  var->is_forced = false;
  var->forced_window = {};
  var->proc_cont_rhs = nullptr;
  if (stmt->kind == StmtKind::kDeassign) {
    var->assign_cont_rhs = nullptr;
    var->assign_cont_window = {};
    return;
  }

  RhsWatcherSpec spec = SpecForSlot(slot, ctx, arena);
  // §10.6.2: "When released, the net shall immediately be assigned the value
  // determined by the drivers of the net."
  if (spec.net != nullptr) spec.net->Resolve(arena);

  // §10.6.1: "Releasing a variable that is driven by a continuous assignment or
  // currently has an active assign procedural continuous assignment shall
  // reestablish that assignment", and the element gets back the window of that
  // assignment's value it held, not the whole of it: without the window,
  // `assign {a, b} = 16'h1234; force {a, b} = ...; release {a, b};` handed `a`
  // the entire sixteen-bit value.
  //
  // The window is the assignment's own rather than this statement's. The two
  // agree only where the release names the target the assign named, and
  // `assign {a, b} = 16'h1234; force a = 8'h55; release a;` is where they part:
  // this release's element is the whole of `a`, whose window is the whole of
  // the value, while the assignment gave `a` the value's high eight bits.
  if (var->assign_cont_rhs) {
    RhsWatcherSpec reestablished;
    reestablished.window = var->assign_cont_window;
    ReestablishContinuousAssignment(var, var->assign_cont_rhs, ctx, arena,
                                    reestablished);
  }
}

// Routes one element to the statement that named it: the two statements that
// install a procedural continuous assignment, and the two that end one.
//
// An element addressing no bit of its target is routed nowhere. §11.5.1 gives
// such a write "no effect on the data stored", and for these four statements
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
// a concatenation target. §10.6.2 admits "a concatenation of these" and §10.6.1
// "a concatenation of variables", so each element is a target of the statement
// in its own right and the elements divide the right-hand value the way
// §11.4.12 divides it for a blocking assignment: the walk runs in reverse so
// that the rightmost element takes the least significant bits. Returns the
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
      // §11.5.1 requires an indexed part-select's width to "be a positive
      // constant", so an element written with a width of zero is illegal
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

// --- §10.6 on an element of a queue or of an associative array ---
//
// §6.4 makes "any data type except an unpacked structure, unpacked union, or
// unpacked array" singular, so an element of one of those containers is a
// singular variable however the container itself is typed, and §10.6.1's
// "singular variable reference" and §10.6.2's "reference to a singular
// variable" both reach it. What such an element does not have is a Variable:
// its value is a bare Logic4Vec inside a QueueObject or an AssocArrayObject,
// with nowhere to keep the flag a force sets or the expression it recomputes
// from. ResolveLhsVariable answers the container's own one-element carrier for
// it, which no read of the container consults, so both statements settled a
// variable nothing reads and the element kept the value it had.

// The element a §10.6 statement names, and the container that holds it. The
// name is carried because a write to an element is announced through the
// variable the container is registered under (§9.4.2), which is what an
// `@(q[0])` and an always_comb reading it are armed on.
struct ContainerElement {
  QueueObject* queue = nullptr;
  AssocArrayObject* assoc = nullptr;
  uint64_t queue_id = 0;
  bool string_key = false;
  int64_t int_key = 0;
  std::string str_key;
  std::string name;
  uint32_t elem_width = 32;
};

// The record `elem`'s drives are kept in. `create` is what a statement
// installing one passes; a statement ending one asks without it and is answered
// null where nothing stands.
static ElementDrive* ElementDriveFor(const ContainerElement& elem,
                                     bool create) {
  if (elem.queue != nullptr) {
    auto& drives = elem.queue->element_drives;
    auto it = drives.find(elem.queue_id);
    if (it != drives.end()) return &it->second;
    return create ? &drives[elem.queue_id] : nullptr;
  }
  if (elem.assoc == nullptr) return nullptr;
  if (elem.string_key) {
    auto& drives = elem.assoc->str_drives;
    auto it = drives.find(elem.str_key);
    if (it != drives.end()) return &it->second;
    return create ? &drives[elem.str_key] : nullptr;
  }
  auto& drives = elem.assoc->int_drives;
  auto it = drives.find(elem.int_key);
  if (it != drives.end()) return &it->second;
  return create ? &drives[elem.int_key] : nullptr;
}

// Drops a record that no longer holds anything, so an element carries a record
// only while a statement stands on it.
static void ForgetEmptyElementDrive(const ContainerElement& elem) {
  ElementDrive* drive = ElementDriveFor(elem, /*create=*/false);
  if (drive == nullptr || drive->Drives()) return;
  if (elem.queue != nullptr) {
    elem.queue->element_drives.erase(elem.queue_id);
  } else if (elem.string_key) {
    elem.assoc->str_drives.erase(elem.str_key);
  } else {
    elem.assoc->int_drives.erase(elem.int_key);
  }
}

// Resolves `lhs` to the queue element it names, and whether it names one. An
// index that is out of range or carries an unknown bit names no element:
// §7.10.1 has such an index ignore a write, and a statement that drives nothing
// installs nothing.
static bool ResolveQueueElement(const Expr* lhs, QueueObject* q,
                                SimContext& ctx, Arena& arena,
                                ContainerElement& out) {
  bool idx_xz = false;
  int64_t idx = QueueElementIndex(lhs->index, q, ctx, arena, &idx_xz);
  if (idx_xz) return false;
  if (idx < 0 || idx >= static_cast<int64_t>(q->elements.size())) return false;
  out.queue = q;
  out.queue_id = q->element_ids[static_cast<size_t>(idx)];
  out.elem_width = q->elem_width;
  return true;
}

// The same for an associative array, whose key is the element's identity.
// §7.8.6 makes an index carrying an unknown bit invalid, and an entry the array
// does not hold is not an element to stand on: §7.8.7 allocates one on a write
// and a §10.6 statement is not that write.
static bool ResolveAssocElement(const Expr* lhs, AssocArrayObject* aa,
                                SimContext& ctx, Arena& arena,
                                ContainerElement& out) {
  auto key_val = EvalExpr(lhs->index, ctx, arena);
  if (aa->is_string_key) {
    out.str_key = AssocStringKey(key_val);
    if (aa->str_data.find(out.str_key) == aa->str_data.end()) return false;
    out.string_key = true;
  } else {
    if (HasUnknownBits(key_val)) return false;
    out.int_key = AssocIntKey(key_val, aa->is_wildcard, aa->index_width,
                              aa->is_index_signed);
    if (aa->int_data.find(out.int_key) == aa->int_data.end()) return false;
  }
  out.assoc = aa;
  out.elem_width = aa->elem_width;
  return true;
}

// Resolves a §10.6 target to the container element it names. A select with a
// second index is a slice rather than an element and names none.
static bool ResolveContainerElement(const Expr* lhs, SimContext& ctx,
                                    Arena& arena, ContainerElement& out) {
  if (lhs == nullptr || lhs->kind != ExprKind::kSelect) return false;
  if (lhs->base == nullptr || lhs->base->kind != ExprKind::kIdentifier)
    return false;
  if (lhs->index == nullptr || lhs->index_end != nullptr) return false;
  out.name = std::string(lhs->base->text);
  if (auto* q = ctx.FindQueue(lhs->base->text)) {
    return ResolveQueueElement(lhs, q, ctx, arena, out);
  }
  if (auto* aa = ctx.FindAssocArray(lhs->base->text)) {
    return ResolveAssocElement(lhs, aa, ctx, arena, out);
  }
  return false;
}

// Stores `val` in the element, at the element's own width, and announces the
// change the way every other write to one does (§9.4.2). The element the
// identity names is looked up again on each store, because a queue's elements
// move under it.
static void StoreContainerElement(const ContainerElement& elem,
                                  const Logic4Vec& val, SimContext& ctx,
                                  Arena& arena) {
  Logic4Vec sized = ResizeToWidth(val, elem.elem_width, arena);
  if (elem.queue != nullptr) {
    const auto& ids = elem.queue->element_ids;
    for (size_t i = 0; i < ids.size() && i < elem.queue->elements.size(); ++i) {
      if (ids[i] != elem.queue_id) continue;
      elem.queue->elements[i] = sized;
      NotifyOwningVar(ctx, elem.name);
      return;
    }
    return;
  }
  if (elem.assoc == nullptr) return;
  if (elem.string_key) {
    auto it = elem.assoc->str_data.find(elem.str_key);
    if (it == elem.assoc->str_data.end()) return;
    it->second = sized;
  } else {
    auto it = elem.assoc->int_data.find(elem.int_key);
    if (it == elem.assoc->int_data.end()) return;
    it->second = sized;
  }
  NotifyOwningVar(ctx, elem.name);
}

// The value one drive puts in the element: the whole right-hand value where the
// statement named the element alone, and §11.4.12's slice of it where the
// target was a concatenation.
static Logic4Vec ElementDriveValue(const ElementDriveSource& src,
                                   SimContext& ctx, Arena& arena) {
  auto val = EvalExpr(src.rhs, ctx, arena, src.rhs_width);
  if (src.width == 0) return val;
  return ExtractBitField(arena, val, src.src_lo, src.width);
}

// Installs, on each variable the drive's expression reads, a watcher that
// recomputes the element while the drive stands. The drive is looked up again
// rather than captured, so a record dropped by a release -- or by the removal
// of the element the queue identity named -- retires the watcher.
static void InstallElementDriveWatchers(const ContainerElement& elem,
                                        const ElementDriveSource& src,
                                        bool forced, SimContext& ctx,
                                        Arena& arena) {
  auto* ctx_ptr = &ctx;
  auto* arena_ptr = &arena;
  for (auto* rhs_var : CollectDistinctRhsVars(src.rhs, ctx, nullptr)) {
    rhs_var->AddWatcher([elem, src, forced, ctx_ptr, arena_ptr]() {
      const ElementDrive* drive = ElementDriveFor(elem, /*create=*/false);
      if (drive == nullptr) return true;
      const ElementDriveSource& standing =
          forced ? drive->forced : drive->assigned;
      if (standing.rhs != src.rhs) return true;
      StoreContainerElement(elem, ElementDriveValue(src, *ctx_ptr, *arena_ptr),
                            *ctx_ptr, *arena_ptr);
      return false;
    });
  }
}

// §10.6.1 and §10.6.2: installs the statement's drive on the element, writes
// the value it computes now, and arms the recomputation. A force installed over
// an assign leaves the assign standing beneath it, which is what §10.6.2's
// release reestablishes.
static void DriveContainerElement(const ContainerElement& elem,
                                  const Stmt* stmt,
                                  const ElementDriveSource& src,
                                  SimContext& ctx, Arena& arena) {
  ElementDrive* drive = ElementDriveFor(elem, /*create=*/true);
  bool forced = stmt->kind == StmtKind::kForce;
  if (forced) {
    drive->forced = src;
  } else {
    drive->assigned = src;
  }
  StoreContainerElement(elem, ElementDriveValue(src, ctx, arena), ctx, arena);
  InstallElementDriveWatchers(elem, src, forced, ctx, arena);
}

// §10.6.2's release and §10.6.1's deassign, on the element the target names.
// Releasing an element that has an assign standing beneath the force
// reestablishes that assignment, which is what the clause requires of a
// variable in the same position.
static void EndContainerElementDrive(const ContainerElement& elem,
                                     const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  ElementDrive* drive = ElementDriveFor(elem, /*create=*/false);
  if (drive == nullptr) return;
  if (stmt->kind == StmtKind::kDeassign) {
    drive->assigned = {};
  } else {
    drive->forced = {};
    if (drive->assigned.rhs != nullptr) {
      StoreContainerElement(
          elem, ElementDriveValue(drive->assigned, ctx, arena), ctx, arena);
    }
  }
  ForgetEmptyElementDrive(elem);
}

// Answers one of the four §10.6 statements on a container element, and whether
// the target named one. `src_lo`, `width` and `rhs_width` are the concatenation
// slot the element takes; a lone target passes a zero width and takes the whole
// right-hand value.
static bool TryContainerElementDrive(const Expr* lhs, const Stmt* stmt,
                                     const ElementDriveSource& slot,
                                     SimContext& ctx, Arena& arena) {
  ContainerElement elem;
  if (!ResolveContainerElement(lhs, ctx, arena, elem)) return false;
  if (stmt->kind == StmtKind::kRelease || stmt->kind == StmtKind::kDeassign) {
    EndContainerElementDrive(elem, stmt, ctx, arena);
    return true;
  }
  ElementDriveSource src = slot;
  src.rhs = stmt->rhs;
  DriveContainerElement(elem, stmt, src, ctx, arena);
  return true;
}

// §10.6.2 gives force and release the same targets, and among them "a net, a
// constant bit-select of a vector net, a constant part-select of a vector net":
// all three stand on one net, which is what holds the strength the force
// settles and what a release re-resolves from its drivers. A select is followed
// to its base for that reason -- one sentence names the three forms and says
// the same thing about them -- while a concatenation names no one net and
// answers none.
static Net* ForceTargetNet(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kIdentifier) return ctx.FindNet(lhs->text);
  if (lhs->kind == ExprKind::kSelect && lhs->base != nullptr &&
      lhs->base->kind == ExprKind::kIdentifier) {
    return ctx.FindNet(lhs->base->text);
  }
  return nullptr;
}

StmtResult ExecForceOrAssignImpl(const Stmt* stmt, SimContext& ctx,
                                 Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  // §10.6.2: "The left-hand side of the assignment can be a reference to a
  // singular variable, a net, a constant bit-select of a vector net, a constant
  // part-select of a vector net, or a concatenation of these", and §10.6.1
  // gives the assign statement "a singular variable reference or a
  // concatenation of variables". A concatenation names no one object, so
  // ResolveLhsVariable answers null for it and the statement returned below
  // having marked nothing and written nothing: `force {a, b} = 16'h1234;` left
  // `a` and `b` at their initial values with is_forced clear on both.
  if (IsConcatLhs(stmt->lhs)) {
    WalkConcatLhsElements(UnwrapTypedPattern(stmt->lhs), stmt, 0, ctx, arena);
    return StmtResult::kDone;
  }
  // §6.4 makes an element of a queue or of an associative array a singular
  // variable, which both statements name among their targets, and it has no
  // Variable for the resolution below to answer with.
  if (TryContainerElementDrive(stmt->lhs, stmt, ElementDriveSource{}, ctx,
                               arena)) {
    return StmtResult::kDone;
  }
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  // §10.6.2's "a constant bit-select of a vector net, a constant part-select of
  // a vector net" are targets in their own right, and ResolveLhsVariable walks
  // a select down to its base and discards the index. Without the window,
  // `force bus[3] = 1'b1;` on a `wire [7:0] bus` marked all eight bits forced
  // and stored the one-bit value as the whole net's value -- the net's width
  // among what it overwrote, a Logic4Vec carrying its own. §11.5.1 resolves
  // which bits the select names, through the same call every writer of a select
  // makes; a select naming no bit of the object is given "no effect on the data
  // stored", which here is a force that holds nothing and marks nothing.
  RhsWatcherSpec spec;
  if (stmt->lhs->kind == ExprKind::kSelect) {
    PartSelectBits dst = SelectStorageBits(*var, stmt->lhs, ctx, arena);
    if (dst.width == 0) return StmtResult::kDone;
    spec.window.src_lo = dst.src_lo;
    spec.window.src_width = dst.width;
    spec.window.dst_lo = dst.lo;
    spec.window.dst_width = dst.width;
  }

  if (stmt->kind == StmtKind::kAssign) {
    var->assign_cont_rhs = stmt->rhs;
    // §10.6.1 gives the assign statement "a singular variable reference or a
    // concatenation of variables", and this is the singular one: it owns every
    // bit of the value and every bit of itself, which is the empty window. It
    // is recorded rather than left alone so that an earlier assign through a
    // concatenation leaves no window behind for this one's release to read.
    var->assign_cont_window = {};
  }
  // §10.6.2 makes force a statement on a net as well as on a variable, and the
  // net is what holds the strength the force settles. A select of a vector net
  // stands on that net as much as its name does -- the clause names both forms
  // in one sentence -- so the lookup follows the select to its base, which is
  // the name ResolveLhsVariable above resolved through.
  spec.net = ForceTargetNet(stmt->lhs, ctx);
  InstallForcedValueWatcher(var, stmt->rhs, ctx, arena, spec);

  return StmtResult::kDone;
}

StmtResult ExecReleaseOrDeassignImpl(const Stmt* stmt, SimContext& ctx,
                                     Arena& arena) {
  if (!stmt->lhs) return StmtResult::kDone;
  // §10.6.1 and §10.6.2 give release and deassign the same targets their
  // installing statements take, so a concatenation is ended element by element.
  // Resolving it as one object answered null, which left `release {a, b};` and
  // `deassign {a, b};` as no-ops and would have made the force above one no
  // release could lift.
  if (IsConcatLhs(stmt->lhs)) {
    WalkConcatLhsElements(UnwrapTypedPattern(stmt->lhs), stmt, 0, ctx, arena);
    return StmtResult::kDone;
  }
  if (TryContainerElementDrive(stmt->lhs, stmt, ElementDriveSource{}, ctx,
                               arena)) {
    return StmtResult::kDone;
  }
  auto* var = ResolveLhsVariable(stmt->lhs, ctx);
  if (!var) return StmtResult::kDone;

  var->is_forced = false;
  var->forced_window = {};
  var->proc_cont_rhs = nullptr;

  if (stmt->kind == StmtKind::kDeassign) {
    var->assign_cont_rhs = nullptr;
    var->assign_cont_window = {};
  } else if (auto* net = ForceTargetNet(stmt->lhs, ctx)) {
    // §10.6.2: "When released, the net shall immediately be assigned the value
    // determined by the drivers of the net", which is as true of the bits a
    // select named as of a whole net. The lookup followed the identifier form
    // alone, so `release bus[3];` cleared the flag and left the net holding the
    // forced value until some driver happened to notify.
    net->Resolve(arena);
  }

  if (var->assign_cont_rhs && stmt->kind != StmtKind::kDeassign) {
    // The window the assignment was installed with, which for an assign through
    // a concatenation is this variable's slice of it and not the whole value.
    RhsWatcherSpec reestablished;
    reestablished.window = var->assign_cont_window;
    ReestablishContinuousAssignment(var, var->assign_cont_rhs, ctx, arena,
                                    reestablished);
  }

  return StmtResult::kDone;
}

}  // namespace delta
