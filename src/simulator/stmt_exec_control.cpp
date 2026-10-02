#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"
#include "simulator/covergroup_instance.h"
#include "simulator/eval_array.h"
#include "simulator/eval_array_class_assoc.h"
#include "simulator/eval_array_class_queue.h"
#include "simulator/eval_array_element_queue.h"
#include "simulator/eval_class_array.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/exec_task.h"
#include "simulator/foreach_dims.h"
#include "simulator/pattern_match.h"
#include "simulator/process.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/stmt_exec.h"
#include "simulator/stmt_exec_internal.h"
#include "simulator/stmt_result.h"

namespace delta {

// §6.21 with §9.3.1: a block declares variables of a scope of its own,
// named or not. A named block's frame is kept under its label; an unnamed
// block declaring variables outside any subroutine is given one kept under
// UnnamedBlockFrameName, so its static variables last from one activation to
// the next and its names hide the module's only inside it. Without it, the
// declaration replaced the module's variable of the same name. Inside a task
// or function the declaration already lands in the subroutine's frame.
static std::string_view BlockFrameName(const Stmt* stmt, SimContext& ctx) {
  if (!stmt->label.empty()) return stmt->label;
  if (!ctx.CurrentFuncName().empty()) return {};
  bool declares = std::ranges::any_of(
      stmt->stmts, [](const Stmt* s) { return s->kind == StmtKind::kVarDecl; });
  return declares ? ctx.UnnamedBlockFrameName(stmt) : std::string_view{};
}

// Pushes the frame BlockFrameName gives `stmt`, and for a named block the
// named scope beside it, answering the frame's name, empty where none. §19.3:
// a named block beginning is a block event a covergroup may sample at.
static std::string_view EnterBlockScope(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  std::string_view frame = BlockFrameName(stmt, ctx);
  if (frame.empty()) return frame;
  ctx.PushStaticScope(frame);
  if (!stmt->label.empty()) {
    ctx.RegisterNamedScope(stmt->label, ctx.CurrentProcess());
    ctx.PushActiveNamedScope(stmt->label);
    SampleAtBlockEvent(stmt->label, true, ctx, arena);
  }
  return frame;
}

// Tears down what EnterBlockScope pushed. A no-op where it pushed nothing.
// Always called immediately before ExecBlock returns so the scope stack is
// balanced on every exit path. §19.3: a named block ending is a block event a
// covergroup may sample at, unless the block was disabled, `ended` false.
static void TeardownBlockScope(const Stmt* stmt, SimContext& ctx, Arena& arena,
                               std::string_view frame, bool ended) {
  if (frame.empty()) return;
  if (!stmt->label.empty()) {
    if (ended) SampleAtBlockEvent(stmt->label, false, ctx, arena);
    ctx.PopActiveNamedScope();
    ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
  }
  ctx.PopStaticScope(frame);
}

// A named block is a scope of the hierarchy, and so is a task or function,
// which stands under its module rather than under the blocks of the process
// calling it; the path therefore starts at the innermost subroutine.
void BindNamedBlockVariable(std::string_view name, SimContext& ctx) {
  const std::vector<std::string_view>& scopes = ctx.ActiveNamedScopes();
  if (scopes.empty()) return;
  size_t first = 0;
  for (size_t i = scopes.size(); i-- > 0;) {
    if (ctx.FindFunction(scopes[i]) != nullptr) {
      first = i;
      break;
    }
  }
  std::string path = ctx.ActiveInstancePrefix();
  for (size_t i = first; i < scopes.size(); ++i) {
    path += scopes[i];
    path += '.';
  }
  path += name;
  ctx.AliasVariable(*ctx.GetArena().Create<std::string>(std::move(path)), name);
}

ExecTask ExecBlock(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool named = !stmt->label.empty();
  std::string_view frame = EnterBlockScope(stmt, ctx, arena);
  for (auto* s : stmt->stmts) {
    auto result = co_await ExecStmt(s, ctx, arena);
    if (result == StmtResult::kDisable) {
      if (named && ctx.GetDisableTarget() == stmt->label) {
        ctx.ClearDisableTarget();
        TeardownBlockScope(stmt, ctx, arena, frame, false);
        co_return StmtResult::kDone;
      }
      TeardownBlockScope(stmt, ctx, arena, frame, false);
      co_return StmtResult::kDisable;
    }
    if (result != StmtResult::kDone) {
      TeardownBlockScope(stmt, ctx, arena, frame, true);
      co_return result;
    }
    if (ctx.StopRequested()) {
      TeardownBlockScope(stmt, ctx, arena, frame, true);
      co_return StmtResult::kDone;
    }

    if (auto* cur = ctx.CurrentProcess(); cur && !cur->active) {
      TeardownBlockScope(stmt, ctx, arena, frame, false);
      co_return StmtResult::kDone;
    }
  }
  TeardownBlockScope(stmt, ctx, arena, frame, true);
  co_return StmtResult::kDone;
}

struct UniqueIfResult {
  const Stmt* first_match = nullptr;
  int match_count = 0;
  bool has_final_else = false;
};

static UniqueIfResult EvalUniqueIfChain(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  UniqueIfResult result;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    auto cond = EvalExpr(cur->condition, ctx, arena);
    if (cond.IsTruthy()) {
      result.match_count++;
      if (!result.first_match) result.first_match = cur;
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      result.has_final_else = true;
    }
  }
  return result;
}

static const Stmt* FindFinalElse(const Stmt* stmt) {
  const Stmt* cur = stmt;
  while (cur->else_branch && cur->else_branch->kind == StmtKind::kIf) {
    cur = cur->else_branch;
  }
  return cur->else_branch;
}

static ExecTask ExecUniqueIf(const Stmt* stmt, CaseQualifier qual,
                             SimContext& ctx, Arena& arena) {
  auto info = EvalUniqueIfChain(stmt, ctx, arena);

  if (info.match_count > 1) {
    ctx.AddPendingViolation(stmt->range.start,
                            "unique if: multiple conditions matched",
                            Subclause("12.4.2.1"));
  }
  if (info.first_match) {
    co_return co_await ExecStmt(info.first_match->then_branch, ctx, arena);
  }
  if (info.has_final_else) {
    const Stmt* final_else = FindFinalElse(stmt);
    if (final_else) co_return co_await ExecStmt(final_else, ctx, arena);
  }
  if (!info.has_final_else && qual == CaseQualifier::kUnique) {
    ctx.AddPendingViolation(stmt->range.start,
                            "unique if: no condition matched",
                            Subclause("12.4.2.1"));
  }
  co_return StmtResult::kDone;
}

static ExecTask ExecPriorityIf(const Stmt* stmt, SimContext& ctx,
                               Arena& arena) {
  bool has_final_else = false;
  for (const Stmt* cur = stmt; cur && cur->kind == StmtKind::kIf;
       cur = cur->else_branch) {
    auto cond = EvalExpr(cur->condition, ctx, arena);
    if (cond.IsTruthy()) {
      co_return co_await ExecStmt(cur->then_branch, ctx, arena);
    }
    if (cur->else_branch && cur->else_branch->kind != StmtKind::kIf) {
      has_final_else = true;
    }
  }
  if (has_final_else) {
    const Stmt* final_else = FindFinalElse(stmt);
    if (final_else) co_return co_await ExecStmt(final_else, ctx, arena);
  }
  if (!has_final_else) {
    ctx.AddPendingViolation(stmt->range.start,
                            "priority if: no condition matched",
                            Subclause("12.4.2.1"));
  }
  co_return StmtResult::kDone;
}

// §12.6.2: an if whose predicate binds pattern identifiers. They are created
// in a scope that holds the predicate's later clauses and the true arm
// (EvalMatchesPredicate); the else arm stands outside it.
static ExecTask ExecIfBindingPredicate(const Stmt* stmt, SimContext& ctx,
                                       Arena& arena) {
  ctx.PushScope();
  if (EvalMatchesPredicate(stmt->condition, ctx, arena)) {
    auto r = co_await ExecStmt(stmt->then_branch, ctx, arena);
    ctx.PopScope();
    co_return r;
  }
  ctx.PopScope();
  if (stmt->else_branch == nullptr) co_return StmtResult::kDone;
  co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
}

// An if with no unique, unique0 or priority qualifier.
static ExecTask ExecPlainIf(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (PatternBindsIdentifiers(stmt->condition)) {
    co_return co_await ExecIfBindingPredicate(stmt, ctx, arena);
  }
  if (EvalExpr(stmt->condition, ctx, arena).IsTruthy()) {
    co_return co_await ExecStmt(stmt->then_branch, ctx, arena);
  }
  if (stmt->else_branch == nullptr) co_return StmtResult::kDone;
  co_return co_await ExecStmt(stmt->else_branch, ctx, arena);
}

ExecTask ExecIf(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  auto qual = stmt->qualifier;
  StmtResult r = StmtResult::kDone;
  if (qual == CaseQualifier::kUnique || qual == CaseQualifier::kUnique0) {
    r = co_await ExecUniqueIf(stmt, qual, ctx, arena);
  } else if (qual == CaseQualifier::kPriority) {
    r = co_await ExecPriorityIf(stmt, ctx, arena);
  } else {
    r = co_await ExecPlainIf(stmt, ctx, arena);
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return r;
}

static void CreateForInitVars(const Stmt* stmt, SimContext& ctx) {
  for (size_t i = 0; i < stmt->for_inits.size(); ++i) {
    if (i >= stmt->for_init_types.size()) break;
    if (stmt->for_init_types[i].kind == DataTypeKind::kImplicit) continue;
    auto* init = stmt->for_inits[i];
    if (!init || !init->lhs) continue;
    uint32_t w = DeclaredTypeWidth(stmt->for_init_types[i], ctx);
    if (w == 0) w = 32;
    // §6.11.3: byte, shortint, int, integer and longint default to signed, so
    // the declared type decides the loop variable's signedness as it decides
    // any other local's. Created from the width alone, an int counter compared
    // its negative values as huge positive ones.
    auto* v = ctx.CreateLocalVariable(
        init->lhs->text, w, DeclaredTypeIsSigned(stmt->for_init_types[i], ctx));
    // §6.11.2: "when a 4-state value is automatically converted to a 2-state
    // value, any unknown or high-impedance bits shall be converted to zeros",
    // and it is this flag that WriteVar consults to make the conversion when
    // the initializer runs as an ordinary assignment below. It defaults to
    // true, so an `int` counter initialized from a 4-state variable kept the
    // unknown bits the clause converts. The width needs no such repair here:
    // the assignment goes through WriteVar, which applies §10.7 to the cell
    // this created.
    v->is_4state = DeclaredTypeIs4State(stmt->for_init_types[i], ctx);
  }
}

static bool HasTypedForInit(const Stmt* stmt) {
  for (const auto& t : stmt->for_init_types) {
    if (t.kind != DataTypeKind::kImplicit) return true;
  }
  return false;
}

// Pops the dynamic scope a typed for-init introduced and the static scope a
// label introduced, in the order ExecFor pushed them. Called on every ExecFor
// exit path to keep the scope stack balanced.
// §9.3.5: a statement label on a foreach loop, or a for loop that declares its
// loop variable, names the implicit begin-end block the loop creates. Pushing
// the static scope alone (for hierarchical name resolution) is not enough for a
// `disable <label>` to find the loop; registering the label as a named scope of
// the running process — exactly as ExecBlock does for a named begin-end block —
// lets the disable resolve so the loop can consume it. Paired 1:1 with
// ExitLoopLabelScope so the scope stack stays balanced on every exit path.
static void EnterLoopLabelScope(const Stmt* stmt, SimContext& ctx,
                                bool labeled) {
  if (!labeled) return;
  ctx.PushStaticScope(stmt->label);
  ctx.RegisterNamedScope(stmt->label, ctx.CurrentProcess());
}

static void ExitLoopLabelScope(const Stmt* stmt, SimContext& ctx,
                               bool labeled) {
  if (!labeled) return;
  ctx.UnregisterNamedScope(stmt->label, ctx.CurrentProcess());
  ctx.PopStaticScope(stmt->label);
}

static void TeardownForScopes(const Stmt* stmt, SimContext& ctx, bool scoped,
                              bool labeled) {
  if (scoped) ctx.PopScope();
  ExitLoopLabelScope(stmt, ctx, labeled);
}

// How a loop should react to the StmtResult returned by its body, factored out
// of the repeated "break / propagate / keep looping" branch shared by every
// loop executor in this file. kPropagate means the caller must unwind its
// scopes and co_return the body's result unchanged.
enum class LoopAction : std::uint8_t { kKeepLooping, kBreakLoop, kPropagate };

static LoopAction ClassifyLoopBodyResult(StmtResult result) {
  if (result == StmtResult::kBreak) return LoopAction::kBreakLoop;
  if (result != StmtResult::kDone && result != StmtResult::kContinue) {
    return LoopAction::kPropagate;
  }
  return LoopAction::kKeepLooping;
}

// §9.3.5: a statement label on a foreach loop, or on a for loop that declares
// its loop variable, names the implicit begin-end block the loop creates. Per
// §9.6.2, disabling a named block terminates it and resumes execution at the
// following statement. So when the loop body bubbles up a kDisable that targets
// the loop's own label, the disable is consumed here and turned into a normal
// loop exit rather than propagating further up the process. Returns true when
// the loop should stop.
static bool LoopDisableTargetsOwnLabel(const Stmt* stmt, StmtResult result,
                                       bool labeled, SimContext& ctx) {
  if (result != StmtResult::kDisable || !labeled) return false;
  if (ctx.GetDisableTarget() != stmt->label) return false;
  ctx.ClearDisableTarget();
  return true;
}

// Evaluates a for-loop's optional continuation condition. A loop with no
// condition runs unconditionally; otherwise it continues only while the
// condition is truthy.
static bool ForConditionHolds(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  if (!stmt->for_cond) return true;
  auto cond = EvalExpr(stmt->for_cond, ctx, arena);
  return cond.IsTruthy();
}

ExecTask ExecFor(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  EnterLoopLabelScope(stmt, ctx, labeled);
  bool scoped = HasTypedForInit(stmt);
  if (scoped) ctx.PushScope();
  CreateForInitVars(stmt, ctx);
  for (auto* init : stmt->for_inits) co_await ExecStmt(init, ctx, arena);
  while (ProcessGoesOn(ctx)) {
    if (!ForConditionHolds(stmt, ctx, arena)) break;
    auto result = co_await ExecStmt(stmt->for_body, ctx, arena);
    auto action = ClassifyLoopBodyResult(result);
    if (action == LoopAction::kBreakLoop) break;
    if (action == LoopAction::kPropagate) {
      if (LoopDisableTargetsOwnLabel(stmt, result, labeled, ctx)) break;
      TeardownForScopes(stmt, ctx, scoped, labeled);
      co_return result;
    }
    for (auto* step : stmt->for_steps) co_await ExecStmt(step, ctx, arena);
  }
  TeardownForScopes(stmt, ctx, scoped, labeled);
  co_return StmtResult::kDone;
}

ExecTask ExecWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  while (ProcessGoesOn(ctx)) {
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (!cond.IsTruthy()) break;
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

ExecTask ExecForever(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  while (ProcessGoesOn(ctx)) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

// §12.7.2: derive how many times a repeat-loop body runs from the count
// expression, already evaluated once before the loop begins. An unknown or
// high-impedance value, or a negative value of a signed expression, yields no
// iterations.
static uint64_t RepeatIterationCount(const Logic4Vec& count_val) {
  if (!count_val.IsKnown()) return 0;
  if (count_val.is_signed && count_val.width > 0) {
    uint32_t msb_word = (count_val.width - 1) / 64;
    uint64_t msb_mask = uint64_t{1} << ((count_val.width - 1) % 64);
    if (count_val.words[msb_word].aval & msb_mask) return 0;
  }
  return count_val.ToUint64();
}

std::optional<uint64_t> LoopIterationLimit(const Stmt* stmt, SimContext& ctx,
                                           Arena& arena) {
  if (stmt->kind != StmtKind::kRepeat) return std::nullopt;
  return RepeatIterationCount(EvalExpr(stmt->condition, ctx, arena));
}

ExecTask ExecRepeat(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  uint64_t count = RepeatIterationCount(EvalExpr(stmt->condition, ctx, arena));
  for (uint64_t i = 0; i < count && ProcessGoesOn(ctx); ++i) {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
  }
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

ExecTask ExecDoWhile(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  if (labeled) ctx.PushStaticScope(stmt->label);
  do {
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (result == StmtResult::kBreak) break;
    if (result != StmtResult::kDone && result != StmtResult::kContinue) {
      if (labeled) ctx.PopStaticScope(stmt->label);
      co_return result;
    }
    auto cond = EvalExpr(stmt->condition, ctx, arena);
    if (!cond.IsTruthy()) break;
  } while (ProcessGoesOn(ctx));
  if (labeled) ctx.PopStaticScope(stmt->label);
  co_return StmtResult::kDone;
}

static uint32_t GetArraySize(const Stmt* stmt, SimContext& ctx) {
  std::string name = GetForeachArrayName(stmt->expr);
  if (name.empty()) return 0;
  auto* info = ctx.FindArrayInfo(name);
  if (info) return info->size;
  auto* var = ctx.FindVariable(name);
  if (!var) return 0;
  // §12.7.3: a string is treated as a dynamic array of bytes, so the loop runs
  // once per character. The value packs eight bits per character, so the
  // character count is the bit width divided by eight.
  if (ctx.IsStringVariable(name)) return var->value.width / 8;
  return var->value.width;
}

// §12.7.3: foreach is illegal on a wildcard-indexed associative array. Reports
// the diagnostic and returns true when `aa` is such a wildcard array,
// signalling that ExecForeach must abandon the loop. `loc` is where the loop
// was written, which the report names along with the name the loop spells.
static bool ForeachOnWildcardAssoc(const AssocArrayObject* aa,
                                   const std::string& arr_name, SimContext& ctx,
                                   SourceLoc loc) {
  if (aa == nullptr || !aa->is_wildcard) return false;
  ctx.GetDiag().Error(
      loc,
      "foreach not allowed on wildcard associative array '" + arr_name + "'",
      Subclause("7.8.1"));
  return true;
}

// Result of the non-coroutine prologue of ExecForeach: the array name, its
// iteration count, and whether the loop should run at all. `bail` is set when
// the loop must terminate immediately (wildcard associative array, or a
// zero-length iteration domain) without entering the body. For an associative
// array `keys` holds the index values the loop variable steps through, one per
// iteration, and `string_keys` whether they are strings. `lo` is the index
// the first iteration takes where the array carries no array-info entry: the
// lowest declared index of a fixed-size array property, 0 otherwise. `dims`
// holds the dimensions the loop walks one named variable per dimension, as
// nested loops (DeclaredForeachDims, ClassArrayForeachDims); empty where the
// loop steps through `keys` or from `lo` instead.
struct ForeachSetup {
  std::string arr_name;
  uint32_t size = 0;
  int64_t lo = 0;
  bool bail = false;
  std::vector<Logic4Vec> keys;
  bool string_keys = false;
  const AssocArrayObject* aa = nullptr;
  std::vector<ForeachDim> dims;
};

// §12.7.3: resolves the array being iterated and how many iterations it
// implies, reporting the wildcard-associative-array error as a side effect.
// Pure prologue computation kept out of the ExecForeach coroutine so the
// coroutine body stays small.
//
// An associative array is iterated over the indices it holds (§12.7.3: each
// loop variable corresponds to one dimension, and the array's dimension is its
// set of indices), in the array's own order, and the array is a declared one
// or, §8.5 restricting no property's type, a property of an object -- named
// through a handle, `o.count`, or bare in a method (§8.11) -- which
// FindAssocArrayOfBase resolves. Before that an associative array was
// iterated as the variable under its name, elem_width times from 0.
static ForeachSetup ComputeForeachSetup(const Stmt* stmt, SimContext& ctx,
                                        Arena& arena) {
  ForeachSetup setup;
  setup.arr_name = GetForeachArrayName(stmt->expr);
  const AssocArrayObject* aa = FindAssocArrayOfBase(stmt->expr, ctx, arena);
  if (ForeachOnWildcardAssoc(aa, setup.arr_name, ctx, stmt->range.start)) {
    setup.bail = true;
    return setup;
  }
  if (aa != nullptr) {
    setup.keys = AssocIndexValues(aa, arena);
    setup.string_keys = aa->is_string_key;
    setup.aa = aa;
    setup.size = static_cast<uint32_t>(setup.keys.size());
  } else if (const QueueObject* q = FindQueueOfBase(stmt->expr, ctx, arena)) {
    // §12.7.3 with §7.10: a queue's one dimension holds as many elements as
    // the queue does, 0 to $, whether the queue is a declared one or a
    // property of an object (§8.5) named bare in a method or through a
    // handle. A declared dynamic array is stored the same way and answers the
    // same. Before this the loop ran over the variable under a declared
    // queue's name, once per bit of one element, and over a property not at
    // all.
    setup.size = static_cast<uint32_t>(q->elements.size());
  } else if (const StructFieldInfo* member =
                 ResolveStructArrayMember(stmt->expr, ctx)) {
    // §12.7.3 with §7.2 and §7.4.2: an unpacked array member of a structure,
    // `m.v`, holds its elements in the structure's bits, from the lower of
    // its bounds. Looked up as an array of its name, it was none.
    setup.size = member->elem_count;
    setup.lo = std::min(member->elem_left, member->elem_right);
    setup.dims = StructMemberForeachDims(stmt, *member);
  } else if (ClassArrayRef ref;
             ResolveClassArray(stmt->expr, ctx, arena, ref)) {
    // §12.7.3 with §7.4.2 and §7.5: a fixed-size or dynamic array property
    // (§8.5) holds its elements on the object, the declared dimension's count
    // from its lowest index for a fixed one and the object's count from 0 for
    // a dynamic one. Before this the property was looked up as a variable of
    // its name, which it is not, and the loop ran no times.
    setup.size = ref.size;
    setup.lo = ref.lo;
    setup.dims = ClassArrayForeachDims(stmt, ref);
  } else {
    setup.size = GetArraySize(stmt, ctx);
    setup.dims = DeclaredForeachDims(stmt, ctx);
  }
  if (setup.size == 0) setup.bail = true;
  return setup;
}

// Returns the foreach loop-variable name, or an empty view when the iteration
// dimension is unnamed (a `,` placeholder in the index list).
static std::string_view ForeachIterName(const Stmt* stmt) {
  if (!stmt->foreach_vars.empty() && !stmt->foreach_vars[0].empty()) {
    return stmt->foreach_vars[0];
  }
  return {};
}

// Assigns the loop variable for iteration `i`: the i-th index the associative
// array holds, where the loop is over one, else the zero-based counter counted
// up from `lo`. A no-op when the dimension is unnamed (`iter_var` is null).
// §12.7.3 types the loop variable after the index type, so a string index
// makes the variable a string.
static void SetForeachIterVar(Variable* iter_var, const ForeachSetup& setup,
                              uint32_t i, Arena& arena) {
  if (!iter_var) return;
  if (!setup.keys.empty()) {
    iter_var->value = setup.keys[i];
    iter_var->is_string = setup.string_keys;
    return;
  }
  iter_var->value =
      MakeLogic4VecVal(arena, 32, static_cast<uint64_t>(setup.lo + i));
}

// Creates the loop variable `iter_name` names in the scope ExecForeach
// pushed, or none where the dimension is unnamed. §12.7.3: the loop variable
// has the index type of an associative array (TypeForeachIterVar).
static Variable* CreateForeachIterVar(std::string_view iter_name,
                                      const ForeachSetup& setup,
                                      SimContext& ctx) {
  if (iter_name.empty()) return nullptr;
  Variable* iter_var = ctx.CreateLocalVariable(iter_name, 32);
  TypeForeachIterVar(iter_name, setup.aa, ctx);
  // §7.8.4: a signed integral index type, `byte` or `bit signed [4:1]`,
  // makes the loop variable signed, so the key -3 reads -3.
  iter_var->is_signed = setup.aa != nullptr && !setup.aa->is_string_key &&
                        setup.aa->is_index_signed;
  return iter_var;
}

// Pops the dynamic scope ExecForeach pushed for the loop body and the static
// scope a label introduced, in the order they were pushed. Called on every
// ExecForeach exit path that runs after the body scope is established.
static void TeardownForeachScopes(const Stmt* stmt, SimContext& ctx,
                                  bool labeled) {
  ctx.PopScope();
  ExitLoopLabelScope(stmt, ctx, labeled);
}

// §12.7.3: drives a foreach over `dims`, one named loop variable per
// dimension, as nested loops. A flat odometer over the product of the
// dimension sizes yields the same nesting the LRM prescribes: the last
// (innermost) dimension changes most rapidly, the first (outermost) most
// slowly, and each walks from its declared left bound (SetForeachDimVars). Each
// step sets the variables before running the body once, so `continue` advances
// to the next combination and `break` (or a disable of the loop's own label)
// leaves the whole loop.
static ExecTask ExecForeachDims(const Stmt* stmt, SimContext& ctx, Arena& arena,
                                const std::vector<ForeachDim>& dims,
                                bool labeled) {
  ctx.PushScope();
  std::vector<Variable*> vars = CreateForeachDimVars(dims, ctx);
  uint64_t total = ForeachCombinationCount(dims);
  for (uint64_t n = 0; n < total && ProcessGoesOn(ctx); ++n) {
    SetForeachDimVars(dims, vars, n, arena);
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    auto action = ClassifyLoopBodyResult(result);
    if (action == LoopAction::kBreakLoop) break;
    if (action == LoopAction::kPropagate) {
      if (LoopDisableTargetsOwnLabel(stmt, result, labeled, ctx)) break;
      TeardownForeachScopes(stmt, ctx, labeled);
      co_return result;
    }
  }
  TeardownForeachScopes(stmt, ctx, labeled);
  co_return StmtResult::kDone;
}

// §12.7.3 with §7.4, §7.8 and §7.10: the second loop variable of a foreach
// over a queue, dynamic array or associative array whose elements are queues
// or fixed-size arrays, `foreach (r[k, j])` over `int r[$][2]`, steps through
// the indices of the element the first names, which is its own queue. `var`
// is that variable, null where the loop names none or the array's elements
// are no queues; `queue` or `assoc` the array.
struct ForeachElementDim {
  Variable* var = nullptr;
  const QueueObject* queue = nullptr;
  const AssocArrayObject* assoc = nullptr;
};

static ForeachElementDim ForeachElementDimOf(const Stmt* stmt,
                                             const ForeachSetup& setup,
                                             SimContext& ctx, Arena& arena) {
  ForeachElementDim dim;
  if (stmt->foreach_vars.size() < 2 || stmt->foreach_vars[1].empty())
    return dim;
  if (setup.aa != nullptr) {
    if (!setup.aa->elements_are_queues) return dim;
    dim.assoc = setup.aa;
  } else {
    const QueueObject* q = FindQueueOfBase(stmt->expr, ctx, arena);
    if (q == nullptr || !q->elements_are_queues) return dim;
    dim.queue = q;
  }
  dim.var = ctx.CreateLocalVariable(stmt->foreach_vars[1], 32);
  return dim;
}

// The queue of the element iteration `i` of the outer loop names.
static const QueueObject* ForeachElementQueue(const ForeachElementDim& dim,
                                              const ForeachSetup& setup,
                                              uint32_t i, Arena& arena) {
  if (dim.assoc != nullptr)
    return AssocElementQueueAt(*dim.assoc, setup.keys[i], arena);
  return ElementQueueOrDefault(*dim.queue, i, arena);
}

// The index position `p` of the element queue `q` stands for: a fixed-size
// element's declared index from its left bound, a queue's position itself.
static int64_t ElementIndexAt(const QueueObject& q, uint32_t p) {
  auto size = static_cast<int64_t>(q.elements.size());
  return q.index_descending ? q.index_lo + size - 1 - p : q.index_lo + p;
}

// The body of the foreach `stmt` run once per index of `element`, the
// second loop variable `var` taking each: answers what the outer loop is to
// do next, as one run of the body would -- kBreak where the body broke out,
// kDone where every index ran or the body continued, and any other result as
// the body gave it.
static ExecTask ExecForeachElement(const Stmt* stmt, SimContext& ctx,
                                   Arena& arena, Variable* var,
                                   const QueueObject* element) {
  for (uint32_t p = 0; p < element->elements.size() && !ctx.StopRequested();
       ++p) {
    var->value = MakeLogic4VecVal(
        arena, 32, static_cast<uint64_t>(ElementIndexAt(*element, p)));
    auto result = co_await ExecStmt(stmt->body, ctx, arena);
    if (ClassifyLoopBodyResult(result) != LoopAction::kKeepLooping)
      co_return result;
  }
  co_return StmtResult::kDone;
}

ExecTask ExecForeach(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  bool labeled = !stmt->label.empty();
  EnterLoopLabelScope(stmt, ctx, labeled);
  ForeachSetup setup = ComputeForeachSetup(stmt, ctx, arena);
  if (setup.bail) {
    ExitLoopLabelScope(stmt, ctx, labeled);
    co_return StmtResult::kDone;
  }
  // §12.7.3: each loop variable walks the declared range of the dimension it
  // names, from its left bound, as nested loops over every named dimension.
  if (!setup.dims.empty()) {
    co_return co_await ExecForeachDims(stmt, ctx, arena, setup.dims, labeled);
  }
  uint32_t size = setup.size;
  std::string_view iter_name = ForeachIterName(stmt);

  ctx.PushScope();
  Variable* iter_var = CreateForeachIterVar(iter_name, setup, ctx);
  ForeachElementDim inner = ForeachElementDimOf(stmt, setup, ctx, arena);

  for (uint32_t i = 0; i < size && !ctx.StopRequested(); ++i) {
    SetForeachIterVar(iter_var, setup, i, arena);
    auto result = inner.var == nullptr
                      ? co_await ExecStmt(stmt->body, ctx, arena)
                      : co_await ExecForeachElement(
                            stmt, ctx, arena, inner.var,
                            ForeachElementQueue(inner, setup, i, arena));
    auto action = ClassifyLoopBodyResult(result);
    if (action == LoopAction::kBreakLoop) break;
    if (action == LoopAction::kPropagate) {
      if (LoopDisableTargetsOwnLabel(stmt, result, labeled, ctx)) break;
      TeardownForeachScopes(stmt, ctx, labeled);
      co_return result;
    }
  }

  TeardownForeachScopes(stmt, ctx, labeled);
  co_return StmtResult::kDone;
}

}  // namespace delta
