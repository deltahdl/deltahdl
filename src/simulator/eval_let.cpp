#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>
#include <unordered_set>
#include <utility>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/types.h"
#include "elaborator/type_eval.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/scope.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"
#include "simulator/variable.h"

namespace delta {

static thread_local std::unordered_set<std::string_view> expanding_lets;
// The let instances whose bodies are being evaluated, innermost last.
static thread_local std::vector<const Expr*> let_instances;
// The lets a block or a subroutine body declares, whose declaring scope is the
// frame their instances stand in (RegisterBlockLet).
static thread_local std::unordered_set<const ModuleItem*> block_lets;

static thread_local uint32_t call_context_width = 0;

uint32_t CallContextWidth() { return call_context_width; }

uint32_t SetCallContextWidth(uint32_t width) {
  return std::exchange(call_context_width, width);
}

uint64_t CurrentLetInstance() {
  return let_instances.empty()
             ? 0
             : reinterpret_cast<uint64_t>(let_instances.back());
}

static int FindLetNamedActualIndex(const FunctionArg& formal, const Expr* call,
                                   size_t positional_count) {
  for (size_t j = 0; j < call->arg_names.size(); ++j) {
    if (call->arg_names[j] == formal.name) {
      return static_cast<int>(positional_count + j);
    }
  }
  return -1;
}

static Logic4Vec EvalLetActualForFormal(const FunctionArg& formal, size_t i,
                                        const ActualBindingCtx& b) {
  if (i < b.positional_count) {
    return EvalExpr(b.call->args[i], b.ctx, b.arena);
  }
  int found = FindLetNamedActualIndex(formal, b.call, b.positional_count);
  if (found >= 0 && b.call->args[static_cast<size_t>(found)]) {
    return EvalExpr(b.call->args[static_cast<size_t>(found)], b.ctx, b.arena);
  }
  // §11.12: a default names what the scope declaring the let gives its
  // names, not what the call's scope does: a module's let reads the module's.
  if (formal.default_value) {
    auto caller_scopes = b.ctx.SwapScopeStack({});
    Logic4Vec value = EvalExpr(formal.default_value, b.ctx, b.arena);
    b.ctx.SwapScopeStack(std::move(caller_scopes));
    return value;
  }
  return MakeLogic4Vec(b.arena, 32);
}

// §11.12: the actual for a non-event typed formal is cast to the formal's type
// before substitution. A 2-state formal type (bit, byte, shortint, int,
// longint) cannot hold x/z, so the cast forces every unknown or high-impedance
// bit of the actual to 0 (example e spells this out: bits with an unknown logic
// value or a high-impedance value become 0).
static bool IsLetFormalTwoState(DataTypeKind kind) {
  switch (kind) {
    case DataTypeKind::kBit:
    case DataTypeKind::kByte:
    case DataTypeKind::kShortint:
    case DataTypeKind::kInt:
    case DataTypeKind::kLongint:
      return true;
    default:
      return false;
  }
}

// §11.12 casts an actual to its formal's type, which a typedef name stands for
// as written out: `bits x` under `typedef bit [15:0] bits` is a sixteen-bit
// two-state formal (§6.18). The name alone gave neither a width nor a kind.
static Logic4Vec ResizeLetActualToFormal(Logic4Vec val,
                                         const DataType& formal_type,
                                         SimContext& ctx, Arena& arena) {
  const DataType* resolved = ctx.PackedTypeBehind(formal_type);
  const auto& dt = resolved != nullptr ? *resolved : formal_type;
  // An untyped formal takes the actual as it is, its sign among it (§11.12's
  // substitution); a typed integral one its own width and sign, an integer
  // atom type's included, `int x` taking 8'hFF as 32 bits.
  if (dt.kind == DataTypeKind::kImplicit && dt.packed_dim_left == nullptr)
    return val;
  uint32_t formal_width = EvalTypeWidth(dt);
  if (!val.is_real && formal_width > 0 && formal_width != val.width) {
    val = ResizeToWidth(val, formal_width, arena);
  }
  if (!val.is_real) val.is_signed = DeclaredTypeIsSigned(dt, ctx);
  // §11.12 rule 2 / example e: casting to a 2-state typed formal drives every
  // unknown (x) or high-impedance (z) actual bit to 0. Work on a fresh copy so
  // the coercion never mutates a value shared with the actual's own storage.
  if (IsLetFormalTwoState(dt.kind)) {
    Logic4Vec coerced = ExtractBitField(arena, val, 0, val.width);
    coerced.is_signed = val.is_signed;
    for (uint32_t i = 0; i < coerced.nwords; ++i) {
      coerced.words[i].aval &= ~coerced.words[i].bval;
      coerced.words[i].bval = 0;
    }
    val = coerced;
  }
  return val;
}

static std::vector<Logic4Vec> EvalLetActuals(ModuleItem* decl, const Expr* call,
                                             SimContext& ctx, Arena& arena) {
  auto& formals = decl->func_args;
  size_t positional_count = call->args.size() - call->arg_names.size();
  ActualBindingCtx binding{call, positional_count, ctx, arena};
  std::vector<Logic4Vec> vals;
  vals.reserve(formals.size());
  // §11.12's example e expands `let ones_match(bits x, y)` with `bits'(b)` for
  // `y`: a formal written with no type of its own takes the type written
  // before it in the list.
  const DataType* written = nullptr;
  for (size_t i = 0; i < formals.size(); ++i) {
    const DataType& own = formals[i].data_type;
    if (own.kind != DataTypeKind::kImplicit || own.packed_dim_left != nullptr)
      written = &own;
    Logic4Vec val = EvalLetActualForFormal(formals[i], i, binding);
    val = ResizeLetActualToFormal(val, written != nullptr ? *written : own, ctx,
                                  arena);
    vals.push_back(val);
  }
  return vals;
}

static void BindLetArgs(ModuleItem* decl, const std::vector<Logic4Vec>& vals,
                        SimContext& ctx) {
  auto& formals = decl->func_args;
  for (size_t i = 0; i < formals.size(); ++i) {
    auto* var = ctx.CreateLocalVariable(formals[i].name, vals[i].width);
    var->value = vals[i];
    var->is_signed = vals[i].is_signed;
    var->is_real = vals[i].is_real;
    var->is_string = vals[i].is_string;
  }
}

Logic4Vec EvalLetExpansion(ModuleItem* decl, const Expr* call, SimContext& ctx,
                           Arena& arena, uint32_t context_width) {
  if (expanding_lets.count(decl->name)) {
    // §11.12: recursive let instantiations are not permitted. Report the
    // illegal self-reference rather than silently expanding it away, then
    // break the cycle by yielding x so the run can continue. The report stands
    // at the reference that found the let already expanding, and call is never
    // null because EvalLetActuals below reads call->args without checking.
    ctx.GetDiag().Error(call->range.start,
                        "recursive instantiation of let '" +
                            std::string(decl->name) + "' is not permitted",
                        Subclause("11.12"));
    return MakeAllX(arena, 32);
  }
  // The actuals are expressions of the call, not of the body, so a call to
  // the let among them, `add(add(1, 2), 3)`, is no recursion: they are
  // evaluated before the let is marked as expanding.
  auto vals = EvalLetActuals(decl, call, ctx, arena);
  expanding_lets.insert(decl->name);

  // §11.12 resolves the body's other names in the scope declaring the let: a
  // block's or a subroutine's let sees that frame, which its instances stand
  // within, and a module's sees the module's names alone.
  const bool kBlockLet = block_lets.contains(decl);
  std::vector<Scope> saved_scopes;
  if (!kBlockLet) saved_scopes = ctx.SwapScopeStack({});
  ctx.PushScope();
  BindLetArgs(decl, vals, ctx);
  let_instances.push_back(call);
  auto result = EvalExpr(decl->init_expr, ctx, arena, context_width);
  let_instances.pop_back();
  ctx.PopScope();
  if (!kBlockLet) ctx.SwapScopeStack(std::move(saved_scopes));
  expanding_lets.erase(decl->name);
  return result;
}

// The key an instance's let is registered under: no bare name and no
// hierarchical path spells it, so neither a compilation unit's let nor an
// instance's variable stands under it.
static std::string InstanceLetKey(std::string_view prefix,
                                  std::string_view name) {
  return "let " + std::string(prefix) + std::string(name);
}

void RegisterInstanceLet(SimContext& ctx, std::string_view prefix,
                         ModuleItem* let) {
  ctx.RegisterLetDecl(
      *ctx.GetArena().Create<std::string>(InstanceLetKey(prefix, let->name)),
      let);
}

ModuleItem* FindVisibleLet(SimContext& ctx, std::string_view name) {
  if (ModuleItem* local = ctx.FindLocalLet(name)) return local;
  if (ModuleItem* own =
          ctx.FindLetDecl(InstanceLetKey(ctx.ActiveInstancePrefix(), name)))
    return own;
  return ctx.FindLetDecl(name);
}

bool BlockDeclaresLet(const Stmt* block) {
  return std::ranges::any_of(block->stmts, [](const Stmt* s) {
    return s->kind == StmtKind::kBlockItemDecl && s->decl_item != nullptr &&
           s->decl_item->kind == ModuleItemKind::kLetDecl;
  });
}

void RegisterBlockLet(const Stmt* stmt, SimContext& ctx) {
  ModuleItem* let = stmt->decl_item;
  if (let == nullptr || let->kind != ModuleItemKind::kLetDecl) return;
  block_lets.insert(let);
  if (ctx.HasLocalScope()) {
    ctx.DeclareLocalLet(let->name, let);
  } else {
    ctx.RegisterLetDecl(let->name, let);
  }
}

}  // namespace delta
