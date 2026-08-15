#include <string>
#include <string_view>
#include <unordered_set>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "elaborator/type_eval.h"
#include "parser/ast.h"
#include "simulator/eval_function_internal.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {

static thread_local std::unordered_set<std::string_view> expanding_lets;

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
  if (formal.default_value) {
    return EvalExpr(formal.default_value, b.ctx, b.arena);
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

static Logic4Vec ResizeLetActualToFormal(Logic4Vec val,
                                         const FunctionArg& formal,
                                         Arena& arena) {
  const auto& dt = formal.data_type;
  if (dt.kind != DataTypeKind::kImplicit && dt.packed_dim_left &&
      dt.packed_dim_right) {
    uint32_t formal_width = EvalTypeWidth(dt);
    if (formal_width > 0 && formal_width != val.width) {
      val = ResizeToWidth(val, formal_width, arena);
    }
  }
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
  for (size_t i = 0; i < formals.size(); ++i) {
    Logic4Vec val = EvalLetActualForFormal(formals[i], i, binding);
    val = ResizeLetActualToFormal(val, formals[i], arena);
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
  }
}

Logic4Vec EvalLetExpansion(ModuleItem* decl, const Expr* call, SimContext& ctx,
                           Arena& arena) {
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
  expanding_lets.insert(decl->name);

  auto vals = EvalLetActuals(decl, call, ctx, arena);

  auto saved_scopes = ctx.SwapScopeStack({});
  ctx.PushScope();
  BindLetArgs(decl, vals, ctx);
  auto result = EvalExpr(decl->init_expr, ctx, arena);
  ctx.PopScope();
  ctx.SwapScopeStack(std::move(saved_scopes));
  expanding_lets.erase(decl->name);
  return result;
}

}  // namespace delta
