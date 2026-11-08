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
#include "elaborator/let_construct.h"
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
static thread_local std::vector<const Expr*> let_instances;
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
  if (formal.default_value) {
    auto caller_scopes = b.ctx.SwapScopeStack({});
    Logic4Vec value = EvalExpr(formal.default_value, b.ctx, b.arena);
    b.ctx.SwapScopeStack(std::move(caller_scopes));
    return value;
  }
  return MakeLogic4Vec(b.arena, 32);
}

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
                                         const DataType& formal_type,
                                         SimContext& ctx, Arena& arena) {
  const DataType* resolved = ctx.PackedTypeBehind(formal_type);
  const auto& dt = resolved != nullptr ? *resolved : formal_type;
  uint32_t formal_width = EvalTypeWidth(dt);
  if (!val.is_real && formal_width > 0 && formal_width != val.width) {
    val = ResizeToWidth(val, formal_width, arena);
  }
  if (!val.is_real) val.is_signed = DeclaredTypeIsSigned(dt, ctx);
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
  std::vector<const DataType*> types = LetFormalTypes(formals);
  for (size_t i = 0; i < formals.size(); ++i) {
    Logic4Vec val = EvalLetActualForFormal(formals[i], i, binding);
    if (types[i] != nullptr) {
      val = ResizeLetActualToFormal(val, *types[i], ctx, arena);
    }
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
    ctx.GetDiag().Error(call->range.start,
                        "recursive instantiation of let '" +
                            std::string(decl->name) + "' is not permitted",
                        Subclause("11.12"));
    return MakeAllX(arena, 32);
  }
  auto vals = EvalLetActuals(decl, call, ctx, arena);
  expanding_lets.insert(decl->name);

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
