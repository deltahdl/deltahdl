#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <optional>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

namespace delta {

namespace {

std::size_t g_visible_lets = std::numeric_limits<std::size_t>::max();

class LetBodyScope {
 public:
  explicit LetBodyScope(std::size_t index) : saved_(g_visible_lets) {
    g_visible_lets = index;
  }
  ~LetBodyScope() { g_visible_lets = saved_; }
  LetBodyScope(const LetBodyScope&) = delete;
  LetBodyScope& operator=(const LetBodyScope&) = delete;

 private:
  std::size_t saved_;
};

std::optional<std::size_t> RegisteredLetIndex(const Expr* call) {
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return std::nullopt;
  const std::size_t kVisible = std::min(g_visible_lets, mod->let_decls.size());
  for (std::size_t k = 0; k < kVisible; ++k) {
    if (mod->let_decls[k]->name == call->callee) return k;
  }
  return std::nullopt;
}

const Expr* LetActual(const Expr* call, const ModuleItem* let, std::size_t k) {
  const std::size_t kPositional = call->args.size() - call->arg_names.size();
  const Expr* actual = nullptr;
  if (k < kPositional) {
    actual = call->args[k];
  } else {
    for (std::size_t i = 0; i < call->arg_names.size(); ++i) {
      if (call->arg_names[i] == let->func_args[k].name) {
        actual = call->args[kPositional + i];
      }
    }
  }
  return actual != nullptr ? actual : let->func_args[k].default_value;
}

}  // namespace

std::optional<bool> LetCallIsConstant(const Expr* call, const ScopeMap& scope) {
  std::optional<std::size_t> index = RegisteredLetIndex(call);
  if (!index) return std::nullopt;
  for (const Expr* arg : call->args) {
    if (arg != nullptr && !IsConstantExpr(arg, scope)) return false;
  }
  const ModuleItem* let = RegisteredModule()->let_decls[*index];
  ScopeMap body_scope = scope;
  for (const auto& formal : let->func_args) body_scope.emplace(formal.name, 0);
  LetBodyScope body(*index);
  return IsConstantExpr(let->init_expr, body_scope);
}

std::optional<ConstVal> ConstEvalLetCall(const Expr* call,
                                         const ScopeMap& scope,
                                         FoldContext ctx) {
  std::optional<std::size_t> index = RegisteredLetIndex(call);
  if (!index) return std::nullopt;
  const ModuleItem* let = RegisteredModule()->let_decls[*index];
  ScopeMap body_scope = scope;
  for (std::size_t k = 0; k < let->func_args.size(); ++k) {
    std::optional<int64_t> value = ConstEvalInt(LetActual(call, let, k), scope);
    if (!value) return std::nullopt;
    body_scope[let->func_args[k].name] = *value;
  }
  LetBodyScope body(*index);
  return ConstEvalFull(let->init_expr, body_scope, ctx);
}

}  // namespace delta
