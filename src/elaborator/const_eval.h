#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>

namespace delta {

struct Expr;
struct ModuleItem;

using ScopeMap = std::unordered_map<std::string_view, int64_t>;

// §13.4.3: a constant function call is evaluated at elaboration time. The
// constant-expression folder cannot see the enclosing scope's function
// declarations on its own, so the elaborator installs the visible function map
// for the duration of a scope guard. While the guard is live, ConstEvalInt /
// ConstEvalReal fold a call to any registered user function (with all-constant
// arguments) by interpreting its body. The pointer is borrowed; the guard
// restores whatever registry was previously active on destruction.
class ConstFuncRegistryGuard {
 public:
  explicit ConstFuncRegistryGuard(
      const std::unordered_map<std::string_view, const ModuleItem*>* funcs);
  ~ConstFuncRegistryGuard();
  ConstFuncRegistryGuard(const ConstFuncRegistryGuard&) = delete;
  ConstFuncRegistryGuard& operator=(const ConstFuncRegistryGuard&) = delete;

 private:
  const std::unordered_map<std::string_view, const ModuleItem*>* prev_;
};

std::optional<int64_t> ConstEvalInt(const Expr* expr);

std::optional<int64_t> ConstEvalInt(const Expr* expr, const ScopeMap& scope);

std::optional<double> ConstEvalReal(const Expr* expr);
std::optional<double> ConstEvalReal(const Expr* expr, const ScopeMap& scope);

bool IsConstantExpr(const Expr* expr, const ScopeMap& scope = {});

// Shared with §13.4.3: the whitelist of system functions admissible inside a
// constant_expression (§11.2.1) is the same set that a constant function may
// invoke per §13.4.3 constraint (g).
bool IsConstantSysFunc(std::string_view name);

std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope = {});

}  // namespace delta
