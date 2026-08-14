#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>

#include "common/packed_range.h"

namespace delta {

struct Expr;
struct ModuleItem;
struct ClassDecl;
struct RtlirModule;

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

// §8.25.1: an explicit specialization used as a scope-resolution prefix in a
// constant expression (e.g. `localparam W = C#(3)::p`) must fold to the
// parameter value in that specialization, not the class default. The folder
// keys parameterized-class access on the "Class.param" name alone and cannot
// see the parameter port order on its own, so the elaborator installs the
// visible parameterized-class declarations for the duration of a scope guard.
// While the guard is live, ConstEvalInt resolves the specialization override
// (ordered or named) for the accessed value parameter. The pointer is borrowed;
// the guard restores the previously active registry on destruction.
class ParamClassRegistryGuard {
 public:
  explicit ParamClassRegistryGuard(
      const std::unordered_map<std::string_view, const ClassDecl*>* classes);
  ~ParamClassRegistryGuard();
  ParamClassRegistryGuard(const ParamClassRegistryGuard&) = delete;
  ParamClassRegistryGuard& operator=(const ParamClassRegistryGuard&) = delete;

 private:
  const std::unordered_map<std::string_view, const ClassDecl*>* prev_;
};

// §11.5.1 puts a parameter among the operands a bit-select addresses -- "a
// vector, packed array, packed structure, parameter, or concatenation" -- and
// §11.5 does the same for part-selects, so a parameter declared with a packed
// range is addressed over that range. A folded constant carries no declaration
// with it and a ScopeMap holds a value and nothing else, so the folder cannot
// turn an index into a bit position on its own. The elaborator installs the
// module whose parameter declarations are in scope for the duration of a guard.
// While the guard is live, a select written on one of those parameters is
// resolved against the range it was declared with rather than over [width-1:0].
// The pointer is borrowed; the guard restores the previously active module on
// destruction.
class ParamRangeRegistryGuard {
 public:
  explicit ParamRangeRegistryGuard(const RtlirModule* mod);
  ~ParamRangeRegistryGuard();
  ParamRangeRegistryGuard(const ParamRangeRegistryGuard&) = delete;
  ParamRangeRegistryGuard& operator=(const ParamRangeRegistryGuard&) = delete;

 private:
  const RtlirModule* prev_;
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
