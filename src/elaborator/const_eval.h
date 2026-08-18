#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>
#include <vector>

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

// The function table a live ConstFuncRegistryGuard installed, or null when none
// is live. §23.9 has the search for a directly referenced identifier "continue
// upward until an item by that name is found or until a module, interface,
// program, or checker boundary is encountered", so a scope nested inside
// another has to install what it found plus its own declarations rather than
// its own alone. This is what such a site reads to find what it found.
const std::unordered_map<std::string_view, const ModuleItem*>*
RegisteredConstFuncs();

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
  std::vector<std::string_view> prev_scopes_;
};

// §23.9 lists "Generate blocks" among the elements that "define a new scope",
// so which of the registered module's parameters an expression may name depends
// on where in that module it stands. ParamRangeRegistryGuard installs the
// module and nothing more, which is not enough: matching by name alone lets a
// parameter one block declares answer an expression written anywhere in the
// module, and refusing every block-local parameter denies a block its own,
// which §23.9 grants by ruling that an identifier "declared locally" names the
// local item.
//
// This guard installs the generate block prefixes in force where the expression
// stands, outermost first, for the readers to hand to ParamVisibleFromScopes.
// A ParamRangeRegistryGuard clears them when it installs a module, so an
// expression among a module's own items needs no guard of this kind. The
// prefixes are borrowed and must outlive the guard.
class RegisteredGenScopeGuard {
 public:
  explicit RegisteredGenScopeGuard(const std::vector<std::string_view>& scopes);
  ~RegisteredGenScopeGuard();
  RegisteredGenScopeGuard(const RegisteredGenScopeGuard&) = delete;
  RegisteredGenScopeGuard& operator=(const RegisteredGenScopeGuard&) = delete;

 private:
  std::vector<std::string_view> prev_;
};

std::optional<int64_t> ConstEvalInt(const Expr* expr);

std::optional<int64_t> ConstEvalInt(const Expr* expr, const ScopeMap& scope);

std::optional<double> ConstEvalReal(const Expr* expr);
std::optional<double> ConstEvalReal(const Expr* expr, const ScopeMap& scope);

// §6.16: the characters of a constant string expression -- a string literal
// with its quotes removed and each escape replaced by the one character it
// stands for, a parameter of the module a live ParamRangeRegistryGuard
// registered, or a concatenation or replication of those, which Table 6-9
// defines over string operands. §6.16 rules that "strings can be of arbitrary
// length and no truncation occurs", which is why the characters are answered
// separately from the §11.10 packed number ConstEvalStringLiteral computes:
// that keeps only the low 64 bits, so a value of more than eight characters is
// no longer recoverable from it.
//
// A string literal of no characters answers an empty string rather than
// std::nullopt, which is what lets §6.16.1 -- "if str is "", then str.len()
// returns 0" -- be answered. Empty for every other expression, and for a name
// the registered module declares no string parameter under.
std::optional<std::string> ConstEvalString(const Expr* expr);

bool IsConstantExpr(const Expr* expr, const ScopeMap& scope);

// Shared with §13.4.3: the whitelist of system functions admissible inside a
// constant_expression (§11.2.1) is the same set that a constant function may
// invoke per §13.4.3 constraint (g).
bool IsConstantSysFunc(std::string_view name);

std::string LongestStaticPrefix(const Expr* expr, const ScopeMap& scope = {});

}  // namespace delta
