#pragma once

#include <cstdint>
#include <optional>
#include <string>
#include <string_view>
#include <unordered_map>

namespace delta {

struct Expr;
struct ModuleItem;
struct ClassDecl;
struct RtlirModule;

using ScopeMap = std::unordered_map<std::string_view, int64_t>;

// §11.5.1: the outermost packed dimension of a declaration, as its two folded
// bounds. "The actual bit that is accessed by an address is, in part,
// determined by the declaration", and the clause makes the point with
// `logic [15:0] acc` beside `logic [2:17] acc` -- two sixteen-bit vectors in
// which the same index addresses a different bit. A select has to name bits by
// their index in this range, because that is the range the select is resolved
// against; counting bits from the least significant end names the intended bit
// only when the declaration was written [N:0].
struct DeclaredPackedRange {
  int64_t left = 0;
  int64_t right = 0;

  // The range of a value carrying no declaration of its own -- a concatenation,
  // a literal, the result of another select -- which is addressed as
  // [width-1:0], so an index and an offset are the same number. This is the
  // fallback the simulator makes as well (Variable::DeclaredRange). A width of
  // zero, which a name that resolves to no signal at all reports, yields [0:0]
  // rather than [-1:0]: the value has no bits to address either way, and a left
  // bound below the right one would read as an ascending range and invert the
  // mapping.
  static DeclaredPackedRange Implicit(uint32_t width) {
    return {width == 0 ? 0 : static_cast<int64_t>(width) - 1, 0};
  }

  // The index naming the bit that sits `offset` places above the least
  // significant end of the range. The right-hand bound is that end whichever
  // way the range runs: §11.5.1 reads `logic [0:31] b_vect; b_vect[0 +: 8]` as
  // `b_vect[0:7]`, so index 31 of that declaration is its least significant
  // bit.
  int64_t IndexAtOffset(int64_t offset) const {
    return (left >= right) ? right + offset : right - offset;
  }

  // The inverse: how far the bit named `index` sits above the least significant
  // end. This is the number of places a value has to be shifted down for that
  // bit to reach the bottom, which is what reading the bit out of a folded
  // constant takes.
  int64_t OffsetOfIndex(int64_t index) const {
    return (left >= right) ? index - right : right - index;
  }

  // The base index an ascending indexed part-select `[base +: width]` is
  // written with to cover the `width` bits starting `offset` above the least
  // significant end. §11.5.1 gives that form the indices `base` through
  // `base + width - 1`, so the base is the numerically lower of the two ends
  // whichever way the declaration runs.
  int64_t PlusSelectBase(int64_t offset, int64_t width) const {
    return (left >= right) ? right + offset : right - offset - width + 1;
  }
};

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
