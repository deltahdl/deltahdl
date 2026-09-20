// What a declaration says about the size of a name. §20.6.2 (printed page
// 629 of ~/LRM.pdf) has $bits answer the number of bits an argument holds,
// which for a literal, a type keyword with or without a packed range, a
// parameter or a variable of the registered module is fixed at elaboration;
// EvalConstSysCall in const_eval.cpp is what asks. Moved out of const_eval.cpp
// for room.

#include <cstdint>
#include <optional>
#include <string_view>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/rtlir.h"
#include "parser/ast_expr.h"

namespace delta {

// §20.6.2: the packed bit width of a built-in integral type keyword. The
// vector atoms (bit/logic/reg) are 1 bit; the integer-atom keywords carry
// their standard widths. Non-integral (real, string, ...) and user-defined
// types are not sized here.
static std::optional<int64_t> IntegralKeywordWidth(std::string_view kw) {
  if (kw == "bit" || kw == "logic" || kw == "reg") return 1;
  if (kw == "byte") return 8;
  if (kw == "shortint") return 16;
  if (kw == "int" || kw == "integer") return 32;
  if (kw == "longint" || kw == "time") return 64;
  return std::nullopt;
}

// §20.6.2: fold $bits on a fixed-size argument to a constant at elaboration.
// An integer literal contributes its declared width. A built-in data type --
// a bare keyword (int, logic, ...) or a ranged vector (logic [7:0]) -- has a
// width knowable from the argument syntax alone, so it folds here as well; the
// ranged form multiplies the atom width by the packed range. A parameter or a
// variable of the module a ParamRangeRegistryGuard installed is sized by its
// declaration, IdentifierBits below. User-defined type names and other typed
// expressions need type/instance resolution unavailable at this layer and are
// left to be sized at run time.
// The ranged form of a built-in data type -- a bare keyword under a packed
// range, `logic [7:0]`. Its width is the atom width times the range span.
static std::optional<int64_t> RangedKeywordBits(const Expr* a,
                                                const ScopeMap& scope) {
  if (a->kind != ExprKind::kSelect || !a->index || !a->index_end ||
      a->is_part_select_plus || a->is_part_select_minus || !a->base ||
      a->base->kind != ExprKind::kIdentifier)
    return std::nullopt;
  auto atom = IntegralKeywordWidth(a->base->text);
  if (!atom) return std::nullopt;
  auto hi = ConstEvalInt(a->index, scope);
  auto lo = ConstEvalInt(a->index_end, scope);
  if (!hi || !lo) return std::nullopt;
  int64_t span = (*hi >= *lo ? *hi - *lo : *lo - *hi) + 1;
  return *atom * span;
}

// §6.20.2 (printed pages 126-127): the number of bits a value parameter holds.
// A parameter declared with a range has the range of its declaration, and one
// declared with a type and no range is of that type, so both answer from
// RtlirParamDecl::decl_width. A parameter declared with neither, or with a
// bare `signed`, takes an implied range from the size of the final value
// assigned to it, at least 32 bits when that value is unsized, which is the
// width the fold of the value carries -- 8 for `localparam Q = 8'hFF` and 32
// for `localparam R = 100`, matching the clause's own `newconst` examples.
// The value an instance overrode is an expression written in the
// instantiating module, whose names mean nothing here, so of those only a
// literal is sized. Empty for a type, real or string parameter, whose value
// is not a bit vector this layer sizes.
static std::optional<int64_t> ParamDeclBits(const RtlirParamDecl& pd) {
  if (pd.is_type_param || pd.is_real_value || pd.is_string_value)
    return std::nullopt;
  if (pd.has_decl_range || (pd.has_decl_type && !pd.decl_type_implicit)) {
    if (pd.decl_width == 0) return std::nullopt;
    return static_cast<int64_t>(pd.decl_width);
  }
  if (pd.from_override) {
    if (pd.override_expr == nullptr ||
        pd.override_expr->kind != ExprKind::kIntegerLiteral)
      return std::nullopt;
    return static_cast<int64_t>(ConstLiteralWidth(pd.override_expr));
  }
  auto value = ConstEvalFull(pd.default_value, RegisteredModuleScope());
  if (!value) return std::nullopt;
  return static_cast<int64_t>(value->width);
}

// §20.6.2 (printed page 629) opens with `logic [31:0] v` and has $bits(v)
// answer 32, the number of bits the declaration gives the variable.
// RtlirVariable::width carries that for a variable the registered module has
// already elaborated, so a variable of the module answers from there. A
// variable with an unpacked dimension holds width bits per element rather
// than in all, and a real, string, event, chandle or class variable holds no
// bit vector this layer sizes, so those are left to the run. A net is left
// to the run as well: RtlirNet carries its width and nothing about an
// unpacked dimension, so a net array cannot be told from a vector here.
static std::optional<int64_t> RegisteredVariableBits(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return std::nullopt;
  for (const auto& var : mod->variables) {
    if (var.name != name) continue;
    if (var.num_unpacked_dims != 0 || var.is_real || var.is_string ||
        var.is_event || var.is_chandle || !var.class_type_name.empty())
      return std::nullopt;
    return static_cast<int64_t>(var.width);
  }
  return std::nullopt;
}

// §20.6.2: the bits an identifier argument of $bits holds. A type keyword is
// sized by IntegralKeywordWidth, and no parameter or variable can be named by
// one, so it is asked first; then a parameter of the registered module by
// its declaration (§6.20.2), then a variable of it by its declared width.
static std::optional<int64_t> IdentifierBits(const Expr* a) {
  if (auto w = IntegralKeywordWidth(a->text)) return w;
  if (const RtlirParamDecl* pd = RegisteredParamNamed(a->text))
    return ParamDeclBits(*pd);
  return RegisteredVariableBits(a->text);
}

std::optional<int64_t> EvalConstBits(const Expr* expr, const ScopeMap& scope) {
  if (expr->args.empty()) return std::nullopt;
  auto* a = expr->args[0];
  if (a->kind == ExprKind::kIntegerLiteral)
    return static_cast<int64_t>(ConstLiteralWidth(a));

  if (a->kind == ExprKind::kIdentifier) return IdentifierBits(a);
  return RangedKeywordBits(a, scope);
}

}  // namespace delta
