// What a declaration says about the size of a name. §20.6.2 (printed page
// 629 of ~/LRM.pdf) has $bits answer the number of bits an argument holds,
// which for a literal, a type keyword with or without a packed range, a
// typedef name of the scope being elaborated (§6.18, printed 118), a
// parameter, a variable or a net of the registered module, and an operator
// expression over those (§11.6.1's Table 11-21, printed 299-300) is fixed at
// elaboration; EvalConstSysCall in const_eval.cpp is what asks. §6.20.2
// (printed 126-127) gives a parameter named in an expression the width and
// signedness of its declaration, which ConstEvalIdentifierFull in
// const_eval_func.cpp asks of RegisteredParamValue.

#include <algorithm>
#include <cstdint>
#include <optional>
#include <string_view>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "elaborator/const_eval.h"
#include "elaborator/const_eval_internal.h"
#include "elaborator/rtlir.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"

namespace delta {

// §6.18: the typedef table of the scope being elaborated and the names in it
// that stand for an unpacked aggregate, installed by the elaborator via
// TypedefRegistryGuard. Null unless a guard is live.
static const TypedefMap* g_typedefs = nullptr;
static const std::unordered_set<std::string_view>* g_aggregate_typedef_names =
    nullptr;

TypedefRegistryGuard::TypedefRegistryGuard(
    const TypedefMap* typedefs,
    const std::unordered_set<std::string_view>* aggregate_names)
    : prev_(g_typedefs), prev_aggregate_names_(g_aggregate_typedef_names) {
  g_typedefs = typedefs;
  g_aggregate_typedef_names = aggregate_names;
}

TypedefRegistryGuard::~TypedefRegistryGuard() {
  g_typedefs = prev_;
  g_aggregate_typedef_names = prev_aggregate_names_;
}

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
// ranged form multiplies the atom width by the packed range. A parameter, a
// variable or a net of the module a ParamRangeRegistryGuard installed is
// sized by its declaration, IdentifierBits below, and an operator expression
// by §11.6.1's Table 11-21 over its operands, SelfDeterminedBits. User-defined
// type names and other typed expressions need type resolution unavailable at
// this layer and are left to be sized at run time.
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

// §6.20.2 (printed pages 126-127): whether the declaration fixes the
// parameter's width -- a range gives it the range's, and a type with no range
// the type's -- as against a parameter declared with neither, or with a bare
// `signed`, which takes an implied range from the size of its final value.
static bool HasDeclaredWidth(const RtlirParamDecl& pd) {
  return pd.has_decl_range || (pd.has_decl_type && !pd.decl_type_implicit);
}

// §6.20.2 (printed page 126): the width a declaration with a range fixes is
// the range's. RtlirParamDecl::decl_width is that width where both bounds
// are literals, but it is folded without the earlier parameters in scope
// (PopulateParamTypeInfo in elaborator_items.cpp), so a bound written as one
// -- `logic [HI:1] V` under `localparam int HI = 8` -- does not fold there and
// leaves decl_width at the vector type's one bit. The two bounds are folded
// against the parameters already elaborated (RecordParamDeclRange), so the
// range they span is the declaration's width wherever it exceeds decl_width.
// 64b2dfbe0 read decl_width alone, which cut V to its low bit and made
// `V[HI]` 0 and $bits(V) 1. A second packed dimension is not recorded with
// the bounds, so `logic [HI:1][3:0]` still reads the first dimension's span.
static uint32_t DeclaredParamWidth(const RtlirParamDecl& pd) {
  if (!pd.has_decl_range || !pd.has_decl_range_bounds) return pd.decl_width;
  int64_t left = pd.decl_range_left;
  int64_t right = pd.decl_range_right;
  int64_t span = (left >= right ? left - right : right - left) + 1;
  return std::max(pd.decl_width, static_cast<uint32_t>(span));
}

// §23.10.2: the expression an instance override gave the parameter where it
// is a literal, which names nothing and so reads the same in every scope.
// Null for an override written as anything else, which stands in the
// instantiating module and means nothing here, and for a parameter no
// instance overrode.
static const Expr* LiteralOverrideExpr(const RtlirParamDecl& pd) {
  if (pd.override_expr == nullptr ||
      pd.override_expr->kind != ExprKind::kIntegerLiteral)
    return nullptr;
  return pd.override_expr;
}

// §6.20.2 (printed pages 126-127): the number of bits a value parameter holds.
// A parameter declared with a range has the range of its declaration, and one
// declared with a type and no range is of that type, so both answer from
// DeclaredParamWidth. A parameter declared with neither, or with a
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
  if (HasDeclaredWidth(pd)) {
    uint32_t width = DeclaredParamWidth(pd);
    if (width == 0) return std::nullopt;
    return static_cast<int64_t>(width);
  }
  if (pd.from_override) {
    const Expr* lit = LiteralOverrideExpr(pd);
    if (lit == nullptr) return std::nullopt;
    return static_cast<int64_t>(ConstLiteralWidth(lit));
  }
  auto value = ConstEvalFull(pd.default_value, RegisteredModuleScope());
  if (!value) return std::nullopt;
  return static_cast<int64_t>(value->width);
}

// §20.6.2 (printed page 629) with §6.24.3: the bits an array of `elem_bits`
// bit elements holds as a bit stream, its element count being the product of
// its unpacked dimensions. Empty when a dimension did not fold, which
// `sizes` then has fewer entries than `num_dims` to say, and for a queue, a
// dynamic or an associative array, whose extent the declaration does not
// fix.
static std::optional<int64_t> ArrayBits(uint32_t elem_bits, uint32_t num_dims,
                                        const std::vector<uint32_t>& sizes) {
  if (sizes.size() != num_dims) return std::nullopt;
  int64_t bits = elem_bits;
  for (uint32_t size : sizes) bits *= size;
  return bits;
}

// §20.6.2 (printed page 629) opens with `logic [31:0] v` and has $bits(v)
// answer 32, the number of bits the declaration gives the variable.
// RtlirVariable::width carries that for a variable the registered module has
// already elaborated, so a variable of the module answers from there. A
// variable with unpacked dimensions holds width bits per element, so it
// answers width times every dimension's size where all of them folded. A
// real, string, event, chandle or class variable holds no bit vector this
// layer sizes, so those are left to the run.
static std::optional<int64_t> RegisteredVariableBits(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return std::nullopt;
  for (const auto& var : mod->variables) {
    if (var.name != name) continue;
    if (var.is_real || var.is_string || var.is_event || var.is_chandle ||
        !var.class_type_name.empty())
      return std::nullopt;
    return ArrayBits(var.width, var.num_unpacked_dims, var.unpacked_dim_sizes);
  }
  return std::nullopt;
}

// §20.6.2 lets $bits size a net as it sizes a variable, `wire [3:0] v` being
// four bits and `wire [7:0] w[3]` twenty-four. RtlirNet::width is the bits of
// one element and RtlirNet::unpacked_dim_sizes the dimensions the
// declaration wrote, so a net of the registered module answers as a variable
// does.
static std::optional<int64_t> RegisteredNetBits(std::string_view name) {
  const RtlirModule* mod = RegisteredModule();
  if (mod == nullptr) return std::nullopt;
  for (const auto& net : mod->nets) {
    if (net.name != name) continue;
    return ArrayBits(net.width, net.num_unpacked_dims, net.unpacked_dim_sizes);
  }
  return std::nullopt;
}

// §20.6.2 (printed page 629) with §6.18 (printed 118): the bits a typedef
// name holds -- the clause's own `$bits(MyType)` of a structure typedef is 9
// -- as EvalTypeWidth sizes the type the name stands for through the table a
// live TypedefRegistryGuard installed, following a name standing for another
// name, with a packed range folded against `scope`. Empty when no guard is
// live, when the table holds no such name, when the name stands for an
// unpacked aggregate -- a queue, a dynamic, an associative or a fixed-size
// unpacked array, whose dimensions the table does not carry, so the entry
// would size one element -- and when the type has no width the fold can
// state: a string, an event, a class, a forward declaration. d6a7eab50 left
// every typedef name to the run, the fold having reached no table.
static std::optional<int64_t> RegisteredTypedefBits(std::string_view name,
                                                    const ScopeMap& scope) {
  if (g_typedefs == nullptr) return std::nullopt;
  auto it = g_typedefs->find(name);
  if (it == g_typedefs->end()) return std::nullopt;
  if (g_aggregate_typedef_names != nullptr &&
      g_aggregate_typedef_names->count(name) != 0)
    return std::nullopt;
  uint32_t width = EvalTypeWidth(it->second, *g_typedefs, scope);
  if (width == 0) return std::nullopt;
  return static_cast<int64_t>(width);
}

// §20.6.2: the bits an identifier argument of $bits holds. A type keyword is
// sized by IntegralKeywordWidth, and no typedef, parameter, variable or net
// can be named by one, so it is asked first; then a typedef of the scope by
// the type it stands for (§6.18), which no parameter of the same scope can
// share a name with; then a parameter of the registered module by its
// declaration (§6.20.2), then a variable of it by its declared width, then a
// net.
static std::optional<int64_t> IdentifierBits(const Expr* a,
                                             const ScopeMap& scope) {
  if (auto w = IntegralKeywordWidth(a->text)) return w;
  if (auto w = RegisteredTypedefBits(a->text, scope)) return w;
  if (const RtlirParamDecl* pd = RegisteredParamNamed(a->text))
    return ParamDeclBits(*pd);
  if (auto w = RegisteredVariableBits(a->text)) return w;
  return RegisteredNetBits(a->text);
}

static std::optional<int64_t> SelfDeterminedBits(const Expr* a,
                                                 const ScopeMap& scope);

// §11.6.1's Table 11-21 (printed pages 299-300): how an operator sizes its
// expression. `+ - * / % & | ^ ^~ ~^` take the larger of their operands'
// lengths; a shift and `**` take the left operand's, the right being
// self-determined, as do unary `+ - ~`; a comparison, an equality, a logical
// operator, an implication, a reduction and `!` are one bit.
enum class BitLengthRule : std::uint8_t {
  kMaxOfOperands,
  kLeftOperand,
  kOneBit
};

// The rule Table 11-21 gives the operator of `a`, a unary or binary
// expression, or empty for an operator outside the table -- the sequence
// implication, which makes no expression, and a prefix increment.
static std::optional<BitLengthRule> BitLengthRuleOf(const Expr* a) {
  static const std::unordered_map<TokenKind, BitLengthRule> kBinary{
      {TokenKind::kPlus, BitLengthRule::kMaxOfOperands},
      {TokenKind::kMinus, BitLengthRule::kMaxOfOperands},
      {TokenKind::kStar, BitLengthRule::kMaxOfOperands},
      {TokenKind::kSlash, BitLengthRule::kMaxOfOperands},
      {TokenKind::kPercent, BitLengthRule::kMaxOfOperands},
      {TokenKind::kAmp, BitLengthRule::kMaxOfOperands},
      {TokenKind::kPipe, BitLengthRule::kMaxOfOperands},
      {TokenKind::kCaret, BitLengthRule::kMaxOfOperands},
      {TokenKind::kTildeCaret, BitLengthRule::kMaxOfOperands},
      {TokenKind::kCaretTilde, BitLengthRule::kMaxOfOperands},
      {TokenKind::kLtLt, BitLengthRule::kLeftOperand},
      {TokenKind::kLtLtLt, BitLengthRule::kLeftOperand},
      {TokenKind::kGtGt, BitLengthRule::kLeftOperand},
      {TokenKind::kGtGtGt, BitLengthRule::kLeftOperand},
      {TokenKind::kPower, BitLengthRule::kLeftOperand},
      {TokenKind::kLt, BitLengthRule::kOneBit},
      {TokenKind::kGt, BitLengthRule::kOneBit},
      {TokenKind::kLtEq, BitLengthRule::kOneBit},
      {TokenKind::kGtEq, BitLengthRule::kOneBit},
      {TokenKind::kEqEq, BitLengthRule::kOneBit},
      {TokenKind::kBangEq, BitLengthRule::kOneBit},
      {TokenKind::kEqEqEq, BitLengthRule::kOneBit},
      {TokenKind::kBangEqEq, BitLengthRule::kOneBit},
      {TokenKind::kEqEqQuestion, BitLengthRule::kOneBit},
      {TokenKind::kBangEqQuestion, BitLengthRule::kOneBit},
      {TokenKind::kAmpAmp, BitLengthRule::kOneBit},
      {TokenKind::kPipePipe, BitLengthRule::kOneBit},
      {TokenKind::kArrow, BitLengthRule::kOneBit},
      {TokenKind::kLtDashGt, BitLengthRule::kOneBit},
  };
  static const std::unordered_map<TokenKind, BitLengthRule> kUnary{
      {TokenKind::kPlus, BitLengthRule::kLeftOperand},
      {TokenKind::kMinus, BitLengthRule::kLeftOperand},
      {TokenKind::kTilde, BitLengthRule::kLeftOperand},
      {TokenKind::kAmp, BitLengthRule::kOneBit},
      {TokenKind::kTildeAmp, BitLengthRule::kOneBit},
      {TokenKind::kPipe, BitLengthRule::kOneBit},
      {TokenKind::kTildePipe, BitLengthRule::kOneBit},
      {TokenKind::kCaret, BitLengthRule::kOneBit},
      {TokenKind::kTildeCaret, BitLengthRule::kOneBit},
      {TokenKind::kCaretTilde, BitLengthRule::kOneBit},
      {TokenKind::kBang, BitLengthRule::kOneBit},
  };
  const auto& rules = a->kind == ExprKind::kUnary ? kUnary : kBinary;
  auto it = rules.find(a->op);
  if (it == rules.end()) return std::nullopt;
  return it->second;
}

// §11.6.1's Table 11-21: the bit length of a unary or binary expression by
// its operator's rule, the operand of a unary expression being its lhs.
static std::optional<int64_t> OperatorBits(const Expr* a,
                                           const ScopeMap& scope) {
  auto rule = BitLengthRuleOf(a);
  if (!rule) return std::nullopt;
  if (*rule == BitLengthRule::kOneBit) return 1;
  auto l = SelfDeterminedBits(a->lhs, scope);
  if (*rule == BitLengthRule::kLeftOperand) return l;
  auto r = SelfDeterminedBits(a->rhs, scope);
  if (!l || !r) return std::nullopt;
  return std::max(*l, *r);
}

// §11.6.1's Table 11-21: a conditional expression is as long as the longer of
// its two arms, the condition being self-determined.
static std::optional<int64_t> TernaryBits(const Expr* a,
                                          const ScopeMap& scope) {
  auto t = SelfDeterminedBits(a->true_expr, scope);
  auto f = SelfDeterminedBits(a->false_expr, scope);
  if (!t || !f) return std::nullopt;
  return std::max(*t, *f);
}

// §20.6.2 with §11.6.1: the number of bits the self-determined expression `a`
// holds, which is what $bits answers and what its result is valid at
// elaboration for. An integer literal is as wide as its size constant
// (§5.7.1), an identifier as its declaration, and an operator expression as
// Table 11-21 sizes it from its operands. A concatenation, a replication, a
// select, a call and a cast are not sized here.
static std::optional<int64_t> SelfDeterminedBits(const Expr* a,
                                                 const ScopeMap& scope) {
  switch (a->kind) {
    case ExprKind::kIntegerLiteral:
      return static_cast<int64_t>(ConstLiteralWidth(a));
    case ExprKind::kIdentifier:
      return IdentifierBits(a, scope);
    case ExprKind::kBinary:
    case ExprKind::kUnary:
      return OperatorBits(a, scope);
    case ExprKind::kTernary:
      return TernaryBits(a, scope);
    default:
      return RangedKeywordBits(a, scope);
  }
}

std::optional<int64_t> EvalConstBits(const Expr* expr, const ScopeMap& scope) {
  if (expr->args.empty()) return std::nullopt;
  return SelfDeterminedBits(expr->args[0], scope);
}

// Folding a parameter's value expression to size a name that reads it folds
// the names that expression reads in turn. A value expression naming its own
// parameter -- which §23.9 makes a self-reference where the name is also an
// outer scope's, and §6.20.1 does not admit -- would do so without end, so
// the depth is capped as a constant function's recursion is.
static int g_param_refold_depth = 0;
static constexpr int kMaxParamRefoldDepth = 32;

// The fold of the parameter's own value expression -- the declaration's
// default, or a literal an instance override gave it -- from which a width
// the declaration leaves to the value (§6.20.2's implied range) and the words
// above bit 63 of a value declared wider than 64 bits are read. Empty where
// there is no such expression, where it does not fold against the registered
// module's parameters, or where the refold is too deep.
static std::optional<ConstVal> RefoldParamValue(const RtlirParamDecl& pd) {
  const Expr* value_expr =
      pd.from_override ? LiteralOverrideExpr(pd) : pd.default_value;
  if (value_expr == nullptr || g_param_refold_depth >= kMaxParamRefoldDepth)
    return std::nullopt;
  ++g_param_refold_depth;
  struct DepthGuard {
    ~DepthGuard() { --g_param_refold_depth; }
  } depth_guard;
  return ConstEvalFull(value_expr, RegisteredModuleScope());
}

// §6.20.2 (printed pages 126-127): what a name standing for a value parameter
// of the registered module is worth. A parameter declared with a range or a
// type has that width and that signedness whatever value it took, so the
// value is read at them: `localparam byte B = 300` is the eight bits 300
// leaves, and `localparam bit [3:0] Y = -1` is 15. One declared with neither
// takes the size and signedness of its final value, which is what the fold of
// the value expression carries, and 32 bits signed where that expression does
// not fold here. Either way a parameter wider than 64 bits has its words
// above bit 63 read from that fold, the ScopeMap holding the low 64 alone.
// `value` is what the ScopeMap holds for the name, and is kept as the low
// word rather than the refold's, since a ScopeMap built for a generate block
// or a defparam may hold a value the refold does not see.
//
// The declaration is consulted only where it agrees with the ScopeMap on the
// value, because a constant function's locals (§13.4.3) sit in the same map
// under bare names, and a formal called as a parameter is would otherwise be
// cut to that parameter's width.
std::optional<ConstVal> RegisteredParamValue(std::string_view name,
                                             int64_t value) {
  const RtlirParamDecl* pd = RegisteredParamNamed(name);
  if (pd == nullptr || pd->resolved_value != value) return std::nullopt;
  bool declared = HasDeclaredWidth(*pd);
  uint32_t decl_width = DeclaredParamWidth(*pd);
  std::optional<ConstVal> refold;
  if (!declared || decl_width > 64) refold = RefoldParamValue(*pd);
  uint32_t width = declared ? decl_width : refold ? refold->width : 32;
  bool is_signed = declared ? pd->decl_is_signed
                   : refold ? refold->is_signed
                            : true;
  ConstVal v = NormalizeConstVal(value, width, is_signed);
  if (refold && width > 64) v.high_words = refold->high_words;
  return v;
}

}  // namespace delta
