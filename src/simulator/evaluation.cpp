#include "simulator/evaluation.h"

#include <algorithm>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>

#include "common/arena.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/statement_assign.h"

namespace delta {
static Logic4Vec EvalIdentifier(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  auto* var = ctx.FindVariable(expr->text);
  if (var) {
    if (var->is_event)
      return MakeLogic4VecVal(arena, 1, var->is_null_event ? 0u : 1u);
    auto val = var->value;
    if (ctx.IsRealVariable(expr->text)) val.is_real = true;
    if (ctx.IsStringVariable(expr->text)) val.is_string = true;
    // An object's signedness is fixed by its own declaration; it is never
    // inherited from a value that flowed in from elsewhere (e.g. across a
    // module port). Derive the read value's signedness from the declaration
    // so a signed value stored into an unsigned object reads back unsigned.
    val.is_signed = var->is_signed;
    return val;
  }
  // §8.10: a static method can directly access static properties of the same
  // class by unqualified reference. With no `this`, resolve against the
  // enclosing class's static properties before falling through.
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  if (method_cls) {
    auto it = method_cls->static_properties.find(std::string(expr->text));
    if (it != method_cls->static_properties.end()) {
      return it->second;
    }
  }
  // §8.6: when reading an unqualified identifier within a method body, if the
  // identifier is not found as a local variable, try to resolve it as a
  // property of the current object (this).
  auto* self = ctx.CurrentThis();
  if (self) {
    return self->GetProperty(expr->text, arena);
  }
  return MakeLogic4Vec(arena, 1);
}
bool HasUnknownBits(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].bval != 0) return true;
  }
  return false;
}
Logic4Vec MakeAllX(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < vec.nwords; ++i) {
    vec.words[i] = {~uint64_t{0}, ~uint64_t{0}};
  }
  return vec;
}

// Writes the low `w` bits of {aval,bval} into `result` starting at bit_pos,
// spanning the 64-bit word boundary when the chunk straddles two words.
static void WriteConcatChunk(Logic4Vec& result, uint32_t bit_pos, uint32_t w,
                             uint64_t aval, uint64_t bval) {
  uint32_t word = bit_pos / 64;
  uint32_t bit = bit_pos % 64;
  if (word >= result.nwords) return;
  result.words[word].aval |= aval << bit;
  result.words[word].bval |= bval << bit;
  if (bit + w > 64 && word + 1 < result.nwords) {
    result.words[word + 1].aval |= aval >> (64 - bit);
    result.words[word + 1].bval |= bval >> (64 - bit);
  }
}

Logic4Vec AssembleConcatParts(const std::vector<Logic4Vec>& parts,
                              uint32_t total_width, Arena& arena) {
  auto result = MakeLogic4Vec(arena, total_width);
  uint32_t bit_pos = 0;
  for (auto it = parts.rbegin(); it != parts.rend(); ++it) {
    // Concatenation places each operand's bits verbatim, so preserve the raw
    // 4-state encoding (aval/bval, not ToUint64()); copy every word so operands
    // wider than 64 bits (e.g. multi-character strings) are not truncated.
    uint32_t remaining = it->width;
    for (uint32_t pw = 0; pw < it->nwords && remaining > 0; ++pw) {
      uint32_t w = (remaining > 64) ? 64 : remaining;
      WriteConcatChunk(result, bit_pos, w, it->words[pw].aval,
                       it->words[pw].bval);
      bit_pos += w;
      remaining -= w;
    }
  }
  return result;
}

static Logic4Vec SelfDeterminedOperand(const Expr* elem, Logic4Vec vec,
                                       Arena& arena) {
  // Concatenation operands are self-determined; an unbased unsized
  // literal contributes one bit (per §5.7.1) rather than its default
  // wide carrier.
  if (elem && elem->kind == ExprKind::kUnbasedUnsizedLiteral && vec.width > 1) {
    auto bit = MakeLogic4Vec(arena, 1);
    if (vec.nwords > 0) {
      bit.words[0].aval = vec.words[0].aval & 1;
      bit.words[0].bval = vec.words[0].bval & 1;
    }
    return bit;
  }
  return vec;
}

static Logic4Vec EvalConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t total_width = 0;
  bool any_string = false;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    auto vec = EvalExpr(elem, ctx, arena);
    vec = SelfDeterminedOperand(elem, vec, arena);
    parts.push_back(vec);
    if (parts.back().is_string) any_string = true;
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 1);
  auto result = AssembleConcatParts(parts, total_width, arena);
  result.is_string = any_string;
  return result;
}

static Logic4Vec CombineBranches(Logic4Vec tv, Logic4Vec fv, Arena& arena) {
  uint32_t width = (tv.width > fv.width) ? tv.width : fv.width;
  auto result = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < result.nwords; ++i) {
    auto tw = (i < tv.nwords) ? tv.words[i] : Logic4Word{};
    auto fw = (i < fv.nwords) ? fv.words[i] : Logic4Word{};
    // §11.4.11 Table 11-22: result is 0 iff both 0, 1 iff both 1, else x. Under
    // the canonical encoding x=(aval=1,bval=1), so every unknown result bit
    // sets aval as well as bval.
    result.words[i].bval = tw.bval | fw.bval | (tw.aval ^ fw.aval);
    result.words[i].aval = (tw.aval & fw.aval) | result.words[i].bval;
  }
  if (tv.is_real || fv.is_real) result.is_real = true;
  return result;
}
// §11.4.11: the unselected conditional operand shall not be evaluated. An
// operand that could mutate state (an embedded assignment, ++/--, or a call)
// is detected here so the determinate-condition path can skip it; a pure
// operand is still evaluated to recover its result-type metadata.
static bool ExprNodeIsSideEffect(const Expr* e) {
  if (e->kind == ExprKind::kCall || e->kind == ExprKind::kSystemCall)
    return true;
  if (e->kind == ExprKind::kBinary &&
      (e->op == TokenKind::kEq || IsCompoundAssignOp(e->op)))
    return true;
  return (e->kind == ExprKind::kUnary || e->kind == ExprKind::kPostfixUnary) &&
         (e->op == TokenKind::kPlusPlus || e->op == TokenKind::kMinusMinus);
}
static bool ExprMayHaveSideEffect(const Expr* e) {
  if (e == nullptr) return false;
  if (ExprNodeIsSideEffect(e)) return true;
  const Expr* children[] = {e->lhs,  e->rhs,   e->condition,  e->true_expr,
                            e->base, e->index, e->false_expr, e->index_end};
  for (const auto* c : children)
    if (ExprMayHaveSideEffect(c)) return true;
  for (const auto* a : e->args)
    if (ExprMayHaveSideEffect(a)) return true;
  for (const auto* el : e->elements)
    if (ExprMayHaveSideEffect(el)) return true;
  return false;
}
static Logic4Vec EvalTernaryUnknownCond(const Expr* expr, SimContext& ctx,
                                        Arena& arena, uint32_t context_width) {
  auto tv = EvalExpr(expr->true_expr, ctx, arena, context_width);
  auto fv = EvalExpr(expr->false_expr, ctx, arena, context_width);
  bool result_signed = tv.is_signed && fv.is_signed;
  uint32_t width = (tv.width > fv.width) ? tv.width : fv.width;
  if (context_width > width) width = context_width;
  if (tv.width < width) tv = ExtendVec(tv, width, result_signed, arena);
  if (fv.width < width) fv = ExtendVec(fv, width, result_signed, arena);
  Logic4Vec result;
  if (EvalCaseEquality(tv, fv)) {
    tv.is_signed = result_signed;
    result = tv;
  } else {
    result = CombineBranches(tv, fv, arena);
    result.is_signed = result_signed;
  }
  // Apply assignment-like context truncation (§10.8 conditional operands)
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}
static Logic4Vec EvalTernary(const Expr* expr, SimContext& ctx, Arena& arena,
                             uint32_t context_width = 0) {
  auto cond = EvalExpr(expr->condition, ctx, arena);

  if (HasUnknownBits(cond)) {
    return EvalTernaryUnknownCond(expr, ctx, arena, context_width);
  }
  // §11.4.11: a determinate condition selects exactly one expression; the
  // other shall not be evaluated. A side-effect-free unselected expression is
  // still evaluated so its width/signedness/realness contribute to the result
  // type, but one that could mutate state is skipped.
  bool cond_true = cond.ToUint64() != 0;
  const Expr* other_expr = cond_true ? expr->false_expr : expr->true_expr;
  auto chosen = EvalExpr(cond_true ? expr->true_expr : expr->false_expr, ctx,
                         arena, context_width);
  bool result_signed = chosen.is_signed;
  uint32_t width = chosen.width;
  if (!ExprMayHaveSideEffect(other_expr)) {
    auto other = EvalExpr(other_expr, ctx, arena, context_width);
    result_signed = chosen.is_signed && other.is_signed;
    if (other.width > width) width = other.width;
    if (other.is_real) chosen.is_real = true;
  }
  if (context_width > width) width = context_width;
  Logic4Vec result;
  if (chosen.width < width) {
    result = ExtendVec(chosen, width, result_signed, arena);
    result.is_signed = result_signed;
  } else {
    result = chosen;
    result.is_signed = result_signed;
  }
  // Apply assignment-like context truncation (§10.8 conditional operands)
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}

static uint32_t AssignExprLhsWidth(const Expr* lhs, SimContext& ctx) {
  if (lhs->kind == ExprKind::kConcatenation) {
    uint32_t total = 0;
    for (auto* elem : lhs->elements) total += AssignExprLhsWidth(elem, ctx);
    return total;
  }
  auto* var = ResolveLhsVariable(lhs, ctx);
  return var ? var->value.width : 0;
}

static Logic4Vec EvalAssignInExpr(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  uint32_t lhs_w = AssignExprLhsWidth(expr->lhs, ctx);
  if (lhs_w == 0) return rhs_val;
  PerformBlockingAssign(expr->lhs, rhs_val, ctx, arena);
  // §11.3.6: a concatenation target yields an unsigned integral result whose
  // width is the sum of its operand widths. Re-pack the value rather than
  // forwarding the right-hand side so the result never inherits the
  // right-hand side's signedness, even when the widths already match.
  bool lhs_is_concat = expr->lhs->kind == ExprKind::kConcatenation;
  if (lhs_w == rhs_val.width && !lhs_is_concat) return rhs_val;
  uint64_t v = rhs_val.ToUint64();
  if (lhs_w < 64) v &= (uint64_t{1} << lhs_w) - 1;
  return MakeLogic4VecVal(arena, lhs_w, v);
}

static bool ArrayElementsEqual(std::string_view a, const ArrayInfo* ai,
                               std::string_view b, SimContext& ctx) {
  for (uint32_t i = 0; i < ai->size; ++i) {
    auto an = std::string(a) + "[" + std::to_string(ai->lo + i) + "]";
    auto bn = std::string(b) + "[" + std::to_string(ai->lo + i) + "]";
    auto* av = ctx.FindVariable(an);
    auto* bv = ctx.FindVariable(bn);
    if (!av || !bv) return false;
    if (av->value.ToUint64() != bv->value.ToUint64()) return false;
  }
  return true;
}

static bool TryArrayEqualityOp(const Expr* expr, SimContext& ctx, Arena& arena,
                               Logic4Vec& out) {
  if (expr->op != TokenKind::kEqEq && expr->op != TokenKind::kBangEq)
    return false;
  if (!expr->lhs || !expr->rhs) return false;
  if (expr->lhs->kind != ExprKind::kIdentifier) return false;
  if (expr->rhs->kind != ExprKind::kIdentifier) return false;
  auto* la = ctx.FindArrayInfo(expr->lhs->text);
  auto* ra = ctx.FindArrayInfo(expr->rhs->text);
  if (!la || !ra) return false;
  bool eq = (la->size == ra->size && la->elem_width == ra->elem_width);
  if (eq) eq = ArrayElementsEqual(expr->lhs->text, la, expr->rhs->text, ctx);
  uint64_t val = (expr->op == TokenKind::kEqEq) == eq ? 1 : 0;
  out = MakeLogic4VecVal(arena, 1, val);
  return true;
}

static Logic4Vec EvalLogicalAnd(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  if (!l_unknown && l.ToUint64() == 0) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool r_unknown = HasUnknownBits(r);
  if (!r_unknown && r.ToUint64() == 0) {
    return MakeLogic4VecVal(arena, 1, 0);
  }
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, 1);
}

static Logic4Vec EvalLogicalOr(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  if (!l_unknown && l.ToUint64() != 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool r_unknown = HasUnknownBits(r);
  if (!r_unknown && r.ToUint64() != 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalLogicalImpl(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  if (!l_unknown && l.ToUint64() == 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool r_unknown = HasUnknownBits(r);
  if (!r_unknown && r.ToUint64() != 0) {
    return MakeLogic4VecVal(arena, 1, 1);
  }
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalLogicalEquiv(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto l = EvalExpr(expr->lhs, ctx, arena);
  auto r = EvalExpr(expr->rhs, ctx, arena);
  bool l_unknown = HasUnknownBits(l);
  bool r_unknown = HasUnknownBits(r);
  if (l_unknown || r_unknown) return MakeAllX(arena, 1);
  bool lv = l.ToUint64() != 0;
  bool rv = r.ToUint64() != 0;
  return MakeLogic4VecVal(arena, 1, (lv == rv) ? 1 : 0);
}
// Operands of an identity-equality comparison, after resolving each side's
// identifier node, bound variable, and null/event classification.
struct IdentityEqualityOperands {
  const Expr* lhs_id;
  const Expr* rhs_id;
  Variable* lv;
  Variable* rv;
  bool lhs_is_event;
  bool rhs_is_event;
  bool lhs_is_null;
  bool rhs_is_null;
  bool is_eq_op;
};

// Returns true when the operator is one of the four equality operators
// (==, !=, ===, !==) and fills `ops` with the resolved operand information.
static bool ResolveIdentityEqualityOperands(const Expr* expr, SimContext& ctx,
                                            IdentityEqualityOperands& ops) {
  if (expr->op != TokenKind::kEqEq && expr->op != TokenKind::kBangEq &&
      expr->op != TokenKind::kEqEqEq && expr->op != TokenKind::kBangEqEq) {
    return false;
  }
  ops.lhs_id = (expr->lhs && expr->lhs->kind == ExprKind::kIdentifier)
                   ? expr->lhs
                   : nullptr;
  ops.rhs_id = (expr->rhs && expr->rhs->kind == ExprKind::kIdentifier)
                   ? expr->rhs
                   : nullptr;
  ops.lv = ops.lhs_id ? ctx.FindVariable(ops.lhs_id->text) : nullptr;
  ops.rv = ops.rhs_id ? ctx.FindVariable(ops.rhs_id->text) : nullptr;
  ops.lhs_is_event = ops.lv && ops.lv->is_event;
  ops.rhs_is_event = ops.rv && ops.rv->is_event;
  ops.lhs_is_null = ops.lhs_id && ops.lhs_id->text == "null" && !ops.lv;
  ops.rhs_is_null = ops.rhs_id && ops.rhs_id->text == "null" && !ops.rv;
  ops.is_eq_op =
      (expr->op == TokenKind::kEqEq || expr->op == TokenKind::kEqEqEq);
  return true;
}

// Compares two event operands by object identity (a null event compares equal
// to an unbound/null event), producing the boolean comparison result.
static Logic4Vec EvalEventIdentityEquality(const IdentityEqualityOperands& ops,
                                           Arena& arena) {
  bool equal = false;
  if (ops.lhs_is_event && ops.rhs_is_event) {
    equal = (ops.lv == ops.rv);
  } else if (ops.lhs_is_event && ops.rhs_is_null) {
    equal = ops.lv->is_null_event;
  } else if (ops.rhs_is_event && ops.lhs_is_null) {
    equal = ops.rv->is_null_event;
  }
  return MakeLogic4VecVal(arena, 1, (ops.is_eq_op == equal) ? 1u : 0u);
}

// §25.9: equality of a virtual interface against another virtual interface,
// an interface instance, or null compares the interface instance each side
// refers to (an unbound virtual interface and null compare equal).
static Logic4Vec EvalVirtualInterfaceEquality(
    const IdentityEqualityOperands& ops, SimContext& ctx, bool lhs_is_vi,
    bool rhs_is_vi, Arena& arena) {
  auto operand_scope = [&](Variable* v, const Expr* id, bool is_vi,
                           bool is_null) -> std::string {
    if (is_vi) return std::string(ctx.VirtualInterfaceBinding(v));
    if (is_null) return std::string();
    if (id) return ctx.ResolveInstanceScope(id->text);
    return std::string();
  };
  std::string ls =
      operand_scope(ops.lv, ops.lhs_id, lhs_is_vi, ops.lhs_is_null);
  std::string rs =
      operand_scope(ops.rv, ops.rhs_id, rhs_is_vi, ops.rhs_is_null);
  bool equal = (ls == rs);
  return MakeLogic4VecVal(arena, 1, (ops.is_eq_op == equal) ? 1u : 0u);
}

// Handles equality comparisons (==, !=, ===, !==) whose operands are event
// variables or virtual interfaces, per the special object-identity semantics.
// Returns true and sets `out` when the special handling applies; otherwise
// returns false so the caller falls through to the generic binary operator.
static bool TryEvalIdentityEquality(const Expr* expr, SimContext& ctx,
                                    Arena& arena, Logic4Vec& out) {
  IdentityEqualityOperands ops;
  if (!ResolveIdentityEqualityOperands(expr, ctx, ops)) return false;
  if (ops.lhs_is_event || ops.rhs_is_event) {
    out = EvalEventIdentityEquality(ops, arena);
    return true;
  }
  bool lhs_is_vi = ctx.IsVirtualInterfaceVar(ops.lv);
  bool rhs_is_vi = ctx.IsVirtualInterfaceVar(ops.rv);
  if (lhs_is_vi || rhs_is_vi) {
    out = EvalVirtualInterfaceEquality(ops, ctx, lhs_is_vi, rhs_is_vi, arena);
    return true;
  }
  return false;
}

static Logic4Vec EvalBinaryExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                                uint32_t context_width = 0) {
  if (expr->op == TokenKind::kEq) return EvalAssignInExpr(expr, ctx, arena);
  {
    Logic4Vec arr_result;
    if (TryArrayEqualityOp(expr, ctx, arena, arr_result)) return arr_result;
  }
  if (expr->op == TokenKind::kAmpAmp) return EvalLogicalAnd(expr, ctx, arena);

  if (expr->op == TokenKind::kAmpAmpAmp) {
    auto lv = EvalExpr(expr->lhs, ctx, arena);
    if (!lv.IsTruthy()) return MakeLogic4VecVal(arena, 1, 0);
    auto rv = EvalExpr(expr->rhs, ctx, arena);
    return MakeLogic4VecVal(arena, 1, rv.IsTruthy() ? 1 : 0);
  }
  if (expr->op == TokenKind::kPipePipe) return EvalLogicalOr(expr, ctx, arena);
  if (expr->op == TokenKind::kArrow) return EvalLogicalImpl(expr, ctx, arena);
  if (expr->op == TokenKind::kLtDashGt)
    return EvalLogicalEquiv(expr, ctx, arena);

  {
    Logic4Vec identity_result;
    if (TryEvalIdentityEquality(expr, ctx, arena, identity_result))
      return identity_result;
  }
  return EvalBinaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena),
                      EvalExpr(expr->rhs, ctx, arena), arena, context_width);
}

static Logic4Vec EvalTaggedExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                                uint32_t context_width = 0) {
  if (expr->lhs) return EvalExpr(expr->lhs, ctx, arena, context_width);

  return MakeLogic4VecVal(arena, 1, 0);
}

static Logic4Vec EvalRealOrTimeLiteral(const Expr* expr, Arena& arena) {
  double v = expr->real_val;
  uint64_t bits = 0;
  std::memcpy(&bits, &v, sizeof(double));
  auto rv = MakeLogic4VecVal(arena, 64, bits);
  rv.is_real = true;
  return rv;
}

static Logic4Vec EvalUnaryExpr(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  if (expr->op == TokenKind::kPlusPlus || expr->op == TokenKind::kMinusMinus) {
    return EvalPrefixUnary(expr, ctx, arena);
  }
  return EvalUnaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena), arena);
}

static Logic4Vec EvalBinaryDispatch(const Expr* expr, SimContext& ctx,
                                    Arena& arena, uint32_t context_width) {
  if (IsCompoundAssignOp(expr->op)) {
    return EvalCompoundAssign(expr, ctx, arena);
  }
  if (expr->op == TokenKind::kKwMatches) {
    return EvalMatches(expr, ctx, arena);
  }
  return EvalBinaryExpr(expr, ctx, arena, context_width);
}

static Logic4Vec EvalMinTypMax(const Expr* expr, SimContext& ctx, Arena& arena,
                               uint32_t context_width) {
  DelayMode mode = ctx.GetDelayMode();
  Logic4Vec result;
  if (mode == DelayMode::kMin)
    result = EvalExpr(expr->lhs, ctx, arena, context_width);
  else if (mode == DelayMode::kMax)
    result = EvalExpr(expr->rhs, ctx, arena, context_width);
  else
    result = EvalExpr(expr->condition, ctx, arena, context_width);
  // Apply assignment-like context truncation (§10.8 mintymax expressions)
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                   uint32_t context_width) {
  if (!expr) return MakeLogic4Vec(arena, 1);

  if (const auto* snap = ctx.FindDeferredArgSnapshot(expr)) {
    return *snap;
  }
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return EvalIntLiteral(expr, arena);
    case ExprKind::kUnbasedUnsizedLiteral:
      return EvalUnbasedUnsized(expr, arena);
    case ExprKind::kStringLiteral:
      return EvalStringLiteral(expr, arena);
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return EvalRealOrTimeLiteral(expr, arena);
    case ExprKind::kIdentifier:
      return EvalIdentifier(expr, ctx, arena);
    case ExprKind::kUnary:
      return EvalUnaryExpr(expr, ctx, arena);
    case ExprKind::kBinary:
      return EvalBinaryDispatch(expr, ctx, arena, context_width);
    case ExprKind::kTernary:
      return EvalTernary(expr, ctx, arena, context_width);
    case ExprKind::kConcatenation:
      return EvalConcat(expr, ctx, arena);
    case ExprKind::kReplicate:
      return EvalReplicate(expr, ctx, arena);
    case ExprKind::kSelect:
      return EvalSelect(expr, ctx, arena);
    case ExprKind::kSystemCall:
      return EvalSystemCall(expr, ctx, arena);
    case ExprKind::kCall:
      return EvalFunctionCall(expr, ctx, arena);
    case ExprKind::kPostfixUnary:
      return EvalPostfixUnary(expr, ctx, arena);
    case ExprKind::kMemberAccess:
      return EvalMemberAccess(expr, ctx, arena);
    case ExprKind::kCast:
      return EvalCast(expr, ctx, arena);
    case ExprKind::kInside:
      return EvalInside(expr, ctx, arena);
    case ExprKind::kStreamingConcat:
      return EvalStreamingConcat(expr, ctx, arena);
    case ExprKind::kAssignmentPattern:
      return EvalAssignmentPattern(expr, ctx, arena);
    case ExprKind::kTagged:
      return EvalTaggedExpr(expr, ctx, arena, context_width);
    case ExprKind::kMinTypMax:
      return EvalMinTypMax(expr, ctx, arena, context_width);
    default:
      return MakeLogic4Vec(arena, 1);
  }
}

}  // namespace delta
