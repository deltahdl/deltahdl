#include "simulator/evaluation.h"

#include <algorithm>
#include <cstdint>
#include <cstring>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/operator_classes.h"
#include "elaborator/type_eval.h"
#include "lexer/token.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_type.h"
#include "simulator/class_object.h"
#include "simulator/class_specialization.h"
#include "simulator/clocking.h"
#include "simulator/eval_array_compare.h"
#include "simulator/eval_function_args_scoped.h"
#include "simulator/eval_instance_task.h"
#include "simulator/evaluation_internal.h"
#include "simulator/instance_bindings.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/statement_assign.h"
#include "simulator/statement_assign_internal.h"
#include "simulator/sva_engine_sampling.h"
#include "simulator/virtual_interface.h"

namespace delta {
static bool DeclaresValueParam(const ClassDecl* decl, std::string_view name) {
  if (decl == nullptr) return false;
  for (const auto& [pname, pexpr] : decl->params) {
    if (pname == name) return decl->type_param_names.count(name) == 0;
  }
  return false;
}

static Logic4Vec EvalIdentifierClassScope(const Expr* expr, SimContext& ctx,
                                          Arena& arena) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  auto* self = ctx.CurrentThis();
  if (self != nullptr && method_cls != nullptr &&
      DeclaresValueParam(method_cls->decl, expr->text)) {
    auto it = self->properties.find(std::string(expr->text));
    if (it != self->properties.end()) return it->second;
  }
  const ClassTypeInfo* owner =
      method_cls ? method_cls->StaticPropertyOwner(expr->text) : nullptr;
  if (owner)
    return owner->static_properties.find(std::string(expr->text))->second;
  const ClassTypeInfo* scope = method_cls ? method_cls
                               : self     ? self->type
                                          : nullptr;
  Logic4Vec literal;
  if (TryClassScopeEnumLiteral(expr->text, scope, arena, literal))
    return literal;
  if (TryEvalParenFreeMethodCall(expr, ctx, arena, literal)) return literal;
  if (!self) return MakeLogic4Vec(arena, 1);
  if (method_cls)
    return self->GetPropertyForType(expr->text, method_cls, arena);
  return self->GetProperty(expr->text, arena);
}

bool ClassScopeDeclares(std::string_view name, SimContext& ctx) {
  const ClassTypeInfo* method_cls = ctx.CurrentMethodClass();
  if (method_cls != nullptr && method_cls->StaticPropertyOwner(name) != nullptr)
    return true;
  const ClassObject* self = ctx.CurrentThis();
  const ClassTypeInfo* scope = method_cls != nullptr ? method_cls
                               : self != nullptr     ? self->type
                                                     : nullptr;
  return scope != nullptr && scope->FindProperty(name) != nullptr;
}

bool NameDenotesVariable(std::string_view name, SimContext& ctx) {
  if (ctx.FindVariable(name) == nullptr) return false;
  if (ctx.FindLocalVariable(name) != nullptr) return true;
  return !ClassScopeDeclares(name, ctx);
}

static bool TryInterfaceInstanceHandle(std::string_view name, SimContext& ctx,
                                       Arena& arena, Logic4Vec& out) {
  if (ClassScopeDeclares(name, ctx)) return false;
  std::string scope = ctx.ResolveInstanceScope(name);
  if (scope.empty()) return false;
  out = MakeLogic4VecVal(arena, 64, ctx.VirtualInterfaceHandle(scope));
  return true;
}

static const Logic4Vec* BoundInstanceValue(const Expr* expr, SimContext& ctx) {
  const InstanceBindings* bindings = ctx.AssertionSamples().Bindings();
  return bindings == nullptr ? nullptr : bindings->Find(expr);
}

static void MarkDeclaredKinds(Logic4Vec& val, std::string_view name,
                              const Variable& var, SimContext& ctx) {
  if (var.is_real || ctx.IsRealVariable(name)) val.is_real = true;
  if (ctx.IsStringVariable(name)) val.is_string = true;
}

static Logic4Vec EvalMemberAccessOrCall(const Expr* expr, SimContext& ctx,
                                        Arena& arena) {
  Logic4Vec call;
  if (TryEvalParenFreeMethodCall(expr, ctx, arena, call)) return call;
  return EvalMemberAccess(expr, ctx, arena);
}

static Logic4Vec EvalIdentifier(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  if (expr->text == "this") {
    return MakeLogic4VecVal(arena, 64, ctx.CurrentThisHandle());
  }
  std::string scoped_name = IdentifierLookupKey(expr);
  std::string_view lookup_name = scoped_name;
  std::string kinds_name = DeclaredKindsKey(expr);
  auto* var = NameDenotesVariable(lookup_name, ctx)
                  ? ctx.FindVariable(lookup_name)
                  : nullptr;
  if (!var) {
    if (auto* let_decl = FindVisibleLet(ctx, expr->text);
        let_decl && let_decl->func_args.empty()) {
      return EvalLetExpansion(let_decl, expr, ctx, arena);
    }
    Logic4Vec instance;
    if (TryInterfaceInstanceHandle(expr->text, ctx, arena, instance))
      return instance;
    return EvalIdentifierClassScope(expr, ctx, arena);
  }
  if (var->is_event) {
    return MakeLogic4VecVal(
        arena, 64, var->is_null_event ? 0 : ctx.RegisterEventIdentity(var));
  }
  auto val = var->value;
  const Logic4Vec* sampled =
      ctx.AssertionSamples().ReadWithinProperty(var, ctx.CurrentTime());
  if (sampled != nullptr && !TryCheckerFormalClockvar(var, ctx, arena, val)) {
    val = *sampled;
  }
  MarkDeclaredKinds(val, kinds_name, *var, ctx);
  val.is_signed = var->is_signed;
  val.fills_width = false;
  return val;
}
bool HasUnknownBits(const Logic4Vec& v) {
  for (uint32_t i = 0; i < v.nwords; ++i) {
    if (v.words[i].bval != 0) return true;
  }
  return false;
}
Logic4Vec MakeAllX(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  FillWithX(vec);
  return vec;
}

Logic4Vec MakeAllHighZ(Arena& arena, uint32_t width) {
  auto vec = MakeLogic4Vec(arena, width);
  for (uint32_t i = 0; i < vec.nwords; ++i) {
    vec.words[i] = {0, WordMaskWithinWidth(width, i)};
  }
  return vec;
}

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

static Logic4Vec EvalConcat(const Expr* expr, SimContext& ctx, Arena& arena) {
  uint32_t total_width = 0;
  bool any_string = false;
  std::vector<Logic4Vec> parts;
  for (auto* elem : expr->elements) {
    parts.push_back(EvalExpr(elem, ctx, arena));
    if (parts.back().is_string) any_string = true;
    total_width += parts.back().width;
  }
  if (total_width == 0) return MakeLogic4Vec(arena, 1);
  auto result = AssembleConcatParts(parts, total_width, arena);
  result.is_string = any_string;
  return result;
}

static Logic4Vec EvalAssignInExpr(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  auto rhs_val = EvalExpr(expr->rhs, ctx, arena);
  PerformBlockingAssign(expr->lhs, rhs_val, ctx, arena);
  return EvalExpr(expr->lhs, ctx, arena);
}

static bool ArrayElementsEqual(std::string_view a, const ArrayInfo* ai,
                               std::string_view b, SimContext& ctx) {
  if (ai->dim_sizes.size() >= 2) {
    for (const std::string& leaf : MultiDimLeafSuffixes(*ai)) {
      auto* av = ctx.FindVariable(std::string(a) + leaf);
      auto* bv = ctx.FindVariable(std::string(b) + leaf);
      if (!av || !bv || av->value.ToUint64() != bv->value.ToUint64())
        return false;
    }
    return true;
  }
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
  if (TryArrayPatternEquality(expr, ctx, arena, out)) return true;
  if (TryDynamicStructEquality(expr, ctx, arena, out)) return true;
  if (expr->op != TokenKind::kEqEq && expr->op != TokenKind::kBangEq)
    return false;
  if (!expr->lhs || !expr->rhs) return false;
  if (expr->lhs->kind != ExprKind::kIdentifier) return false;
  if (expr->rhs->kind != ExprKind::kIdentifier) return false;
  auto* la = ctx.FindArrayInfo(expr->lhs->text);
  auto* ra = ctx.FindArrayInfo(expr->rhs->text);
  if (!la || !ra) return false;
  bool eq = (la->size == ra->size && la->elem_width == ra->elem_width &&
             la->dim_sizes == ra->dim_sizes);
  if (eq) eq = ArrayElementsEqual(expr->lhs->text, la, expr->rhs->text, ctx);
  uint64_t val = (expr->op == TokenKind::kEqEq) == eq ? 1 : 0;
  out = MakeLogic4VecVal(arena, 1, val);
  return true;
}

static Logic4Vec EvalLogicalAnd(const Expr* expr, SimContext& ctx,
                                Arena& arena) {
  const Truth kLeft = TruthOf(EvalExpr(expr->lhs, ctx, arena));
  if (kLeft == Truth::kFalse) return TruthBit(Truth::kFalse, arena);
  const Truth kRight = TruthOf(EvalExpr(expr->rhs, ctx, arena));
  if (kRight == Truth::kFalse) return TruthBit(Truth::kFalse, arena);
  return TruthBit(kLeft == Truth::kTrue && kRight == Truth::kTrue
                      ? Truth::kTrue
                      : Truth::kAmbiguous,
                  arena);
}

static Logic4Vec EvalLogicalOr(const Expr* expr, SimContext& ctx,
                               Arena& arena) {
  const Truth kLeft = TruthOf(EvalExpr(expr->lhs, ctx, arena));
  if (kLeft == Truth::kTrue) return TruthBit(Truth::kTrue, arena);
  const Truth kRight = TruthOf(EvalExpr(expr->rhs, ctx, arena));
  if (kRight == Truth::kTrue) return TruthBit(Truth::kTrue, arena);
  return TruthBit(kLeft == Truth::kFalse && kRight == Truth::kFalse
                      ? Truth::kFalse
                      : Truth::kAmbiguous,
                  arena);
}

static Logic4Vec EvalLogicalImpl(const Expr* expr, SimContext& ctx,
                                 Arena& arena) {
  const Truth kLeft = TruthOf(EvalExpr(expr->lhs, ctx, arena));
  if (kLeft == Truth::kFalse) return TruthBit(Truth::kTrue, arena);
  const Truth kRight = TruthOf(EvalExpr(expr->rhs, ctx, arena));
  if (kRight == Truth::kTrue) return TruthBit(Truth::kTrue, arena);
  return TruthBit(kLeft == Truth::kTrue && kRight == Truth::kFalse
                      ? Truth::kFalse
                      : Truth::kAmbiguous,
                  arena);
}

static Logic4Vec EvalLogicalEquiv(const Expr* expr, SimContext& ctx,
                                  Arena& arena) {
  const Truth kLeft = TruthOf(EvalExpr(expr->lhs, ctx, arena));
  const Truth kRight = TruthOf(EvalExpr(expr->rhs, ctx, arena));
  if (kLeft == Truth::kAmbiguous || kRight == Truth::kAmbiguous)
    return TruthBit(Truth::kAmbiguous, arena);
  return TruthBit(kLeft == kRight ? Truth::kTrue : Truth::kFalse, arena);
}
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

static Logic4Vec EvalVirtualInterfaceEquality(const Expr* expr, bool is_eq_op,
                                              SimContext& ctx, Arena& arena) {
  bool equal = VirtualInterfaceOperandHandle(expr->lhs, ctx, arena) ==
               VirtualInterfaceOperandHandle(expr->rhs, ctx, arena);
  return MakeLogic4VecVal(arena, 1, (is_eq_op == equal) ? 1u : 0u);
}

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
    out = EvalVirtualInterfaceEquality(expr, ops.is_eq_op, ctx, arena);
    return true;
  }
  return false;
}

static bool IsSizedComparisonOp(TokenKind op) {
  using enum TokenKind;
  return op == kEqEq || op == kBangEq || op == kEqEqEq || op == kBangEqEq ||
         op == kEqEqQuestion || op == kBangEqQuestion || op == kLt ||
         op == kLtEq || op == kGt || op == kGtEq;
}

static Logic4Vec EvalSizedComparison(const Expr* expr, SimContext& ctx,
                                     Arena& arena) {
  uint32_t w =
      std::max(SimSelfWidth(expr->lhs, ctx), SimSelfWidth(expr->rhs, ctx));
  Logic4Vec l = EvalExpr(expr->lhs, ctx, arena, w);
  Logic4Vec r = EvalExpr(expr->rhs, ctx, arena, w);
  bool plain = !l.is_real && !r.is_real && !l.is_string && !r.is_string;
  if (plain) {
    bool sign = l.is_signed && r.is_signed;
    if (l.width < w) l = ExtendVec(l, w, sign, arena);
    if (r.width < w) r = ExtendVec(r, w, sign, arena);
  }
  return EvalBinaryOp(expr->op, l, r, arena, 0);
}

static Logic4Vec EvalContextDeterminedBinary(const Expr* expr, SimContext& ctx,
                                             Arena& arena,
                                             uint32_t context_width,
                                             bool unsigned_context) {
  if (IsMaxWidthBinaryOp(expr->op)) {
    uint32_t w = std::max({context_width, SimSelfWidth(expr->lhs, ctx),
                           SimSelfWidth(expr->rhs, ctx)});
    const bool kUnsigned = unsigned_context || !SimSelfSigned(expr->lhs, ctx) ||
                           !SimSelfSigned(expr->rhs, ctx);
    Logic4Vec lhs = EvalExprInContext(expr->lhs, ctx, arena, w, kUnsigned);
    Logic4Vec rhs = EvalExprInContext(expr->rhs, ctx, arena, w, kUnsigned);
    if (kUnsigned && !lhs.is_real && !rhs.is_real) {
      lhs.is_signed = false;
      rhs.is_signed = false;
    }
    return EvalBinaryOp(expr->op, lhs, rhs, arena, context_width);
  }
  if (IsLeftWidthBinaryOp(expr->op)) {
    uint32_t w = std::max(context_width, SimSelfWidth(expr->lhs, ctx));
    Logic4Vec lhs =
        EvalExprInContext(expr->lhs, ctx, arena, w, unsigned_context);
    if (unsigned_context && !lhs.is_real) lhs.is_signed = false;
    if (!lhs.is_real && lhs.width < w) lhs = ResizeToWidth(lhs, w, arena);
    return EvalBinaryOp(expr->op, lhs, EvalExpr(expr->rhs, ctx, arena), arena,
                        context_width);
  }
  if (IsSizedComparisonOp(expr->op))
    return EvalSizedComparison(expr, ctx, arena);
  return EvalBinaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena),
                      EvalExpr(expr->rhs, ctx, arena), arena, context_width);
}

struct TypeRefRuntimeId {
  std::string_view name;
  bool is_class = false;
  bool resolved = false;
};

static TypeRefRuntimeId ResolveTypeRefRuntimeId(const Expr* op,
                                                SimContext& ctx) {
  TypeRefRuntimeId id;
  if (!op || op->kind != ExprKind::kTypeRef) return id;
  if (op->lhs && op->lhs->kind == ExprKind::kIdentifier) {
    std::string_view name = op->lhs->text;
    if (name == "this") {
      const ClassTypeInfo* cls = ctx.CurrentMethodClass();
      if (!cls) return id;
      id.name = cls->name;
      id.is_class = true;
      id.resolved = true;
      return id;
    }
    id.name = name;
    id.is_class = ctx.FindClassType(name) != nullptr;
    id.resolved = true;
    return id;
  }
  if (!op->text.empty()) {
    id.name = op->text;
    ClassTypeInfo* cls = ctx.FindClassType(op->text);
    id.is_class = cls != nullptr;
    id.resolved = true;
    if (cls != nullptr && op->type_value != nullptr &&
        !op->type_value->type_params.empty()) {
      id.name = SpecializationOf(cls, op->type_value->type_params, ctx,
                                 ctx.GetArena())
                    ->name;
    }
  }
  return id;
}

static bool IsTypeRef(const Expr* operand) {
  return operand != nullptr && operand->kind == ExprKind::kTypeRef;
}

static bool TryTypeRefComparison(const Expr* expr, SimContext& ctx,
                                 Arena& arena, Logic4Vec& out) {
  bool is_eq = expr->op == TokenKind::kEqEq || expr->op == TokenKind::kEqEqEq;
  bool is_neq =
      expr->op == TokenKind::kBangEq || expr->op == TokenKind::kBangEqEq;
  if (!is_eq && !is_neq) return false;
  if (!IsTypeRef(expr->lhs) || !IsTypeRef(expr->rhs)) return false;
  if (std::optional<bool> holds = ctx.TypeRefCompareHere(expr)) {
    out = MakeLogic4VecVal(arena, 1, *holds ? 1 : 0);
    return true;
  }
  TypeRefRuntimeId a = ResolveTypeRefRuntimeId(expr->lhs, ctx);
  TypeRefRuntimeId b = ResolveTypeRefRuntimeId(expr->rhs, ctx);
  if (!a.resolved || !b.resolved) return false;
  bool matched = a.is_class == b.is_class && a.name == b.name;
  bool result = is_eq ? matched : !matched;
  out = MakeLogic4VecVal(arena, 1, result ? 1 : 0);
  return true;
}

static Logic4Vec EvalBinaryExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                                uint32_t context_width, bool unsigned_context) {
  if (expr->op == TokenKind::kEq) return EvalAssignInExpr(expr, ctx, arena);
  {
    Logic4Vec type_ref_result;
    if (TryTypeRefComparison(expr, ctx, arena, type_ref_result))
      return type_ref_result;
  }
  {
    Logic4Vec arr_result;
    if (TryArrayEqualityOp(expr, ctx, arena, arr_result)) return arr_result;
  }
  if (expr->op == TokenKind::kAmpAmp) return EvalLogicalAnd(expr, ctx, arena);

  if (expr->op == TokenKind::kAmpAmpAmp) {
    Truth first = TruthOf(EvalExpr(expr->lhs, ctx, arena));
    if (first == Truth::kFalse) return TruthBit(first, arena);
    return TruthBit(
        ClauseConjunction(first, TruthOf(EvalExpr(expr->rhs, ctx, arena))),
        arena);
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
  return EvalContextDeterminedBinary(expr, ctx, arena, context_width,
                                     unsigned_context);
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

static Logic4Vec EvalUnaryExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                               uint32_t context_width, bool unsigned_context) {
  if (expr->op == TokenKind::kPlusPlus || expr->op == TokenKind::kMinusMinus) {
    return EvalPrefixUnary(expr, ctx, arena);
  }
  if (expr->op == TokenKind::kBang || IsUnaryReductionOp(expr->op) ||
      context_width == 0) {
    return EvalUnaryOp(expr->op, EvalExpr(expr->lhs, ctx, arena), arena);
  }
  uint32_t width = std::max(context_width, SimSelfWidth(expr->lhs, ctx));
  Logic4Vec operand =
      EvalExprInContext(expr->lhs, ctx, arena, width, unsigned_context);
  if (unsigned_context && !operand.is_real) operand.is_signed = false;
  if (!operand.is_real && operand.width < width)
    operand = ExtendVec(operand, width, operand.is_signed, arena);
  return EvalUnaryOp(expr->op, operand, arena);
}

static Logic4Vec EvalBinaryDispatch(const Expr* expr, SimContext& ctx,
                                    Arena& arena, uint32_t context_width,
                                    bool unsigned_context) {
  if (IsCompoundAssignOp(expr->op)) {
    return EvalCompoundAssign(expr, ctx, arena);
  }
  if (expr->op == TokenKind::kKwMatches) {
    return EvalMatches(expr, ctx, arena);
  }
  return EvalBinaryExpr(expr, ctx, arena, context_width, unsigned_context);
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
  if (context_width > 0 && result.width > context_width) {
    result = ResizeToWidth(result, context_width, arena);
  }
  return result;
}

Logic4Vec FillUnbasedUnsized(const Logic4Vec& v, uint32_t width, Arena& arena) {
  uint64_t af = (v.nwords > 0 && (v.words[0].aval & 1)) ? ~uint64_t{0} : 0;
  uint64_t bf = (v.nwords > 0 && (v.words[0].bval & 1)) ? ~uint64_t{0} : 0;
  auto out = MakeLogic4Vec(arena, width);
  for (uint32_t w = 0; w < out.nwords; ++w) {
    out.words[w].aval = af;
    out.words[w].bval = bf;
  }
  uint32_t rem = width % 64;
  if (rem != 0 && out.nwords > 0) {
    uint64_t mask = (uint64_t{1} << rem) - 1;
    out.words[out.nwords - 1].aval &= mask;
    out.words[out.nwords - 1].bval &= mask;
  }
  return out;
}

static Logic4Vec EvalCallInContext(const Expr* expr, SimContext& ctx,
                                   Arena& arena, uint32_t context_width) {
  const uint32_t kOuter = SetCallContextWidth(context_width);
  Logic4Vec result = EvalFunctionCall(expr, ctx, arena);
  SetCallContextWidth(kOuter);
  return result;
}

Logic4Vec EvalExpr(const Expr* expr, SimContext& ctx, Arena& arena,
                   uint32_t context_width) {
  return EvalExprInContext(expr, ctx, arena, context_width, false);
}

Logic4Vec EvalExprInContext(const Expr* expr, SimContext& ctx, Arena& arena,
                            uint32_t context_width, bool unsigned_context) {
  if (!expr) return MakeLogic4Vec(arena, 1);

  if (const auto* snap = ctx.FindDeferredArgSnapshot(expr)) {
    return *snap;
  }
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return EvalIntLiteral(expr, arena, context_width);
    case ExprKind::kUnbasedUnsizedLiteral: {
      auto v = EvalUnbasedUnsized(expr, arena);
      if (context_width == 0 || context_width == v.width) return v;
      return FillUnbasedUnsized(v, context_width, arena);
    }
    case ExprKind::kStringLiteral:
      return EvalStringLiteral(expr, arena);
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return EvalRealOrTimeLiteral(expr, arena);
    case ExprKind::kIdentifier:
      if (const Logic4Vec* bound = BoundInstanceValue(expr, ctx)) return *bound;
      return EvalIdentifier(expr, ctx, arena);
    case ExprKind::kUnary:
      return EvalUnaryExpr(expr, ctx, arena, context_width, unsigned_context);
    case ExprKind::kBinary:
      return EvalBinaryDispatch(expr, ctx, arena, context_width,
                                unsigned_context);
    case ExprKind::kTernary:
      return EvalTernary(expr, ctx, arena, context_width, unsigned_context);
    case ExprKind::kConcatenation:
      return EvalConcat(expr, ctx, arena);
    case ExprKind::kReplicate:
      return EvalReplicate(expr, ctx, arena);
    case ExprKind::kSelect:
      return EvalSelect(expr, ctx, arena);
    case ExprKind::kSystemCall:
      return EvalSystemCall(expr, ctx, arena);
    case ExprKind::kCall:
      return EvalCallInContext(expr, ctx, arena, context_width);
    case ExprKind::kPostfixUnary:
      return EvalPostfixUnary(expr, ctx, arena);
    case ExprKind::kMemberAccess:
      return EvalMemberAccessOrCall(expr, ctx, arena);
    case ExprKind::kCast:
      if (const Logic4Vec* bound = BoundInstanceValue(expr, ctx)) return *bound;
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
