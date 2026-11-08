#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/operator_classes.h"
#include "elaborator/system_function_types.h"
#include "elaborator/typename_writer.h"
#include "lexer/token.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"
#include "simulator/eval_function_hier.h"
#include "simulator/eval_function_internal.h"
#include "simulator/eval_member_path.h"
#include "simulator/evaluation.h"
#include "simulator/evaluation_internal.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"
#include "simulator/variable.h"

namespace delta {

static SelfType ReadSelfType(const Expr* expr, SimContext& ctx) {
  uint32_t width = SimSelfWidth(expr, ctx);
  return {width, SimSelfSigned(expr, ctx), SimSelf4State(expr, ctx), width > 0};
}

static bool HoldsIntegralValue(DataTypeKind kind) {
  static constexpr std::array kNonIntegral = {
      DataTypeKind::kReal,   DataTypeKind::kShortreal, DataTypeKind::kRealtime,
      DataTypeKind::kString, DataTypeKind::kChandle,   DataTypeKind::kEvent};
  return std::ranges::find(kNonIntegral, kind) == kNonIntegral.end();
}

static const Variable* PackedVariable(std::string_view name, SimContext& ctx) {
  if (ctx.FindQueue(name) != nullptr || ctx.FindAssocArray(name) != nullptr)
    return nullptr;
  const Variable* var = ctx.FindVariable(name);
  if (var == nullptr || var->is_string || !var->declared_unpacked.empty())
    return nullptr;
  return var;
}

static uint64_t SelectedCount(const Expr* expr, SimContext& ctx) {
  if (expr->index_end == nullptr) return 1;
  Arena& arena = ctx.GetArena();
  auto end =
      static_cast<int64_t>(EvalExpr(expr->index_end, ctx, arena).ToUint64());
  if (expr->is_part_select_plus || expr->is_part_select_minus)
    return static_cast<uint64_t>(end);
  auto start =
      static_cast<int64_t>(EvalExpr(expr->index, ctx, arena).ToUint64());
  return static_cast<uint64_t>(std::abs(start - end) + 1);
}

static SelfType SelectSelfType(const Expr* expr, SimContext& ctx) {
  if (expr->base->kind != ExprKind::kIdentifier) return {};
  std::string_view name = expr->base->text;
  if (const ArrayInfo* array = ctx.FindArrayInfo(name)) {
    if (expr->index_end != nullptr || !array->dim_sizes.empty() ||
        !HoldsIntegralValue(array->elem_type_kind))
      return {};
    return {array->elem_width, array->elem_is_signed.value_or(true),
            array->is_4state, true};
  }
  const Variable* var = PackedVariable(name, ctx);
  if (var == nullptr) return {};
  uint64_t element = std::max(var->packed_elem_width, 1u);
  auto width = static_cast<uint32_t>(
      std::min<uint64_t>(SelectedCount(expr, ctx) * element, var->value.width));
  return {width, false, var->is_4state, width > 0};
}

static SelfType MemberSelfType(const Expr* expr, SimContext& ctx) {
  const StructFieldInfo* field = ResolveStructMember(expr, ctx);
  if (field == nullptr || !HoldsIntegralValue(field->type_kind)) return {};
  return {field->width, field->is_signed, !MemberIsTwoState(*field, ctx), true};
}

static SelfType ConcatenationSelfType(const Expr* expr, SimContext& ctx) {
  uint32_t width = 0;
  bool four_state = false;
  for (const Expr* element : expr->elements) {
    SelfType part = ReadSelfType(element, ctx);
    if (!part.known) return {};
    width += part.width;
    four_state = four_state || part.four_state;
  }
  return {width, false, four_state, width > 0};
}

static SelfType ReplicationSelfType(const Expr* expr, SimContext& ctx) {
  SelfType copy = ConcatenationSelfType(expr, ctx);
  auto count = static_cast<uint32_t>(
      EvalExpr(expr->repeat_count, ctx, ctx.GetArena()).ToUint64());
  uint32_t width = copy.width * count;
  return {width, false, copy.four_state, width > 0};
}

static SelfType CallSelfType(const Expr* expr, SimContext& ctx) {
  const ModuleItem* func = FindSubroutineTarget(expr, ctx, ctx.GetArena()).func;
  if (func == nullptr || DeclaredTypeIsReal(func->return_type, ctx)) return {};
  const DataType& type = func->return_type;
  uint32_t width = DeclaredTypeWidth(type, ctx);
  return {width, DeclaredTypeIsSigned(type, ctx),
          DeclaredTypeIs4State(type, ctx), width > 0};
}

static SelfType SystemCallSelfType(const Expr* expr, SimContext& ctx) {
  for (const SystemFunctionType& listed : kSystemFunctionTypes) {
    if (listed.name == expr->callee) return listed.type;
  }
  const bool kSigned = expr->callee == "$signed";
  const bool kResigned = kSigned || expr->callee == "$unsigned";
  if (expr->args.empty() ||
      (!kResigned && std::ranges::find(kArgumentTypedFunctions, expr->callee) ==
                         kArgumentTypedFunctions.end()))
    return {};
  SelfType arg = ReadSelfType(expr->args[0], ctx);
  if (kResigned) arg.is_signed = kSigned;
  return arg;
}

static SelfType OperandSelfType(const Expr* expr, SimContext& ctx) {
  switch (expr->kind) {
    case ExprKind::kSelect:
      return SelectSelfType(expr, ctx);
    case ExprKind::kMemberAccess:
      return MemberSelfType(expr, ctx);
    case ExprKind::kConcatenation:
      return ConcatenationSelfType(expr, ctx);
    case ExprKind::kReplicate:
      return ReplicationSelfType(expr, ctx);
    case ExprKind::kCall:
      return CallSelfType(expr, ctx);
    case ExprKind::kSystemCall:
      return SystemCallSelfType(expr, ctx);
    case ExprKind::kCast:
      return CastSelfType(expr, ctx);
    default:
      return {};
  }
}

static bool OperandIsSigned(const Expr* expr, SimContext& ctx) {
  SelfType type = OperandSelfType(expr, ctx);
  return !type.known || type.is_signed;
}

static bool OperandIs4State(const Expr* expr, SimContext& ctx) {
  SelfType type = OperandSelfType(expr, ctx);
  return !type.known || type.four_state;
}

uint32_t SimSelfWidth(const Expr* expr, SimContext& ctx) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return LiteralWidth(expr->text, expr->int_val);
    case ExprKind::kUnbasedUnsizedLiteral:
      return 1;
    case ExprKind::kIdentifier: {
      auto* var = ctx.FindVariable(expr->text);
      return var ? var->value.width : 0;
    }
    case ExprKind::kUnary:
      if (expr->op == TokenKind::kBang || IsUnaryReductionOp(expr->op))
        return 1;
      return SimSelfWidth(expr->lhs, ctx);
    case ExprKind::kBinary:
      if (IsMaxWidthBinaryOp(expr->op))
        return std::max(SimSelfWidth(expr->lhs, ctx),
                        SimSelfWidth(expr->rhs, ctx));
      if (IsLeftWidthBinaryOp(expr->op)) return SimSelfWidth(expr->lhs, ctx);
      return 1;
    case ExprKind::kTernary:
      return std::max(SimSelfWidth(expr->true_expr, ctx),
                      SimSelfWidth(expr->false_expr, ctx));
    default:
      return OperandSelfType(expr, ctx).width;
  }
}

bool SimSelfSigned(const Expr* expr, SimContext& ctx) {
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return IsSignedLiteral(expr->text);
    case ExprKind::kIdentifier: {
      const Variable* var = ctx.FindVariable(expr->text);
      return var == nullptr || var->is_signed || var->is_real;
    }
    case ExprKind::kUnary:
      return expr->op != TokenKind::kBang && !IsUnaryReductionOp(expr->op) &&
             SimSelfSigned(expr->lhs, ctx);
    case ExprKind::kBinary:
      if (IsMaxWidthBinaryOp(expr->op))
        return SimSelfSigned(expr->lhs, ctx) && SimSelfSigned(expr->rhs, ctx);
      return IsLeftWidthBinaryOp(expr->op) && SimSelfSigned(expr->lhs, ctx);
    case ExprKind::kTernary:
      return SimSelfSigned(expr->true_expr, ctx) &&
             SimSelfSigned(expr->false_expr, ctx);
    case ExprKind::kConcatenation:
      return false;
    default:
      return OperandIsSigned(expr, ctx);
  }
}

bool SimSelfReal(const Expr* expr, SimContext& ctx) {
  switch (expr->kind) {
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return true;
    case ExprKind::kSystemCall:
      return std::ranges::find(kRealSystemFunctions, expr->callee) !=
             kRealSystemFunctions.end();
    case ExprKind::kIdentifier: {
      const Variable* var = ctx.FindVariable(expr->text);
      return var != nullptr && var->is_real;
    }
    case ExprKind::kBinary:
      return IsMaxWidthBinaryOp(expr->op) &&
             (SimSelfReal(expr->lhs, ctx) || SimSelfReal(expr->rhs, ctx));
    case ExprKind::kTernary:
      return SimSelfReal(expr->true_expr, ctx) ||
             SimSelfReal(expr->false_expr, ctx);
    default:
      return false;
  }
}

bool SimSelf4State(const Expr* expr, SimContext& ctx) {
  switch (expr->kind) {
    case ExprKind::kIdentifier: {
      const Variable* var = ctx.FindVariable(expr->text);
      return var == nullptr || var->is_4state;
    }
    case ExprKind::kUnary:
      return SimSelf4State(expr->lhs, ctx);
    case ExprKind::kBinary:
      return SimSelf4State(expr->lhs, ctx) || SimSelf4State(expr->rhs, ctx);
    case ExprKind::kTernary:
      return SimSelf4State(expr->condition, ctx) ||
             SimSelf4State(expr->true_expr, ctx) ||
             SimSelf4State(expr->false_expr, ctx);
    default:
      return OperandIs4State(expr, ctx);
  }
}

}  // namespace delta
