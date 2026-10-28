// §11.6.1 and §11.8.1: the self-determined length and signedness of an
// expression as its form gives them, which the context-determined evaluators
// in evaluation.cpp and eval_ternary.cpp size and sign their operands by
// (§11.8.2), by the classes of operator elaborator/operator_classes.h names;
// and §11.3.4's 2- or 4-state nature of it, which a cast to a type reference
// (§6.23) takes.

#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "elaborator/operator_classes.h"
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

// The three readers below answer about `expr` together; unknown where its
// width is.
static SelfType ReadSelfType(const Expr* expr, SimContext& ctx) {
  uint32_t width = SimSelfWidth(expr, ctx);
  return {width, SimSelfSigned(expr, ctx), SimSelf4State(expr, ctx), width > 0};
}

// Whether a value of `kind` is integral (§6.11.1), which the readers here
// size: not a real, a string, a chandle or an event.
static bool HoldsIntegralValue(DataTypeKind kind) {
  static constexpr std::array kNonIntegral = {
      DataTypeKind::kReal,   DataTypeKind::kShortreal, DataTypeKind::kRealtime,
      DataTypeKind::kString, DataTypeKind::kChandle,   DataTypeKind::kEvent};
  return std::ranges::find(kNonIntegral, kind) == kNonIntegral.end();
}

// The variable named `name` where a select addresses its bits as a packed
// vector (§7.4.1); null for a string, of which a select reads a byte (§6.16),
// and for an unpacked array, a queue or an associative array, of which it
// reads an element.
static const Variable* PackedVariable(std::string_view name, SimContext& ctx) {
  if (ctx.FindQueue(name) != nullptr || ctx.FindAssocArray(name) != nullptr)
    return nullptr;
  const Variable* var = ctx.FindVariable(name);
  if (var == nullptr || var->is_string || !var->declared_unpacked.empty())
    return nullptr;
  return var;
}

// §11.5.1: the number of elements a select names -- one for an index, the
// width of an indexed part-select, or the span of a part-select's bounds.
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

// §11.5.1 with §7.4.1 and §11.8.1: a select of a packed variable is as many of
// its outermost elements as it names, each one bit for a plain vector, never
// wider than the variable; it is unsigned, and 2- or 4-state as the variable
// is. An element of an unpacked array of one dimension has the array's
// element type (§7.4.2) where that is integral. Unknown for a slice or a
// select of anything else.
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

// §7.2: a member of a structure has the type its member was declared with,
// 2-state where that type is (§7.2.1); unknown where that type is not
// integral.
static SelfType MemberSelfType(const Expr* expr, SimContext& ctx) {
  const StructFieldInfo* field = ResolveStructMember(expr, ctx);
  if (field == nullptr || !HoldsIntegralValue(field->type_kind)) return {};
  return {field->width, field->is_signed, !MemberIsTwoState(*field, ctx), true};
}

// §11.4.12: a concatenation is unsigned, as wide as its operands together and
// 4-state where one of them is; unknown where an operand's width is.
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

// §11.4.12.1: a replication is its count of copies of its operands'
// concatenation.
static SelfType ReplicationSelfType(const Expr* expr, SimContext& ctx) {
  SelfType copy = ConcatenationSelfType(expr, ctx);
  auto count = static_cast<uint32_t>(
      EvalExpr(expr->repeat_count, ctx, ctx.GetArena()).ToUint64());
  uint32_t width = copy.width * count;
  return {width, false, copy.four_state, width > 0};
}

// §13.4.1: a call of a function has the type it returns, read from its
// declaration without calling it; unknown for a real or a type nothing sizes.
static SelfType CallSelfType(const Expr* expr, SimContext& ctx) {
  const ModuleItem* func = FindSubroutineTarget(expr, ctx, ctx.GetArena()).func;
  if (func == nullptr || DeclaredTypeIsReal(func->return_type, ctx)) return {};
  const DataType& type = func->return_type;
  uint32_t width = DeclaredTypeWidth(type, ctx);
  return {width, DeclaredTypeIsSigned(type, ctx),
          DeclaredTypeIs4State(type, ctx), width > 0};
}

// §11.7: $signed and $unsigned are their argument's bits with the signing
// each names; §20.6.2: $bits is an integer. Unknown for any other system
// function.
static SelfType SystemCallSelfType(const Expr* expr, SimContext& ctx) {
  if (expr->callee == "$bits") return {32, true, true, true};
  if (expr->args.size() != 1 ||
      (expr->callee != "$signed" && expr->callee != "$unsigned"))
    return {};
  SelfType arg = ReadSelfType(expr->args[0], ctx);
  arg.is_signed = expr->callee == "$signed";
  return arg;
}

// The self-determined type of an operand none of the readers' own cases
// takes, as far as its form says; unknown for a form this does not read.
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

// Whether an operand of a form the readers' own cases do not take is signed:
// as its type says, and signed where that is unknown, which leaves the
// operand's own sign to decide.
static bool OperandIsSigned(const Expr* expr, SimContext& ctx) {
  SelfType type = OperandSelfType(expr, ctx);
  return !type.known || type.is_signed;
}

// Whether such an operand is 4-state: as its type says, and 4-state where
// that is unknown.
static bool OperandIs4State(const Expr* expr, SimContext& ctx) {
  SelfType type = OperandSelfType(expr, ctx);
  return !type.known || type.four_state;
}

// §11.6.1: the self-determined bit length of an expression, resolving variable
// widths through the simulation context. Returns 0 ("indeterminate") for a
// form whose width this cannot read; callers treat 0 as "do not force-widen",
// so such an operand keeps its own evaluated width and the result is left
// unchanged.
uint32_t SimSelfWidth(const Expr* expr, SimContext& ctx) {
  if (!expr) return 0;
  switch (expr->kind) {
    case ExprKind::kIntegerLiteral:
      return LiteralWidth(expr->text, expr->int_val);
    case ExprKind::kUnbasedUnsizedLiteral:
      return 1;  // §5.7.1: one bit where self-determined
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
      return 1;  // comparison / equality / logical -> one-bit result
    case ExprKind::kTernary:
      return std::max(SimSelfWidth(expr->true_expr, ctx),
                      SimSelfWidth(expr->false_expr, ctx));
    default:
      return OperandSelfType(expr, ctx).width;
  }
}

// §11.8.1: whether an expression's self-determined type is signed, as far as
// its form says. A literal is signed by its base, a name by its declared type,
// an arithmetic or bitwise operator where both its operands are, a unary
// operator and a shift or power by the operand they size from, and a
// conditional where both its results are. A comparison, a logical operator, a
// reduction, a concatenation and a select of a packed vector are unsigned. A
// form this does not read, and a real value, answer signed, which leaves the
// operand's own sign to decide.
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

// §11.4.11 with §6.12: whether an expression's self-determined type is real,
// as its form says: a real or time literal, a real variable, and an operator
// one of whose operands it takes its type from is.
bool SimSelfReal(const Expr* expr, SimContext& ctx) {
  switch (expr->kind) {
    case ExprKind::kRealLiteral:
    case ExprKind::kTimeLiteral:
      return true;
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

// §11.3.4: whether an expression's self-determined type is 4-state, as its
// form says. An operator applied to 2-state operands only gives a 2-state
// result, so a name is 4-state by its declared type, an operator and a
// conditional where any operand they read is, the condition included, and an
// operand of another form by its own type; a form this does not read, a
// literal among them, is 4-state.
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
