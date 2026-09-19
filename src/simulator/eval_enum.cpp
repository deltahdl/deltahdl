#include <cstddef>
#include <cstdint>
#include <string>
#include <string_view>

#include "common/arena.h"
#include "common/types.h"
#include "parser/ast_expr.h"
#include "simulator/class_object.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"
#include "simulator/sim_context_types.h"

namespace delta {

bool TryClassScopeEnumLiteral(std::string_view name, const ClassTypeInfo* cls,
                              Arena& arena, Logic4Vec& out) {
  for (; cls != nullptr; cls = cls->parent) {
    auto it = cls->enum_members.find(std::string(name));
    if (it == cls->enum_members.end()) continue;
    out = MakeLogic4VecVal(arena, 32, it->second);
    return true;
  }
  return false;
}

static Logic4Vec EnumFirst(const EnumTypeInfo& info, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  return MakeLogic4VecVal(arena, 32, info.members.front().value);
}

static Logic4Vec EnumLast(const EnumTypeInfo& info, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  return MakeLogic4VecVal(arena, 32, info.members.back().value);
}

static int FindMemberIndex(const EnumTypeInfo& info, uint64_t value) {
  for (size_t i = 0; i < info.members.size(); ++i) {
    if (info.members[i].value == value) return static_cast<int>(i);
  }
  return -1;
}

static Logic4Vec EnumNext(const EnumTypeInfo& info, uint64_t current,
                          uint32_t count, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int idx = FindMemberIndex(info, current);
  if (idx < 0) return MakeLogic4VecVal(arena, 32, info.members.front().value);
  auto n = static_cast<int>(info.members.size());
  int new_idx = (idx + static_cast<int>(count % n)) % n;
  return MakeLogic4VecVal(arena, 32, info.members[new_idx].value);
}

static Logic4Vec EnumPrev(const EnumTypeInfo& info, uint64_t current,
                          uint32_t count, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int idx = FindMemberIndex(info, current);
  if (idx < 0) return MakeLogic4VecVal(arena, 32, info.members.front().value);
  auto n = static_cast<int>(info.members.size());
  int offset = static_cast<int>(count % n);
  int new_idx = ((idx - offset) % n + n) % n;
  return MakeLogic4VecVal(arena, 32, info.members[new_idx].value);
}

static Logic4Vec EnumNum(const EnumTypeInfo& info, Arena& arena) {
  return MakeLogic4VecVal(arena, 32, info.members.size());
}

static Logic4Vec EnumName(const EnumTypeInfo& info, uint64_t current,
                          Arena& arena) {
  for (auto& m : info.members) {
    if (m.value != current) continue;
    auto name = m.name;
    uint32_t width = static_cast<uint32_t>(name.size()) * 8;
    if (width == 0) width = 8;
    auto vec = MakeLogic4Vec(arena, width);
    for (size_t i = 0; i < name.size(); ++i) {
      auto byte_idx = static_cast<uint32_t>(name.size() - 1 - i);
      uint32_t word = (byte_idx * 8) / 64;
      uint32_t bit = (byte_idx * 8) % 64;
      vec.words[word].aval |= static_cast<uint64_t>(name[i]) << bit;
    }
    return vec;
  }

  return MakeLogic4VecVal(arena, 8, 0);
}

static uint32_t ParseStepCount(const Expr* call_expr, SimContext& ctx,
                               Arena& arena) {
  if (call_expr->args.empty()) return 1;
  return static_cast<uint32_t>(
      EvalExpr(call_expr->args[0], ctx, arena).ToUint64());
}

struct EnumMethodArgs {
  const EnumTypeInfo& info;
  uint64_t current;
  const Expr* call_expr;
  SimContext& ctx;
  Arena& arena;
};

static bool DispatchEnumMethod(std::string_view method,
                               const EnumMethodArgs& args, Logic4Vec& out) {
  if (method == "first") {
    out = EnumFirst(args.info, args.arena);
    return true;
  }
  if (method == "last") {
    out = EnumLast(args.info, args.arena);
    return true;
  }
  if (method == "next") {
    uint32_t count = ParseStepCount(args.call_expr, args.ctx, args.arena);
    out = EnumNext(args.info, args.current, count, args.arena);
    return true;
  }
  if (method == "prev") {
    uint32_t count = ParseStepCount(args.call_expr, args.ctx, args.arena);
    out = EnumPrev(args.info, args.current, count, args.arena);
    return true;
  }
  if (method == "num") {
    out = EnumNum(args.info, args.arena);
    return true;
  }
  if (method == "name") {
    out = EnumName(args.info, args.current, args.arena);
    return true;
  }
  return false;
}

void RecordVariableEnumType(std::string_view var_name, const DataType& type,
                            SimContext& ctx) {
  if (type.type_name.empty()) return;
  if (ctx.FindEnumType(type.type_name) == nullptr) return;
  ctx.SetVariableEnumType(var_name, type.type_name);
}

// §6.19.5.1 through §6.19.5.4 give first(), last(), next() and prev() the
// enumeration's own type as their result, so a call written as `e.m()` with
// `e` one of those calls is itself an enum method call on that type.
static bool ReturnsTheEnumType(std::string_view method) {
  return method == "first" || method == "last" || method == "next" ||
         method == "prev";
}

// The enumeration type an expression standing as the base of an enum method
// call carries: a variable declared with the type, or a call of one of the
// methods of §6.19.5 that return the type, whose own base decides it in turn,
// as deep as the chain is written (`s.first().next().name()`).
static const EnumTypeInfo* EnumTypeOfBase(const Expr* base, SimContext& ctx) {
  if (!base) return nullptr;
  if (base->kind == ExprKind::kIdentifier) {
    return ctx.GetVariableEnumType(base->text);
  }
  if (base->kind != ExprKind::kCall) return nullptr;
  const auto* access = base->lhs;
  if (!access || access->kind != ExprKind::kMemberAccess) return nullptr;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier)
    return nullptr;
  if (!ReturnsTheEnumType(access->rhs->text)) return nullptr;
  return EnumTypeOfBase(access->lhs, ctx);
}

// The value the method starts from: the variable's own for a bare name, and
// for a chained call the value that call yields, evaluated through this same
// dispatch.
static uint64_t CurrentValueOfBase(const Expr* base, SimContext& ctx,
                                   Arena& arena) {
  if (base->kind == ExprKind::kIdentifier) {
    auto* var = ctx.FindVariable(base->text);
    return var ? var->value.ToUint64() : 0;
  }
  return EvalExpr(base, ctx, arena).ToUint64();
}

bool TryEvalEnumMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;
  const auto* access = expr->lhs;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;

  const auto* info = EnumTypeOfBase(access->lhs, ctx);
  if (!info) return false;

  uint64_t current = CurrentValueOfBase(access->lhs, ctx, arena);

  EnumMethodArgs args{*info, current, expr, ctx, arena};
  return DispatchEnumMethod(access->rhs->text, args, out);
}

bool TryEvalEnumProperty(std::string_view var_name, std::string_view method,
                         SimContext& ctx, Arena& arena, Logic4Vec& out) {
  const auto* info = ctx.GetVariableEnumType(var_name);
  if (!info) return false;

  auto* var = ctx.FindVariable(var_name);
  uint64_t current = var ? var->value.ToUint64() : 0;

  if (method == "first") {
    out = EnumFirst(*info, arena);
    return true;
  }
  if (method == "last") {
    out = EnumLast(*info, arena);
    return true;
  }
  if (method == "next") {
    out = EnumNext(*info, current, 1, arena);
    return true;
  }
  if (method == "prev") {
    out = EnumPrev(*info, current, 1, arena);
    return true;
  }
  if (method == "num") {
    out = EnumNum(*info, arena);
    return true;
  }
  return false;
}

}  // namespace delta
