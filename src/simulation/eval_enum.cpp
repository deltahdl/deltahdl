#include <string>
#include <string_view>

#include "common/arena.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

namespace delta {

// §6.19.5.1: first() — returns the value of the first enum member.
static Logic4Vec EnumFirst(const EnumTypeInfo& info, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  return MakeLogic4VecVal(arena, 32, info.members.front().value);
}

// §6.19.5.2: last() — returns the value of the last enum member.
static Logic4Vec EnumLast(const EnumTypeInfo& info, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  return MakeLogic4VecVal(arena, 32, info.members.back().value);
}

// Find the index of the member with the given value, or -1 if not found.
static int FindMemberIndex(const EnumTypeInfo& info, uint64_t value) {
  for (size_t i = 0; i < info.members.size(); ++i) {
    if (info.members[i].value == value) return static_cast<int>(i);
  }
  return -1;
}

// §6.19.5.3: next(N) — returns the Nth next member, wrapping around.
static Logic4Vec EnumNext(const EnumTypeInfo& info, uint64_t current,
                          uint32_t count, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int idx = FindMemberIndex(info, current);
  if (idx < 0) return MakeLogic4VecVal(arena, 32, info.members.front().value);
  auto n = static_cast<int>(info.members.size());
  int new_idx = (idx + static_cast<int>(count % n)) % n;
  return MakeLogic4VecVal(arena, 32, info.members[new_idx].value);
}

// §6.19.5.4: prev(N) — returns the Nth previous member, wrapping around.
static Logic4Vec EnumPrev(const EnumTypeInfo& info, uint64_t current,
                          uint32_t count, Arena& arena) {
  if (info.members.empty()) return MakeLogic4VecVal(arena, 32, 0);
  int idx = FindMemberIndex(info, current);
  if (idx < 0) return MakeLogic4VecVal(arena, 32, info.members.back().value);
  auto n = static_cast<int>(info.members.size());
  int offset = static_cast<int>(count % n);
  int new_idx = ((idx - offset) % n + n) % n;
  return MakeLogic4VecVal(arena, 32, info.members[new_idx].value);
}

// §6.19.5.5: num() — returns the number of members in the enum.
static Logic4Vec EnumNum(const EnumTypeInfo& info, Arena& arena) {
  return MakeLogic4VecVal(arena, 32, info.members.size());
}

// §6.19.5.6: name() — returns the string name of the current value.
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
  // Invalid value: return empty string (0).
  return MakeLogic4VecVal(arena, 8, 0);
}

// Parse the optional count argument for next()/prev(), defaulting to 1.
static uint32_t ParseStepCount(const Expr* call_expr, SimContext& ctx,
                               Arena& arena) {
  if (call_expr->args.empty()) return 1;
  return static_cast<uint32_t>(
      EvalExpr(call_expr->args[0], ctx, arena).ToUint64());
}

// Dispatch an enum method call. Returns true if dispatched.
// Uses a struct to bundle context and stay within the 5-argument limit.
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

// §6.19: Try to evaluate an enum method call.
// Returns true and sets `out` if the call is an enum method.
bool TryEvalEnumMethodCall(const Expr* expr, SimContext& ctx, Arena& arena,
                           Logic4Vec& out) {
  // Enum method calls appear as kCall where lhs is a kMemberAccess.
  if (!expr->lhs || expr->lhs->kind != ExprKind::kMemberAccess) return false;

  auto* access = expr->lhs;
  if (!access->lhs || access->lhs->kind != ExprKind::kIdentifier) return false;
  if (!access->rhs || access->rhs->kind != ExprKind::kIdentifier) return false;

  auto var_name = access->lhs->text;
  auto method_name = access->rhs->text;

  const auto* info = ctx.GetVariableEnumType(var_name);
  if (!info) return false;

  auto* var = ctx.FindVariable(var_name);
  uint64_t current = var ? var->value.ToUint64() : 0;

  EnumMethodArgs args{*info, current, expr, ctx, arena};
  return DispatchEnumMethod(method_name, args, out);
}

}  // namespace delta
