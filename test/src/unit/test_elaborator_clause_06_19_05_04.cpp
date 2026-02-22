// §6.19.5.4: Prev()

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>
#include <string>
#include <string_view>
#include <vector>

using namespace delta;

// =============================================================================
// Test fixture: sets up SimContext with an enum type and variable
// =============================================================================
struct EnumFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  // Register an enum type with the given members and values.
  // Returns the variable associated with the enum.
  Variable *
  RegisterEnum(std::string_view var_name, std::string_view type_name,
               const std::vector<std::pair<std::string, uint64_t>> &members) {
    EnumTypeInfo info;
    char *tn = arena.AllocString(type_name.data(), type_name.size());
    info.type_name = std::string_view(tn, type_name.size());
    for (auto &[name, val] : members) {
      EnumMemberInfo m;
      char *mn = arena.AllocString(name.c_str(), name.size());
      m.name = std::string_view(mn, name.size());
      m.value = val;
      info.members.push_back(m);
    }
    ctx.RegisterEnumType(info.type_name, info);

    auto *var = ctx.CreateVariable(var_name, 32);
    var->value = MakeLogic4VecVal(arena, 32, members[0].second);
    ctx.SetVariableEnumType(var_name, info.type_name);
    return var;
  }

  // Build a method call expression: var_name.method_name(args...)
  Expr *MakeEnumMethodCall(std::string_view var_name,
                           std::string_view method_name) {
    return MakeEnumMethodCallWithArgs(var_name, method_name, {});
  }

  Expr *MakeEnumMethodCallWithArgs(std::string_view var_name,
                                   std::string_view method_name,
                                   std::vector<Expr *> args) {
    // Build: var_name.method_name(args...)
    auto *id = arena.Create<Expr>();
    id->kind = ExprKind::kIdentifier;
    id->text = var_name;

    auto *member = arena.Create<Expr>();
    member->kind = ExprKind::kIdentifier;
    member->text = method_name;

    auto *access = arena.Create<Expr>();
    access->kind = ExprKind::kMemberAccess;
    access->lhs = id;
    access->rhs = member;

    auto *call = arena.Create<Expr>();
    call->kind = ExprKind::kCall;
    call->lhs = access;
    call->args = std::move(args);
    return call;
  }

  Expr *MakeIntLiteral(uint64_t val) {
    auto *lit = arena.Create<Expr>();
    lit->kind = ExprKind::kIntegerLiteral;
    lit->int_val = val;
    return lit;
  }
};
namespace {

// =============================================================================
// §6.19.5.4: prev(N) — returns the Nth previous member (default N=1)
// =============================================================================
TEST(EnumMethods, PrevReturnsPrevMember) {
  EnumFixture f;
  auto *var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2); // BLUE
  auto *call = f.MakeEnumMethodCall("color", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 1u); // GREEN
}

TEST(EnumMethods, PrevWrapsFromFirst) {
  EnumFixture f;
  auto *var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 0); // RED
  auto *call = f.MakeEnumMethodCall("color", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 2u); // wraps to BLUE
}

TEST(EnumMethods, PrevWithCount) {
  EnumFixture f;
  auto *var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 2); // BLUE
  auto *call =
      f.MakeEnumMethodCallWithArgs("color", "prev", {f.MakeIntLiteral(2)});
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u); // RED (back 2 from BLUE)
}

TEST(EnumMethods, PrevOnNonMemberValue) {
  EnumFixture f;
  auto *var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 99);
  auto *call = f.MakeEnumMethodCall("color", "prev");
  auto result = EvalExpr(call, f.ctx, f.arena);
  // For invalid current value, prev() returns last member.
  EXPECT_EQ(result.ToUint64(), 2u);
}

TEST(EnumMethods, PrevFullIteration) {
  // Verify prev() can iterate backwards and wrap around.
  EnumFixture f;
  auto *var =
      f.RegisterEnum("state", "state_t", {{"A", 10}, {"B", 20}, {"C", 30}});
  var->value = MakeLogic4VecVal(f.arena, 32, 10); // A

  std::vector<uint64_t> visited;
  for (int i = 0; i < 4; ++i) {
    visited.push_back(var->value.ToUint64());
    auto *call = f.MakeEnumMethodCall("state", "prev");
    auto result = EvalExpr(call, f.ctx, f.arena);
    var->value = result;
  }
  EXPECT_EQ(visited, (std::vector<uint64_t>{10, 30, 20, 10}));
}

} // namespace
