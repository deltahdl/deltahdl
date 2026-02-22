// §6.19.5.6: Name()

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
// §6.19.5.6: name() — returns the string name of the current value
// =============================================================================
TEST(EnumMethods, NameReturnsStringRep) {
  EnumFixture f;
  auto *var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 1); // GREEN
  auto *call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);

  // Extract string from result.
  std::string name_str;
  uint64_t v = result.ToUint64();
  uint32_t nbytes = (result.width + 7) / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    auto ch = static_cast<char>((v >> ((i - 1) * 8)) & 0xFF);
    if (ch != 0)
      name_str += ch;
  }
  EXPECT_EQ(name_str, "GREEN");
}

TEST(EnumMethods, NameForFirstMember) {
  EnumFixture f;
  auto *var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 0); // RED
  auto *call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  std::string name_str;
  uint64_t v = result.ToUint64();
  uint32_t nbytes = (result.width + 7) / 8;
  for (uint32_t i = nbytes; i > 0; --i) {
    auto ch = static_cast<char>((v >> ((i - 1) * 8)) & 0xFF);
    if (ch != 0)
      name_str += ch;
  }
  EXPECT_EQ(name_str, "RED");
}

TEST(EnumMethods, NameForUnknownValue) {
  EnumFixture f;
  auto *var = f.RegisterEnum("color", "color_t",
                             {{"RED", 0}, {"GREEN", 1}, {"BLUE", 2}});
  var->value = MakeLogic4VecVal(f.arena, 32, 99); // Not a valid member
  auto *call = f.MakeEnumMethodCall("color", "name");
  auto result = EvalExpr(call, f.ctx, f.arena);
  // name() returns empty string for invalid enum values.
  EXPECT_EQ(result.ToUint64(), 0u);
}

} // namespace
