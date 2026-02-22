// §6.16.10: Atoreal()

#include <gtest/gtest.h>

#include <cstring>
#include <string>
#include <string_view>
#include <vector>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "parser/ast.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;

// =============================================================================
// Test fixture: sets up SimContext with a string variable
// =============================================================================
struct StringFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};

  // Create a string variable and store the given string value.
  Variable *CreateStringVar(std::string_view var_name, std::string_view value) {
    uint32_t width = static_cast<uint32_t>(value.size()) * 8;
    if (width == 0) width = 8;
    auto *var = ctx.CreateVariable(var_name, width);
    var->value = MakeLogic4Vec(arena, width);
    for (size_t i = 0; i < value.size(); ++i) {
      auto byte_idx = static_cast<uint32_t>(value.size() - 1 - i);
      uint32_t word = (byte_idx * 8) / 64;
      uint32_t bit = (byte_idx * 8) % 64;
      var->value.words[word].aval |=
          static_cast<uint64_t>(static_cast<unsigned char>(value[i])) << bit;
    }
    ctx.RegisterStringVariable(var_name);
    return var;
  }

  // Build a method call expression: var_name.method_name(args...)
  Expr *MakeMethodCall(std::string_view var_name, std::string_view method_name,
                       std::vector<Expr *> args = {}) {
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

  Expr *MakeStringLiteral(std::string_view text) {
    std::string quoted = "\"" + std::string(text) + "\"";
    char *buf = arena.AllocString(quoted.c_str(), quoted.size());
    auto *lit = arena.Create<Expr>();
    lit->kind = ExprKind::kStringLiteral;
    lit->text = std::string_view(buf, quoted.size());
    return lit;
  }
};
namespace {

// =============================================================================
// §6.16.10: atoreal() -- convert string to real
// =============================================================================
TEST(StringMethods, Atoreal) {
  StringFixture f;
  f.CreateStringVar("s", "3.14");
  auto *call = f.MakeMethodCall("s", "atoreal");
  auto result = EvalExpr(call, f.ctx, f.arena);
  uint64_t bits = result.ToUint64();
  double d = 0.0;
  std::memcpy(&d, &bits, sizeof(double));
  EXPECT_NEAR(d, 3.14, 0.001);
}

}  // namespace
