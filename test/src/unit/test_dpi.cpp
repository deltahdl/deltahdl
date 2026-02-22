// Non-LRM tests

#include <gtest/gtest.h>
#include <cstdint>
#include <vector>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/dpi.h"
#include "simulation/eval.h"
#include "simulation/sim_context.h"

using namespace delta;


struct DpiSimFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};
namespace {

// =============================================================================
// DpiContext registration
// =============================================================================
TEST(Dpi, RegisterImport) {
  DpiContext ctx;
  DpiFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.return_type = DataTypeKind::kInt;
  func.impl = [](const std::vector<uint64_t>& args) -> uint64_t {
    return args[0] + args[1];
  };
  ctx.RegisterImport(func);

  EXPECT_EQ(ctx.ImportCount(), 1u);
  EXPECT_TRUE(ctx.HasImport("sv_add"));
  EXPECT_FALSE(ctx.HasImport("nonexistent"));
}

TEST(Dpi, FindImport) {
  DpiContext ctx;
  DpiFunction func;
  func.c_name = "c_mul";
  func.sv_name = "sv_mul";
  func.return_type = DataTypeKind::kInt;
  ctx.RegisterImport(func);

  const auto* found = ctx.FindImport("sv_mul");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->c_name, "c_mul");

  EXPECT_EQ(ctx.FindImport("missing"), nullptr);
}

TEST(Dpi, CallFunction) {
  DpiContext ctx;
  DpiFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.impl = [](const std::vector<uint64_t>& args) -> uint64_t {
    return args[0] + args[1];
  };
  ctx.RegisterImport(func);

  auto result = ctx.Call("sv_add", {10, 20});
  EXPECT_EQ(result, 30u);
}

TEST(Dpi, CallMissingReturnsZero) {
  DpiContext ctx;
  auto result = ctx.Call("nonexistent", {1, 2});
  EXPECT_EQ(result, 0u);
}

TEST(Dpi, RegisterExport) {
  DpiContext ctx;
  DpiExport exp;
  exp.c_name = "c_callback";
  exp.sv_name = "sv_callback";
  ctx.RegisterExport(exp);

  EXPECT_EQ(ctx.ExportCount(), 1u);
  EXPECT_TRUE(ctx.HasExport("sv_callback"));
  EXPECT_FALSE(ctx.HasExport("missing"));
}

TEST(Dpi, EvalExprDispatchesToDpiImport) {
  DpiSimFixture f;

  // Register DPI import: sv_add(a, b) -> a + b.
  DpiContext dpi_ctx;
  DpiFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.impl = [](const std::vector<uint64_t>& args) -> uint64_t {
    return args[0] + args[1];
  };
  dpi_ctx.RegisterImport(func);
  f.ctx.SetDpiContext(&dpi_ctx);

  // Build call expression: sv_add(10, 20)
  auto* arg0 = f.arena.Create<Expr>();
  arg0->kind = ExprKind::kIntegerLiteral;
  arg0->int_val = 10;

  auto* arg1 = f.arena.Create<Expr>();
  arg1->kind = ExprKind::kIntegerLiteral;
  arg1->int_val = 20;

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "sv_add";
  call->args = {arg0, arg1};

  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 30u);
}

TEST(Dpi, EvalExprDpiMultipleArgs) {
  DpiSimFixture f;

  DpiContext dpi_ctx;
  DpiFunction func;
  func.c_name = "c_mul3";
  func.sv_name = "sv_mul3";
  func.impl = [](const std::vector<uint64_t>& args) -> uint64_t {
    return args[0] * args[1] * args[2];
  };
  dpi_ctx.RegisterImport(func);
  f.ctx.SetDpiContext(&dpi_ctx);

  auto* a0 = f.arena.Create<Expr>();
  a0->kind = ExprKind::kIntegerLiteral;
  a0->int_val = 2;
  auto* a1 = f.arena.Create<Expr>();
  a1->kind = ExprKind::kIntegerLiteral;
  a1->int_val = 3;
  auto* a2 = f.arena.Create<Expr>();
  a2->kind = ExprKind::kIntegerLiteral;
  a2->int_val = 7;

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "sv_mul3";
  call->args = {a0, a1, a2};

  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 42u);
}

}  // namespace
