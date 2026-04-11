#include <cstdint>
#include <vector>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/dpi.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ImportExportSimulation, EvalExprDispatchesToDpiImport) {
  DpiSimFixture f;

  DpiContext dpi_ctx;
  DpiFunction func;
  func.c_name = "c_add";
  func.sv_name = "sv_add";
  func.impl = [](const std::vector<uint64_t>& args) -> uint64_t {
    return args[0] + args[1];
  };
  dpi_ctx.RegisterImport(func);
  f.ctx.SetDpiContext(&dpi_ctx);

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

TEST(ImportExportSimulation, EvalExprDpiMultipleArgs) {
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

TEST(ImportExportSimulation, DpiImportNoArgs) {
  DpiSimFixture f;

  DpiContext dpi_ctx;
  DpiFunction func;
  func.c_name = "c_seed";
  func.sv_name = "sv_seed";
  func.impl = [](const std::vector<uint64_t>&) -> uint64_t { return 99; };
  dpi_ctx.RegisterImport(func);
  f.ctx.SetDpiContext(&dpi_ctx);

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "sv_seed";

  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 99u);
}

TEST(ImportExportSimulation, UnregisteredImportReturnsZero) {
  DpiSimFixture f;

  DpiContext dpi_ctx;
  f.ctx.SetDpiContext(&dpi_ctx);

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "nonexistent_import";

  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 0u);
}

}  // namespace
