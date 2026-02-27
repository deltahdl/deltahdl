// §12.5: Case statement


#include <cstdint>
#include <string_view>

#include "common/types.h"
#include "parser/ast.h"
#include "simulation/awaiters.h"
#include "simulation/exec_task.h"
#include "simulation/process.h"
#include "simulation/stmt_exec.h"
#include "simulation/stmt_result.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

// Helper fixture providing scheduler, arena, diag, and sim context.
// Helper to create a simple identifier expression.
Expr* MakeIdent(Arena& arena, std::string_view name) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIdentifier;
  e->text = name;
  return e;
}

// Helper to create an integer literal expression.
Expr* MakeIntLit(Arena& arena, uint64_t val) {
  auto* e = arena.Create<Expr>();
  e->kind = ExprKind::kIntegerLiteral;
  e->int_val = val;
  return e;
}

// Helper to create a blocking assignment statement: lhs = rhs_val.
Stmt* MakeBlockAssign(Arena& arena, std::string_view lhs_name,
                      uint64_t rhs_val) {
  auto* s = arena.Create<Stmt>();
  s->kind = StmtKind::kBlockingAssign;
  s->lhs = MakeIdent(arena, lhs_name);
  s->rhs = MakeIntLit(arena, rhs_val);
  return s;
}

// Driver coroutine that co_awaits an ExecTask and stores its result.
struct DriverResult {
  StmtResult value = StmtResult::kDone;
};

SimCoroutine DriverCoroutine(const Stmt* stmt, SimContext& ctx, Arena& arena,
                             DriverResult* out) {
  out->value = co_await ExecStmt(stmt, ctx, arena);
}

// Helper to run ExecStmt synchronously (for non-suspending statements).
// Creates a wrapper coroutine, resumes it, and returns the result.
StmtResult RunStmt(const Stmt* stmt, SimContext& ctx, Arena& arena) {
  DriverResult result;
  auto coro = DriverCoroutine(stmt, ctx, arena, &result);
  coro.Resume();
  return result.value;
}
namespace {

// =============================================================================
// 12. Unique case / Priority case
// =============================================================================
TEST(StmtExec, UniqueCaseExactMatch) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("uc", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->qualifier = CaseQualifier::kUnique;
  stmt->condition = MakeIntLit(f.arena, 2);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 1));
  item1.body = MakeBlockAssign(f.arena, "uc", 10);
  stmt->case_items.push_back(item1);

  CaseItem item2;
  item2.patterns.push_back(MakeIntLit(f.arena, 2));
  item2.body = MakeBlockAssign(f.arena, "uc", 20);
  stmt->case_items.push_back(item2);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 20u);
}

TEST(StmtExec, PriorityCaseNoMatchNoDefaultWarning) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("pcw", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->qualifier = CaseQualifier::kPriority;
  stmt->condition = MakeIntLit(f.arena, 99);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 1));
  item1.body = MakeBlockAssign(f.arena, "pcw", 10);
  stmt->case_items.push_back(item1);

  // No default => should warn.
  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 0u);
  EXPECT_GE(f.diag.WarningCount(), 1u);
}

// =============================================================================
// 17. Case with exact match (baseline)
// =============================================================================
TEST(StmtExec, CaseExactMatchBaseline) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("ce", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCase;
  stmt->condition = MakeIntLit(f.arena, 3);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 1));
  item1.body = MakeBlockAssign(f.arena, "ce", 10);
  stmt->case_items.push_back(item1);

  CaseItem item2;
  item2.patterns.push_back(MakeIntLit(f.arena, 3));
  item2.body = MakeBlockAssign(f.arena, "ce", 30);
  stmt->case_items.push_back(item2);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "ce", 99);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 30u);
}

// =============================================================================
// 21. Case multiple patterns in one item
// =============================================================================
TEST(StmtExec, CaseMultiplePatterns) {
  StmtFixture f;
  auto* result_var = f.ctx.CreateVariable("cmp", 32);
  result_var->value = MakeLogic4VecVal(f.arena, 32, 0);

  auto* stmt = f.arena.Create<Stmt>();
  stmt->kind = StmtKind::kCase;
  stmt->case_kind = TokenKind::kKwCase;
  stmt->condition = MakeIntLit(f.arena, 5);

  CaseItem item1;
  item1.patterns.push_back(MakeIntLit(f.arena, 3));
  item1.patterns.push_back(MakeIntLit(f.arena, 5));
  item1.patterns.push_back(MakeIntLit(f.arena, 7));
  item1.body = MakeBlockAssign(f.arena, "cmp", 111);
  stmt->case_items.push_back(item1);

  CaseItem def;
  def.is_default = true;
  def.body = MakeBlockAssign(f.arena, "cmp", 0);
  stmt->case_items.push_back(def);

  RunStmt(stmt, f.ctx, f.arena);
  EXPECT_EQ(result_var->value.ToUint64(), 111u);
}

// =============================================================================
// Simulation tests — A.6.7 Case statements
// =============================================================================
// §12.5: case statement — first matching item
TEST(SimA607, CaseFirstMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd1;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "      8'd2: x = 8'd30;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.5: case falls to default when no item matches
TEST(SimA607, CaseDefaultFallthrough) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    sel = 8'd5;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "      default: x = 8'd99;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

// §12.5: no default, no match — no change
TEST(SimA607, CaseNoDefaultNoMatch) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] sel, x;\n"
      "  initial begin\n"
      "    x = 8'd42;\n"
      "    sel = 8'd5;\n"
      "    case(sel)\n"
      "      8'd0: x = 8'd10;\n"
      "      8'd1: x = 8'd20;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

// §12.5: case inside for loop
TEST(SimA607, CaseInsideForLoop) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    total = 8'd0;\n"
      "    for (int i = 0; i < 3; i = i + 1) begin\n"
      "      case(i)\n"
      "        0: total = total + 8'd1;\n"
      "        1: total = total + 8'd10;\n"
      "        2: total = total + 8'd100;\n"
      "      endcase\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("total");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 111u);
}

// §12.5: nested case statements
TEST(SimA607, NestedCaseExecution) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b, x;\n"
      "  initial begin\n"
      "    a = 8'd0;\n"
      "    b = 8'd1;\n"
      "    case(a)\n"
      "      8'd0: case(b)\n"
      "              8'd0: x = 8'd10;\n"
      "              8'd1: x = 8'd20;\n"
      "              default: x = 8'd30;\n"
      "            endcase\n"
      "      default: x = 8'd40;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 20u);
}

// §12.5: case with block body in item
TEST(SimA607, CaseWithBlockBody) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x, y;\n"
      "  initial begin\n"
      "    case(1)\n"
      "      1: begin x = 8'd5; y = 8'd6; end\n"
      "      default: begin x = 8'd0; y = 8'd0; end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* x = f.ctx.FindVariable("x");
  auto* y = f.ctx.FindVariable("y");
  ASSERT_NE(x, nullptr);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(x->value.ToUint64(), 5u);
  EXPECT_EQ(y->value.ToUint64(), 6u);
}

}  // namespace
