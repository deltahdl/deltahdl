// §18.17: Random sequence generation—randsequence

#include <algorithm>
#include <cstdint>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/constraint_solver.h"

using namespace delta;

namespace {

// =============================================================================
// §18.17: randsequence (basic structure)
// =============================================================================
TEST(Constraint, RandsequenceBasicProduction) {
  ConstraintSolver solver(42);
  RandVariable v;
  v.name = "production";
  v.min_val = 0;
  v.max_val = 2;
  solver.AddVariable(v);

  ConstraintBlock block;
  block.name = "c_seq";
  ConstraintExpr c;
  c.kind = ConstraintKind::kDist;
  c.var_name = "production";
  c.dist_weights = {{0, 1}, {1, 1}, {2, 1}};
  block.constraints.push_back(c);
  solver.AddConstraintBlock(block);

  ASSERT_TRUE(solver.Solve());
  int64_t val = solver.GetValue("production");
  EXPECT_GE(val, 0);
  EXPECT_LE(val, 2);
}

// =============================================================================
// Simulation tests — A.6.12 Randsequence
// =============================================================================
// Basic randsequence: code block side effects execute
TEST(SimA612, CodeBlockSideEffect) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : { x = 8'd42; };\n"
      "    endsequence\n"
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

// Sequence of productions: all execute in order
TEST(SimA612, ProductionSequenceOrder) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : first second;\n"
      "      first : { x = x + 8'd10; };\n"
      "      second : { x = x + 8'd20; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

// No production name — first production is used as top
TEST(SimA612, NoProductionNameUsesFirst) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence()\n"
      "      top : { x = 8'd55; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

}  // namespace
