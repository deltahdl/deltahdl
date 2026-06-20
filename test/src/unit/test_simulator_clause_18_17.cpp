#include <algorithm>
#include <cstdint>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "fixture_simulator.h"
#include "simulator/constraint_solver.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(RandsequenceSim, RandsequenceBasicProduction) {
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

TEST(RandsequenceSim, CodeBlockSideEffect) {
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

TEST(RandsequenceSim, ProductionSequenceOrder) {
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

TEST(RandsequenceSim, NamedTopProductionDesignatesEntry) {
  // 18.17: the optional production name after the randsequence keyword
  // designates the top-level production. It need not be the first production;
  // here the entry is the second one declared, so only its code block runs.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(second)\n"
      "      first  : { x = 8'd11; };\n"
      "      second : { x = 8'd99; };\n"
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
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

TEST(RandsequenceSim, AlternativeProductionListsChosenAtRandom) {
  // 18.17: production lists separated by '|' are a set of choices the generator
  // makes at random. Running the block many times must exercise both
  // alternatives while keeping every selection a valid one (total preserved).
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer ca;\n"
      "  integer cb;\n"
      "  initial begin\n"
      "    ca = 0;\n"
      "    cb = 0;\n"
      "    for (int i = 0; i < 200; i++) begin\n"
      "      randsequence(main)\n"
      "        main : a | b;\n"
      "        a : { ca = ca + 1; };\n"
      "        b : { cb = cb + 1; };\n"
      "      endsequence\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* ca = f.ctx.FindVariable("ca");
  auto* cb = f.ctx.FindVariable("cb");
  ASSERT_NE(ca, nullptr);
  ASSERT_NE(cb, nullptr);
  EXPECT_GT(ca->value.ToUint64(), 0u);
  EXPECT_GT(cb->value.ToUint64(), 0u);
  EXPECT_EQ(ca->value.ToUint64() + cb->value.ToUint64(), 200u);
}

TEST(RandsequenceSim, NoProductionNameUsesFirst) {
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

TEST(RandsequenceSim, NonterminalDecomposesToTerminals) {
  // 18.17: a nonterminal is decomposed into its constituent productions, which
  // are themselves decomposed until only terminals (code blocks) remain. Here
  // 'group' expands to two further nonterminals; the digits accumulated into x
  // record that the terminal code blocks ran in fully-decomposed order.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main  : group tail;\n"
      "      group : alpha beta;\n"
      "      alpha : { x = x * 10 + 1; };\n"
      "      beta  : { x = x * 10 + 2; };\n"
      "      tail  : { x = x * 10 + 3; };\n"
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
  EXPECT_EQ(var->value.ToUint64(), 123u);
}

TEST(RandsequenceSim, ChosenProductionListStreamsItemsInOrder) {
  // 18.17: a production list holding several items streams them in sequence,
  // and lists separated by '|' are alternative choices. Whichever alternative
  // the generator picks, its items must run left-to-right, so x ends as one of
  // the two ordered outcomes and never an interleaving of the two lists.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : p q | r s;\n"
      "      p : { x = x * 10 + 1; };\n"
      "      q : { x = x * 10 + 2; };\n"
      "      r : { x = x * 10 + 3; };\n"
      "      s : { x = x * 10 + 4; };\n"
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
  auto result = var->value.ToUint64();
  EXPECT_TRUE(result == 12u || result == 34u);
}

TEST(RandsequenceSim, CodeBlockLocalsAreAutomaticPerInvocation) {
  // 18.17: each code block is an anonymous automatic scope, so a variable it
  // declares starts fresh on every execution. Production 'p' runs twice; were
  // its local 'y' persistent the accumulator would reach 1+2=3, but automatic
  // lifetime makes each run observe y == 1, so acc sums to 2.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  integer acc;\n"
      "  initial begin\n"
      "    acc = 0;\n"
      "    randsequence(main)\n"
      "      main : p p;\n"
      "      p : { int y; y = y + 1; acc = acc + y; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("acc");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

}  // namespace
