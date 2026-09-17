#include <cstdint>
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : { x = 8'd42; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

TEST(RandsequenceSim, ProductionSequenceOrder) {
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(RandsequenceSim, NamedTopProductionDesignatesEntry) {
  // 18.17: the optional production name after the randsequence keyword
  // designates the top-level production. It need not be the first production;
  // here the entry is the second one declared, so only its code block runs.
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
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
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence()\n"
      "      top : { x = 8'd55; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 55u);
}

TEST(RandsequenceSim, NonterminalDecomposesToTerminals) {
  // 18.17: a nonterminal is decomposed into its constituent productions, which
  // are themselves decomposed until only terminals (code blocks) remain. Here
  // 'group' expands to two further nonterminals; the digits accumulated into x
  // record that the terminal code blocks ran in fully-decomposed order.
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 123u);
}

TEST(RandsequenceSim, ChosenProductionListStreamsItemsInOrder) {
  // 18.17: a production list holding several items streams them in sequence,
  // and lists separated by '|' are alternative choices. Whichever alternative
  // the generator picks, its items must run left-to-right, so x ends as one of
  // the two ordered outcomes and never an interleaving of the two lists.
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "x");
  ASSERT_NE(var, nullptr);
  auto result = var->value.ToUint64();
  EXPECT_TRUE(result == 12u || result == 34u);
}

TEST(RandsequenceSim, SequencedCodeBlockTerminalsRunInOrder) {
  // 18.17: a production list streams its items in sequence. Here the items are
  // anonymous code-block terminals rather than named nonterminals, so the two
  // blocks execute directly and in written order. The first multiplies-and-adds
  // 1, the second 2, so x reads 12 -- proving terminal code blocks in a list
  // are generated left-to-right just like production references.
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer x;\n"
      "  initial begin\n"
      "    x = 0;\n"
      "    randsequence(main)\n"
      "      main : { x = x * 10 + 1; } { x = x * 10 + 2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(RandsequenceSim, ProductionIdentifiersAreLocalToRandsequenceScope) {
  // 18.17: a randsequence statement creates its own automatic scope, and every
  // production identifier is local to that scope. Two sibling randsequence
  // statements may therefore each declare a production named 'main' with no
  // collision, and each statement must resolve 'main' to the production
  // declared within itself -- not to the other statement's like-named
  // production. The first block records the digit 1 and the second records the
  // digit 2, so a scope-local resolution yields 12; a shared/leaked production
  // identifier would instead run one of the two bodies twice (11 or 22).
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer log;\n"
      "  initial begin\n"
      "    log = 0;\n"
      "    randsequence(main)\n"
      "      main : { log = log * 10 + 1; };\n"
      "    endsequence\n"
      "    randsequence(main)\n"
      "      main : { log = log * 10 + 2; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "log");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 12u);
}

TEST(RandsequenceSim, CodeBlockLocalsAreAutomaticPerInvocation) {
  // 18.17: each code block is an anonymous automatic scope, so a variable it
  // declares starts fresh on every execution. Production 'p' runs twice; were
  // its local 'y' persistent the accumulator would reach 1+2=3, but automatic
  // lifetime makes each run observe y == 1, so acc sums to 2.
  SimFixture f;
  auto* var = RunAndFindVar(
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
      f, "acc");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 2u);
}

// §18.17: "each code block within the randsequence block creates an anonymous
// automatic scope". CodeBlockLocalsAreAutomaticPerInvocation above covers the
// block written as a production of its own, which ExecRsProdCodeBlock pushes a
// scope for. This is the other place Syntax 18-14 puts a code block:
// `rs_rule ::= rs_production_list [ := rs_weight_specification [ rs_code_block
// ] ]`, the block a rule carries after its weight. That one ran in the
// enclosing production's scope, so its declaration outlived it and was still
// standing when the same rule was selected again.
//
// Production a is selected twice and its block increments a local. Automatic
// lifetime makes each run observe y == 1, so the block contributes 1 + 1; a
// declaration that survived would contribute 1 + 2. p adds 10 each time it
// generates, so the total tells the two apart as 22 against 23 and also says
// the rule really was activated twice rather than once.
TEST(RandsequenceSim, WeightCodeBlockLocalsAreAutomaticPerActivation) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer acc;\n"
      "  initial begin\n"
      "    acc = 0;\n"
      "    randsequence(main)\n"
      "      main : a a;\n"
      "      a : p := 1 { int y; y = y + 1; acc = acc + y; };\n"
      "      p : { acc = acc + 10; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "acc");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 22u);
}

// The same rule for the trailing block of a production named as a rand join
// operand, which is a second execution path: §18.17.5's interleaving runs each
// operand production's selected rule through a helper of its own rather than
// through the one the case above exercises. §18.17 puts no condition on where
// a code block stands, so both want the scope.
//
// m is generated twice and each generation interleaves p and q, so p's trailing
// block runs twice and s generates four times. Automatic lifetime gives
// 40 + 1 + 1; a surviving declaration gives 40 + 1 + 2. The interleaving order
// §18.17.5 leaves unspecified does not reach the total, every contribution
// being a sum.
TEST(RandsequenceSim, RandJoinOperandWeightCodeBlockLocalsAreAutomatic) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer acc;\n"
      "  initial begin\n"
      "    acc = 0;\n"
      "    randsequence(main)\n"
      "      main : m m;\n"
      "      m : rand join p q;\n"
      "      p : s := 1 { int y; y = y + 1; acc = acc + y; };\n"
      "      q : s;\n"
      "      s : { acc = acc + 10; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f, "acc");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
