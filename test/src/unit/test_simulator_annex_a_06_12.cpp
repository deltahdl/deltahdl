#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_randseq_sim.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(RandsequenceSim, IfTrueBranchExecutes) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    randsequence(main)\n"
                                   "      main : if (1) a else b;\n"
                                   "      a : { x = 8'd1; };\n"
                                   "      b : { x = 8'd2; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

TEST(RandsequenceSim, ReturnTerminatesProduction) {
  SimFixture f;
  // 18.17.6: a return ends generation of the *current* production and no other;
  // the code after it in that production's block does not run, but sequence
  // generation continues with the next production in the enclosing list. Here
  // `first`'s `x = 8'd55` is skipped by the return (so x stays 10), yet
  // `second` is still generated and adds 5, leaving x == 15.
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    randsequence(main)\n"
                                   "      main : first second;\n"
                                   "      first : { x = 8'd10; return; "
                                   "x = 8'd55; };\n"
                                   "      second : { x = x + 8'd5; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 15u);
}

TEST(RandsequenceSim, CaseDefaultExecutes) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(
      f,
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    x = 8'd0;\n"
      "    randsequence(main)\n"
      "      main : case (99) 0: a; 1: b; default: c; endcase;\n"
      "      a : { x = 8'd10; };\n"
      "      b : { x = 8'd20; };\n"
      "      c : { x = 8'd30; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 30u);
}

TEST(RandsequenceSim, WeightCodeBlockExecutes) {
  SimFixture f;
  auto* y = RunRandseqAndFindVar(f,
                                 "module t;\n"
                                 "  logic [7:0] x;\n"
                                 "  logic [7:0] y;\n"
                                 "  initial begin\n"
                                 "    x = 8'd0;\n"
                                 "    y = 8'd0;\n"
                                 "    randsequence(main)\n"
                                 "      main : a := 1 { y = 8'd77; };\n"
                                 "      a : { x = 8'd42; };\n"
                                 "    endsequence\n"
                                 "  end\n"
                                 "endmodule\n",
                                 "y");
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 77u);
}

TEST(RandsequenceSim, NestedRandsequenceExecutes) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  logic [7:0] x;\n"
                                   "  initial begin\n"
                                   "    x = 8'd0;\n"
                                   "    randsequence(outer)\n"
                                   "      outer : {\n"
                                   "        randsequence(inner)\n"
                                   "          inner : { x = 8'd33; };\n"
                                   "        endsequence\n"
                                   "      };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 33u);
}

// §18.17.7 passes data to a production in a task call's syntax, so A.6.12's
// rs_production_item takes A.8.4's list_of_arguments: a positional argument
// left empty and a named one written `.b()` take the formal's default, and a
// named argument binds the formal of its name wherever it stands. Each call
// appends its two digits, a then b, so a formal bound by position where its
// name should have bound it shows as a swapped pair.
TEST(RandsequenceSim, ProductionArgumentsBindByNameAndOmittedTakeDefaults) {
  SimFixture f;
  auto* var = RunRandseqAndFindVar(f,
                                   "module t;\n"
                                   "  int x;\n"
                                   "  initial begin\n"
                                   "    x = 0;\n"
                                   "    randsequence(main)\n"
                                   "      main : p(1, ) p(.a(2)) "
                                   "p(.b(), .a(3)) p(.b(5), .a(4));\n"
                                   "      void p(int a, int b = 7) : "
                                   "{ x = x * 100 + a * 10 + b; };\n"
                                   "    endsequence\n"
                                   "  end\n"
                                   "endmodule\n",
                                   "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 17273745u);
}

}  // namespace
