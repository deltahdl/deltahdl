#include "fixture_simulator.h"
#include "helpers_scheduler.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

TEST(KeywordIdentifierSim, KeywordDefinesConstruct) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd0;\n"
      "    for (int i = 0; i < 5; i++) result = result + 8'd1;\n"
      "    if (result == 8'd5) result = result + 8'd10;\n"
      "    else result = 8'd0;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 15u);
}

TEST(KeywordIdentifierSim, EscapedKeywordCoexistsWithKeyword) {
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\begin ;\n"
      "  initial begin\n"
      "    \\begin = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "begin");
  EXPECT_EQ(result, 42u);
}

TEST(KeywordIdentifierSim, KeywordLowercaseOnly) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  logic [7:0] Initial, result;\n"
      "  initial begin\n"
      "    Initial = 8'd7;\n"
      "    result = Initial + 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}
