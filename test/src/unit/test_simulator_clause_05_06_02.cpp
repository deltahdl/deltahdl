
#include "preprocessor/preprocessor.h"
#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

// §5.6.2 Keywords

TEST(SimCh50602, KeywordDefinesConstruct) {
  // §5.6.2: Keywords define language constructs (if/else/begin/end/for).
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

TEST(SimCh50602, EscapedKeywordCoexistsWithKeyword) {
  // §5.6.2: Escaped keyword (\begin) used as variable inside begin/end block.
  auto result = RunAndGet(
      "module t;\n"
      "  logic [7:0] \\begin ;\n"
      "  initial begin\n"
      "    \\begin = 8'd42;\n"
      "  end\n"
      "endmodule\n",
      "\\begin");
  EXPECT_EQ(result, 42u);
}

TEST(SimCh50602, KeywordLowercaseOnly) {
  // §5.6.2: Keywords are lowercase only; uppercase is an identifier.
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] Initial, result;\n"
      "  initial begin\n"
      "    Initial = 8'd7;\n"
      "    result = Initial + 8'd3;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 10u);
}
