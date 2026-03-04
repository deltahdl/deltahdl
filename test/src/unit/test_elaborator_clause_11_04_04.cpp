#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

TEST(ConstEval, Comparison) {
  EvalFixture f;
  struct Case {
    const char* expr;
    int64_t expected;
  };
  const Case kCases[] = {
      {"3 < 5", 1},  {"5 < 3", 0},  {"5 > 3", 1},  {"3 >= 3", 1},
      {"3 <= 3", 1}, {"3 == 3", 1}, {"3 != 4", 1},
  };
  for (const auto& c : kCases) {
    EXPECT_EQ(ConstEvalInt(ParseExprFrom(c.expr, f)), c.expected) << c.expr;
  }
}

TEST(SimCh9, AlwaysCombComparison) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] a, b;\n"
      "  logic result;\n"
      "  initial begin\n"
      "    a = 8'd10;\n"
      "    b = 8'd5;\n"
      "  end\n"
      "  always_comb begin\n"
      "    result = (a > b);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("result");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}
