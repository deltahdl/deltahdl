#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The source the cases share: clk rises at 5, 15, 25, ...; a is high for the
// tick at 15, b for the tick at 25, c for the tick at 45 and d for the tick
// at 55; and a process counts the ticks at which the named sequence `rule`,
// whose body is `body`, reaches its end point, keeping the last such time.
std::string PrecedenceSource(const std::string& body) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic a = 0;\n"
         "  logic b = 0;\n"
         "  logic c = 0;\n"
         "  logic d = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n"
         "  sequence rule;\n"
         "    @(posedge clk) " +
         body +
         ";\n"
         "  endsequence\n"
         "  initial begin\n"
         "    #10 a = 1;\n"
         "    #10 a = 0; b = 1;\n"
         "    #10 b = 0;\n"
         "    #10 c = 1;\n"
         "    #10 c = 0; d = 1;\n"
         "    #10 d = 0;\n"
         "    #20 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

// §16.9.1, Table 16-1: `##` binds tighter than `or`, so `a ##1 b or c ##1 d`
// is `(a ##1 b) or (c ##1 d)` and ends where either concatenation does, at 25
// and at 55. Read as `a ##1 (b or c) ##1 d` it would need d at 35, low then,
// and end at 55 alone; `or` alone ends at each tick either operand holds at.
TEST(SequenceOperatorPrecedence, ConcatenationBindsTighterThanOr) {
  SimFixture f;
  auto* hits = RunAndFindVar(PrecedenceSource("a ##1 b or c ##1 d"), f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
  SimFixture g;
  auto* either = RunAndFindVar(PrecedenceSource("a or c"), g, "hits");
  ASSERT_NE(either, nullptr);
  EXPECT_EQ(either->value.ToUint64(), 2u);
  EXPECT_EQ(g.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

}  // namespace
