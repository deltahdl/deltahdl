#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// The source the cases share: clk rises at 5, 15, 25, ...; the eight-bit v
// holds 8'h02 for the tick at 15 and 8'h01 for the tick at 25, both written
// between ticks; and a process counts the ticks at which the named sequence
// `rule`, declared as `decls` has it, reaches its end point, keeping the last
// such time.
std::string TypedSource(const std::string& decls) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic [7:0] v = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n" +
         decls +
         "  initial begin\n"
         "    #10 v = 8'h02;\n"
         "    #10 v = 8'h01;\n"
         "    #10 v = 0;\n"
         "    #30 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

// §16.8.1 (c): an actual passed to a formal of type bit is cast to bit by
// truncation, so s2's x reads bit'(v): 8'h02 truncates to 0 and 8'h01 to 1,
// and the one-operand sequence ends at the tick at 25 alone, where an untyped
// formal would read 8'h02 as true at 15 as well.
TEST(TypedSequenceFormals, ActualIsCastToTheFormalsType) {
  SimFixture f;
  auto* hits = RunAndFindVar(TypedSource("  sequence s2(bit x);\n"
                                         "    x;\n"
                                         "  endsequence\n"
                                         "  sequence rule;\n"
                                         "    @(posedge clk) s2(v);\n"
                                         "  endsequence\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
  SimFixture g;
  auto* untyped = RunAndFindVar(TypedSource("  sequence s1(x);\n"
                                            "    x;\n"
                                            "  endsequence\n"
                                            "  sequence rule;\n"
                                            "    @(posedge clk) s1(v);\n"
                                            "  endsequence\n"),
                                g, "hits");
  ASSERT_NE(untyped, nullptr);
  EXPECT_EQ(untyped->value.ToUint64(), 2u);
}

// §16.8.1 (b): a formal of type event takes an event_expression, so
// event_arg_example(posedge clk) is `@(posedge clk) x ##1 y`: v reads 2 at 15
// and 1 at 25, and the sequence ends at 25.
TEST(TypedSequenceFormals, EventFormalTakesTheClockingEvent) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(TypedSource("  sequence event_arg_example(event ev);\n"
                                "    @(ev) v == 2 ##1 v == 1;\n"
                                "  endsequence\n"
                                "  sequence rule;\n"
                                "    event_arg_example(posedge clk);\n"
                                "  endsequence\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

// §16.8.1: an actual meant to be combined with an edge is passed to a formal
// not typed event, so event_arg_example2(clk) with `@(posedge sig)` over the
// formal sig is `@(posedge clk) x ##1 y` as well.
TEST(TypedSequenceFormals, SignalFormalUnderAnEdgeTakesTheSignal) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(TypedSource("  sequence event_arg_example2(reg sig);\n"
                                "    @(posedge sig) v == 2 ##1 v == 1;\n"
                                "  endsequence\n"
                                "  sequence rule;\n"
                                "    event_arg_example2(clk);\n"
                                "  endsequence\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

// §16.8.1: a typed formal referenced in a cycle_delay_range is a shortint,
// int or longint whose actual is an elaboration-time constant, a parameter
// here: delay_arg_example(my_delay, my_delay - 1) reads `v == 2 ##2 v == 0
// ##1 v == 0`, which with v at 2 for the tick at 15 and 0 from the tick at 35
// ends at 45.
TEST(TypedSequenceFormals, TypedDelayFormalTakesAConstantActual) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      TypedSource(
          "  parameter my_delay = 2;\n"
          "  sequence delay_arg_example(shortint delay1, delay2);\n"
          "    v == 2 ##delay1 v == 0 ##delay2 v == 0;\n"
          "  endsequence\n"
          "  sequence rule;\n"
          "    @(posedge clk) delay_arg_example(my_delay, my_delay - 1);\n"
          "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

}  // namespace
