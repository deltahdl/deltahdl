#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(NamedSequenceLowering, EndPointVariableIsCreated) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b;\n"
      "  sequence ab;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindSequenceDecl("ab"), nullptr);
  auto* ep = f.ctx.FindVariable("__seq_ab");
  ASSERT_NE(ep, nullptr);
  EXPECT_TRUE(ep->is_event);
}

TEST(NamedSequenceLowering, MultipleSequencesEachGetEndPoint) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic clk, a, b, c;\n"
      "  sequence first;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence second;\n"
      "    @(posedge clk) b ##1 c;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);

  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);

  EXPECT_NE(f.ctx.FindVariable("__seq_first"), nullptr);
  EXPECT_NE(f.ctx.FindVariable("__seq_second"), nullptr);
}

// The source the instantiation cases share: clk rises at 5, 15, 25, ...; req
// is high for the tick at 15 alone and gnt for the ticks at 35, 45 and 55; and
// a process counts the ticks at which the named sequence `rule`, declared as
// `decls` has it, reaches its end point, keeping the last such time.
std::string InstanceSource(const std::string& decls) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic req = 0;\n"
         "  logic gnt = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n" +
         decls +
         "  initial begin\n"
         "    #10 req = 1;\n"
         "    #10 req = 0;\n"
         "    #10 gnt = 1;\n"
         "    #30 gnt = 0;\n"
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

// §16.8: a named sequence declared without a clock inherits one from the
// sequence that instantiates it, and the instance behaves as the flattened
// sequence, `req ##1 gnt` here: the clause's `rule` example in miniature. gnt
// is low at the tick after req's, so nothing ends there; `req ##2 gnt` would
// end at 35, and the inherited-clock instance reads the delay §16.7 gives ##1.
TEST(NamedSequenceInstance, ClocklessSequenceInheritsTheInstantiatingClock) {
  SimFixture f;
  auto* hits = RunAndFindVar(InstanceSource("  sequence s;\n"
                                            "    req ##2 gnt;\n"
                                            "  endsequence\n"
                                            "  sequence rule;\n"
                                            "    @(posedge clk) s;\n"
                                            "  endsequence\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

// §16.8: the delay before an instance and the instantiated body's own leading
// delay add: `req ##1 s` with `s` being `##1 gnt` reads gnt two ticks after
// req, at 35.
TEST(NamedSequenceInstance, DelayBeforeAnInstanceAddsToItsLeadingDelay) {
  SimFixture f;
  auto* hits = RunAndFindVar(InstanceSource("  sequence s;\n"
                                            "    ##1 gnt;\n"
                                            "  endsequence\n"
                                            "  sequence rule;\n"
                                            "    @(posedge clk) req ##1 s;\n"
                                            "  endsequence\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

// §16.8: actual arguments bound to formals by position are substituted for
// the formals' references, in an operand and in a delay bound alike, and `$`
// as an actual is the upper bound of a cycle_delay_const_range_expression:
// win(req, gnt, 3, $) is `req ##[3:$] gnt`, which ends at 45 and 55.
TEST(NamedSequenceInstance, PositionalActualsSubstituteForTheFormals) {
  SimFixture f;
  auto* hits =
      RunAndFindVar(InstanceSource("  sequence win(x, y, lo, hi);\n"
                                   "    x ##[lo:hi] y;\n"
                                   "  endsequence\n"
                                   "  sequence rule;\n"
                                   "    @(posedge clk) win(req, gnt, 3, $);\n"
                                   "  endsequence\n"),
                    f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

// §16.8: actual arguments may be bound to formals by name, in any order, and
// an actual that is an expression stands as one term: win(.hi(2), .lo(2),
// .y(gnt && !req), .x(req)) is `req ##[2:2] (gnt && !req)`, ending at 35.
TEST(NamedSequenceInstance, NamedActualsSubstituteForTheFormals) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      InstanceSource("  sequence win(x, y, lo, hi);\n"
                     "    x ##[lo:hi] y;\n"
                     "  endsequence\n"
                     "  sequence rule;\n"
                     "    @(posedge clk) win(.hi(2), .lo(2), .y(gnt && !req), "
                     ".x(req));\n"
                     "  endsequence\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

// §16.8: a named sequence may be instantiated before its declaration, the
// reference being resolved when the sequences are lowered together.
TEST(NamedSequenceInstance, InstanceMayPrecedeTheDeclaration) {
  SimFixture f;
  auto* hits = RunAndFindVar(InstanceSource("  sequence rule;\n"
                                            "    @(posedge clk) later;\n"
                                            "  endsequence\n"
                                            "  sequence later;\n"
                                            "    req ##2 gnt;\n"
                                            "  endsequence\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

}  // namespace
