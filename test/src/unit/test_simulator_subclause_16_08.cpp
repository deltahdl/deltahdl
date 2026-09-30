#include <gtest/gtest.h>

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

// §16.8: an instance that omits a formal with a default actual takes the
// default. a is high at the rises of 5, 25 and 55 and b at 15, 35, 65 and 85,
// so `a ##1 b` with y defaulted to b matches from 5, 25 and 55.
TEST(NamedSequenceInstance, AnOmittedFormalTakesItsDefault) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1010010000, bv = 10'b0101001010;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  int cdef = 0;\n"
      "  sequence s_def(x, y = b); x ##1 y; endsequence\n"
      "  cover property (@(posedge clk) s_def(a)) cdef++;\n"
      "  initial #98 $display(\"cdef=%0d\", cdef);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("cdef=3\n"), std::string::npos);
}

// A typed formal's default stands where the formal does, a cycle delay among
// them: with d defaulted to 3, `a ##3 b` matches from 5 and 55 alone, where
// the delay read as 1 matched three times.
TEST(NamedSequenceInstance, AnOmittedDelayFormalTakesItsDefault) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b1010010000, bv = 10'b0101001010;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  int c1 = 0;\n"
      "  sequence s_def2(x, shortint d = 3); x ##d b; endsequence\n"
      "  cover property (@(posedge clk) s_def2(a)) c1++;\n"
      "  initial #98 $display(\"c1=%0d\", c1);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("c1=2\n"), std::string::npos);
}

// §16.8 with §26.3: a sequence declared in a package, instantiated through an
// import and by its package-qualified name as the consequent of `|->`, starts
// at the end of the antecedent's match. a is high at the rises of 15 and 45
// and b at 25 alone, so the attempt of 15 holds, that of 45 fails at 55, and
// the other eight hold vacuously.
TEST(NamedSequenceInstance, APackageSequenceIsInstantiatedByImportAndByScope) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  sequence s2(x, y); x ##1 y; endsequence\n"
      "endpackage\n"
      "import pk::*;\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b0100100000, bv = 10'b0010000000;\n"
      "  bit a, b; assign a = av[0]; assign b = bv[0];\n"
      "  always @(negedge clk) begin av <= av << 1; bv <= bv << 1; end\n"
      "  int p = 0, f = 0, p2 = 0, f2 = 0;\n"
      "  assert property (@(posedge clk) a |-> s2(a, b)) p++; else f++;\n"
      "  assert property (@(posedge clk) a |-> pk::s2(a, b)) p2++; else f2++;\n"
      "  initial #98 $display(\"p=%0d f=%0d p2=%0d f2=%0d\", p, f, p2, f2);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "p=9 f=1 p2=9 f2=1\n");
}

// §16.8 with §26.3: a package sequence with no formals is named through the
// package scope with no parentheses, `pk::s`, as it is declared. As the
// consequent of `|->` it starts at the antecedent's tick and matches at the
// next, so every attempt holds; read as a Boolean the two attempts whose
// antecedent holds, at 15 and 45, would fail.
TEST(NamedSequenceInstance, APackageSequenceIsNamedThroughTheScopeAlone) {
  SimFixture f;
  std::string out = RunCapture(
      "package pk;\n"
      "  sequence s; 1'b1 ##1 1'b1; endsequence\n"
      "endpackage\n"
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  bit [0:9] av = 10'b0100100000;\n"
      "  bit a; assign a = av[0];\n"
      "  always @(negedge clk) av <= av << 1;\n"
      "  int p = 0, f = 0;\n"
      "  assert property (@(posedge clk) a |-> pk::s) p++; else f++;\n"
      "  initial #98 $display(\"p=%0d f=%0d\", p, f);\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "p=10 f=0\n");
}

// §16.8 with §16.8.1 b) and §16.16: a sequence clocked on its event formal,
// the formal left to its default, `posedge clk`, is the whole property of the
// statement, so the statement is attempted at every rise of clk, the default
// in the formal's place, as it is with the event given.
TEST(NamedSequenceInstance, AnEventFormalLeftToItsDefaultClocksTheStatement) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  logic clk = 0; initial repeat (20) #5 clk = ~clk;\n"
      "  logic a = 1;\n"
      "  int c3 = 0, c4 = 0;\n"
      "  sequence s_p(untyped x, event e = posedge clk); @(e) x; endsequence\n"
      "  cover property (s_p(a)) c3++;\n"
      "  cover property (s_p(a, posedge clk)) c4++;\n"
      "  initial #98 $display(\"c3=%0d c4=%0d\", c3, c4);\n"
      "endmodule\n",
      f);
  EXPECT_NE(out.find("c3=10 c4=10\n"), std::string::npos);
}

}  // namespace
