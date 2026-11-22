#include <gtest/gtest.h>

#include <string>

#include "fixture_elaborator.h"
#include "helpers_bracketed_operand_places.h"
#include "helpers_named_property_places.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(AssertionDeclElaboration, PropertyDeclElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  property p;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, PropertyDeclWithPortsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  property p(x, y);\n"
      "    x |-> y;\n"
      "  endproperty\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, SequenceDeclElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, SequenceDeclWithPortsElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m;\n"
      "  sequence s(x, y);\n"
      "    x ##1 y;\n"
      "  endsequence\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, AssertPropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, AssumePropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  assume property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, CoverPropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  cover property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, CoverSequenceElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  cover sequence (@(posedge clk) a ##1 b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, RestrictPropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  restrict property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, PropertyDeclWithAssertElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  property p;\n"
      "    @(posedge clk) a |-> b;\n"
      "  endproperty\n"
      "  assert property (p);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, SequenceDeclWithCoverElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  sequence s;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  cover sequence (s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, PropertyAndSequenceDeclsTogether) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic a, b); logic clk;\n"
      "  default clocking @(posedge clk); endclocking\n"
      "  property p; a; endproperty\n"
      "  sequence s; b; endsequence\n"
      "  assert property (p);\n"
      "  cover sequence (s);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, AllFiveConcurrentAssertionsElaborate) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b, c, d, e);\n"
      "  assert property (@(posedge clk) a);\n"
      "  assume property (@(posedge clk) b);\n"
      "  cover property (@(posedge clk) c);\n"
      "  cover sequence (@(posedge clk) d);\n"
      "  restrict property (@(posedge clk) e);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, AssertPropertyWithDisableIffElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, rst, a, b);\n"
      "  assert property (\n"
      "    @(posedge clk) disable iff (rst) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(AssertionDeclElaboration, NamedAssertPropertyElaborates) {
  ElabFixture f;
  auto* design = Elaborate(
      "module m(input logic clk, a, b);\n"
      "  my_assert: assert property (@(posedge clk) a |-> b);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NamedPropertyInASequencePosition,
     DISABLED_AsACycleDelayOperandIsReportedInEachPlace) {
  ExpectNamedSpecsReported({"p ##1 c", "a ##1 p", "pa(a, b) ##2 c", "pb ##1 c"},
                           {"pk::p ##1 c", "a ##1 pk::pb"});
}

TEST(NamedPropertyInASequencePosition,
     DISABLED_AsARepetitionOperandIsReportedInEachPlace) {
  ExpectNamedSpecsReported({"p[*2]", "p[=1]", "p[->1]", "pb[*2]", "(pb)[*2]"},
                           {"pk::pb[*2]"});
}

TEST(NamedPropertyInASequencePosition,
     DISABLED_AsASequenceOperatorOperandIsReportedInEachPlace) {
  ExpectNamedSpecsReported(
      {"p intersect (c ##1 c)", "c within p", "a throughout p",
       "pb intersect (c ##1 c)", "c within pb"},
      {"c within pk::p"});
}

TEST(NamedPropertyInASequencePosition,
     DISABLED_AsTheOperandOfStrongWeakOrFirstMatchIsReportedInEachPlace) {
  ExpectNamedSpecsReported({"strong(p)", "weak(p)", "first_match(p)",
                            "strong(pb)", "weak(pa(a, b))", "first_match(pb)"},
                           {"strong(pk::p)"});
}

TEST(NamedPropertyInASequencePosition,
     DISABLED_AsTheSequenceOfAMatchItemListIsReportedInEachPlace) {
  ExpectNamedSpecsReported({"(p, $display(\"x\"))", "(pb, $display(\"x\"))"},
                           {"(pk::p, $display(\"x\"))"});
}

TEST(NamedPropertyInASequencePosition,
     ANamedSequenceInTheSamePositionsIsAcceptedInEachPlace) {
  ExpectNamedSpecsAccepted(
      {"s ##1 c", "a ##1 s", "sa(a, b) ##2 c", "s[*2]", "(s)[*2]", "a[=1]",
       "a[->1]", "s intersect (c ##1 c)", "c within s", "a throughout s",
       "strong(s)", "weak(sa(a, b))", "first_match(s)", "(s, $display(\"x\"))"},
      {"pk::s ##1 c", "a ##1 pk::s", "pk::s[*2]", "c within pk::s",
       "strong(pk::s)", "(pk::s, $display(\"x\"))"});
}

constexpr const char* kCoverPlaces[] = {"module",    "procedural", "generate",
                                        "interface", "program",    "checker"};

std::string CoverIn(const std::string& place, const std::string& spec) {
  std::string src = NamedIn(place, spec);
  const std::string kAssert = "assert property";
  src.replace(src.find(kAssert), kAssert.size(), "cover sequence");
  return src;
}

TEST(NamedPropertyInASequencePosition,
     DISABLED_AsACoverSequenceIsReportedInEachPlace) {
  for (const char* place : kCoverPlaces) {
    for (const char* spec : {"p", "pb", "pa(a, b)"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      ElabFixture f;
      ElaborateSrc(CoverIn(place, spec), f);
      EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kPropertyForSequence,
                                NamedLine(place), "A.2.10"));
    }
  }
}

TEST(NamedPropertyInASequencePosition,
     ANamedSequenceAsACoverSequenceIsAcceptedInEachPlace) {
  for (const char* place : kCoverPlaces) {
    for (const char* spec : {"s", "sa(a, b)", "s ##1 c"}) {
      SCOPED_TRACE(std::string(place) + " " + spec);
      ElabFixture f;
      ElaborateSrc(CoverIn(place, spec), f);
      EXPECT_FALSE(f.diag.HasErrors());
    }
  }
}

TEST(NexttimeIndex, ARangeIsReportedInEachPlace) {
  for (const char* spec : {"nexttime [1:2] a", "s_nexttime [1:2] a",
                           "nexttime [0:0] a", "s_nexttime [1:1] a"}) {
    ExpectInEachPlace(spec, ExpectGrammarReported);
  }
}

TEST(NexttimeIndex, ASingleIndexOrNoneIsAcceptedInEachPlace) {
  for (const char* spec : {"nexttime [2] a", "s_nexttime [2] a", "nexttime a",
                           "s_nexttime a", "nexttime [0] a"}) {
    ExpectInEachPlace(spec, ExpectOperandAccepted);
  }
}

}  // namespace
