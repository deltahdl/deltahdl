#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

// §9.4.2: Event control synchronizes a procedural statement with the
// occurrence of an event. The @-operator-led event control text must
// pass through the preprocessor unchanged so the lexer/parser can
// recognize it as such.
TEST(EventControlPreprocessor, PosedgeEventControlSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg clk;\n"
      "  reg q;\n"
      "  always @(posedge clk) q <= 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(posedge clk)"), std::string::npos);
}

// §9.4.2: A negedge edge_identifier event control must survive
// preprocessing unchanged.
TEST(EventControlPreprocessor, NegedgeEventControlSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg clk;\n"
      "  reg q;\n"
      "  always @(negedge clk) q <= 0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(negedge clk)"), std::string::npos);
}

// §9.4.2: The `edge` keyword (third edge_identifier alternative,
// indicating a change toward either 1 or 0) must survive preprocessing
// unchanged so it reaches the lexer's keyword recognizer.
TEST(EventControlPreprocessor, EdgeEventControlSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg clk;\n"
      "  reg q;\n"
      "  always @(edge clk) q <= 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(edge clk)"), std::string::npos);
}

// §9.4.2: The non-edge implicit event form @(expr) (firing on any
// change in the value of the expression) must survive preprocessing
// intact.
TEST(EventControlPreprocessor, BareSignalEventControlSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg sig;\n"
      "  reg q;\n"
      "  always @(sig) q = sig;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(sig)"), std::string::npos);
}

// §9.4.2: A logical-OR-separated event_expression list ("@ ( posedge
// clk_a or negedge rst )") must survive preprocessing unchanged.
TEST(EventControlPreprocessor, OrEventExpressionSurvivesPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module m;\n"
      "  reg clk_a, rst;\n"
      "  reg q;\n"
      "  always @(posedge clk_a or negedge rst) q <= 0;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(posedge clk_a or negedge rst)"),
            std::string::npos);
}

// §9.4.2: A macro expanding to an edge_identifier must produce a valid
// event control after expansion.
TEST(EventControlPreprocessor, MacroExpansionInEdgeIdentifier) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EDGE posedge\n"
      "module m;\n"
      "  reg clk;\n"
      "  reg q;\n"
      "  always @(`EDGE clk) q <= 1;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("posedge clk"), std::string::npos);
}

// §9.4.2 ↔ §15.5.2 cross-reference: §9.4.2 lists "the occurrence of a
// named event (see 15.5.2)" as a synchronization source for the same
// @ event control operator. A macro expanding to a named event used
// in @(...) must survive preprocessing intact.
TEST(EventControlPreprocessor, MacroExpansionInNamedEventControl) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define EV my_event\n"
      "module m;\n"
      "  event my_event;\n"
      "  initial @(`EV) ;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("@(my_event)"), std::string::npos);
}

}  // namespace
