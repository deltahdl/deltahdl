// §31.7: Enabling timing checks with conditioned events

#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// scalar_timing_check_condition ::= expression === scalar_constant
TEST(ParserA70503, ScalarTimingCheckCondCaseEquality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en === 1'b1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// scalar_timing_check_condition ::= expression !== scalar_constant
TEST(ParserA70503, ScalarTimingCheckCondCaseInequality) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& (mode !== 1'b0), data, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// =============================================================================
// A.7.5.3 scalar_constant
// =============================================================================
// scalar_constant ::= 1'b0
TEST(ParserA70503, ScalarConstant1b0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'b0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// scalar_constant ::= 1'B1
TEST(ParserA70503, ScalarConstant1B1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1'B1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// scalar_constant ::= 1
TEST(ParserA70503, ScalarConstantDecimal1) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en == 1), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// scalar_constant ::= 0
TEST(ParserA70503, ScalarConstantDecimal0) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& (en != 0), posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// A.7.5.3 &&& condition on both reference and data events
// =============================================================================
// &&& on both reference and data events
TEST(ParserA70503, ConditionBothEvents) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& en, data &&& reset, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_NE(tc->ref_condition, nullptr);
  EXPECT_NE(tc->data_condition, nullptr);
}

// Terminal with bit select + &&& condition combined
TEST(ParserA70503, TerminalBitSelectWithCondition) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data[0] &&& en, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->ref_terminal.range_kind, SpecifyRangeKind::kBitSelect);
  EXPECT_NE(tc->ref_condition, nullptr);
}

// Edge + terminal with part select + &&& condition
TEST(ParserA70503, EdgeTerminalPartSelectWithCondition) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $hold(posedge clk &&& en, data[3:0] &&& reset, 5);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->data_terminal.name, "data");
  EXPECT_EQ(tc->data_terminal.range_kind, SpecifyRangeKind::kPartSelect);
  EXPECT_NE(tc->data_condition, nullptr);
}

using ConfigParseTest = ProgramTestParse;

TEST(ParserSection28, Sec28_12_TimingCheckWithEdges) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(negedge d, posedge clk, 8);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNegedge);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "d");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
}

struct ParseResult31 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult31 Parse(const std::string& src) {
  ParseResult31 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §31.7 Conditioned events
// =============================================================================
TEST_F(SpecifyTest, ConditionedSetup) {
  auto* cu = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data &&& clr, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  auto* spec = FirstSpecifyBlock(cu);
  ASSERT_NE(spec, nullptr);
  auto& tc = spec->specify_items[0]->timing_check;
  EXPECT_EQ(tc.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc.ref_terminal.name, "data");
  EXPECT_NE(tc.ref_condition, nullptr);
}

}  // namespace
