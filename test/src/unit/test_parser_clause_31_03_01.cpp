// §31.3.1: $setup

#include "fixture_parser.h"

using namespace delta;

namespace {

// =============================================================================
// A.7.5.1 $setup_timing_check
// =============================================================================
// $setup ( data_event , reference_event , timing_check_limit [ , [ notifier ] ]
// )
TEST(ParserA70501, SetupTimingCheck) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(tc->data_terminal.name, "clk");
  ASSERT_EQ(tc->limits.size(), 1u);
}

// $setup with notifier
TEST(ParserA70501, SetupWithNotifier) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10, ntfr);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->notifier, "ntfr");
}

TEST(ParserAnnexA, A7TimingCheckSetup) {
  auto r = Parse(
      "module m;\n"
      "  specify $setup(data, posedge clk, 10); endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

ModuleItem* FindSpecifyBlock(const std::vector<ModuleItem*>& items) {
  for (auto* item : items) {
    if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
  }
  return nullptr;
}

TEST(ParserA701, SpecifyItemSystemTimingCheck) {
  auto r = Parse(
      "module m;\n"
      "  specify\n"
      "    $setup(data, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* spec = FindSpecifyBlock(r.cu->modules[0]->items);
  ASSERT_NE(spec, nullptr);
  ASSERT_EQ(spec->specify_items.size(), 1u);
  EXPECT_EQ(spec->specify_items[0]->kind, SpecifyItemKind::kTimingCheck);
}

// =============================================================================
// A.7.5.2 timing_check_limit ::= expression
// =============================================================================
TEST(ParserA70502, TimingCheckLimitExpression) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, posedge clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  ASSERT_EQ(tc->limits.size(), 1u);
  EXPECT_NE(tc->limits[0], nullptr);
}

// =============================================================================
// A.7.5.3 timing_check_event
// =============================================================================
// timing_check_event with no edge (edge is optional)
TEST(ParserA70503, TimingCheckEventNoEdge) {
  auto r = Parse(
      "module m;\n"
      "specify\n"
      "  $setup(data, clk, 10);\n"
      "endspecify\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* tc = GetSoleTimingCheck(r);
  ASSERT_NE(tc, nullptr);
  EXPECT_EQ(tc->ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->data_edge, SpecifyEdge::kNone);
  EXPECT_EQ(tc->ref_terminal.name, "data");
  EXPECT_EQ(tc->data_terminal.name, "clk");
}

using SpecifyParseTest = ProgramTestParse;

// =============================================================================
// Parser test fixture
// =============================================================================
struct SpecifyTest : ::testing::Test {
 protected:
  CompilationUnit* Parse(const std::string& src) {
    source_ = src;
    lexer_ = std::make_unique<Lexer>(source_, 0, diag_);
    parser_ = std::make_unique<Parser>(*lexer_, arena_, diag_);
    return parser_->Parse();
  }

  // Helper: get first specify block from first module.
  ModuleItem* FirstSpecifyBlock(CompilationUnit* cu) {
    for (auto* item : cu->modules[0]->items) {
      if (item->kind == ModuleItemKind::kSpecifyBlock) return item;
    }
    return nullptr;
  }

  SourceManager mgr_;
  Arena arena_;
  DiagEngine diag_{mgr_};
  std::string source_;
  std::unique_ptr<Lexer> lexer_;
  std::unique_ptr<Parser> parser_;
};

struct ParseResult30 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult30 Parse(const std::string& src) {
  ParseResult30 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST_F(SpecifyParseTest, SpecifyBlockWithTimingCheck) {
  auto* unit = Parse(
      "module m; specify $setup(data, posedge clk, 10); endspecify "
      "endmodule");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kSpecifyBlock);
}

using ConfigParseTest = ProgramTestParse;

TEST(ParserSection28, Sec28_12_TimingCheckSetup) {
  auto sp = ParseSpecifySingle(
      "module m(input d, clk);\n"
      "  specify\n"
      "    $setup(d, posedge clk, 10);\n"
      "  endspecify\n"
      "endmodule\n");
  ASSERT_NE(sp.pr.cu, nullptr);
  EXPECT_FALSE(sp.pr.has_errors);
  ASSERT_NE(sp.sole_item, nullptr);
  auto* si = sp.sole_item;
  EXPECT_EQ(si->kind, SpecifyItemKind::kTimingCheck);
  EXPECT_EQ(si->timing_check.check_kind, TimingCheckKind::kSetup);
  EXPECT_EQ(si->timing_check.ref_edge, SpecifyEdge::kNone);
  EXPECT_EQ(si->timing_check.ref_terminal.name, "d");
  EXPECT_EQ(si->timing_check.data_edge, SpecifyEdge::kPosedge);
  EXPECT_EQ(si->timing_check.data_terminal.name, "clk");
  ASSERT_EQ(si->timing_check.limits.size(), 1u);
}

}  // namespace
