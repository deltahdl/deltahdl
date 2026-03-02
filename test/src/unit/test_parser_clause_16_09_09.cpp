// §16.9.9: Conditions over sequences

#include "fixture_parser.h"

using namespace delta;

namespace {

// sequence_expr ::= expression_or_dist throughout sequence_expr
TEST(ParserA210, SequenceExpr_Throughout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk)\n"
              "    en throughout (a ##1 b ##1 c));\n"
              "endmodule\n"));
}

using VerifyParseTest = ProgramTestParse;

// Assert property with throughout operator.
TEST(ParserSection16, Sec16_5_1_SequenceThroughout) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) !burst throughout (##2 trdy[*7]));\n"
              "endmodule\n"));
}

// --- Test helpers ---
struct ParseResult16b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16b Parse(const std::string& src) {
  ParseResult16b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

// =============================================================================
// §16.9.4 Sequence throughout
// =============================================================================
TEST(ParserSection16, SequenceThroughoutBasic) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) !burst_mode throughout (##2 trdy[*7]));\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// --- F.7: throughout ---
TEST(ParserAnnexF, AnnexFThroughout) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) enable throughout (a ##1 b ##1 c));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

TEST(ParserSection16, SequenceThroughoutInSeqDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence burst_rule;\n"
      "    @(posedge clk)\n"
      "    (!burst_mode) throughout (##2 (trdy && irdy)[*7]);\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* sq =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(sq, nullptr);
}

// =============================================================================
// §16.9.4 -- Sequence throughout (additional tests)
// =============================================================================
TEST(ParserSection16, SequenceThroughoutWithImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (\n"
      "    @(posedge clk) req |-> en throughout (##2 ack[*3]));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
