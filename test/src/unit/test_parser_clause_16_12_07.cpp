// §16.12.7: Implication

#include "fixture_parser.h"

using namespace delta;

namespace {

// property_expr ::= sequence_expr |-> property_expr
TEST(ParserA210, PropertyExpr_OverlappedImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= sequence_expr |=> property_expr
TEST(ParserA210, PropertyExpr_NonOverlappedImplication) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) req |=> ack);\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #30: sequence_instance
// sequence_instance ::=
//     ps_or_hierarchical_sequence_identifier
//     [ ( [sequence_list_of_arguments] ) ]
// =============================================================================
TEST(ParserA210, SequenceInstance_InProperty) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s; a ##1 b; endsequence\n"
              "  property p; s |-> c; endproperty\n"
              "  assert property (p);\n"
              "endmodule\n"));
}

struct ParseResult16c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16c Parse(const std::string& src) {
  ParseResult16c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using VerifyParseTest = ProgramTestParse;

// Assert property with overlapped implication (|->).
TEST(ParserSection16, Sec16_5_1_AssertPropertyOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |-> ack);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

// Assert property with non-overlapped implication (|=>).
TEST(ParserSection16, Sec16_5_1_AssertPropertyNonOverlappedImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) req |=> gnt);\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu, nullptr);
  auto* ap =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kAssertProperty);
  ASSERT_NE(ap, nullptr);
  EXPECT_NE(ap->assert_expr, nullptr);
}

bool HasItemKind(ParseResult& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return true;
  }
  return false;
}

// --- F.13: Overlapping implication |-> ---
TEST(ParserAnnexF, AnnexFOverlapImplication) {
  auto r = Parse(
      "module m;\n"
      "  assert property (@(posedge clk) a && b |-> c);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_TRUE(HasItemKind(r, ModuleItemKind::kAssertProperty));
}

}  // namespace
