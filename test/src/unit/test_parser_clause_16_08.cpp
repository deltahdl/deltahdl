// §16.8: Declaring sequences

#include "fixture_parser.h"

using namespace delta;

static ModuleItem* FindItemByKind(const std::vector<ModuleItem*>& items,
                                  ModuleItemKind kind) {
  for (auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

namespace {

TEST(ParserA210, AssertionItemDecl_SequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_handshake;\n"
      "    req ##[1:3] ack;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "s_handshake");
}

// =============================================================================
// §A.2.10 Production #21: sequence_declaration
// sequence_declaration ::=
//     sequence sequence_identifier [ ( [sequence_port_list] ) ] ;
//     { assertion_variable_declaration }
//     sequence_expr [ ; ]
//     endsequence [ : sequence_identifier ]
// =============================================================================
TEST(ParserA210, SequenceDecl_WithEndLabel) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_req;\n"
      "    req ##[1:3] ack;\n"
      "  endsequence : s_req\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "s_req");
}

TEST(ParserA210, SequenceDecl_WithPortList) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b);\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceDecl_SourceLoc) {
  auto r = Parse(
      "module m;\n"
      "  sequence my_seq;\n"
      "    a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->loc.IsValid());
}

// =============================================================================
// §A.2.10 Production #31: sequence_list_of_arguments
// =============================================================================
TEST(ParserA210, SequenceListOfArguments_Positional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(x, y));\n"
              "endmodule\n"));
}

// =============================================================================
// §A.2.10 Production #32: sequence_actual_arg
// sequence_actual_arg ::= event_expression | sequence_expr | $
// =============================================================================
TEST(ParserA210, SequenceActualArg_Dollar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(x, $));\n"
              "endmodule\n"));
}

// sequence_list_of_arguments — named arguments
TEST(ParserA210, SequenceListOfArguments_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(.a(x), .b(y)));\n"
              "endmodule\n"));
}

// sequence_port_item with default value
TEST(ParserA210, SequencePortItem_DefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b = 1'b1);\n"
              "    a ##1 b;\n"
              "  endsequence\n"
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
// §16.8 Sequence declarations
// =============================================================================
TEST(ParserSection16, SequenceDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_req;\n"
      "    req ##1 ack;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      found = true;
      EXPECT_EQ(item->name, "s_req");
    }
  }
  EXPECT_TRUE(found);
}

// =============================================================================
// A.6.11 clocking_item — assertion_item_declaration (sequence_declaration)
// =============================================================================
TEST(ParserA611, ClockingItemSequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  clocking cb @(posedge clk);\n"
      "    input data;\n"
      "    sequence s;\n"
      "      data;\n"
      "    endsequence\n"
      "  endclocking\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindClockingBlock(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->clocking_signals.size(), 1u);
}

TEST(ParserAnnexF, AnnexFSequenceDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  bool found = false;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kSequenceDecl) {
      found = true;
      EXPECT_EQ(item->name, "s1");
    }
  }
  EXPECT_TRUE(found);
}

}  // namespace
