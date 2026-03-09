#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

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

TEST(ParserA210, SequenceListOfArguments_Positional) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(x, y));\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceActualArg_Dollar) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(x, $));\n"
              "endmodule\n"));
}

TEST(ParserA210, SequenceListOfArguments_Named) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b); a ##1 b; endsequence\n"
              "  assert property (@(posedge clk) s(.a(x), .b(y)));\n"
              "endmodule\n"));
}

TEST(ParserA210, SequencePortItem_DefaultValue) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s(a, b = 1'b1);\n"
              "    a ##1 b;\n"
              "  endsequence\n"
              "endmodule\n"));
}

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

TEST(ParserSection16, SequenceWithFormalArgsDecl) {
  auto r = Parse(
      "module m;\n"
      "  sequence s_req_ack(req, ack);\n"
      "    req ##1 ack;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
