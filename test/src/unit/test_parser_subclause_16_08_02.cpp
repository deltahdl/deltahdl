#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(SequenceLocalLvarArgumentParsing, LocalKeywordOnSequenceFormalParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local logic a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

TEST(SequenceLocalLvarArgumentParsing, LocalDirectionsCaptured) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local input logic a,\n"
      "             local inout int b,\n"
      "             local output bit c);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 3u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[1], Direction::kInout);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[2], Direction::kOutput);
}

TEST(SequenceLocalLvarArgumentParsing, DirectionWithoutLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(output logic a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "sequence port direction requires the 'local' keyword", 2,
      "16.8.2"));
}

TEST(SequenceLocalLvarArgumentParsing, InputDirectionWithoutLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(input logic a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "sequence port direction requires the 'local' keyword", 2,
      "16.8.2"));
}

TEST(SequenceLocalLvarArgumentParsing, InoutDirectionWithoutLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(inout int b);\n"
      "    @(posedge clk) b;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "sequence port direction requires the 'local' keyword", 2,
      "16.8.2"));
}

TEST(SequenceLocalLvarArgumentParsing, DefaultActualOnInoutLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local inout int b = 1);\n"
      "    @(posedge clk) b;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "default actual argument is illegal for a local "
                            "variable formal argument of direction inout or "
                            "output",
                            2, "16.8.2"));
}

TEST(SequenceLocalLvarArgumentParsing, DefaultActualOnOutputLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local output bit c = 0);\n"
      "    @(posedge clk) c;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "default actual argument is illegal for a local "
                            "variable formal argument of direction inout or "
                            "output",
                            2, "16.8.2"));
}

TEST(SequenceLocalLvarArgumentParsing, DefaultActualOnInputLocalParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local input logic a = 1'b1);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

TEST(SequenceLocalLvarArgumentParsing, IdentifierOnlyItemInheritsLocalDir) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local inout logic a, b, c);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 3u);
  EXPECT_EQ(item->prop_formals[0], "a");
  EXPECT_EQ(item->prop_formals[1], "b");
  EXPECT_EQ(item->prop_formals[2], "c");
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 3u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInout);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[1], Direction::kInout);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[2], Direction::kInout);
}

TEST(SequenceLocalLvarArgumentParsing, LocalWithoutExplicitTypeIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a local variable formal argument requires an "
                            "explicit type in its own port item",
                            2, "16.8.2"));
}

TEST(SequenceLocalLvarArgumentParsing, LocalWithUserDefinedTypeParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local my_type_t a);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "a");
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

TEST(SequenceLocalLvarArgumentParsing, ExplicitTypeBreaksLocalCarry) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local logic a, bit b);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 2u);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

TEST(SequenceLocalLvarArgumentParsing, LocalEventTypeIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local event e);\n"
      "    @(posedge clk) e;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "the type of a local variable formal argument must "
                            "be one of the types allowed in",
                            2, "16.8.2"));
}

TEST(SequenceLocalLvarArgumentParsing, LocalPropertyTypeIsError) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local property p);\n"
      "    @(posedge clk) 1;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "the type of a local variable formal argument must "
                            "be one of the types allowed in",
                            2, "16.8.2"));
}

TEST(SequenceLocalLvarArgumentParsing, LocalSequenceOrUntypedTypeIsError) {
  auto r1 = Parse(
      "module m;\n"
      "  sequence s(local sequence q);\n"
      "    @(posedge clk) 1;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r1.diags,
                            "the type of a local variable formal argument must "
                            "be one of the types allowed in",
                            2, "16.8.2"));
  auto r2 = Parse(
      "module m;\n"
      "  sequence s(local untyped u);\n"
      "    @(posedge clk) 1;\n"
      "  endsequence\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r2.diags,
                            "the type of a local variable formal argument must "
                            "be one of the types allowed in",
                            2, "16.8.2"));
}

TEST(SequenceLocalLvarArgumentParsing, LocalSixteenSixTypeParses) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local int lv);\n"
      "    @(posedge clk) lv;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 1u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInput);
}

TEST(SequenceLocalLvarArgumentParsing, SubsequentLocalRestartsCarry) {
  auto r = Parse(
      "module m;\n"
      "  sequence s(local inout logic a, local input bit b);\n"
      "    @(posedge clk) a;\n"
      "  endsequence\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kSequenceDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 2u);
  EXPECT_EQ(item->prop_formals[0], "a");
  EXPECT_EQ(item->prop_formals[1], "b");
  ASSERT_EQ(item->prop_seq_local_lvar_directions.size(), 2u);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[0], Direction::kInout);
  EXPECT_EQ(item->prop_seq_local_lvar_directions[1], Direction::kInput);
}

}  // namespace
