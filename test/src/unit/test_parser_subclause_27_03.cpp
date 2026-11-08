#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(GenerateRegion, DirectRegionNestingRejected) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    generate\n"
      "    endgenerate\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "this generate region opens inside another one, which is not allowed", 3,
      "27.3"));
}

TEST(GenerateRegion, RegionNestedInGenerateIfBodyRejected) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    if (1) begin\n"
      "      generate\n"
      "      endgenerate\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags,
      "this generate region opens inside another one, which is not allowed", 4,
      "27.3"));
}

TEST(GenerateRegion, GenerateRegionAtModuleScopeAllowedOncePerSibling) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  generate\n"
              "    wire a;\n"
              "  endgenerate\n"
              "  generate\n"
              "    wire b;\n"
              "  endgenerate\n"
              "endmodule\n"));
}

TEST(GenerateRegion, MissingEndgenerateRejected) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endgenerate', got 'endmodule'",
                            4, "27.3"));
}

TEST(GenerateRegion,
     MissingEndgenerateLeavesTheEnclosingEndmoduleToItsOwnProduction) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    wire w;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endgenerate', got 'endmodule'",
                            4, "27.3"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(GenerateRegion, MissingEndInAGenerateBlockNamesTheEndgenerate) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    if (1) begin\n"
      "      wire w;\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endgenerate'", 5, "27.3"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(GenerateCaseConstruct, MissingEndInACaseItemNamesTheEndcase) {
  auto r = Parse(
      "module m;\n"
      "  case (1)\n"
      "    0: begin\n"
      "      wire w;\n"
      "  endcase\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(r.diags, "expected 'end', got 'endcase'", 5, "27.3"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(GenerateRegion, OptionalRegionKeywordsProduceSameItems) {
  auto with_region = Parse(
      "module m;\n"
      "  generate\n"
      "    if (1) begin : blk\n"
      "      wire w;\n"
      "    end\n"
      "  endgenerate\n"
      "endmodule\n");
  auto without_region = Parse(
      "module m;\n"
      "  if (1) begin : blk\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(with_region.cu, nullptr);
  ASSERT_NE(without_region.cu, nullptr);
  EXPECT_FALSE(with_region.has_errors);
  EXPECT_FALSE(without_region.has_errors);
  ASSERT_EQ(with_region.cu->modules[0]->items.size(),
            without_region.cu->modules[0]->items.size());
  EXPECT_EQ(with_region.cu->modules[0]->items[0]->kind,
            without_region.cu->modules[0]->items[0]->kind);
}

TEST(GenerateRegion, EmptyRegionProducesNoItems) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(r.cu->modules[0]->items.empty());
}

TEST(GenerateCaseConstruct, ValueAndDefaultItemsParse) {
  auto r = Parse(
      "module m;\n"
      "  parameter SEL = 0;\n"
      "  case (SEL)\n"
      "    0, 1: begin : lo\n"
      "      wire a;\n"
      "    end\n"
      "    default: begin : hi\n"
      "      wire b;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ModuleItem* gen_case = nullptr;
  for (auto* it : mod->items) {
    if (it->kind == ModuleItemKind::kGenerateCase) gen_case = it;
  }
  ASSERT_NE(gen_case, nullptr);
  ASSERT_EQ(gen_case->gen_case_items.size(), 2u);
  EXPECT_EQ(gen_case->gen_case_items[0].patterns.size(), 2u);
  EXPECT_FALSE(gen_case->gen_case_items[0].is_default);
  EXPECT_TRUE(gen_case->gen_case_items[1].is_default);
}

TEST(GenerateIfConstruct, IfElseBlocksParse) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : t\n"
      "    wire a;\n"
      "  end else begin : f\n"
      "    wire b;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateIf);
  EXPECT_NE(mod->items[0]->gen_cond, nullptr);
  ASSERT_NE(mod->items[0]->gen_else, nullptr);
  EXPECT_FALSE(mod->items[0]->gen_else->gen_body.empty());
}

TEST(GenerateIfConstruct, MissingEndBeforeElseNamesTheElseKeyword) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    wire w;\n"
      "  else begin\n"
      "    wire x;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'end', got 'else'", 4, "27.3"));
  EXPECT_EQ(r.diags.size(), 1u);
}

TEST(GenerateIfConstruct, MissingEndBeforeElseStillReadsTheElseBranch) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin\n"
      "    wire w;\n"
      "  else begin\n"
      "    wire x;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'end', got 'else'", 4, "27.3"));
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  ASSERT_EQ(mod->items[0]->gen_body.size(), 1u);
  ASSERT_NE(mod->items[0]->gen_else, nullptr);
  EXPECT_EQ(mod->items[0]->gen_else->gen_body.size(), 1u);
}

TEST(GenerateLoopConstruct, ForWithInlineGenvarParsesAllClauses) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i = i + 1) begin : g\n"
      "    wire a;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* mod = r.cu->modules[0];
  ModuleItem* loop = nullptr;
  for (auto* it : mod->items) {
    if (it->kind == ModuleItemKind::kGenerateFor) loop = it;
  }
  ASSERT_NE(loop, nullptr);
  EXPECT_NE(loop->gen_init, nullptr);
  EXPECT_NE(loop->gen_cond, nullptr);
  EXPECT_NE(loop->gen_step, nullptr);
}

TEST(GenerateRegion, MalformedGenerateRegionNames27_3) {
  auto r = Parse(
      "module m;\n"
      "  generate\n");
  EXPECT_TRUE(ReportedError(r.diags, "expected 'endgenerate'", 3, "27.3"));
}

TEST(GenerateItemContent, DesignElementDeclaredInAGenerateBlockIsReported) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : g\n"
      "    module inner; endmodule\n"
      "    program p; endprogram\n"
      "    interface i; endinterface\n"
      "    checker c; endchecker\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'module' declares a design element, which is not "
                            "an item of a generate block or region",
                            3, "27.3"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "'program' declares a design element, which is not "
                            "an item of a generate block or region",
                            4, "27.3"));
  EXPECT_TRUE(ReportedError(r.diags,
                            "'interface' declares a design element, which is "
                            "not an item of a generate block or region",
                            5, "27.3"));
  EXPECT_FALSE(ReportedError(r.diags, "declares a design element", 6, "27.3"));
}

TEST(GenerateItemContent, DesignElementDeclaredInAGenerateRegionIsReported) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    macromodule inner; endmodule\n"
      "  endgenerate\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'macromodule' declares a design element, which is "
                            "not an item of a generate block or region",
                            3, "27.3"));
}

TEST(GenerateItemContent, DesignElementAsASingleItemGenerateBodyIsReported) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar k = 0; k < 2; k++)\n"
      "    module inner; endmodule\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags,
                            "'module' declares a design element, which is not "
                            "an item of a generate block or region",
                            3, "27.3"));
}

TEST(GenerateItemContent, NestedModuleAndGenerateInterfaceClassAreAccepted) {
  auto r = Parse(
      "module m;\n"
      "  module inner; endmodule\n"
      "  if (1) begin : g\n"
      "    interface class ic; endclass\n"
      "  end\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
