#include <gtest/gtest.h>

#include "elaborator/elaborator.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

namespace {

TEST(TopLevelModules, EmptySourceTopNotFoundReturnsNull) {
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  ASSERT_NE(cu, nullptr);
  Elaborator elab(f.arena, f.diag, cu);
  auto* design = elab.Elaborate("top");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(), "top module 'top' not found", 0, ""));
}

TEST(TopLevelModules, ElaboratedDesignContainsTopModule) {
  ElabFixture f;
  auto* design = ElaborateSrc("module top; endmodule", f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
}

TEST(TopLevelModules, SelectSpecificTopFromMultipleModules) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n",
      f, "b");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "b");
}

TEST(TopLevelModules, NonexistentTopIsError) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module a; endmodule\n"
      "module b; endmodule\n",
      f, "nonexistent");
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "top module 'nonexistent' not found", 0, ""));
}

bool HasTopNamed(const RtlirDesign* design, std::string_view name) {
  for (auto* m : design->top_modules)
    if (m->name == name) return true;
  return false;
}

TEST(TopLevelModules, AutoTopRootsEveryUninstantiatedModule) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module a; endmodule\n"
      "module b; endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 2u);
  EXPECT_TRUE(HasTopNamed(design, "a"));
  EXPECT_TRUE(HasTopNamed(design, "b"));
}

TEST(TopLevelModules, DesignWithNoTopLevelModuleIsError) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module a;\n"
      "  b b1();\n"
      "endmodule\n"
      "module b;\n"
      "  a a1();\n"
      "endmodule\n",
      f, "", true);
  EXPECT_EQ(design, nullptr);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "design contains no top-level module", 0,
                            "23.3.1"));
}

TEST(TopLevelModules, NoTopLevelModuleReportStandsAtNoPosition) {
  ElabFixture f;
  ElaborateWithPreprocessor(
      "module a;\n"
      "  b b1();\n"
      "endmodule\n"
      "module b;\n"
      "  a a1();\n"
      "endmodule\n",
      f, "", true);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "design contains no top-level module", 0,
                            "23.3.1"));
}

TEST(TopLevelModules, AutoTopExcludesNormallyInstantiatedChild) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

TEST(TopLevelModules, AutoTopExcludesModuleInstantiatedOnlyInGenerateIf) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module wrapper;\n"
      "  if (0) begin\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "wrapper");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

TEST(TopLevelModules, AutoTopExcludesModuleInstantiatedOnlyInGenerateElse) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module wrapper;\n"
      "  if (1) begin\n"
      "    logic keep;\n"
      "  end else begin\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "wrapper");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

TEST(TopLevelModules, AutoTopExcludesModuleInstantiatedOnlyInGenerateCase) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module wrapper;\n"
      "  parameter SEL = 9;\n"
      "  case (SEL)\n"
      "    0: begin\n"
      "      child c1();\n"
      "    end\n"
      "    default: begin\n"
      "      logic keep;\n"
      "    end\n"
      "  endcase\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "wrapper");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

TEST(TopLevelModules, AutoTopExcludesModuleInstantiatedOnlyInGenerateFor) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child; endmodule\n"
      "module wrapper;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 2; i = i + 1) begin\n"
      "    child c1();\n"
      "  end\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "wrapper");
  EXPECT_FALSE(HasTopNamed(design, "child"));
}

TEST(TopLevelModules, DollarRootRefResolvesToTopInstance) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module top;\n"
      "  logic [7:0] x;\n"
      "  assign x = $root.top.x;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(TopLevelModules, DollarRootMultiLevelPathResolves) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module child;\n"
      "  logic sig;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic x;\n"
      "  assign x = $root.top.c1.sig;\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
