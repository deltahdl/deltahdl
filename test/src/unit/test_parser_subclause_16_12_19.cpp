#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

TEST(PropertyLocalLvarArgumentParsing, LocalInoutInPropertyIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local inout logic a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyLocalLvarArgumentParsing, LocalOutputInPropertyIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local output bit a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyLocalLvarArgumentParsing, ExplicitInputInPropertyParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "a");
}

TEST(PropertyLocalLvarArgumentParsing, InferredInputInPropertyParses) {
  auto r = Parse(
      "module m;\n"
      "  property p(local logic a);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 1u);
  EXPECT_EQ(item->prop_formals[0], "a");
}

TEST(PropertyLocalLvarArgumentParsing, InoutOnNonFirstLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a, local inout int b);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyLocalLvarArgumentParsing, OutputOnNonFirstLocalIsError) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a, local output bit b);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "property port direction must be 'input'",
                            2, "16.12.19"));
}

TEST(PropertyLocalLvarArgumentParsing, MultipleInputLocalsParse) {
  auto r = Parse(
      "module m;\n"
      "  property p(local input logic a, local bit b);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formals.size(), 2u);
  EXPECT_EQ(item->prop_formals[0], "a");
  EXPECT_EQ(item->prop_formals[1], "b");
}

TEST(PropertyLocalLvarArgumentParsing, AUserDefinedTypeEndsALocalRun) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [1:0] my_t;\n"
      "  property p(local int a, my_t x, local my_t y);\n"
      "    @(posedge clk) a;\n"
      "  endproperty\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kPropertyDecl);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->prop_formal_is_local.size(), 3u);
  EXPECT_TRUE(item->prop_formal_is_local[0]);
  EXPECT_FALSE(item->prop_formal_is_local[1]);
  EXPECT_TRUE(item->prop_formal_is_local[2]);
}

}  // namespace
