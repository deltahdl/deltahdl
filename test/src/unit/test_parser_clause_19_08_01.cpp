// §19.8.1: Overriding the built-in sample method

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA211, CovergroupDecl_WithSampleFunction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(int x, bit y);\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverageEvent_WithFunctionSample) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(bit [3:0] val);\n"
              "    coverpoint val;\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_SampleFunctionWithBody) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  covergroup cg with function sample(int val);\n"
              "    coverpoint val {\n"
              "      bins low = {[0:127]};\n"
              "      bins high = {[128:255]};\n"
              "    }\n"
              "  endgroup\n"
              "endmodule\n"));
}

TEST(ParserA211, CoverGroup_SampleFunctionASTVerification) {
  auto r = Parse(
      "module m;\n"
      "  covergroup sampled_cg with function sample(int data);\n"
      "    coverpoint data;\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kCovergroupDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "sampled_cg");
}

}  // namespace
