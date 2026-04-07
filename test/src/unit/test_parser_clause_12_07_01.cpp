#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(LoopSyntaxParsing, ForWithMultipleVarDecls) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0, int j = 10; i < j; i++, j--)\n"
      "      a = i + j;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, ForCommaSeparatedUntypedInit) {
  auto r = Parse(
      "module m;\n"
      "  integer i, j;\n"
      "  initial begin\n"
      "    for (i = 0, j = 10; i < j; i++, j--)\n"
      "      a = i + j;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, ForEmptyInit) {
  auto r = Parse(
      "module m;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    i = 0;\n"
      "    for (; i < 5; i++)\n"
      "      a = i;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, ForEmptyCondition) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0;; i++) begin\n"
      "      if (i == 5) break;\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, ForEmptyStep) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10;)\n"
      "      i = i + 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LoopSyntaxParsing, ForAllComponentsEmpty) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    for (;;)\n"
      "      break;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
