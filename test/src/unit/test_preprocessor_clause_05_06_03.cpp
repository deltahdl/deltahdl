#include <gtest/gtest.h>

#include "fixture_preprocessor.h"

using namespace delta;

namespace {

TEST(SystemNamePreprocessor, SystemTaskPassesThroughPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  initial $display(\"hello\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$display"), std::string::npos);
}

TEST(SystemNamePreprocessor, SystemFunctionPassesThroughPreprocessor) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  logic [31:0] w;\n"
      "  assign w = $clog2(16);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$clog2"), std::string::npos);
}

TEST(SystemNamePreprocessor, SystemTaskInMacroExpansion) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define LOG(msg) $display(msg)\n"
      "module t;\n"
      "  initial `LOG(\"hello\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(SystemNamePreprocessor, EmbeddedDollarSystemIdPreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  initial $test$plusargs(\"flag\");\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$test$plusargs"), std::string::npos);
}

TEST(SystemNamePreprocessor, MultipleSystemTasksPreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  initial begin\n"
      "    $display(\"a\");\n"
      "    $finish;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$display"), std::string::npos);
  EXPECT_NE(result.find("$finish"), std::string::npos);
}

TEST(SystemNamePreprocessor, UnderscoreLeadingSystemIdPreserved) {
  PreprocFixture f;
  auto result = Preprocess(
      "module t;\n"
      "  initial $_my_task;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$_my_task"), std::string::npos);
}

TEST(SystemNamePreprocessor, SystemIdNotConfusedWithDirective) {
  PreprocFixture f;
  auto result = Preprocess(
      "`define WIDTH 8\n"
      "module t;\n"
      "  initial $display(`WIDTH);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
  EXPECT_NE(result.find("$display"), std::string::npos);
}

}  // namespace
