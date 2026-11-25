#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(ConcatenationElaboration, ConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b, c;\n"
      "  assign a = {b, c};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationElaboration, MultipleConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a;\n"
      "  logic [3:0] b;\n"
      "  assign a = {2{b}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationElaboration, StreamingConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] a;\n"
      "  logic [7:0] b, c;\n"
      "  initial a = {>> {b, c}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationElaboration, EmptyUnpackedArrayConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int q[$];\n"
      "  initial q = {};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationElaboration, ConstantConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = {8'hAB, 8'hCD};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ConcatenationElaboration, ConstantMultipleConcatenationElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter P = {4{4'hF}};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

std::vector<uint32_t> ErrorLinesOfCondition(const std::string& condition) {
  ElabFixture f;
  ElaborateSrc(
      "module m(input a, b, c, input [1:0] n, output y);\n"
      "  specparam K = 2;\n"
      "  specify\n"
      "    if (" +
          condition +
          ") (a => y) = 1;\n"
          "  endspecify\n"
          "endmodule\n",
      f);
  std::vector<uint32_t> lines;
  for (const auto& d : f.diag.Diagnostics()) {
    if (d.severity == DiagSeverity::kError) lines.push_back(d.loc.line);
  }
  return lines;
}

TEST(ConcatenationElaboration,
     AModulePathConcatenationTakesModulePathOperations) {
  for (const char* condition : {"{a & b, c}", "{~a, b}", "{a ? b : c, a}",
                                "{{a, b}, c}", "{2{a}}", "{K{a & b}}"}) {
    EXPECT_TRUE(ErrorLinesOfCondition(condition).empty()) << condition;
  }
}

TEST(ConcatenationElaboration,
     DISABLED_AModulePathReplicationCountMustBeConstant) {
  for (const char* condition : {"{n{a}}", "{b{a}}", "{(n){a, b}}"}) {
    EXPECT_EQ(ErrorLinesOfCondition(condition), std::vector<uint32_t>{4})
        << condition;
  }
}

TEST(ConcatenationElaboration,
     DISABLED_AModulePathReplicationCountTakesAnyConstantOperator) {
  for (const char* condition :
       {"{(1 + 1){a}}", "{(K * 1){a}}", "{(K > 1 ? 2 : 3){a}}"}) {
    EXPECT_TRUE(ErrorLinesOfCondition(condition).empty()) << condition;
  }
}

}  // namespace
