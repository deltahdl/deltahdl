#include <gtest/gtest.h>

#include <format>
#include <string>
#include <string_view>

#include "fixture_simulator.h"

using namespace delta;

namespace {

constexpr std::string_view kUnsizedParams =
    "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } s_t;\n"
    "  parameter logic [7:0] D [] = '{8'h6C, 8'h9A};\n"
    "  parameter logic [7:0] Q [$] = '{8'h12, 8'h34};\n"
    "  parameter s_t S [$] = '{8'hAB, 8'hCD};\n"
    "  localparam int SQ [$] = '{1, 2};\n"
    "  int nq [$];\n"
    "  localparam type(nq) PTQ = '{3, 4};\n"
    "  localparam int LD = D[1][3];\n"
    "  localparam int LDP = D[1][7:4];\n"
    "  localparam int LQ = Q[1][2];\n"
    "  localparam int LQP = Q[0][7:4];\n"
    "  localparam int LS = S[1].hi;\n"
    "  logic [D[1][7:4]:0] wd;\n"
    "  logic [Q[1][7:4]:0] wq;\n"
    "  logic [S[0].lo:0] ws;\n"
    "  logic [D[0][3]:0] wb;\n";

std::string UnsizedParamReads(std::string_view prefix) {
  return std::format(
      "  initial begin\n"
      "    $display(\"%h %h %h %h %h %h %h %h %h\",\n"
      "        {0}D[1][3], {0}D[1][2], {0}D[5][3], {0}D[0], {0}D[1][7:4],\n"
      "        {0}Q[1][2], {0}Q[0][7:4], {0}S[1].hi, {0}S[0]);\n"
      "    $display(\"%0d %0d %h %0d %0d %0d %0d\",\n"
      "        {0}D.size(), {0}Q.size(), {0}Q[$], {0}SQ.size(), {0}SQ[$],\n"
      "        {0}PTQ.size(), {0}PTQ[$]);\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d\",\n"
      "        {0}LD, {0}LDP, {0}LQ, {0}LQP, {0}LS, $bits({0}wd),\n"
      "        $bits({0}wq), $bits({0}ws), $bits({0}wb));\n"
      "  end\n",
      prefix);
}

constexpr std::string_view kUnsizedParamsPrinted =
    "1 0 x 6c 9 1 1 c ab\n"
    "2 2 34 2 2 2 4\n"
    "1 9 1 1 12 10 4 12 2\n";

TEST(UnsizedArrayParameterReads, ModuleParameterElementsReadTheirValues) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::format("module top;\n{}{}endmodule\n",
                                   kUnsizedParams, UnsizedParamReads("")),
                       f),
            kUnsizedParamsPrinted);
}

TEST(UnsizedArrayParameterReads, PackageParameterElementsReadTheirValues) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::format("package pk;\n{}endpackage\n"
                                   "module top;\n{}endmodule\n",
                                   kUnsizedParams, UnsizedParamReads("pk::")),
                       f),
            kUnsizedParamsPrinted);
}

TEST(UnsizedArrayParameterReads,
     CompilationUnitParameterElementsReadTheirValues) {
  SimFixture f;
  EXPECT_EQ(RunCapture(std::format("{}module top;\n{}endmodule\n",
                                   kUnsizedParams, UnsizedParamReads("")),
                       f),
            kUnsizedParamsPrinted);
}

}  // namespace
