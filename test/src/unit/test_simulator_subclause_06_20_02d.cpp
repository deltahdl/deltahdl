#include <gtest/gtest.h>

#include <format>
#include <string>
#include <string_view>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

constexpr std::string_view kUnsizedParams =
    "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } s_t;\n"
    "  parameter logic [1:0][3:0] D [] = '{8'h6C, 8'h9A};\n"
    "  parameter logic [1:0][3:0] Q [$] = '{8'h12, 8'h34};\n"
    "  parameter logic [7:0] V [] = '{8'h56, 8'h78};\n"
    "  parameter s_t S [$] = '{8'hAB, 8'hCD};\n"
    "  parameter logic [1:0][3:0] A [2] = '{8'h6C, 8'h9A};\n"
    "  localparam int SQ [$] = '{1, 2};\n"
    "  int nq [$];\n"
    "  localparam type(nq) PTQ = '{3, 4};\n"
    "  localparam int LD = D[1][1];\n"
    "  localparam int LQ = Q[0][1];\n"
    "  localparam int LV = V[1][7:4];\n"
    "  localparam int LS = S[1].hi;\n"
    "  localparam int LA = A[1][1];\n"
    "  logic [D[1][1]:0] wd;\n"
    "  logic [Q[0][1]:0] wq;\n"
    "  logic [V[0][3:0]:0] wv;\n"
    "  logic [S[0].lo:0] ws;\n"
    "  logic [A[1][1]:0] wa;\n";

std::string UnsizedParamReads(std::string_view prefix) {
  return std::format(
      "  initial begin\n"
      "    $display(\"%h %h %h %h %h %h %h %h %h\",\n"
      "        {0}D[1][1], {0}D[0], {0}D[1][1][3:2], {0}Q[0][1], {0}Q[1],\n"
      "        {0}V[1], {0}V[1][7:4], {0}S[1].hi, {0}S[0]);\n"
      "    $display(\"%0d %0d %h %0d %0d %0d %0d\",\n"
      "        {0}D.size(), {0}Q.size(), {0}Q[$], {0}SQ.size(), {0}SQ[$],\n"
      "        {0}PTQ.size(), {0}PTQ[$]);\n"
      "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d %0d %0d\",\n"
      "        {0}LD, {0}LQ, {0}LV, {0}LS, {0}LA,\n"
      "        $bits({0}wd), $bits({0}wq), $bits({0}wv), $bits({0}ws),\n"
      "        $bits({0}wa));\n"
      "    $display(\"%h %h\", {0}A[1][1], {0}A[0]);\n"
      "  end\n",
      prefix);
}

constexpr std::string_view kUnsizedParamsPrinted =
    "9 6c 2 1 34 78 7 c ab\n"
    "2 2 34 2 2 2 4\n"
    "9 1 7 12 9 10 2 7 12 10\n"
    "9 6c\n";

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
