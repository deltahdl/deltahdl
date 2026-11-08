#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

std::string LocalSource(const std::string& decls, const std::string& drive) {
  return "module t;\n"
         "  logic clk = 0;\n"
         "  logic c = 0;\n"
         "  logic a = 0;\n"
         "  logic b = 0;\n"
         "  int data = 0;\n"
         "  int data_in = 0;\n"
         "  int data_out = 0;\n"
         "  int do1 = 0;\n"
         "  int hits = 0;\n"
         "  int last = 0;\n"
         "  always #5 clk = ~clk;\n" +
         decls + "  initial begin\n" + drive +
         "    #40 $finish;\n"
         "  end\n"
         "  initial forever begin\n"
         "    wait (rule.triggered);\n"
         "    hits = hits + 1;\n"
         "    last = $time;\n"
         "    @(posedge clk);\n"
         "  end\n"
         "endmodule\n";
}

TEST(LocalVariableFormals, BodyLocalAssignedByAMatchItemIsReadLater) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      LocalSource("  sequence rule;\n"
                  "    int v1;\n"
                  "    @(posedge clk) (c, v1 = data) ##2 (do1 == v1);\n"
                  "  endsequence\n",
                  "    #10 c = 1; data = 5;\n"
                  "    #10 c = 0; data = 6; do1 = 6;\n"
                  "    #10 do1 = 5;\n"
                  "    #10 do1 = 0;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 35u);
}

TEST(LocalVariableFormals, EachAttemptHoldsItsOwnCopy) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      LocalSource("  sequence rule;\n"
                  "    int v1;\n"
                  "    @(posedge clk) (c, v1 = data) ##2 (do1 == v1);\n"
                  "  endsequence\n",
                  "    #10 c = 1; data = 5;\n"
                  "    #10 data = 6;\n"
                  "    #10 c = 0; do1 = 5;\n"
                  "    #10 do1 = 6;\n"
                  "    #10 do1 = 0;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 2u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 45u);
}

TEST(LocalVariableFormals, InputLocalFormalIsInitializedFromTheActual) {
  SimFixture f;
  auto* hits = RunAndFindVar(LocalSource("  sequence sub(local input int lv);\n"
                                         "    c ##1 (do1 == lv);\n"
                                         "  endsequence\n"
                                         "  sequence rule;\n"
                                         "    @(posedge clk) sub(data);\n"
                                         "  endsequence\n",
                                         "    #10 c = 1; data = 5;\n"
                                         "    #10 c = 0; data = 6; do1 = 5;\n"
                                         "    #10 do1 = 6;\n"
                                         "    #10 do1 = 0;\n"),
                             f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

TEST(LocalVariableFormals, ALocalFormalTakesItsDeclaredType) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      LocalSource(
          "  typedef logic [7:0] byte_t;\n"
          "  sequence sub(local input logic [7:0] lv,\n"
          "               local input bit [7:0] lb,\n"
          "               local input byte_t lt,\n"
          "               local input logic [8:1] lr,\n"
          "               local input logic signed [7:0] ls,\n"
          "               local input byte unsigned lu);\n"
          "    c ##1 (do1 == lv && do1 == lb && do1 == lt && lr[1] &&\n"
          "           ls < 0 && lu > 128);\n"
          "  endsequence\n"
          "  sequence rule;\n"
          "    @(posedge clk) sub(data, data, data, data, data, data);\n"
          "  endsequence\n",
          "    #10 c = 1; data = 165;\n"
          "    #10 c = 0; data = 6; do1 = 165;\n"
          "    #10 do1 = 6;\n"
          "    #10 do1 = 0;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 25u);
}

TEST(LocalVariableFormals, InoutLocalFormalIsAssignedBackAtTheMatch) {
  SimFixture f;
  auto* hits = RunAndFindVar(
      LocalSource("  sequence sub_seq2(local inout int lv);\n"
                  "    (a ##1 !a, lv += data_in) ##1 b && (data_out == lv);\n"
                  "  endsequence\n"
                  "  sequence rule;\n"
                  "    int v1;\n"
                  "    @(posedge clk) (c, v1 = data) ##1 sub_seq2(v1) ##1 "
                  "(do1 == v1);\n"
                  "  endsequence\n",
                  "    #10 c = 1; data = 5;\n"
                  "    #10 c = 0; a = 1;\n"
                  "    #10 a = 0; data_in = 3;\n"
                  "    #10 b = 1; data_out = 8;\n"
                  "    #10 b = 0; do1 = 8;\n"
                  "    #10 do1 = 0;\n"),
      f, "hits");
  ASSERT_NE(hits, nullptr);
  EXPECT_EQ(hits->value.ToUint64(), 1u);
  EXPECT_EQ(f.ctx.FindVariable("last")->value.ToUint64(), 55u);
}

}  // namespace
