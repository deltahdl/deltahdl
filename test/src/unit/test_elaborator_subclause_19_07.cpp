#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(CoverageOptionWrites, DefinitionOnlyOptionWrittenProcedurallyIsError) {
  ElabFixture f;
  ElaborateSrc(
      "typedef struct { int per_instance; } opt_t;\n"
      "module m;\n"
      "  struct { opt_t option; } s;\n"
      "  bit v;\n"
      "  covergroup cg;\n"
      "    a: coverpoint v;\n"
      "  endgroup\n"
      "  cg c = new;\n"
      "  initial begin\n"
      "    c.option.per_instance = 1;\n"
      "    c.option.get_inst_coverage = 1;\n"
      "    c.a.option.auto_bin_max = 4;\n"
      "    c.option.detect_overlap = 1;\n"
      "    c.option.cross_retain_auto_bins = 0;\n"
      "    c.option.comment = \"x\";\n"
      "    c.a.option.weight = 3;\n"
      "    s.option.per_instance = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (auto [line, member] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {10u, "per_instance"}, {11u, "get_inst_coverage"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("option '") + member +
                                  "' can be set only in the covergroup "
                                  "definition",
                              line, "19.7"));
  }
  for (auto [line, member] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {12u, "auto_bin_max"},
           {13u, "detect_overlap"},
           {14u, "cross_retain_auto_bins"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("option '") + member +
                                  "' can be set only in the covergroup or "
                                  "coverpoint definition",
                              line, "19.7"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 5u);
}

TEST(CoverageOptionWeight, ConstantNegativeWeightIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    option.weight = -1;\n"
      "    ca: coverpoint a { type_option.weight = -2; }\n"
      "    cb: coverpoint b { option.weight = 0; }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the weight -1 is negative; a weight is a "
                            "non-negative integral value",
                            4, "19.7"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the weight -2 is negative; a weight is a "
                            "non-negative integral value",
                            5, "19.7"));
  EXPECT_EQ(f.diag.ErrorCount(), 2u);
}

TEST(CoverageOptionWeight, ConstantNegativeWeightIsErrorAtEveryLevel) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    type_option.weight = -1;\n"
      "    ca: coverpoint a { option.weight = -2; }\n"
      "    cb: coverpoint b;\n"
      "    x: cross ca, cb { type_option.weight = -3; }\n"
      "    y: cross ca, cb { option.weight = -4; }\n"
      "    z: cross ca, cb { type_option.weight = 0; option.weight = 0; }\n"
      "  endgroup\n"
      "endmodule\n",
      f);
  for (auto [line, weight] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {4u, "-1"}, {5u, "-2"}, {7u, "-3"}, {8u, "-4"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("the weight ") + weight +
                                  " is negative; a weight is a non-negative "
                                  "integral value",
                              line, "19.7"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 4u);
}

TEST(CoverageOptionWrites, DefinitionOnlyOptionWrittenAtEveryLevelIsError) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  bit [1:0] a, b;\n"
      "  covergroup cg;\n"
      "    option.get_inst_coverage = 1;\n"
      "    ca: coverpoint a; cb: coverpoint b;\n"
      "    x: cross ca, cb;\n"
      "  endgroup\n"
      "  cg k = new;\n"
      "  initial begin\n"
      "    k.option.auto_bin_max = 4;\n"
      "    k.ca.option.detect_overlap = 1;\n"
      "    k.x.option.cross_retain_auto_bins = 0;\n"
      "    k.x.option.at_least = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (auto [line, member] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {10u, "auto_bin_max"},
           {11u, "detect_overlap"},
           {12u, "cross_retain_auto_bins"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("option '") + member +
                                  "' can be set only in the covergroup or "
                                  "coverpoint definition",
                              line, "19.7"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

TEST(CoverageOptionWrites,
     DISABLED_ADefinitionOnlyOptionWrittenThroughAClassCovergroupIsError) {
  ElabFixture f;
  ElaborateSrc(
      "class C;\n"
      "  bit v;\n"
      "  covergroup cg; coverpoint v; endgroup\n"
      "  function new; cg = new; endfunction\n"
      "  function void f; cg.option.per_instance = 1; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C o;\n"
      "  initial begin\n"
      "    o = new;\n"
      "    o.cg.option.per_instance = 1;\n"
      "    o.cg.option.get_inst_coverage = 1;\n"
      "    o.cg.option.comment = \"c\";\n"
      "  end\n"
      "endmodule\n",
      f);
  for (auto [line, member] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {5u, "per_instance"},
           {11u, "per_instance"},
           {12u, "get_inst_coverage"}}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("option '") + member +
                                  "' can be set only in the covergroup "
                                  "definition",
                              line, "19.7"));
  }
  EXPECT_EQ(f.diag.ErrorCount(), 3u);
}

}  // namespace
