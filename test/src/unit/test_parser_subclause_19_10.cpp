#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <tuple>

#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, MemberTheLevelsStructureLacksIsError) {
  Parse(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    a: coverpoint x { option.name = \"n\"; }\n"
      "    b: coverpoint y { option.get_inst_coverage = 1; }\n"
      "    c: coverpoint x { option.cross_retain_auto_bins = 0; }\n"
      "    ab: cross a, b { option.name = \"n\"; }\n"
      "    ba: cross a, b { option.per_instance = 1; }\n"
      "    ac: cross a, c { option.detect_overlap = 1; }\n"
      "    bc: cross b, c { type_option.merge_instances = 1; }\n"
      "    ca: cross c, a { type_option.distribute_first = 1; }\n"
      "  endgroup\n"
      "endmodule\n");
  for (auto [line, member, level, subclause] : std::initializer_list<
           std::tuple<uint32_t, const char*, const char*, const char*>>{
           {3u, "option.name", "coverpoint", "19.7"},
           {4u, "option.get_inst_coverage", "coverpoint", "19.7"},
           {5u, "option.cross_retain_auto_bins", "coverpoint", "19.7"},
           {6u, "option.name", "cross", "19.7"},
           {7u, "option.per_instance", "cross", "19.7"},
           {8u, "option.detect_overlap", "cross", "19.7"},
           {9u, "type_option.merge_instances", "cross", "19.7.1"},
           {10u, "type_option.distribute_first", "cross", "19.7.1"}}) {
    EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                              std::string("coverage option '") + member +
                                  "' may not be specified at the " + level +
                                  " level",
                              line, subclause))
        << member << " at line " << line;
  }
  EXPECT_EQ(diag_.ErrorCount(), 8u);
}

TEST_F(VerifyParseTest, MemberTheLevelsStructureHoldsIsAccepted) {
  Parse(
      "module m;\n"
      "  covergroup cg @(posedge clk);\n"
      "    a: coverpoint x { option.detect_overlap = 1; option.goal = 90;\n"
      "      option.comment = \"c\"; option.at_least = 2; }\n"
      "    b: coverpoint y;\n"
      "    ab: cross a, b { option.cross_retain_auto_bins = 0;\n"
      "      option.goal = 80; option.comment = \"d\"; option.at_least = 2;\n"
      "      type_option.weight = 2; type_option.goal = 70;\n"
      "      type_option.comment = \"e\"; }\n"
      "  endgroup\n"
      "endmodule\n");
  EXPECT_EQ(diag_.ErrorCount(), 0u);
}

}  // namespace
