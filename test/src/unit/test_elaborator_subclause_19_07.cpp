#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <utility>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.7: per_instance and get_inst_coverage can be set only in the covergroup
// definition, and auto_bin_max, detect_overlap and cross_retain_auto_bins only
// in the covergroup or coverpoint definition; a procedural write to one of
// them through an instance, at the covergroup's level or a coverpoint's, is an
// error. The other instance options can be assigned after instantiation, and a
// struct member that happens to be named `option` is no covergroup's.
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

}  // namespace
