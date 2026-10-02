#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <tuple>

#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.7.1, Table 19-4: strobe, merge_instances and distribute_first are type
// options of the covergroup level alone, and real_interval of the covergroup
// and coverpoint levels, so each written in a coverpoint or cross body the
// table excludes it from is an error.
TEST_F(VerifyParseTest, TypeOptionAtALevelTable194ExcludesIsError) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        a: coverpoint x { type_option.strobe = 1; }
        b: coverpoint y { type_option.merge_instances = 1; }
        c: coverpoint x { type_option.distribute_first = 1; }
        ab: cross a, b { type_option.real_interval = 2.0; }
        ba: cross a, b { type_option.strobe = 1; }
      endgroup
    endmodule
  )");
  for (auto [line, member, level] :
       std::initializer_list<std::tuple<uint32_t, const char*, const char*>>{
           {4u, "strobe", "coverpoint"},
           {5u, "merge_instances", "coverpoint"},
           {6u, "distribute_first", "coverpoint"},
           {7u, "real_interval", "cross"},
           {8u, "strobe", "cross"}}) {
    EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                              std::string("coverage option 'type_option.") +
                                  member + "' may not be specified at the " +
                                  level + " level",
                              line, "19.7.1"));
  }
  EXPECT_EQ(diag_.ErrorCount(), 5u);
}

// §19.7.1, Table 19-4: weight, goal and comment are type options of every
// level, and real_interval of a coverpoint, so none of them is reported.
TEST_F(VerifyParseTest, TypeOptionAtALevelTable194AllowsIsAccepted) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        a: coverpoint x {
          type_option.weight = 2;
          type_option.goal = 90;
          type_option.comment = "a";
          type_option.real_interval = 2.0;
        }
        b: coverpoint y;
        ab: cross a, b {
          type_option.weight = 3;
          type_option.goal = 80;
          type_option.comment = "ab";
        }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

}  // namespace
