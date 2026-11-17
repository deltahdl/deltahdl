#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>
#include <string>
#include <tuple>
#include <utility>

#include "fixture_program.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST_F(VerifyParseTest, CovergroupWithOption) {
  auto* unit = Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        option.per_instance = 1;
        coverpoint x;
      endgroup
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, DistinctCovergroupOptionsAccepted) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        option.per_instance = 1;
        option.comment = "hi";
        option.goal = 90;
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, DuplicateCovergroupOptionIsError) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        option.goal = 90;
        option.goal = 80;
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'option.goal' is assigned more "
                            "than once in the same covergroup definition",
                            5, "19.7"));
}

TEST_F(VerifyParseTest, NonAdjacentDuplicateCovergroupOptionIsError) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        option.weight = 2;
        option.comment = "c";
        option.weight = 3;
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'option.weight' is assigned more "
                            "than once in the same covergroup definition",
                            6, "19.7"));
}

TEST_F(VerifyParseTest, InstanceAndTypeOptionSameMemberAccepted) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        option.comment = "inst";
        type_option.comment = "type";
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, DuplicateTypeOptionIsError) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        type_option.weight = 2;
        type_option.weight = 5;
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'type_option.weight' is assigned "
                            "more than once in the same covergroup definition",
                            5, "19.7"));
}

TEST_F(VerifyParseTest, OptionValueMayBeCovergroupFormal) {
  Parse(R"(
    module m;
      covergroup g1 (int w, string instComment) @(posedge clk);
        option.weight = w;
        option.comment = instComment;
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, SameOptionAtCovergroupAndCoverpointAccepted) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        option.weight = 1;
        cp: coverpoint x {
          option.weight = 2;
        }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, ClassEmbeddedCovergroupDistinctOptionsAccepted) {
  Parse(R"(
    class c;
      covergroup cg;
        option.per_instance = 1;
        option.comment = "hi";
        coverpoint x;
      endgroup
    endclass
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, ClassEmbeddedCovergroupDuplicateOptionIsError) {
  Parse(R"(
    class c;
      covergroup cg;
        option.goal = 90;
        option.goal = 80;
        coverpoint x;
      endgroup
    endclass
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'option.goal' is assigned more "
                            "than once in the same covergroup definition",
                            5, "19.7"));
}

TEST_F(VerifyParseTest, DuplicateOptionWithoutClockingEventIsError) {
  Parse(R"(
    module m;
      covergroup cg;
        option.weight = 1;
        option.weight = 2;
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'option.weight' is assigned more "
                            "than once in the same covergroup definition",
                            5, "19.7"));
}

TEST_F(VerifyParseTest, DuplicateOptionWithCustomSampleMethodIsError) {
  Parse(R"(
    module m;
      covergroup cg with function sample(int y);
        option.at_least = 1;
        option.at_least = 2;
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'option.at_least' is assigned "
                            "more than once in the same covergroup definition",
                            5, "19.7"));
}

TEST_F(VerifyParseTest, CoverpointLevelAllowedOptionsAccepted) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        cp: coverpoint x {
          option.at_least = 2;
          option.auto_bin_max = 8;
          option.detect_overlap = 1;
        }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, PerInstanceAtCoverpointLevelIsError) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        cp: coverpoint x {
          option.per_instance = 1;
        }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'option.per_instance' may not be "
                            "specified at the coverpoint level",
                            5, "19.7"));
}

TEST_F(VerifyParseTest, CrossOnlyOptionAtCoverpointLevelIsError) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        cp: coverpoint x {
          option.cross_num_print_missing = 3;
        }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'option.cross_num_print_missing' "
                            "may not be specified at the coverpoint level",
                            5, "19.7"));
}

TEST_F(VerifyParseTest, CrossLevelAllowedOptionsAccepted) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        a: coverpoint x;
        b: coverpoint y;
        c: cross a, b {
          option.weight = 3;
          option.cross_num_print_missing = 5;
          option.cross_retain_auto_bins = 1;
        }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest, AutoBinMaxAtCrossLevelIsError) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        a: coverpoint x;
        b: coverpoint y;
        c: cross a, b {
          option.auto_bin_max = 8;
        }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'option.auto_bin_max' may not be "
                            "specified at the cross level",
                            7, "19.7"));
}

TEST_F(VerifyParseTest, GetInstCoverageAtCrossLevelIsError) {
  Parse(R"(
    module m;
      covergroup cg @(posedge clk);
        a: coverpoint x;
        b: coverpoint y;
        c: cross a, b {
          option.get_inst_coverage = 1;
        }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "coverage option 'option.get_inst_coverage' may "
                            "not be specified at the cross level",
                            7, "19.7"));
}

TEST_F(VerifyParseTest, TypeOptionNamingCovergroupFormalIsError) {
  Parse(R"(
    module m;
      bit v;
      bit w;
      covergroup cg (int k);
        option.weight = k;
        type_option.weight = k;
        type_option.goal = $clog2(k);
        a: coverpoint v { type_option.goal = k + 1; }
        b: coverpoint w;
        x: cross a, b { type_option.weight = k; }
      endgroup
    endmodule
  )");
  EXPECT_EQ(diag_.ErrorCount(), 4u);
  for (uint32_t line : {7u, 8u, 9u, 11u}) {
    EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                              "a type option is set with a constant "
                              "expression; covergroup formal 'k' is not one",
                              line, "19.7.1"));
  }
}

TEST_F(VerifyParseTest, SameOptionInTwoCoverpointOrCrossBodiesAccepted) {
  Parse(R"(
    module m;
      bit [1:0] x, y;
      covergroup cg;
        a: coverpoint x { option.weight = 1; type_option.goal = 3; }
        b: coverpoint y { option.weight = 2; type_option.goal = 4; }
        ab: cross a, b { option.goal = 1; type_option.comment = "a"; }
        ba: cross b, a { option.goal = 2; type_option.comment = "b"; }
      endgroup
    endmodule
  )");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(VerifyParseTest,
       DISABLED_AnOptionSetTwiceInOneCoverpointOrCrossIsError) {
  Parse(R"(
    module m;
      bit [1:0] x, y;
      covergroup cg;
        a: coverpoint x { option.weight = 1; option.weight = 2; }
        b: coverpoint y { type_option.goal = 3; type_option.goal = 4; }
        ab: cross a, b { option.goal = 1; option.goal = 2; }
        ba: cross b, a { type_option.comment = "a"; type_option.comment = "b"; }
      endgroup
    endmodule
  )");
  for (auto [line, option] :
       std::initializer_list<std::pair<uint32_t, const char*>>{
           {5u, "option.weight"},
           {6u, "type_option.goal"},
           {7u, "option.goal"},
           {8u, "type_option.comment"}}) {
    EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                              std::string("coverage option '") + option +
                                  "' is assigned more than once in the same "
                                  "covergroup definition",
                              line, "19.7"));
  }
  EXPECT_EQ(diag_.ErrorCount(), 4u);
}

TEST_F(VerifyParseTest, ADuplicateOptionIsAnErrorInEveryScope) {
  Parse(R"(
    bit gx;
    covergroup gcu; option.goal = 1; option.goal = 2; coverpoint gx; endgroup
    package p;
      bit v;
      covergroup g; option.goal = 1; option.goal = 2; coverpoint v; endgroup
    endpackage
    interface i;
      bit v;
      covergroup g; option.goal = 1; option.goal = 2; coverpoint v; endgroup
    endinterface
    program pr;
      bit v;
      covergroup g; option.goal = 1; option.goal = 2; coverpoint v; endgroup
    endprogram
    checker ck(bit v);
      covergroup g; option.goal = 1; option.goal = 2; coverpoint v; endgroup
    endchecker
  )");
  for (uint32_t line : {3u, 6u, 10u, 14u, 17u}) {
    EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                              "coverage option 'option.goal' is assigned more "
                              "than once in the same covergroup definition",
                              line, "19.7"));
  }
  EXPECT_EQ(diag_.ErrorCount(), 5u);
}

TEST_F(VerifyParseTest, InstanceOptionsAtALevelThatDoesNotTakeThemAreErrors) {
  Parse(R"(
    module m;
      bit [1:0] x, y;
      covergroup cg;
        a: coverpoint x {
          option.name = "n";
          option.get_inst_coverage = 1;
          option.cross_retain_auto_bins = 1;
          option.weight = 2; option.goal = 90; option.comment = "c";
        }
        b: coverpoint y;
        ab: cross a, b {
          option.name = "n";
          option.per_instance = 1;
          option.detect_overlap = 1;
          option.at_least = 2; option.goal = 80; option.comment = "d";
        }
      endgroup
    endmodule
  )");
  for (auto [line, member, level] :
       std::initializer_list<std::tuple<uint32_t, const char*, const char*>>{
           {6u, "name", "coverpoint"},
           {7u, "get_inst_coverage", "coverpoint"},
           {8u, "cross_retain_auto_bins", "coverpoint"},
           {13u, "name", "cross"},
           {14u, "per_instance", "cross"},
           {15u, "detect_overlap", "cross"}}) {
    EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                              std::string("coverage option 'option.") + member +
                                  "' may not be specified at the " + level +
                                  " level",
                              line, "19.7"));
  }
  EXPECT_EQ(diag_.ErrorCount(), 6u);
}

}  // namespace
