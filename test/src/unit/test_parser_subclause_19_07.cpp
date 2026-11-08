#include <gtest/gtest.h>

#include <cstdint>

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

}  // namespace
