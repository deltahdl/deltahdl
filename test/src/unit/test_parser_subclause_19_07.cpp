#include "fixture_program.h"

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

// §19.7: distinct covergroup-level options may each be assigned once.
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

// §19.7: specifying a value for the same option more than once within the same
// covergroup definition is an error.
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
  EXPECT_TRUE(diag_.HasErrors());
}

// §19.7: the repeat is detected even when other, distinct option assignments
// separate the two assignments of the same option.
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
  EXPECT_TRUE(diag_.HasErrors());
}

// §19.7: the same member name assigned once through `option` and once through
// `type_option` names two different options, so it is not a repeat.
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

// §19.7: an option repeated at the covergroup level in the same definition is
// an error even for a type_option.
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
  EXPECT_TRUE(diag_.HasErrors());
}

// §19.7: the option value is an expression. The LRM's own example initializes
// option.weight from a covergroup formal argument, so an identifier value that
// names a formal (declared with the §19.3 formal-list syntax) must be accepted.
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

// §19.7: the same-option-twice error is scoped to a single syntactic level. The
// same option assigned once at the covergroup level and once inside a
// coverpoint body names two distinct option instances, so it is not a repeat.
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

// §19.7: a covergroup may be declared as a class member; the option-assignment
// syntax and the distinct-options acceptance hold in that syntactic position
// too.
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

// §19.7: the same-option-twice rule applies to a class-embedded covergroup as
// well as one declared at module scope.
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
  EXPECT_TRUE(diag_.HasErrors());
}

// §19.7: the clocking event on a covergroup header is optional; the duplicate
// option is still diagnosed when the header names no event.
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
  EXPECT_TRUE(diag_.HasErrors());
}

// §19.7: the duplicate-option diagnosis also holds for a covergroup that
// overrides its sample method, whose option values are scanned on a different
// path than an ordinary covergroup's.
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
  EXPECT_TRUE(diag_.HasErrors());
}

// §19.7, Table 19-2: options allowed at the coverpoint level (weight, goal,
// comment, at_least, auto_bin_max, detect_overlap) are accepted inside a
// coverpoint body.
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

// §19.7, Table 19-2: a covergroup-only option (per_instance) may not be
// specified at the coverpoint level.
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
  EXPECT_TRUE(diag_.HasErrors());
}

// §19.7, Table 19-2: a cross-only option (cross_num_print_missing) may not be
// specified at the coverpoint level.
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
  EXPECT_TRUE(diag_.HasErrors());
}

// §19.7, Table 19-2: options allowed at the cross level (weight, goal, comment,
// at_least, cross_num_print_missing, cross_retain_auto_bins) are accepted
// inside a cross body.
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

// §19.7, Table 19-2: a coverpoint-only option (auto_bin_max) may not be
// specified at the cross level.
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
  EXPECT_TRUE(diag_.HasErrors());
}

// §19.7, Table 19-2: a covergroup-only option (get_inst_coverage) may not be
// specified at the cross level.
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
  EXPECT_TRUE(diag_.HasErrors());
}

}  // namespace
