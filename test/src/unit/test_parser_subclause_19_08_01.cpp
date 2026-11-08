#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(OverriddenSampleMethod, BasicOverrideParses) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, OutputSampleFormalRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(output int x);
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a sample method formal argument cannot designate "
                            "an output direction",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, InoutSampleFormalRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(inout int x);
        coverpoint x;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a sample method formal argument cannot designate "
                            "an output direction",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, InputSampleFormalAllowed) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(input int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, NameSharedBetweenBothListsRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg (int v) with function sample(int v, bit b);
        coverpoint v;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'v' shares the "
                            "covergroup argument scope and cannot reuse a "
                            "covergroup formal-argument name",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, DistinctNamesAcrossListsAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg (int w) with function sample(int v, bit b);
        coverpoint v;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SharedNameAmongManyFormalsRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg (int a, ref int data) with function sample(bit c, int data);
        coverpoint c;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'data' shares the "
                            "covergroup argument scope and cannot reuse a "
                            "covergroup formal-argument name",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, DefaultValuedSampleFormalStillCollides) {
  auto r = Parse(R"(
    module m;
      covergroup cg (int v) with function sample(int v = 0);
        coverpoint v;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'v' shares the "
                            "covergroup argument scope and cannot reuse a "
                            "covergroup formal-argument name",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, OutputOnLaterSampleFormalRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int a, output int b);
        coverpoint a;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "a sample method formal argument cannot designate "
                            "an output direction",
                            3, "19.8.1"));
}

TEST(OverriddenSampleMethod, RefSampleFormalAllowed) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(ref int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalInOptionAssignmentRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
        option.per_instance = a;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'a' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            5, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInTypeOptionAssignmentRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int weight_src, int x);
        coverpoint x;
        type_option.weight = weight_src;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'weight_src' may "
                            "only designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            5, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInsideOptionValueExpressionRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int a, int x);
        coverpoint x;
        option.weight = a + 1;
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'a' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            5, "19.8.1"));
}

TEST(OverriddenSampleMethod, NonFormalInOptionAssignmentAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      int w;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
        option.weight = w;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalInConditionalGuardAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x iff (a);
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalAsCrossItemAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
        cross x, a;
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalInBinRangeRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { bins b = {[0:w]}; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInTransitionRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { bins b = (w => 1); }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInBinWithFilterRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { bins b[] = {[0:7]} with (item < w); }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInBinArraySizeRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { bins b[w] = {[0:7]}; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInIllegalBinsValueRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { illegal_bins b = {w}; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a bin specification",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInCoverpointOptionRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        coverpoint v { option.weight = w; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            4, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInCrossOptionRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        a: coverpoint v;
        b: coverpoint w;
        X: cross a, b { option.weight = w; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a coverage-option value",
                            6, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInCrossIntersectRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w);
        a: coverpoint v;
        b: coverpoint w;
        X: cross a, b { bins s = binsof(a) intersect {w}; }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'w' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a cross bin select expression",
                            6, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInCrossWithRejected) {
  auto r = Parse(R"(
    module m;
      covergroup cg with function sample(int v, int w, int lim);
        a: coverpoint v;
        b: coverpoint w;
        X: cross a, b { bins s = X with (a < lim); }
      endgroup
    endmodule
  )");
  EXPECT_TRUE(ReportedError(r.diags,
                            "sample method formal argument 'lim' may only "
                            "designate a coverpoint or conditional guard "
                            "expression, not a cross bin select expression",
                            6, "19.8.1"));
}

TEST(OverriddenSampleMethod, SampleFormalInBinGuardAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int v, bit en);
        coverpoint v { bins b = {[0:3]} iff (en); }
      endgroup
    endmodule
  )"));
}

TEST(OverriddenSampleMethod, SampleFormalInCrossBinGuardAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int v, int w, bit en);
        a: coverpoint v;
        b: coverpoint w;
        X: cross a, b { bins s = binsof(a) iff (en); }
      endgroup
    endmodule
  )"));
}

}  // namespace
