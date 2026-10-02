#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §19.8.1: a covergroup may override the built-in sample() method with a
// triggering function that accepts formal arguments. A well-formed override
// parses cleanly.
TEST(OverriddenSampleMethod, BasicOverrideParses) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// §19.8.1: a formal argument of an overridden sample method shall not designate
// an output direction.
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

// §19.8.1: inout designates an output direction as well and is likewise not
// permitted for a sample method formal argument.
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

// §19.8.1: an input-direction sample formal (the default) is allowed.
TEST(OverriddenSampleMethod, InputSampleFormalAllowed) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(input int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// §19.8.1: the sample method formals share the covergroup's argument scope (the
// formals consumed by the covergroup new operator), so it shall be an error for
// the same argument name to appear in both lists.
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

// §19.8.1: distinct names across the covergroup and sample argument lists do
// not collide and are accepted.
TEST(OverriddenSampleMethod, DistinctNamesAcrossListsAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg (int w) with function sample(int v, bit b);
        coverpoint v;
      endgroup
    endmodule
  )"));
}

// §19.8.1: the collision check applies to any shared name, including one buried
// among several covergroup and sample formals.
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

// §19.8.1: the shared-name error is about the argument name, so it still fires
// when the colliding sample formal carries a default value -- the name is bound
// before the default expression and is checked against the covergroup formals
// all the same.
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

// §19.8.1: the output-direction prohibition applies to every sample formal, not
// only the first, so an output direction on a later formal is also rejected.
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

// §19.8.1: only an output direction is forbidden for a sample formal. A
// pass-by-reference (ref) formal does not designate an output direction and is
// therefore accepted.
TEST(OverriddenSampleMethod, RefSampleFormalAllowed) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(ref int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// §19.8.1: a sample method formal may only designate a coverpoint or a
// conditional guard expression; it shall be an error to use one in any other
// context. Referencing the sample formal 'a' from a coverage-option assignment
// (as in the LRM's own error example, option.per_instance = b) is rejected.
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

// §19.8.1: the prohibition applies to a type_option assignment just as to an
// option assignment; a sample formal on the right-hand side is still illegal.
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

// §19.8.1: the illegal reference need not be the whole option value -- a sample
// formal appearing anywhere inside the value expression is still an illegal
// use, so it is detected even when embedded in a larger arithmetic expression.
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

// §19.8.1: the usage check flags only sample formals. An option assignment
// whose value expression names something other than a sample formal (here an
// enclosing-scope variable) is left alone, so the covergroup parses cleanly.
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

// §19.8.1: the second legal context is a conditional guard expression. A sample
// formal referenced from a coverpoint's `iff` guard designates such a guard and
// is accepted, not flagged like the coverage-option case.
TEST(OverriddenSampleMethod, SampleFormalInConditionalGuardAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x iff (a);
      endgroup
    endmodule
  )"));
}

// §19.8.1: a cross item designates a (possibly implicit) coverpoint, so naming
// a sample formal as a cross item is legal. This mirrors §19.8.1's own valid
// example, `cross x, a`, where a and x are the overridden sample method
// formals.
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

// §19.8.1: a bin's value range is neither a coverpoint nor a conditional guard
// expression, so a sample formal bounding the range is an error.
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

// §19.8.1: a sample formal written as a step of a transition bin is used
// outside the two legal contexts.
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

// §19.8.1: a bin's `with` filter is a with_covergroup_expression, not a
// coverpoint or guard, so a sample formal there is an error.
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

// §19.8.1: the size of a fixed bin array is another context than the two the
// clause allows.
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

// §19.8.1: an illegal_bins value naming a sample formal is rejected as a bins
// value is.
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

// §19.8.1: an option set inside a coverpoint is a coverage-option value just as
// one set at the covergroup level is.
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

// §19.8.1: an option set inside a cross body is a coverage-option value too.
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

// §19.8.1: the range a cross bin's `binsof ... intersect` selects by is a
// select expression, not a coverpoint or guard.
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

// §19.8.1: a cross bin's `with` expression names the cross items; a sample
// formal that is not one of them is used outside the legal contexts.
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

// §19.8.1: a bin's own `iff` is a conditional guard expression, one of the two
// legal contexts, so a sample formal there is accepted.
TEST(OverriddenSampleMethod, SampleFormalInBinGuardAccepted) {
  EXPECT_TRUE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int v, bit en);
        coverpoint v { bins b = {[0:3]} iff (en); }
      endgroup
    endmodule
  )"));
}

// §19.8.1: a cross bin's `iff` is a conditional guard expression as well.
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
