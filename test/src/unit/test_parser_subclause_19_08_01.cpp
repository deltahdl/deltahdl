#include "fixture_parser.h"

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
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg with function sample(output int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
}

// §19.8.1: inout designates an output direction as well and is likewise not
// permitted for a sample method formal argument.
TEST(OverriddenSampleMethod, InoutSampleFormalRejected) {
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg with function sample(inout int x);
        coverpoint x;
      endgroup
    endmodule
  )"));
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
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg (int v) with function sample(int v, bit b);
        coverpoint v;
      endgroup
    endmodule
  )"));
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
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg (int a, ref int data) with function sample(bit c, int data);
        coverpoint c;
      endgroup
    endmodule
  )"));
}

// §19.8.1: the shared-name error is about the argument name, so it still fires
// when the colliding sample formal carries a default value -- the name is bound
// before the default expression and is checked against the covergroup formals
// all the same.
TEST(OverriddenSampleMethod, DefaultValuedSampleFormalStillCollides) {
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg (int v) with function sample(int v = 0);
        coverpoint v;
      endgroup
    endmodule
  )"));
}

// §19.8.1: the output-direction prohibition applies to every sample formal, not
// only the first, so an output direction on a later formal is also rejected.
TEST(OverriddenSampleMethod, OutputOnLaterSampleFormalRejected) {
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int a, output int b);
        coverpoint a;
      endgroup
    endmodule
  )"));
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
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg with function sample(bit a, int x);
        coverpoint x;
        option.per_instance = a;
      endgroup
    endmodule
  )"));
}

// §19.8.1: the prohibition applies to a type_option assignment just as to an
// option assignment; a sample formal on the right-hand side is still illegal.
TEST(OverriddenSampleMethod, SampleFormalInTypeOptionAssignmentRejected) {
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int weight_src, int x);
        coverpoint x;
        type_option.weight = weight_src;
      endgroup
    endmodule
  )"));
}

// §19.8.1: the illegal reference need not be the whole option value -- a sample
// formal appearing anywhere inside the value expression is still an illegal
// use, so it is detected even when embedded in a larger arithmetic expression.
TEST(OverriddenSampleMethod, SampleFormalInsideOptionValueExpressionRejected) {
  EXPECT_FALSE(ParseOk(R"(
    module m;
      covergroup cg with function sample(int a, int x);
        coverpoint x;
        option.weight = a + 1;
      endgroup
    endmodule
  )"));
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

}  // namespace
