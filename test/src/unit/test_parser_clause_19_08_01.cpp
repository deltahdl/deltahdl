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

}  // namespace
