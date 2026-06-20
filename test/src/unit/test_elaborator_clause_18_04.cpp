#include "fixture_elaborator.h"

using namespace delta;

namespace {

// 18.4: real variables shall not be declared randc.
TEST(RandomVariableTypes, RealRandcRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc real r;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

TEST(RandomVariableTypes, ShortrealRandcRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc shortreal r;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: a real variable may still be declared rand.
TEST(RandomVariableTypes, RealRandAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand real r;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// An integral randc variable is legal.
TEST(RandomVariableTypes, IntegralRandcAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  randc bit [3:0] y;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: object handles shall not be declared randc.
TEST(RandomVariableTypes, ObjectHandleRandcRejected) {
  EXPECT_FALSE(
      ElabOk("class D;\n"
             "endclass\n"
             "class C;\n"
             "  randc D h;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: an object handle may be declared rand.
TEST(RandomVariableTypes, ObjectHandleRandAccepted) {
  EXPECT_TRUE(
      ElabOk("class D;\n"
             "endclass\n"
             "class C;\n"
             "  rand D h;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: an unpacked union shall not be declared rand or randc.
TEST(RandomVariableTypes, UnpackedUnionRandRejected) {
  EXPECT_FALSE(
      ElabOk("typedef union { byte a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  rand u_t u;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: a packed untagged union may be declared rand (treated as integral).
// The same declaration that is rejected when unpacked is accepted when packed,
// isolating the rule to the union's packed/tagged shape.
TEST(RandomVariableTypes, PackedUntaggedUnionRandAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef union packed { bit [7:0] a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  rand u_t u;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: a packed tagged union shall not be declared rand or randc.
TEST(RandomVariableTypes, PackedTaggedUnionRandRejected) {
  EXPECT_FALSE(
      ElabOk("typedef union tagged packed { bit [7:0] a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  rand u_t u;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
