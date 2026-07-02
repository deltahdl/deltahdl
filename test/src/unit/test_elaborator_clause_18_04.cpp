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

// 18.4: because a packed untagged union is treated as an integral value, it may
// also be declared randc, not just rand. This is the cyclic-qualifier form of
// the positive legality above; the identical unpacked union is rejected under
// randc (below via UnpackedUnionRandRejected's shape), isolating the rule to
// the packed integral shape rather than to the qualifier.
TEST(RandomVariableTypes, PackedUntaggedUnionRandcAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef union packed { bit [7:0] a; bit [7:0] b; } u_t;\n"
             "class C;\n"
             "  randc u_t u;\n"
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

// 18.4: an unpacked structure may be declared rand (its random members are
// solved concurrently).
TEST(RandomVariableTypes, UnpackedStructRandAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef struct { rand int a; int b; } s_t;\n"
             "class C;\n"
             "  rand s_t s;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: unpacked structures shall not be declared randc. The identical
// declaration is accepted as rand above, isolating the rule to the randc
// qualifier on an unpacked aggregate.
TEST(RandomVariableTypes, UnpackedStructRandcRejected) {
  EXPECT_FALSE(
      ElabOk("typedef struct { rand int a; int b; } s_t;\n"
             "class C;\n"
             "  randc s_t s;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: a packed structure is treated as an integral value, so it may be
// declared rand or randc. The same structure that is rejected as randc when
// unpacked is accepted when packed, isolating the rule to the packed shape.
TEST(RandomVariableTypes, PackedStructRandcAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef struct packed { bit [7:0] a; bit [7:0] b; } s_t;\n"
             "class C;\n"
             "  randc s_t s;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: a member of an unpacked structure may carry a rand modifier in its
// type declaration.
TEST(RandomVariableTypes, UnpackedStructMemberRandAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef struct { rand int a; int b; } s_t;\n"
             "module m; endmodule\n"));
}

// 18.4: members of packed structures shall not have a rand or randc modifier.
// The same member declaration accepted when the structure is unpacked is
// rejected when it is packed, isolating the rule to the packed shape.
TEST(RandomVariableTypes, PackedStructMemberRandRejected) {
  EXPECT_FALSE(
      ElabOk("typedef struct packed { rand bit [7:0] a; bit [7:0] b; } s_t;\n"
             "module m; endmodule\n"));
}

// 18.4: members of packed untagged unions shall not have a rand or randc
// modifier.
TEST(RandomVariableTypes, PackedUnionMemberRandRejected) {
  EXPECT_FALSE(
      ElabOk("typedef union packed { rand bit [7:0] a; bit [7:0] b; } u_t;\n"
             "module m; endmodule\n"));
}

// 18.4: the "no real randc" rule covers every real flavor, not just 'real'.
// 'realtime' is the third real type (with 'real' and 'shortreal', already
// exercised), so a randc realtime property is likewise rejected.
TEST(RandomVariableTypes, RealtimeRandcRejected) {
  EXPECT_FALSE(
      ElabOk("class C;\n"
             "  randc realtime r;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: the solver randomizes singular integral variables, so a plain packed
// 2-state vector may carry the rand modifier. This is the rand (noncyclic)
// counterpart of the already-covered randc bit-vector acceptance, confirming a
// bare integral vector is a legal random variable under either qualifier.
TEST(RandomVariableTypes, IntegralVectorRandAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand bit [7:0] v;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: a 4-state integral vector is equally a singular integral random
// variable, so a rand logic vector is accepted just as the 2-state form is;
// the state-ness of the integral type does not bear on rand legality.
TEST(RandomVariableTypes, FourStateLogicVectorRandAccepted) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  rand logic [3:0] v;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: an enumeration is an integral type, so an enum-typed property is a
// legal singular random variable and may be declared rand.
TEST(RandomVariableTypes, EnumRandAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef enum { RED, GREEN, BLUE } e_t;\n"
             "class C;\n"
             "  rand e_t e;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

// 18.4: because an enum presents a single integral value it may also be
// declared randc (cyclic), unlike an unpacked aggregate or a real variable.
// This isolates the rule to the type's integral shape rather than to the
// qualifier.
TEST(RandomVariableTypes, EnumRandcAccepted) {
  EXPECT_TRUE(
      ElabOk("typedef enum { RED, GREEN, BLUE } e_t;\n"
             "class C;\n"
             "  randc e_t e;\n"
             "endclass\n"
             "module m; endmodule\n"));
}

}  // namespace
