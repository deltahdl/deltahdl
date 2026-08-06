#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

// §6.19.5.2 Last()
//
// The single normative rule of this subclause: the last() method returns the
// value of the last member of the enumeration. Which member is "last" and what
// value it carries are decided entirely by the enum declaration, so the
// behavior depends on how the input is produced. These tests therefore build
// the enumeration from real source (§6.19 declarations, §6.19.2 element
// ranges) and drive it through the full pipeline, reading back the result of a
// call to last().

using namespace delta;

namespace {

// Default increment values: the last member of a plain three-member
// enumeration takes the increment 2.
TEST(EnumLastMethod, DefaultIncrementLastValue) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial r = c.last();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 2u);
}

// "Last" follows declaration order, never the largest numeric value: here the
// last-declared member carries the smallest value. This also confirms last()
// returns the explicitly-assigned value of the final member.
TEST(EnumLastMethod, FollowsDeclarationOrderNotMaximum) {
  const char* src = R"(
module m;
  typedef enum { HIGH = 100, MID = 50, LOW = 1 } level_t;
  level_t v;
  int r;
  initial r = v.last();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// last() reports the last member regardless of what the variable currently
// holds: seed the variable with the first member and confirm last() is
// unaffected.
TEST(EnumLastMethod, IgnoresCurrentValue) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = c.last();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 2u);
}

// A single-member enumeration: the only member is also the last.
TEST(EnumLastMethod, SingleMember) {
  const char* src = R"(
module m;
  typedef enum { ONLY = 7 } solo_t;
  solo_t v;
  int r;
  initial r = v.last();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 7u);
}

// §6.19.2 indexed ranges with assigned base values: the last generated
// constant is alt4, whose value is 10 (assigned to alt2) incremented twice.
TEST(EnumLastMethod, RangeIndexedLastConstant) {
  const char* src = R"(
module m;
  typedef enum { gpr[2] = 1, alt[2:4] = 10 } e_t;
  e_t v;
  int r;
  initial r = v.last();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 12u);
}

// Explicit 2-state base type: last() returns the last member's value under a
// sized packed base type (§6.19 enum_base_type).
TEST(EnumLastMethod, ExplicitBitBaseType) {
  const char* src = R"(
module m;
  typedef enum bit [3:0] { A = 3, B, C } e_t;
  e_t v;
  int r;
  initial r = v.last();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 5u);
}

// Explicit 4-state base type: last() behaves identically when the base type is
// integer.
TEST(EnumLastMethod, ExplicitIntegerBaseType) {
  const char* src = R"(
module m;
  typedef enum integer { X = 2, Y, Z } e_t;
  e_t v;
  int r;
  initial r = v.last();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 4u);
}

// last() used as an operand within a larger expression: its returned value
// participates like any enum-typed value.
TEST(EnumLastMethod, ResultAsExpressionOperand) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN = 4, BLUE } color_t;
  color_t c;
  int r;
  initial r = c.last() + 100;
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 105u);
}

// last() in a declaration-initializer position: a variable of the enum type is
// seeded from another variable's last(), exercising the method-call path
// during variable initialization rather than a procedural assignment.
TEST(EnumLastMethod, ResultAsDeclarationInitializer) {
  const char* src = R"(
module m;
  typedef enum { LOW = 1, MID, HIGH } level_t;
  level_t a;
  level_t b = a.last();
  int r;
  initial r = b;
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

}  // namespace
