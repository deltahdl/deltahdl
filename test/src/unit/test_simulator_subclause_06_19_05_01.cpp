#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

// §6.19.5.1 First()
//
// The single normative rule of this subclause: the first() method returns the
// value of the first member of the enumeration. Which member is "first" and
// what value it carries are decided entirely by the enum declaration, so the
// behavior depends on how the input is produced. These tests therefore build
// the enumeration from real source (§6.19 declarations, §6.19.2 element
// ranges) and drive it through the full pipeline, reading back the result of
// a call to first().

using namespace delta;

namespace {

// Default increment values: the first member of a plain enumeration takes 0.
TEST(EnumFirstMethod, DefaultIncrementFirstIsZero) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial r = c.first();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 0u);
}

// Explicitly valued members: first() reports the value attached to the first
// member, not a positional index.
TEST(EnumFirstMethod, ExplicitNonZeroFirst) {
  const char* src = R"(
module m;
  typedef enum { IDLE = 5, ACTIVE = 10, DONE = 15 } status_t;
  status_t s;
  int r;
  initial r = s.first();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 5u);
}

// "First" follows declaration order, never the smallest numeric value: here
// the first-declared member outranks every later one.
TEST(EnumFirstMethod, FollowsDeclarationOrderNotMinimum) {
  const char* src = R"(
module m;
  typedef enum { HIGH = 100, MID = 50, LOW = 1 } level_t;
  level_t v;
  int r;
  initial r = v.first();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 100u);
}

// first() reports the first member regardless of what the variable currently
// holds: move the variable to the last member and confirm first() is
// unaffected.
TEST(EnumFirstMethod, IgnoresCurrentValue) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = c.first();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 0u);
}

// A single-member enumeration: the only member is also the first.
TEST(EnumFirstMethod, SingleMember) {
  const char* src = R"(
module m;
  typedef enum { ONLY = 7 } solo_t;
  solo_t v;
  int r;
  initial r = v.first();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 7u);
}

// §6.19.2 indexed range with an assigned base value: the first generated
// constant (gpr0) carries the assigned value 1.
TEST(EnumFirstMethod, RangeIndexedFirstConstant) {
  const char* src = R"(
module m;
  typedef enum { gpr[2] = 1, alt[2:4] = 10 } e_t;
  e_t v;
  int r;
  initial r = v.first();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// Explicit 2-state base type: first() returns the first member's value under a
// sized packed base type (§6.19 enum_base_type).
TEST(EnumFirstMethod, ExplicitBitBaseType) {
  const char* src = R"(
module m;
  typedef enum bit [3:0] { A = 3, B, C } e_t;
  e_t v;
  int r;
  initial r = v.first();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// Explicit 4-state base type: first() behaves identically when the base type
// is integer.
TEST(EnumFirstMethod, ExplicitIntegerBaseType) {
  const char* src = R"(
module m;
  typedef enum integer { X = 2, Y, Z } e_t;
  e_t v;
  int r;
  initial r = v.first();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 2u);
}

// first() used as an operand within a larger expression: its returned value
// participates like any enum-typed value.
TEST(EnumFirstMethod, ResultAsExpressionOperand) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN = 4, BLUE } color_t;
  color_t c;
  int r;
  initial r = c.first() + 100;
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 100u);
}

// first() in a declaration-initializer position: a variable of the enum type
// is seeded from another variable's first(), exercising the method-call path
// during variable initialization rather than a procedural assignment.
TEST(EnumFirstMethod, ResultAsDeclarationInitializer) {
  const char* src = R"(
module m;
  typedef enum { LOW = 1, MID, HIGH } level_t;
  level_t a;
  level_t b = a.first();
  int r;
  initial r = b;
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

}  // namespace
