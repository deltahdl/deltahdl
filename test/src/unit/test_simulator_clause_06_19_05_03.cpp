#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

// §6.19.5.3 Next()
//
// Prototype:  function enum next( int unsigned N = 1 );
//
// Normative rules owned by this subclause:
//   C1  next() returns the Nth next enumeration value starting from the current
//       value of the variable; the argument N defaults to 1 (the next member).
//   C2  when advancing past the last member, the walk wraps to the first
//   member. C3  when the current value is not a member of the enumeration,
//   next()
//       returns the enumeration's default initial value (Table 6-7, referenced
//       but owned elsewhere).
//
// Which member is "next", where the walk wraps, and what counts as a member are
// all decided by the enum declaration and by the value the variable currently
// holds. That makes the behavior depend on how the input is produced, so these
// tests build the enumeration and its current value from real source (§6.8
// variable declarations, §6.19 enum declarations) and drive the whole pipeline,
// reading back the value a call to next() yields.

using namespace delta;

namespace {

// C1, default N: with no argument the walk advances exactly one member, from
// the first member to the second.
TEST(EnumNextMethod, DefaultAdvancesOneMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = c.next();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// C2: advancing one step past the last member wraps around to the first.
TEST(EnumNextMethod, WrapsFromLastMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = c.next();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 0u);
}

// C1, N is a literal: two steps forward from the first member lands on the
// third.
TEST(EnumNextMethod, LiteralCountAdvancesN) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = c.next(2);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 2u);
}

// C2, N exceeds the member count: the step reduces modulo the size, so four
// steps over three members advances a net one position.
TEST(EnumNextMethod, CountLargerThanSizeWraps) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = c.next(4);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// C1, N is zero: a zero-length walk hands back the member already held.
TEST(EnumNextMethod, ZeroCountReturnsCurrent) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = GREEN;
    r = c.next(0);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// C1, N is a run-time variable: confirms the step count is read at call time
// rather than requiring a compile-time constant.
TEST(EnumNextMethod, CountFromVariable) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int unsigned n;
  int r;
  initial begin
    c = RED;
    n = 2;
    r = c.next(n);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 2u);
}

// C1: the walk follows declaration order, not numeric ordering. With
// non-contiguous explicit values, next() from the first member yields the
// value of the second-declared member, not first-value-plus-one.
TEST(EnumNextMethod, FollowsDeclarationOrderWithGaps) {
  const char* src = R"(
module m;
  typedef enum { A = 5, B = 9, C = 20 } e_t;
  e_t v;
  int r;
  initial begin
    v = A;
    r = v.next();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 9u);
}

// C1, explicit 2-state packed base type (§6.19 enum_base_type): next() advances
// to the following member's value under a sized bit base.
TEST(EnumNextMethod, ExplicitBitBaseType) {
  const char* src = R"(
module m;
  typedef enum bit [3:0] { A = 3, B, C } e_t;
  e_t v;
  int r;
  initial begin
    v = A;
    r = v.next();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 4u);
}

// C1, explicit 4-state base type: behavior is identical when the base type is
// integer.
TEST(EnumNextMethod, ExplicitIntegerBaseType) {
  const char* src = R"(
module m;
  typedef enum integer { X = 2, Y, Z } e_t;
  e_t v;
  int r;
  initial begin
    v = X;
    r = v.next();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// C3: a value that is not a member of the enumeration is produced by casting an
// out-of-range integer onto the enum type (§6.19.4 casting performs no validity
// check). next() then returns the default initial value, the first member.
TEST(EnumNextMethod, NonMemberValueReturnsDefault) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = color_t'(99);
    r = c.next();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 0u);
}

// C1, result used as an operand within a larger expression: the returned enum
// value participates like any other value.
TEST(EnumNextMethod, ResultAsExpressionOperand) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN = 4, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = c.next() + 100;
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 104u);
}

// C1, result in a declaration-initializer position: one enum variable is seeded
// from another's next(), exercising the method-call path during variable
// initialization rather than a procedural assignment.
TEST(EnumNextMethod, ResultAsDeclarationInitializer) {
  const char* src = R"(
module m;
  typedef enum { LOW = 1, MID, HIGH } level_t;
  level_t a = MID;
  level_t b = a.next();
  int r;
  initial r = b;
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// C1 + C2 together: iterating next() around a three-member enum four times from
// the first member wraps once and lands on the second member.
TEST(EnumNextMethod, IterativeWalkWraps) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  int i;
  initial begin
    c = RED;
    for (i = 0; i < 4; i = i + 1)
      c = c.next();
    r = c;
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

}  // namespace
