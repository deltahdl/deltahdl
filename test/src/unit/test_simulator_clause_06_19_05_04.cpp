#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

// §6.19.5.4 Prev()
//
// Prototype:  function enum prev( int unsigned N = 1 );
//
// Normative rules owned by this subclause:
//   P1  prev() returns the Nth previous enumeration value starting from the
//       current value of the variable; the argument N defaults to 1 (the
//       previous member).
//   P2  when retreating past the first member, the walk wraps to the last
//       member.
//   P3  when the current value is not a member of the enumeration, prev()
//       returns the enumeration's default initial value (Table 6-7, referenced
//       but owned elsewhere).
//
// prev() is the reverse of next() (§6.19.5.3). Which member is "previous",
// where the walk wraps, and what counts as a member are all decided by the enum
// declaration and by the value the variable currently holds. That makes the
// behavior depend on how the input is produced, so these tests build the
// enumeration and its current value from real source (§6.8 variable
// declarations, §6.19 enum declarations) and drive the whole pipeline, reading
// back the value a call to prev() yields.

using namespace delta;

namespace {

// P1, default N: with no argument the walk retreats exactly one member, from
// the third member to the second.
TEST(EnumPrevMethod, DefaultRetreatsOneMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = c.prev();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// P2: retreating one step before the first member wraps around to the last.
TEST(EnumPrevMethod, WrapsFromFirstMember) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = RED;
    r = c.prev();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 2u);
}

// P1, N is a literal: two steps back from the third member lands on the first.
TEST(EnumPrevMethod, LiteralCountRetreatsN) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = c.prev(2);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 0u);
}

// P2, N exceeds the member count: the step reduces modulo the size, so four
// steps back over three members retreats a net one position.
TEST(EnumPrevMethod, CountLargerThanSizeWraps) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = c.prev(4);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// P1, N is zero: a zero-length walk hands back the member already held.
TEST(EnumPrevMethod, ZeroCountReturnsCurrent) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = GREEN;
    r = c.prev(0);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// P1, N is a run-time variable: confirms the step count is read at call time
// rather than requiring a compile-time constant.
TEST(EnumPrevMethod, CountFromVariable) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int unsigned n;
  int r;
  initial begin
    c = BLUE;
    n = 2;
    r = c.prev(n);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 0u);
}

// P1: the walk follows declaration order, not numeric ordering. With
// non-contiguous explicit values, prev() from the last member yields the value
// of the second-declared member, not last-value-minus-one.
TEST(EnumPrevMethod, FollowsDeclarationOrderWithGaps) {
  const char* src = R"(
module m;
  typedef enum { A = 5, B = 9, C = 20 } e_t;
  e_t v;
  int r;
  initial begin
    v = C;
    r = v.prev();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 9u);
}

// P1, explicit 2-state packed base type (§6.19 enum_base_type): prev() retreats
// to the preceding member's value under a sized bit base.
TEST(EnumPrevMethod, ExplicitBitBaseType) {
  const char* src = R"(
module m;
  typedef enum bit [3:0] { A = 3, B, C } e_t;
  e_t v;
  int r;
  initial begin
    v = C;
    r = v.prev();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 4u);
}

// P1, explicit 4-state base type: behavior is identical when the base type is
// integer.
TEST(EnumPrevMethod, ExplicitIntegerBaseType) {
  const char* src = R"(
module m;
  typedef enum integer { X = 2, Y, Z } e_t;
  e_t v;
  int r;
  initial begin
    v = Z;
    r = v.prev();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// P3: a value that is not a member of the enumeration is produced by casting an
// out-of-range integer onto the enum type (§6.19.4 casting performs no validity
// check). prev() then returns the default initial value, the first member.
TEST(EnumPrevMethod, NonMemberValueReturnsDefault) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = color_t'(99);
    r = c.prev();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 0u);
}

// P1, result used as an operand within a larger expression: the returned enum
// value participates like any other value.
TEST(EnumPrevMethod, ResultAsExpressionOperand) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN = 4, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = c.prev() + 100;
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 104u);
}

// P1, result in a declaration-initializer position: one enum variable is seeded
// from another's prev(), exercising the method-call path during variable
// initialization rather than a procedural assignment.
TEST(EnumPrevMethod, ResultAsDeclarationInitializer) {
  const char* src = R"(
module m;
  typedef enum { LOW = 1, MID, HIGH } level_t;
  level_t a = MID;
  level_t b = a.prev();
  int r;
  initial r = b;
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// P1 + P2 together: iterating prev() around a three-member enum four times from
// the first member wraps once and lands on the last member.
TEST(EnumPrevMethod, IterativeWalkWraps) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  int i;
  initial begin
    c = RED;
    for (i = 0; i < 4; i = i + 1)
      c = c.prev();
    r = c;
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 2u);
}

// P1, no-parens property form: a default-N prev() invoked without parentheses
// reaches the property-dispatch path rather than the call path, and still walks
// one member back.
TEST(EnumPrevMethod, PropertyFormNoParens) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = BLUE;
    r = c.prev;
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

}  // namespace
