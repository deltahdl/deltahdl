#include <gtest/gtest.h>

#include <string>

#include "fixture_enum_methods.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

// §6.19.5.5 Num()
//
// Prototype:  function int num();
//
// Normative rules owned by this subclause:
//   N1  num() returns the number of elements (members) in the given
//       enumeration.
//   N2  the result is an int (32-bit).
//
// How many members an enumeration has is decided entirely by its declaration:
// how many names are listed, whether a name uses the §6.19.2 range shorthand
// that expands into several members, and so on. The current value the variable
// happens to hold plays no part. Because the count depends on how the enum type
// is produced, these tests build the enumeration from real source (§6.19 enum
// declarations, §6.19.2 range members, §6.8 variable declarations) and drive
// the whole pipeline, reading back what a call to num() yields. The lone int
// return-width claim (N2) is a fixed property of the result independent of the
// enum, so it is checked directly at the evaluation stage.

using namespace delta;

namespace {

// N1: a three-member enumeration reports three members.
TEST(EnumNumMethod, CountsMembers) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial r = c.num();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// N1, boundary: a single-member enumeration reports one member.
TEST(EnumNumMethod, CountsSingleMember) {
  const char* src = R"(
module m;
  typedef enum { SOLE } one_t;
  one_t o;
  int r;
  initial r = o.num();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

// N1: the count reflects the number of members, not anything about their
// assigned values. A sparse, non-contiguous value set still yields the member
// count.
TEST(EnumNumMethod, CountsMembersNotValues) {
  const char* src = R"(
module m;
  typedef enum { LOW = 2, MID = 50, HIGH = 9999 } sparse_t;
  sparse_t s;
  int r;
  initial r = s.num();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// N1: the count does not depend on the value the variable currently holds. Even
// when the variable is forced to a value that is not a member of the
// enumeration (via an out-of-range cast, §6.19.4), num() still returns the
// declared member count.
TEST(EnumNumMethod, IndependentOfCurrentValue) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial begin
    c = color_t'(99);
    r = c.num();
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// N1, §6.19.2 range members: a name written with the range shorthand expands
// into one member per index, and num() counts the expanded members rather than
// the single written entry. `OP[3]` yields OP0, OP1, OP2 -> three members.
TEST(EnumNumMethod, CountsRangeExpandedMembers) {
  const char* src = R"(
module m;
  typedef enum { OP[3] } op_t;
  op_t v;
  int r;
  initial r = v.num();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// N1, §6.19.2 range members combined with plain names: the count is the total
// after expansion. ONE plus TWO..FOUR (three) plus LAST -> five members.
TEST(EnumNumMethod, CountsMixedPlainAndRangeMembers) {
  const char* src = R"(
module m;
  typedef enum { ONE, TWO[2:4], LAST } mix_t;
  mix_t v;
  int r;
  initial r = v.num();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 5u);
}

// N1, explicit packed base type (§6.19 enum_base_type): declaring the enum over
// a sized base type does not change the member count.
TEST(EnumNumMethod, CountsWithExplicitBaseType) {
  const char* src = R"(
module m;
  typedef enum bit [2:0] { A, B, C, D, E } e_t;
  e_t v;
  int r;
  initial r = v.num();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 5u);
}

// N1 + N2, result used as an int operand within a larger expression: the
// returned count behaves as an ordinary integer in arithmetic.
TEST(EnumNumMethod, ResultAsExpressionOperand) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial r = c.num() * 10 + 1;
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 31u);
}

// N1, result in a declaration-initializer position: a variable is seeded from
// num() at its declaration, exercising the variable-initialization lowering
// path rather than a procedural assignment.
TEST(EnumNumMethod, ResultAsDeclarationInitializer) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int n = c.num();
  int r;
  initial r = n;
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// N1, no-parens property form: num invoked without parentheses reaches the
// property-dispatch path rather than the call path and still reports the member
// count.
TEST(EnumNumMethod, PropertyFormNoParens) {
  const char* src = R"(
module m;
  typedef enum { RED, GREEN, BLUE } color_t;
  color_t c;
  int r;
  initial r = c.num;
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

// N2: the num() result is an int, i.e. 32 bits wide. Result width is a fixed
// property of the method independent of how the enumeration is declared, so it
// is observed directly at the evaluation stage where the width lives.
TEST(EnumNumMethod, ResultIsIntWidth) {
  EnumFixture f;
  f.RegisterEnum("ab", "ab_t", {{"A", 0}, {"B", 1}});
  auto* call = f.MakeEnumMethodCall("ab", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

}  // namespace
