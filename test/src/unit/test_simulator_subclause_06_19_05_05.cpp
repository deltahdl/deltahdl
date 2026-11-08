#include <gtest/gtest.h>

#include <string>

#include "fixture_enum_methods.h"
#include "helpers_scheduler.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

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

TEST(EnumNumMethod, ResultIsIntWidth) {
  EnumFixture f;
  f.RegisterEnum("ab", "ab_t", {{"A", 0}, {"B", 1}});
  auto* call = f.MakeEnumMethodCall("ab", "num");
  auto result = EvalExpr(call, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
}

}  // namespace
