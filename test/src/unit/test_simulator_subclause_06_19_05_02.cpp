#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
