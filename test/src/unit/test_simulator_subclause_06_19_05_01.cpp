#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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
