#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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

TEST(EnumPrevMethod, NonMemberValueReturnsDefault) {
  const char* src = R"(
module m;
  typedef enum { RED = 1, GREEN, BLUE } color_t;
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

TEST(EnumPrevMethod, NonMemberValueOfA4StateEnumReturnsX) {
  const char* src = R"(
module m;
  enum integer { A = 1, B = 2 } c;
  integer v;
  int r;
  initial begin
    v = c.prev();
    r = (v === 'x);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

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

TEST(EnumPrevMethod, StepsOntoAndFromAnXMember) {
  const char* src = R"(
module m;
  enum integer {IDLE, XX='x, S1='b01, S2='b10} s, p;
  int r;
  initial begin
    s = XX;
    p = s.prev();
    r = (S1.prev() === XX) * 10 + (p === IDLE);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 11u);
}

}  // namespace
