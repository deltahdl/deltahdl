#include <gtest/gtest.h>

#include <string>

#include "helpers_scheduler.h"

using namespace delta;

namespace {

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

TEST(EnumNextMethod, NonMemberValueReturnsDefault) {
  const char* src = R"(
module m;
  typedef enum { RED = 1, GREEN, BLUE } color_t;
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

TEST(EnumNextMethod, NonMemberValueOfA4StateEnumReturnsX) {
  const char* src = R"(
module m;
  enum integer { A = 1, B = 2 } c;
  integer v;
  int r;
  initial begin
    v = c.next();
    r = (v === 'x);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
}

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

TEST(EnumNextMethod, ResultAsProceduralDeclarationInitializer) {
  const char* src = R"(
module m;
  typedef enum { LOW = 1, MID, HIGH } level_t;
  int r;
  initial begin
    static level_t a = MID;
    static level_t b = a.next();
    r = b;
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

TEST(EnumNextMethod, ResultAsSubprogramLocalDeclarationInitializer) {
  const char* src = R"(
module m;
  typedef enum { LOW = 1, MID, HIGH } level_t;
  int r;
  function int step();
    static level_t a = MID;
    static level_t b = a.next();
    return b;
  endfunction
  initial r = step();
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 3u);
}

TEST(EnumNextMethod, StepsOntoAndFromAnXMember) {
  const char* src = R"(
module m;
  enum integer {IDLE, XX='x, S1='b01, S2='b10} s, n;
  int r;
  initial begin
    s = XX;
    n = s.next();
    r = (IDLE.next() === XX) * 10 + (n === S1);
  end
endmodule
)";
  EXPECT_EQ(RunAndGet(src, "r"), 11u);
}

}  // namespace
