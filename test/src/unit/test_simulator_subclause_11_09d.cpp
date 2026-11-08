#include <gtest/gtest.h>

#include <iostream>
#include <sstream>
#include <streambuf>
#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

Variable* RunReadingY(const std::string& src, SimFixture& f) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design == nullptr) return nullptr;
  EXPECT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* y = f.ctx.FindVariable("y");
  EXPECT_NE(y, nullptr);
  return y;
}

std::string RunPrinting(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

TEST(TaggedUnionEval, MemberReadConsistentWithTheMembersTagIsClean) {
  SimFixture f;
  auto* y = RunReadingY(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  s_t s;\n"
      "  logic [31:0] y;\n"
      "  initial begin\n"
      "    s.u = tagged Valid 9;\n"
      "    y = s.u.Valid;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 9u);
  EXPECT_FALSE(ReportedError(f.diag.Diagnostics(),
                             "run-time error: accessing member", 8, "11.9"));
}

TEST(TaggedUnionEval, MemberReadIsCheckedAgainstTheMembersTag) {
  SimFixture f;
  auto* y = RunReadingY(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  s_t s;\n"
      "  logic [31:0] y;\n"
      "  initial begin\n"
      "    s.u = tagged Valid 9;\n"
      "    y = s.u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(y, nullptr);
  EXPECT_FALSE(y->value.IsKnown());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "run-time error: accessing member 'Other' of tagged union 's.u' which "
      "currently has tag 'Valid'",
      8, "11.9"));
}

TEST(TaggedUnionEval, TwoLevelMemberReadIsCheckedAgainstItsUnionsTag) {
  SimFixture f;
  auto* y = RunReadingY(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  typedef struct { s_t s; int d; } m_t;\n"
      "  m_t m;\n"
      "  logic [31:0] y, z;\n"
      "  initial begin\n"
      "    m.s.u = tagged Valid 9;\n"
      "    y = m.s.u.Valid;\n"
      "    z = m.s.u.Other;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(y, nullptr);
  EXPECT_EQ(y->value.ToUint64(), 9u);
  auto* z = f.ctx.FindVariable("z");
  ASSERT_NE(z, nullptr);
  EXPECT_FALSE(z->value.IsKnown());
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "run-time error: accessing member 'Other' of tagged union 'm.s.u' which "
      "currently has tag 'Valid'",
      10, "11.9"));
}

TEST(TaggedUnionEval, MemberTaggedUnionPrintsTagAndValue) {
  SimFixture f;
  auto out = RunPrinting(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; int Other; } u_t;\n"
      "  typedef struct { u_t u; int c; } s_t;\n"
      "  s_t s;\n"
      "  initial begin\n"
      "    s.u = tagged Valid 9;\n"
      "    $display(\"%p\", s.u);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
  EXPECT_EQ(out, "'{Valid:9}\n");
}

TEST(TaggedUnionSim, ANestedTaggedExpressionKeepsItsStructsFirstMember) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef union tagged {\n"
      "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
      "    union tagged { bit [9:0] JmpU;\n"
      "      struct { bit [1:0] cc; bit [9:0] addr; } JmpC; } Jmp;\n"
      "  } Instr;\n"
      "  Instr i1, i2, i3;\n"
      "  bit [4:0] e1 = 1, e2 = 2, ed = 3;\n"
      "  bit e = 1;\n"
      "  initial begin\n"
      "    i1 = e ? tagged Add '{e1, 4, ed}\n"
      "           : tagged Add '{reg2: e2, regd: 3, reg1: 19};\n"
      "    i3 = !e ? tagged Add '{e1, 4, ed}\n"
      "            : tagged Add '{reg2: e2, regd: 3, reg1: 19};\n"
      "    i2 = tagged Jmp (tagged JmpC '{2, 83});\n"
      "    $display(\"%0d %0d %0d %0d %0d\", i1.Add.reg1, i1.Add.reg2,\n"
      "             i3.Add.reg1, i2.Jmp.JmpC.cc, i2.Jmp.JmpC.addr);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 4 19 2 83\n");
}

TEST(TaggedUnionEval, AStringMemberOfAStructureReadAgainstTheTagIsEmpty) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef struct {logic [3:0] n; string s;} pair_t;\n"
      "  typedef union tagged {int i; pair_t p;} u_t;\n"
      "  u_t u;\n"
      "  pair_t q;\n"
      "  initial begin\n"
      "    u = tagged i 5;\n"
      "    q = u.p;\n"
      "    $display(\"%h [%s]\", q.n, q.s);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "x []\n");
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "accessing member 'p' of tagged union 'u' which "
                            "currently has tag 'i'",
                            8, "11.9"));
}

}  // namespace
