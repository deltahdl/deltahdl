#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(TaggedUnionSimulation, TaggedAssignment_SetsTagAndValue) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged Valid 42;\n"
      "    result = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

TEST(TaggedUnionSimulation, TaggedAssignment_OverwriteTag) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 10;\n"
      "    u = tagged B 20;\n"
      "    result = u.B;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 20u);
}

TEST(TaggedUnionSimulation, VoidMemberTaggedAssignment) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; int Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged Invalid;\n"
      "    u = tagged Valid 99;\n"
      "    result = u.Valid;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 99u);
}

TEST(TaggedUnionSimulation, MismatchedMemberReadIsUnknownFromRealSource) {
  SimFixture f;
  auto* result = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 42;\n"
      "    result = $isunknown(u.B);\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(result, nullptr);
  EXPECT_EQ(result->value.ToUint64(), 1u);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "run-time error: accessing member 'B' of tagged "
                            "union 'u' which currently has tag 'A'",
                            7, "11.9"));
}

TEST(TaggedUnionSimulation, MatchingMemberReadIsKnownFromRealSource) {
  auto known = RunAndGet(
      "module t;\n"
      "  typedef union tagged { int A; int B; } U;\n"
      "  U u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    u = tagged A 42;\n"
      "    result = $isunknown(u.A);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(known, 0u);
}

TEST(TaggedUnionSimulation, PackedTaggedUnionBitsIsTagPlusMaxMember) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged packed { void Invalid; bit [31:0] Valid; } "
      "VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = $bits(VInt);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 33u);
}

TEST(TaggedUnionSimulation, PackedTaggedUnionRetagRewritesTagBits) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  union tagged packed { bit [6:0] v1; bit [6:0] v2; } "
                       "un;\n"
                       "  initial begin\n"
                       "    un = tagged v2 (10);\n"
                       "    un = tagged v1 (85);\n"
                       "    $display(\"%b\", un);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "01010101\n");
}

TEST(TaggedUnionSimulation, UnpackedTaggedUnionBitsHasNoTagBits) {
  auto v = RunAndGet(
      "module t;\n"
      "  typedef union tagged { void Invalid; bit [31:0] Valid; } VInt;\n"
      "  VInt u;\n"
      "  int result;\n"
      "  initial begin\n"
      "    result = $bits(VInt);\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 32u);
}

TEST(TaggedUnionSimulation, FourStateMemberAfterTwoStateMemberKeepsZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged { bit [3:0] A; logic [3:0] B; } "
                       "U;\n"
                       "  typedef union tagged { logic [3:0] A; logic [3:0] B; "
                       "} W;\n"
                       "  U u; W w;\n"
                       "  initial begin\n"
                       "    u = tagged B (4'b1z01);\n"
                       "    w = tagged B (4'b1z01);\n"
                       "    $display(\"%b %b\", u.B, w.B);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1z01 1z01\n");
}

TEST(TaggedUnionSimulation, TwoStateMemberBesideFourStateMemberDropsZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged { bit [3:0] A; logic [3:0] B; } "
                       "U;\n"
                       "  U u;\n"
                       "  initial begin\n"
                       "    u = tagged B (4'b1z01);\n"
                       "    u = tagged A (4'b1z01);\n"
                       "    $display(\"%b\", u.A);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1001\n");
}

TEST(TaggedUnionSimulation, BlockLocalUnionKeepsFourStateMemberZ) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged { bit [3:0] A; logic [3:0] B; } "
                       "U;\n"
                       "  initial begin : blk\n"
                       "    U bu;\n"
                       "    bu = tagged B (4'b1z01);\n"
                       "    $display(\"%b\", bu.B);\n"
                       "    bu = tagged A (4'b1z01);\n"
                       "    $display(\"%b\", bu.A);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1z01\n1001\n");
}

TEST(TaggedUnionSimulation, UnionLedByTwoStateMemberStartsAtZero) {
  SimFixture f;
  auto* u = RunAndFindVar(
      "module t;\n"
      "  typedef union tagged { bit [3:0] A; logic [3:0] B; } U;\n"
      "  U u;\n"
      "endmodule\n",
      f, "u");
  ASSERT_NE(u, nullptr);
  EXPECT_TRUE(u->value.IsKnown());
  EXPECT_EQ(u->value.ToUint64(), 0u);
}

TEST(TaggedUnionSimulation, NestedTaggedValuePrintsInnerTag) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged {\n"
                       "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                       "    union tagged { bit [9:0] JmpU; bit [9:0] JmpV; } "
                       "Jmp;\n"
                       "  } Instr;\n"
                       "  Instr instr;\n"
                       "  initial begin\n"
                       "    instr = tagged Jmp (tagged JmpV 10);\n"
                       "    $display(\"%p\", instr);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{Jmp:'{JmpV:10}}\n");
}

TEST(TaggedUnionSimulation, NestedTaggedValueMatchesInnerTagPattern) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged {\n"
                       "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                       "    union tagged { bit [9:0] JmpU; bit [9:0] JmpV; } "
                       "Jmp;\n"
                       "  } Instr;\n"
                       "  Instr instr;\n"
                       "  initial begin\n"
                       "    instr = tagged Jmp (tagged JmpV 10);\n"
                       "    case (instr) matches\n"
                       "      tagged Jmp (tagged JmpU .u): $display(\"u=%0d\", "
                       "u);\n"
                       "      tagged Jmp (tagged JmpV .v): $display(\"v=%0d\", "
                       "v);\n"
                       "      default: $display(\"none\");\n"
                       "    endcase\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "v=10\n");
}

TEST(TaggedUnionSimulation, CopyingAUnionCopiesItsNestedTags) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged {\n"
                       "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                       "    union tagged { bit [9:0] JmpU; bit [9:0] JmpV; } "
                       "Jmp;\n"
                       "  } Instr;\n"
                       "  Instr a, b;\n"
                       "  initial begin\n"
                       "    a = tagged Jmp (tagged JmpV 10);\n"
                       "    b = tagged Jmp (tagged JmpU 3);\n"
                       "    b = a;\n"
                       "    $display(\"%p\", b);\n"
                       "    case (b) matches\n"
                       "      tagged Jmp (tagged JmpU .u): $display(\"u=%0d\", "
                       "u);\n"
                       "      tagged Jmp (tagged JmpV .v): $display(\"v=%0d\", "
                       "v);\n"
                       "      default: $display(\"none\");\n"
                       "    endcase\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "'{Jmp:'{JmpV:10}}\nv=10\n");
}

TEST(TaggedUnionSimulation, CopyingAUnionWithAStructMemberCopiesItsTag) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  typedef union tagged {\n"
                       "    struct { bit [4:0] reg1, reg2, regd; } Add;\n"
                       "    union tagged { bit [9:0] JmpU; bit [9:0] JmpV; } "
                       "Jmp;\n"
                       "  } Instr;\n"
                       "  Instr c, d;\n"
                       "  initial begin\n"
                       "    c = tagged Add '{5'd1, 5'd2, 5'd3};\n"
                       "    d = tagged Jmp (tagged JmpU 3);\n"
                       "    d = c;\n"
                       "    case (d) matches\n"
                       "      tagged Add '{.r1, .r2, .rd}: $display(\"%0d\", "
                       "r1 + r2 + rd);\n"
                       "      default: $display(\"none\");\n"
                       "    endcase\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "6\n");
}

TEST(TaggedUnionSimulation, RealMemberHoldsItsReal) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef union tagged { real R; int I; } U;\n"
                      "  U u;\n"
                      "  int n;\n"
                      "  initial begin\n"
                      "    u = tagged R 2.5;\n"
                      "    n = int'(u.R * 4);\n"
                      "    u = tagged R 3;\n"
                      "    n = n * 100 + int'(u.R * 4);\n"
                      "  end\n"
                      "endmodule\n",
                      "n"),
            1012u);
}

TEST(TaggedUnionSimulation, RealMemberInitializerHoldsItsReal) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  typedef union tagged { real R; int I; } U;\n"
                      "  U u = tagged R 2.5;\n"
                      "  int n;\n"
                      "  initial n = int'(u.R * 4);\n"
                      "endmodule\n",
                      "n"),
            10u);
}

TEST(TaggedUnionSimulation, RealMemberHoldsItsRealOnEveryWritePath) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  typedef union tagged { real R; int I; } U;\n"
                "  U u;\n"
                "  int n;\n"
                "  function automatic int f();\n"
                "    U w = tagged R 2.5;\n"
                "    return int'(w.R * 4);\n"
                "  endfunction\n"
                "  initial begin : b\n"
                "    automatic U v = tagged R 0.5;\n"
                "    u <= tagged R 2.5;\n"
                "    #1 n = int'(u.R * 4) * 100 + f() * 10 + int'(v.R * 4);\n"
                "  end\n"
                "endmodule\n",
                "n"),
      1102u);
}

}  // namespace
