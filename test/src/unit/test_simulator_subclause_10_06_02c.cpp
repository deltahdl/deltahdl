#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(ForceReleaseSim, ForceOfAScalarNetKeepsItsWidth) {
  SimFixture f;
  auto* w = RunAndFindVar(
      "module t;\n"
      "  wire w;\n"
      "  logic a;\n"
      "  assign w = a;\n"
      "  initial begin\n"
      "    a = 1;\n"
      "    force w = 0;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "w");
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(w->value.width, 1u);
  EXPECT_EQ(w->value.ToUint64(), 0u);
  EXPECT_TRUE(w->is_forced);
}

TEST(ForceReleaseSim, ForceOfAVectorVariableTruncatesToItsWidth) {
  SimFixture f;
  auto* q = RunAndFindVar(
      "module t;\n"
      "  logic [3:0] q;\n"
      "  initial begin\n"
      "    force q = 8'hA5;\n"
      "    #1;\n"
      "  end\n"
      "endmodule\n",
      f, "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(q->value.width, 4u);
  EXPECT_EQ(q->value.ToUint64(), 0x5u);
}

TEST(ForceReleaseSim, ChildInstanceReleaseReresolvesFromTheInstancesDriver) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module M;\n"
      "  wire w;\n"
      "  int r, forced, released;\n"
      "  assign w = 1'b0;\n"
      "  initial begin\n"
      "    force w = 1'b1;\n"
      "    #1 forced = w;\n"
      "    release w;\n"
      "    #1 released = w;\n"
      "    r = forced * 10 + released;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  M m();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  auto* r = f.ctx.FindVariable("m.r");
  ASSERT_NE(r, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 10u);
}

TEST(ForceReleaseSim, ReleasedUndrivenNetAndNetArrayElementReadTheirDrivers) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  wire a;\n"
                       "  wire n[0:1];\n"
                       "  wire [3:0] v[2];\n"
                       "  wire s;\n"
                       "  assign n[1] = 1'b1;\n"
                       "  assign v[0] = 4'h3;\n"
                       "  assign s = n[0];\n"
                       "  initial begin\n"
                       "    force a = 1'b1;\n"
                       "    force n[0] = 1'b1;\n"
                       "    force v[0][3] = 1'b1;\n"
                       "    #1 $display(\"%b %b%b %b %h\", a, n[0], n[1], s, "
                       "v[0]);\n"
                       "    release a;\n"
                       "    release n[0];\n"
                       "    release v[0][3];\n"
                       "    #1 $display(\"%b %b%b %b %h\", a, n[0], n[1], s, "
                       "v[0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "1 11 1 b\nz z1 z 3\n");
}

TEST(ForceReleaseSim, AnAssignAndAForceAreTwoHolds) {
  const char* src =
      "module t;\n"
      "  logic [7:0] d, p, q, r, s;\n"
      "  initial begin\n"
      "    d = 10;\n"
      "    assign p = d; force p = 99; release p; p = 55;\n"
      "    assign q = d; force q = 99; release q; force q = 77;\n"
      "    force r = 99; assign r = d;\n"
      "    force s = 99; deassign s; s = 1;\n"
      "    #1 d = 5;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "p"), 5u);
  EXPECT_EQ(RunAndGet(src, "q"), 77u);
  EXPECT_EQ(RunAndGet(src, "r"), 99u);
  EXPECT_EQ(RunAndGet(src, "s"), 99u);
}

TEST(ForceReleaseSim, ReleaseReevaluatesTheContinuousAssignment) {
  const char* src =
      "module t;\n"
      "  logic [7:0] src, x, seen;\n"
      "  assign x = src;\n"
      "  initial begin\n"
      "    src = 10;\n"
      "    #1 force x = 99;\n"
      "    #1 release x;\n"
      "    #1 seen = x;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "seen"), 10u);
}

TEST(ForceReleaseSim, ForcesOnDifferentBitsOfANetHoldTheirOwnBits) {
  const char* src =
      "module t;\n"
      "  wire [7:0] bus;\n"
      "  logic [7:0] s, a, b, c, d, e;\n"
      "  assign bus = s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    force bus[3] = 1'b1;\n"
      "    force bus[5] = 1'b1;\n"
      "    #1 s = 8'h01;\n"
      "    #1 a = bus;\n"
      "    release bus[3];\n"
      "    #1 b = bus;\n"
      "    force bus[5] = 1'b0;\n"
      "    #1 c = bus;\n"
      "    force bus = 8'hAA;\n"
      "    #1 d = bus;\n"
      "    release bus;\n"
      "    #1 e = bus;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x29u);
  EXPECT_EQ(RunAndGet(src, "b"), 0x21u);
  EXPECT_EQ(RunAndGet(src, "c"), 0x01u);
  EXPECT_EQ(RunAndGet(src, "d"), 0xAAu);
  EXPECT_EQ(RunAndGet(src, "e"), 0x01u);
}

TEST(ForceReleaseSim, ReleasingAConcatenationRestoresANetBitSelect) {
  const char* src =
      "module t;\n"
      "  wire w;\n"
      "  wire [7:0] bus;\n"
      "  logic [7:0] a, b;\n"
      "  assign w = 1'b0;\n"
      "  assign bus = 8'h55;\n"
      "  initial begin\n"
      "    #1 force {w, bus[3]} = 2'b11;\n"
      "    #1 a = bus;\n"
      "    release {w, bus[3]};\n"
      "    #1 b = bus;\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "a"), 0x5Du);
  EXPECT_EQ(RunAndGet(src, "b"), 0x55u);
}

TEST(ForceReleaseSim, ForcedSwitchGroupMemberKeepsItsForce) {
  const char* src =
      "module t;\n"
      "  wire a, b, q; wire [1:0] p; logic c = 1;\n"
      "  tranif1 (a, b, c);\n"
      "  tranif1 (p[0], q, c);\n"
      "  logic r, s, z0;\n"
      "  initial begin\n"
      "    force a = 1'b1;\n"
      "    force p[1] = 1'b1;\n"
      "    #1 c = 0;\n"
      "    #1 begin r = a; s = p[1]; z0 = (p[0] === 1'bz); end\n"
      "  end\n"
      "endmodule\n";
  EXPECT_EQ(RunAndGet(src, "r"), 1u);
  EXPECT_EQ(RunAndGet(src, "s"), 1u);
  EXPECT_EQ(RunAndGet(src, "z0"), 1u);
}

}  // namespace
