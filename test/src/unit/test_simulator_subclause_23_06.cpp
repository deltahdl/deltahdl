#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

TEST(HierarchicalNameSimulation, ReadChildInstanceVariable) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] val;\n"
      "  initial val = 8'd42;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = c1.val;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 42u);
}

TEST(HierarchicalNameSimulation, WriteChildInstanceVariable) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic [7:0] val;\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  initial begin\n"
      "    c1.val = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f, "c1.val");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 99u);
}

TEST(HierarchicalNameSimulation, MultiLevelHierarchicalRead) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module leaf;\n"
      "  logic [7:0] data;\n"
      "  initial data = 8'd77;\n"
      "endmodule\n"
      "module mid;\n"
      "  leaf l1();\n"
      "endmodule\n"
      "module top;\n"
      "  mid m1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    #1;\n"
      "    result = m1.l1.data;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 77u);
}

TEST(HierarchicalNameSimulation, RootPrefixedHierarchicalRead) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module top;\n"
      "  logic [7:0] sig;\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    sig = 8'd33;\n"
      "    #1;\n"
      "    result = $root.top.sig;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 33u);
}

TEST(HierarchicalNameSimulation, HierarchicalNameInEventExpression) {
  SimFixture f;
  auto* v = RunAndFindVar(
      "module child;\n"
      "  logic done;\n"
      "  initial begin\n"
      "    done = 0;\n"
      "    #10 done = 1;\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  child c1();\n"
      "  logic [7:0] result;\n"
      "  initial begin\n"
      "    result = 8'd0;\n"
      "    @(posedge c1.done);\n"
      "    result = 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f, "result");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(v->value.ToUint64(), 1u);
}

// §23.6 (printed page 754): an element of an array of instances is named by
// the instance name and its index, `arr[1]`, and its items are reached
// through it as any instance's. §23.3.2 writes the dimension as an
// unpacked_dimension, so `leaf arr[2]()` is arr[0] and arr[1] (§7.4.2's
// `[size]`); it was one instance named arr, and the name dropped its index,
// so `arr[1].v = 11` wrote that one instance and `arr[1].v` read nothing.
TEST(HierarchicalNames, InstanceArrayElementIsReachedByItsIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf #(parameter K = 0)();\n"
                       "  int v = K * 10 + 1;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  leaf #(1) arr[2]();\n"
                       "  leaf #(5) one();\n"
                       "  initial begin\n"
                       "    arr[1].v = 11;\n"
                       "    #1 $display(\"%0d %0d %0d\", arr[1].v, arr[0].v, "
                       "one.v);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "11 11 51\n");
}

// An element of an array written with a range and connected through ports is
// reached the same way; each element drives its own slice of the bus.
TEST(HierarchicalNames, RangedInstanceArrayElementIsReachedByItsIndex) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module leaf(input i, output o);\n"
                       "  assign o = ~i;\n"
                       "endmodule\n"
                       "module top;\n"
                       "  reg [1:0] a = 2'b01; wire [1:0] y;\n"
                       "  leaf arr[1:0](.i(a), .o(y));\n"
                       "  initial #1 $display(\"%b %b %b\", y, arr[1].o, "
                       "arr[0].o);\n"
                       "endmodule\n",
                       f),
            "10 1 0\n");
}

// §11.8.1 (printed page 302) with §23.6: an operand's signedness is its
// declaration's, reached by a simple name or a hierarchical one alike. A
// one-bit `logic w` set to the signed literal 1 through `a.w` read back as -1
// under %0d; a signed declaration still reads signed.
TEST(HierarchicalNames, ReadOfAnUnsignedVariableByHierarchicalNameIsUnsigned) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("interface I; logic w; endinterface\n"
                 "module sub;\n"
                 "  logic u;\n"
                 "  logic signed [3:0] s;\n"
                 "  int i;\n"
                 "endmodule\n"
                 "module top;\n"
                 "  I a();\n"
                 "  sub b();\n"
                 "  initial begin\n"
                 "    a.w = 1; b.u = 1; b.s = -3; b.i = -5;\n"
                 "    #1 $display(\"%0d %0d %0d %0d\", a.w, b.u, b.s, b.i);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "1 1 -3 -5\n");
}

// §23.6: an element select of an array named from $root reads and writes
// the top's array, never the like-named one of the instance running it: sub
// sets its own arr[1] to 0, writes 0 into top's arr[0] by the rooted name,
// and reads top's arr[1], which stays 1.
TEST(HierarchicalNames, RootHeadedArrayElementIsTheTopsElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  logic arr [1:0] = '{1, 1};\n"
                       "  initial begin\n"
                       "    arr[1] = 0;\n"
                       "    $root.top.arr[0] = 0;\n"
                       "    #1 $display(\"%0d %0d %0d\", $root.top.arr[1],\n"
                       "                $root.top.arr[0], arr[0]);\n"
                       "  end\n"
                       "endmodule\n"
                       "module top;\n"
                       "  logic arr [1:0] = '{1, 1};\n"
                       "  sub c();\n"
                       "endmodule\n",
                       f),
            "1 0 1\n");
}

// §23.6 with §7.2: a hierarchical name writes a member of another instance's
// structure, blocking and nonblocking: s1.v.B takes 9 and s1.v.A 4 while the
// other member keeps what sub wrote. The name was split at its first dot,
// taking the instance s1 for the variable, and both writes were dropped,
// printing A=1 B=2.
TEST(HierarchicalNames, MemberOfAnotherInstancesStructureIsWritten) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int A; int B; } s_t;\n"
                       "module sub ();\n"
                       "  s_t v = '{A: 1, B: 2};\n"
                       "  initial #2 $display(\"A=%0d B=%0d\", v.A, v.B);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  sub s1 ();\n"
                       "  initial begin\n"
                       "    #1 s1.v.B = 9;\n"
                       "    s1.v.A <= 4;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "A=4 B=9\n");
}

// The same through a structure whose type is the module's type parameter,
// overridden at the instance, as §6.20.3's `s2.v3.A = 9` writes it.
TEST(HierarchicalNames, MemberOfATypeParameterStructureIsWritten) {
  SimFixture f;
  EXPECT_EQ(RunCapture("typedef struct { int A; } a_t;\n"
                       "module ma #(parameter type t_3 = int) ();\n"
                       "  t_3 v3;\n"
                       "  initial #2 $display(\"A=%0d\", v3.A);\n"
                       "endmodule\n"
                       "module t;\n"
                       "  ma #(.t_3(a_t)) s2 ();\n"
                       "  initial #1 s2.v3.A = 9;\n"
                       "endmodule\n",
                       f),
            "A=9\n");
}

}  // namespace
