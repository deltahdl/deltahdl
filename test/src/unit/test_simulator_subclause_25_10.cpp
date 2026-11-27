#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

std::string RunWithoutErrors(const std::string& src) {
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

TEST(InterfaceObjectAccess, ContinuousAssignmentFollowsAnInterfaceMember) {
  SimFixture f;
  auto out = RunCapture(
      "interface gi;\n"
      "  logic d;\n"
      "endinterface\n"
      "module t;\n"
      "  gi dif();\n"
      "  wire w;\n"
      "  assign w = dif.d;\n"
      "  initial begin\n"
      "    dif.d = 0;\n"
      "    #10 dif.d = 1;\n"
      "    #1 $display(\"%0d\", w);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(InterfaceObjectAccess, AlwaysCombRerunsOnAnInterfaceMember) {
  SimFixture f;
  auto out = RunCapture(
      "interface gi;\n"
      "  logic d;\n"
      "endinterface\n"
      "module t;\n"
      "  gi dif();\n"
      "  logic q;\n"
      "  always_comb q = dif.d;\n"
      "  initial begin\n"
      "    dif.d = 0;\n"
      "    #10 dif.d = 1;\n"
      "    #1 $display(\"%0d\", q);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1\n");
}

TEST(InterfacePortTypedefSim, TypeTakenThroughAPortIsTheInterfacesType) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc; typedef enum logic [2:0] {Y=1,N=5} "
                       "choice; endinterface\n"
                       "module sub(ifc i); typedef i.choice yes_no;\n"
                       "  yes_no P = yes_no'(5);\n"
                       "  initial #1 $display(\"n=%s num=%0d\", P.name(), "
                       "P.num());\n"
                       "endmodule\n"
                       "module Top; ifc x(); sub s(x); endmodule\n",
                       f),
            "n=N num=2\n");
}

TEST(InterfacePortTypedefSim,
     TypeTakenThroughAPortArrayElementGainsNoDimension) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  typedef byte IT;\n"
                       "  typedef byte IA [3];\n"
                       "endinterface\n"
                       "module sub(ifc i [2]);\n"
                       "  typedef i[1].IT T;\n"
                       "  typedef i[0].IA A;\n"
                       "  T v;\n"
                       "  A a;\n"
                       "  initial begin\n"
                       "    v = 8'h5A;\n"
                       "    a = '{1, 2, 3};\n"
                       "    #1 $display(\"%0d %h %0d %0d\", $bits(v), v, "
                       "$size(a), a[2]);\n"
                       "  end\n"
                       "endmodule\n"
                       "module Top; ifc x [2] (); sub s(x); endmodule\n",
                       f),
            "8 5a 3 3\n");
}

TEST(InterfacePortTypedefSim, TypeTakenThroughAPortKeepsItsUnpackedDimensions) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface ifc;\n"
                       "  typedef byte IA [3];\n"
                       "  typedef int IQ [$];\n"
                       "  typedef int ID [];\n"
                       "  typedef int IS [string];\n"
                       "endinterface\n"
                       "module one(ifc i);\n"
                       "  typedef i.IA A;\n"
                       "  typedef i.IQ Q;\n"
                       "  typedef i.ID D;\n"
                       "  typedef i.IS S;\n"
                       "  A a;\n"
                       "  Q q;\n"
                       "  D d;\n"
                       "  S s;\n"
                       "  initial begin\n"
                       "    a = '{4, 5, 6};\n"
                       "    q.push_back(7);\n"
                       "    q.push_back(9);\n"
                       "    d = new[4];\n"
                       "    s[\"k\"] = 11;\n"
                       "    #1 $display(\"%0d %0d %0d %0d %0d %0d\", $size(a), "
                       "a[0], q.size(), q[$], d.size(), s[\"k\"]);\n"
                       "  end\n"
                       "endmodule\n"
                       "module Top; ifc y (); one o(y); endmodule\n",
                       f),
            "3 4 2 9 4 11\n");
}

TEST(HierarchicalInterfaceAccessSim,
     AWriteFromAModportPortModuleIgnoresTheModportsDirection) {
  EXPECT_EQ(RunWithoutErrors(
                "interface ebus_i; integer I; logic [3:0] Q; modport mp(input "
                "Q); endinterface\n"
                "module sub(ebus_i.mp i);\n"
                "  initial begin\n"
                "    #1 top.ebus.Q = 9;\n"
                "    top.ebus.I = 7;\n"
                "    #1 $display(\"Q=%0d I=%0d\", i.Q, top.ebus.I);\n"
                "  end\n"
                "endmodule\n"
                "module top;\n"
                "  ebus_i ebus();\n"
                "  sub s1(ebus.mp);\n"
                "  initial #3 $display(\"top Q=%0d I=%0d\", ebus.Q, ebus.I);\n"
                "endmodule\n"),
            "Q=9 I=7\ntop Q=9 I=7\n");
}

TEST(HierarchicalInterfaceAccessSim, AModportPortModuleReadsAnUnlistedObject) {
  EXPECT_EQ(RunWithoutErrors("interface ebus_i; integer I; logic Q; modport "
                             "mp(input Q); endinterface\n"
                             "module sub(ebus_i.mp i);\n"
                             "  initial #1 $display(\"I=%0d\", top.ebus.I);\n"
                             "endmodule\n"
                             "module top;\n"
                             "  ebus_i ebus();\n"
                             "  sub s1(ebus.mp);\n"
                             "  initial ebus.I = 5;\n"
                             "endmodule\n"),
            "I=5\n");
}

TEST(HierarchicalInterfaceAccessSim,
     AModportPortProgramWritesAndReadsAnUnlistedObject) {
  EXPECT_EQ(RunWithoutErrors("interface ebus_i; integer I; logic Q; modport "
                             "mp(input Q); endinterface\n"
                             "program p(ebus_i.mp i);\n"
                             "  initial begin\n"
                             "    top.ebus.I = 3;\n"
                             "    #1 $display(\"I=%0d\", top.ebus.I);\n"
                             "  end\n"
                             "endprogram\n"
                             "module top;\n"
                             "  ebus_i ebus();\n"
                             "  p p1(ebus.mp);\n"
                             "endmodule\n"),
            "I=3\n");
}

TEST(HierarchicalInterfaceAccessSim,
     AClassMethodBesideAModportVirtualInterfaceWritesAnUnlistedObject) {
  EXPECT_EQ(RunWithoutErrors("interface ebus_i; integer I; logic Q; modport "
                             "mp(input Q); endinterface\n"
                             "module top;\n"
                             "  ebus_i ebus();\n"
                             "  virtual ebus_i.mp v;\n"
                             "  class C;\n"
                             "    task poke(); top.ebus.I = 6; endtask\n"
                             "  endclass\n"
                             "  C c;\n"
                             "  initial begin\n"
                             "    v = ebus;\n"
                             "    c = new;\n"
                             "    c.poke();\n"
                             "    #1 $display(\"I=%0d\", ebus.I);\n"
                             "  end\n"
                             "endmodule\n"),
            "I=6\n");
}

TEST(HierarchicalInterfaceAccessSim,
     AWriteBesideAModportPortAndAModportVirtualInterfaceLands) {
  EXPECT_EQ(RunWithoutErrors("interface ebus_i; integer I; logic Q; modport "
                             "mp(input Q); endinterface\n"
                             "module sub(ebus_i.mp i); endmodule\n"
                             "module top;\n"
                             "  ebus_i ebus();\n"
                             "  sub s1(ebus.mp);\n"
                             "  virtual ebus_i.mp v;\n"
                             "  initial begin\n"
                             "    v = ebus;\n"
                             "    top.ebus.I = 0;\n"
                             "    #1 top.ebus.I = 11;\n"
                             "    #1 $display(\"I=%0d\", ebus.I);\n"
                             "  end\n"
                             "endmodule\n"),
            "I=11\n");
}

TEST(ModportUnlistableObjectSim,
     ATypeTakenThroughAModportPortIsTheInterfacesEnum) {
  EXPECT_EQ(RunWithoutErrors(
                "interface ebus_i;\n"
                "  typedef enum logic [2:0] {Y=1, N=5} choice;\n"
                "  logic Q;\n"
                "  modport mp(input Q);\n"
                "endinterface\n"
                "module sub(ebus_i.mp i);\n"
                "  typedef i.choice yes_no;\n"
                "  yes_no P;\n"
                "  initial begin\n"
                "    P = yes_no'(5);\n"
                "    $display(\"%s %0d %0d\", P.name(), P.num(), $bits(P));\n"
                "  end\n"
                "endmodule\n"
                "module top; ebus_i ebus(); sub s1(ebus.mp); endmodule\n"),
            "N 2 3\n");
}

TEST(ModportUnlistableObjectSim,
     TheSubclausesExampleRunsThroughAGenericModportPort) {
  EXPECT_EQ(RunWithoutErrors("interface ebus_i;\n"
                             "  typedef enum {Y, N} choice;\n"
                             "  choice Q;\n"
                             "  localparam True = 1;\n"
                             "  integer I;\n"
                             "  modport mp(input Q);\n"
                             "endinterface\n"
                             "module sub(interface.mp i);\n"
                             "  typedef i.choice yes_no;\n"
                             "  yes_no P;\n"
                             "  assign P = i.Q;\n"
                             "  initial #1 $display(\"I=%0d Q=%0d P=%s\", "
                             "top.ebus.I, i.Q, P.name());\n"
                             "endmodule\n"
                             "module top;\n"
                             "  ebus_i ebus();\n"
                             "  sub s1(ebus.mp);\n"
                             "  initial begin\n"
                             "    ebus.Q = ebus.True;\n"
                             "    ebus.I = 0;\n"
                             "  end\n"
                             "endmodule\n"),
            "I=0 Q=1 P=N\n");
}

TEST(ModportUnlistableObjectSim,
     AParameterReadThroughAModportPortIsTheInstances) {
  EXPECT_EQ(RunWithoutErrors("interface bbus; parameter Width = 4; logic Q; "
                             "modport mp(input Q); endinterface\n"
                             "interface pbus #(parameter PW = 3); logic Q; "
                             "modport mp(input Q); endinterface\n"
                             "module sub(bbus.mp i);\n"
                             "  initial $display(\"%m %0d\", i.Width);\n"
                             "endmodule\n"
                             "module psub(pbus.mp i);\n"
                             "  initial $display(\"%m %0d\", i.PW);\n"
                             "endmodule\n"
                             "module gsub(interface.mp i);\n"
                             "  initial $display(\"%m %0d\", i.Width);\n"
                             "endmodule\n"
                             "module top;\n"
                             "  bbus e();\n"
                             "  bbus #(.Width(9)) f();\n"
                             "  pbus g();\n"
                             "  pbus #(6) h();\n"
                             "  sub a(e.mp);\n"
                             "  sub b(f.mp);\n"
                             "  psub c(g.mp);\n"
                             "  psub d(h.mp);\n"
                             "  gsub x(e.mp);\n"
                             "  gsub y(f.mp);\n"
                             "endmodule\n"),
            "top.a 4\ntop.b 9\ntop.c 3\ntop.d 6\ntop.x 4\ntop.y 9\n");
}

TEST(ModportUnlistableObjectSim,
     AParameterReadThroughAModportVirtualInterfaceIsTheInstances) {
  EXPECT_EQ(RunWithoutErrors("interface ebus_i #(parameter W = 4); logic Q; "
                             "modport mp(input Q); endinterface\n"
                             "module top;\n"
                             "  ebus_i #(.W(7)) ebus();\n"
                             "  ebus_i dbus();\n"
                             "  virtual ebus_i #(.W(7)).mp v;\n"
                             "  virtual ebus_i.mp w;\n"
                             "  initial begin\n"
                             "    v = ebus;\n"
                             "    w = dbus;\n"
                             "    $display(\"%0d %0d\", v.W, w.W);\n"
                             "  end\n"
                             "endmodule\n"),
            "7 4\n");
}

TEST(ModportUnlistableObjectSim, AnEnumConstantReadThroughAModportPort) {
  EXPECT_EQ(RunWithoutErrors(
                "interface ebus_i; typedef enum {Y, N} choice; logic Q; "
                "modport mp(input Q); endinterface\n"
                "module sub(ebus_i.mp i);\n"
                "  initial $display(\"%0d %0d\", i.N, i.Y);\n"
                "endmodule\n"
                "module top; ebus_i ebus(); sub s1(ebus.mp); endmodule\n"),
            "1 0\n");
}

TEST(GenericPortTypedefSim,
     ATypeTakenThroughAGenericPortIsTheConnectedInterfaces) {
  EXPECT_EQ(RunWithoutErrors(
                "interface ia; typedef int IT [$]; logic Q; modport mp(input "
                "Q); endinterface\n"
                "interface ib; typedef int IT [2]; logic Q; modport mp(input "
                "Q); endinterface\n"
                "\n"
                "module m (interface i);\n"
                "  typedef i.IT T1;\n"
                "  T1 v;\n"
                "  initial $display(\"%m %0d\", $size(v));\n"
                "endmodule\n"
                "module top; ia a(); ib b(); m ua(a); m ub(b); endmodule\n"),
            "top.ua 0\ntop.ub 2\n");
}

TEST(GenericPortTypedefSim, AQueueTypeTakenThroughAGenericPortTakesAPush) {
  EXPECT_EQ(RunWithoutErrors("interface ia; typedef int IT [$]; logic Q; "
                             "modport mp(input Q); endinterface\n"
                             "interface ib; typedef int IT [2]; logic Q; "
                             "modport mp(input Q); endinterface\n"
                             "\n"
                             "module m (interface i);\n"
                             "  typedef i.IT T1;\n"
                             "  T1 v;\n"
                             "  initial begin\n"
                             "    v.push_back(4);\n"
                             "    $display(\"%0d\", v.size());\n"
                             "  end\n"
                             "endmodule\n"
                             "module top; ia a(); m ua(a); endmodule\n"),
            "1\n");
}

TEST(GenericPortTypedefSim, AQueueTypeTakenThroughANamedPortTakesAPush) {
  EXPECT_EQ(RunWithoutErrors("interface ia; typedef int IT [$]; logic Q; "
                             "modport mp(input Q); endinterface\n"
                             "interface ib; typedef int IT [2]; logic Q; "
                             "modport mp(input Q); endinterface\n"
                             "\n"
                             "module m (ia i);\n"
                             "  typedef i.IT T1;\n"
                             "  T1 v;\n"
                             "  initial begin\n"
                             "    v.push_back(4);\n"
                             "    $display(\"%0d\", v.size());\n"
                             "  end\n"
                             "endmodule\n"
                             "module top; ia a(); m ua(a); endmodule\n"),
            "1\n");
}

TEST(GenericPortTypedefSim,
     ATypeTakenThroughAGenericModportPortIsTheConnectedInterfaces) {
  EXPECT_EQ(
      RunWithoutErrors(
          "interface ia; typedef int IT [$]; logic Q; modport mp(input Q); "
          "endinterface\n"
          "interface ib; typedef int IT [2]; logic Q; modport mp(input Q); "
          "endinterface\n"
          "\n"
          "module n (interface.mp i);\n"
          "  typedef i.IT T1;\n"
          "  T1 v;\n"
          "  initial $display(\"%m %0d\", $size(v));\n"
          "endmodule\n"
          "module top; ia a(); ib b(); n na(a.mp); n nb(b.mp); endmodule\n"),
      "top.na 0\ntop.nb 2\n");
}

TEST(GenericPortTypedefSim, ATypeTakenThroughAGenericPortInAGenerateBlock) {
  EXPECT_EQ(RunWithoutErrors(
                "interface ia; typedef int IT [$]; logic Q; modport mp(input "
                "Q); endinterface\n"
                "interface ib; typedef int IT [2]; logic Q; modport mp(input "
                "Q); endinterface\n"
                "\n"
                "module g (interface i);\n"
                "  if (1) begin : blk\n"
                "    typedef i.IT T1;\n"
                "    T1 v;\n"
                "    initial $display(\"%m %0d\", $size(v));\n"
                "  end\n"
                "endmodule\n"
                "module top; ia a(); ib b(); g ga(a); g gb(b); endmodule\n"),
            "top.ga.blk 0\ntop.gb.blk 2\n");
}

TEST(GenericPortTypedefSim,
     DISABLED_ATypeTakenThroughAGenericPortInAProceduralBlock) {
  EXPECT_EQ(RunWithoutErrors(
                "interface ia; typedef int IT [$]; logic Q; modport mp(input "
                "Q); endinterface\n"
                "interface ib; typedef int IT [2]; logic Q; modport mp(input "
                "Q); endinterface\n"
                "\n"
                "module g (interface i);\n"
                "  initial begin\n"
                "    typedef i.IT T2;\n"
                "    T2 w;\n"
                "    $display(\"%m %0d\", $size(w));\n"
                "  end\n"
                "endmodule\n"
                "module top; ia a(); ib b(); g ga(a); g gb(b); endmodule\n"),
            "top.ga 0\ntop.gb 2\n");
}

}  // namespace
