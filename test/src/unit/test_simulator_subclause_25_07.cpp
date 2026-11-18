#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(InterfaceSubroutineSim, CalledThroughNamedInterfacePort) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface bus;\n"
                       "  int calls;\n"
                       "  function void hit(int v); $display(\"hit %0d in "
                       "%m\", v); calls += v; endfunction\n"
                       "  task automatic tick(output int o); #2 o = 9; "
                       "endtask\n"
                       "endinterface\n"
                       "module user2(bus b);\n"
                       "  int o;\n"
                       "  initial begin\n"
                       "    #1 b.hit(10); $display(\"calls via port %0d\", "
                       "b.calls);\n"
                       "    b.tick(o); $display(\"tick o=%0d t=%0t\", o, "
                       "$time);\n"
                       "  end\n"
                       "endmodule\n"
                       "module t;\n"
                       "  bus i();\n"
                       "  user2 v(i);\n"
                       "  initial #2 $display(\"%0d\", i.calls);\n"
                       "endmodule\n",
                       f),
            "hit 10 in t.i.hit\ncalls via port 10\n10\ntick o=9 t=3\n");
}

TEST(InterfaceSubroutineSim, ModportPrototypeDefaultIsTheOneUsed) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface sb;\n"
                       "  function automatic int f(int a, int b = 9); "
                       "return b; endfunction\n"
                       "  modport mp(import function int f(int a, int b = "
                       "4));\n"
                       "endinterface\n"
                       "module m(sb.mp p);\n"
                       "  initial $display(\"v=%0d %0d %0d %0d\", p.f(1), "
                       "p.f(1, ), p.f(.a(1)), p.f(.a(1), .b()));\n"
                       "endmodule\n"
                       "module top; sb s(); m u(s.mp); endmodule\n",
                       f),
            "v=4 4 4 4\n");
}

std::string RunWithoutErrors(const std::string& src) {
  SimFixture f;
  auto out = RunCapture(src, f);
  EXPECT_FALSE(f.diag.HasErrors());
  return out;
}

constexpr const char* kSubroutineBus =
    "interface ifc;\n"
    "  int v = 4;\n"
    "  function int f(int a, int b = 0); return a + b + v; endfunction\n"
    "  function int get(); return v * 2; endfunction\n"
    "  function void vf(); v = v + 1; endfunction\n"
    "  task t(); #1 v = v + 10; endtask\n"
    "  modport mp(import f, t);\n"
    "endinterface\n";

TEST(InterfaceSubroutineSim, ANonvoidFunctionThroughTheInstanceIsAnOperand) {
  EXPECT_EQ(RunWithoutErrors(std::string(kSubroutineBus) +
                             "module top;\n"
                             "  ifc sb_intf();\n"
                             "  int x;\n"
                             "  initial begin\n"
                             "    sb_intf.v = 7;\n"
                             "    x = sb_intf.f(1) * 2;\n"
                             "    $display(\"%0d\", x);\n"
                             "  end\n"
                             "endmodule\n"),
            "16\n");
}

TEST(InterfaceSubroutineSim, ANonvoidFunctionThroughATypedPortIsAnOperand) {
  EXPECT_EQ(RunWithoutErrors(std::string(kSubroutineBus) +
                             "module m(ifc b);\n"
                             "  int x;\n"
                             "  initial begin x = b.get() + 1; "
                             "$display(\"%0d\", x); end\n"
                             "endmodule\n"
                             "module top;\n"
                             "  ifc i();\n"
                             "  m u(i);\n"
                             "  initial i.v = 3;\n"
                             "endmodule\n"),
            "7\n");
}

TEST(InterfaceSubroutineSim, EveryKindOfSubroutineRunsThroughAGenericPort) {
  EXPECT_EQ(RunWithoutErrors(std::string(kSubroutineBus) +
                             "module m(interface a);\n"
                             "  int x;\n"
                             "  initial begin\n"
                             "    a.vf();\n"
                             "    a.t();\n"
                             "    x = a.get() + 1;\n"
                             "    $display(\"%0d at %0t\", x, $time);\n"
                             "  end\n"
                             "endmodule\n"
                             "module top;\n"
                             "  ifc i();\n"
                             "  m u(i);\n"
                             "  initial #2 $display(\"top %0d\", i.v);\n"
                             "endmodule\n"),
            "31 at 1\ntop 15\n");
}

TEST(InterfaceSubroutineSim, SubroutinesImportedByNameRunInTheInstance) {
  EXPECT_EQ(RunWithoutErrors(std::string(kSubroutineBus) +
                             "module m(ifc.mp p);\n"
                             "  int x;\n"
                             "  initial begin\n"
                             "    x = p.f(1, 2);\n"
                             "    p.t();\n"
                             "    $display(\"%0d at %0t\", x, $time);\n"
                             "  end\n"
                             "endmodule\n"
                             "module top;\n"
                             "  ifc i();\n"
                             "  m u(i.mp);\n"
                             "  initial #2 $display(\"top %0d\", i.v);\n"
                             "endmodule\n"),
            "7 at 1\ntop 14\n");
}

TEST(InterfaceSubroutineSim, AnExternPrototypeTakesABodyOfAMatchingType) {
  EXPECT_EQ(RunWithoutErrors("typedef int myint;\n"
                             "interface ifc;\n"
                             "  extern function int f(int a);\n"
                             "endinterface\n"
                             "module m(interface p);\n"
                             "  function int p.f(myint a); return a + 2; "
                             "endfunction\n"
                             "endmodule\n"
                             "module top;\n"
                             "  ifc i();\n"
                             "  m u(i);\n"
                             "  initial #1 $display(\"%0d\", i.f(4));\n"
                             "endmodule\n"),
            "6\n");
}

TEST(InterfaceSubroutineSim, AnImportPrototypesDefaultIsTheOneUsed) {
  EXPECT_EQ(RunWithoutErrors("interface ifc;\n"
                             "  task t(int a = 5); $display(\"t %0d\", a); "
                             "endtask\n"
                             "  modport mp(import task t(int a = 7));\n"
                             "endinterface\n"
                             "module m(ifc.mp p);\n"
                             "  initial p.t();\n"
                             "endmodule\n"
                             "module top; ifc i(); m u(i.mp); endmodule\n"),
            "t 7\n");
}

TEST(InterfaceSubroutineSim, AnExportedTasksPrototypeDefaultIsTheOneUsed) {
  EXPECT_EQ(RunWithoutErrors("interface ifc;\n"
                             "  modport ex(export task t(int a = 7));\n"
                             "  modport im(import task t(int a = 7));\n"
                             "endinterface\n"
                             "module d(ifc.ex p);\n"
                             "  task p.t(int a = 5); $display(\"t %0d\", a); "
                             "endtask\n"
                             "endmodule\n"
                             "module c(ifc.im p);\n"
                             "  initial p.t();\n"
                             "endmodule\n"
                             "module top; ifc i(); d u(i.ex); c v(i.im); "
                             "endmodule\n"),
            "t 7\n");
}

TEST(InterfaceSubroutineSim, DISABLED_AnExternPrototypesDefaultIsTheOneUsed) {
  EXPECT_EQ(RunWithoutErrors("interface ifc;\n"
                             "  extern task t(int a = 7);\n"
                             "endinterface\n"
                             "module d(interface p);\n"
                             "  task p.t(int a = 5); $display(\"t %0d\", a); "
                             "endtask\n"
                             "endmodule\n"
                             "module top; ifc i(); d u(i); initial i.t(); "
                             "endmodule\n"),
            "t 7\n");
}

TEST(InterfaceSubroutineSim,
     AFunctionAnotherModuleDefinesRunsThroughAPrototype) {
  EXPECT_EQ(RunWithoutErrors("interface ifc;\n"
                             "  modport ex(export f);\n"
                             "  modport im(import function int f(int a));\n"
                             "endinterface\n"
                             "module d(ifc.ex p);\n"
                             "  function int p.f(int a); return a + 1; "
                             "endfunction\n"
                             "endmodule\n"
                             "module c(ifc.im p);\n"
                             "  initial $display(\"%0d\", p.f(1));\n"
                             "endmodule\n"
                             "module top; ifc i(); d u(i.ex); c v(i.im); "
                             "endmodule\n"),
            "2\n");
}

TEST(InterfaceSubroutineSim, AFullTaskPrototypeTakesByNameAndDefaultCalls) {
  EXPECT_EQ(RunWithoutErrors("interface ifc;\n"
                             "  task t(int a, int b = 3); "
                             "$display(\"t %0d %0d\", a, b); endtask\n"
                             "  modport mp(import task t(int a, int b = 3));\n"
                             "endinterface\n"
                             "module m(ifc.mp p);\n"
                             "  initial begin p.t(1, 2); p.t(.b(4), .a(5)); "
                             "p.t(6); end\n"
                             "endmodule\n"
                             "module top; ifc i(); m u(i.mp); endmodule\n"),
            "t 1 2\nt 5 4\nt 6 3\n");
}

TEST(InterfaceSubroutineSim, AnExternTaskAModuleDefinesRunsThroughTheInstance) {
  EXPECT_EQ(RunWithoutErrors("interface ifc;\n"
                             "  int cnt;\n"
                             "  extern task t();\n"
                             "endinterface\n"
                             "module m(interface p);\n"
                             "  task p.t(); #4 p.cnt = 5; endtask\n"
                             "endmodule\n"
                             "module top;\n"
                             "  ifc i();\n"
                             "  m u(i);\n"
                             "  initial begin i.t(); $display(\"%0d at %0t\", "
                             "i.cnt, $time); end\n"
                             "endmodule\n"),
            "5 at 4\n");
}

}  // namespace
