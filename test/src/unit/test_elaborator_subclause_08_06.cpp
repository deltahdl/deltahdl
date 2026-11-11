#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ObjectMethodElaboration, ClassWithMethodElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int data;\n"
             "  function int get_data();\n"
             "    return data;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(ObjectMethodElaboration, MethodCallOnInstanceElaborates) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  function int current_status();\n"
             "    return 0;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    automatic int s;\n"
             "    s = p.current_status();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectMethodElaboration, MethodCallWithArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class Adder;\n"
             "  int total;\n"
             "  function void add(int v);\n"
             "    total = total + v;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Adder a;\n"
             "    a = new;\n"
             "    a.add(5);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectMethodElaboration, TaskCallOnInstanceElaborates) {
  EXPECT_TRUE(
      ElabOk("class Worker;\n"
             "  int done;\n"
             "  task do_work();\n"
             "    done = 1;\n"
             "  endtask\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Worker w;\n"
             "    w = new;\n"
             "    w.do_work();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectMethodElaboration, MultipleMethodCallsElaborate) {
  EXPECT_TRUE(
      ElabOk("class Counter;\n"
             "  int count;\n"
             "  function void inc();\n"
             "    count = count + 1;\n"
             "  endfunction\n"
             "  function int get();\n"
             "    return count;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    automatic int v;\n"
             "    Counter c;\n"
             "    c = new;\n"
             "    c.inc();\n"
             "    v = c.get();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectMethodElaboration, UndeclaredMemberAndMethodAreReported) {
  ElabFixture f;
  ElabOk(
      "module top;\n"
      "  class H; task run(); endtask endclass\n"
      "  class B; H h = new; endclass\n"
      "  B b = new;\n"
      "  initial begin b.nosuch.run(); b.h.nosuch(); end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'B' has no member named 'nosuch'", 5,
                            "8.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'H' has no member named 'nosuch'", 5,
                            "8.6"));
}

TEST(ObjectMethodElaboration, InheritedAndBuiltInMethodsAreMembers) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  task run(); endtask\n"
             "endclass\n"
             "class D extends Base;\n"
             "endclass\n"
             "module m;\n"
             "  D d = new;\n"
             "  initial begin\n"
             "    d.run();\n"
             "    d.srandom(1);\n"
             "    void'(d.randomize());\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectMethodElaboration, MethodOfAnInterfaceClassIsAMember) {
  EXPECT_TRUE(
      ElabOk("interface class J;\n"
             "  pure virtual function void j();\n"
             "endclass\n"
             "interface class I1 extends J;\n"
             "endclass\n"
             "interface class I2 extends J;\n"
             "endclass\n"
             "class C implements I1, I2;\n"
             "  virtual function void j(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c = new;\n"
             "  I1 i;\n"
             "  initial begin\n"
             "    i = c;\n"
             "    c.j();\n"
             "    i.j();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ObjectMethodElaboration, UndeclaredMethodThroughAPropertyIsReported) {
  ElabFixture f;
  ElabOk(
      "class H; task run(); endtask endclass\n"
      "class B;\n"
      "  H h;\n"
      "  task go(); h.nosuch(); endtask\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'H' has no member named 'nosuch'", 4,
                            "8.6"));
}

TEST(ObjectMethodElaboration, SelectFromAMethodResultIsUnchecked) {
  EXPECT_TRUE(
      ElabOk("class H;\n"
             "  int v;\n"
             "  function H get(); return this; endfunction\n"
             "endclass\n"
             "module m;\n"
             "  H h = new;\n"
             "  initial $display(h.get().v);\n"
             "endmodule\n"));
}

TEST(ObjectMethodElaboration, BareTaskMethodEnableOutsideItsClassIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  integer status;\n"
      "  task clean(); status = 0; endtask\n"
      "endclass\n"
      "interface ifc;\n"
      "  Packet p = new;\n"
      "  initial clean(p);\n"
      "  initial p.clean();\n"
      "endinterface\n"
      "program pg;\n"
      "  Packet p = new;\n"
      "  initial clean(p);\n"
      "  initial p.clean();\n"
      "endprogram\n"
      "module t;\n"
      "  Packet p = new;\n"
      "  ifc i();\n"
      "  pg q();\n"
      "  task tk(); clean(p); endtask\n"
      "  task tk2(); p.clean(); endtask\n"
      "  initial begin\n"
      "    clean(p);\n"
      "    clean();\n"
      "    p.clean();\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {7u, 12u, 19u, 22u, 23u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "undeclared identifier 'clean'", kLine, "23.9"))
        << kLine;
  }
  for (const uint32_t kLine : {8u, 13u, 20u, 24u}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), kLine)) << kLine;
  }
}

TEST(ObjectMethodElaboration,
     DISABLED_BareTaskMethodEnableInAPackageOrUnitTaskIsReported) {
  ElabFixture f;
  ElabOk(
      "package k;\n"
      "  class PP; task clean(); endtask endclass\n"
      "  task pt(PP q); clean(q); endtask\n"
      "  task pt2(PP q); q.clean(); endtask\n"
      "endpackage\n"
      "class Packet;\n"
      "  task clean(); endtask\n"
      "endclass\n"
      "task ut(Packet p); clean(p); endtask\n"
      "task ut2(Packet p); p.clean(); endtask\n"
      "module t;\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {3u, 9u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "undeclared identifier 'clean'", kLine, "23.9"))
        << kLine;
  }
  for (const uint32_t kLine : {4u, 10u}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), kLine)) << kLine;
  }
}

TEST(ObjectMethodElaboration,
     DISABLED_BareFunctionMethodCallOutsideItsClassIsReported) {
  ElabFixture f;
  ElabOk(
      "package k;\n"
      "  class PP;\n"
      "    integer status;\n"
      "    function integer current_status(); return status; endfunction\n"
      "  endclass\n"
      "  function integer pf(PP q); return current_status(q); endfunction\n"
      "  function integer pf2(PP q); return q.current_status(); endfunction\n"
      "endpackage\n"
      "class Packet;\n"
      "  integer status;\n"
      "  function integer current_status(); return status; endfunction\n"
      "endclass\n"
      "function integer uf(Packet p); return current_status(p); endfunction\n"
      "interface ifc;\n"
      "  Packet p = new;\n"
      "  integer s;\n"
      "  initial s = current_status(p);\n"
      "endinterface\n"
      "program pg;\n"
      "  Packet p = new;\n"
      "  integer s;\n"
      "  initial s = current_status(p);\n"
      "endprogram\n"
      "module t;\n"
      "  Packet p = new;\n"
      "  integer s;\n"
      "  ifc i();\n"
      "  pg q();\n"
      "  task tk(); s = current_status(p); endtask\n"
      "  function integer fn(); return current_status(p); endfunction\n"
      "  initial begin\n"
      "    s = current_status(p);\n"
      "    s = current_status();\n"
      "    s = p.current_status();\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {6u, 13u, 17u, 22u, 29u, 30u, 32u, 33u}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              "undeclared identifier 'current_status'", kLine,
                              "23.9"))
        << kLine;
  }
  for (const uint32_t kLine : {7u, 34u}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), kLine)) << kLine;
  }
}

}  // namespace
