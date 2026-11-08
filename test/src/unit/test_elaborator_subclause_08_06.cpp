#include <gtest/gtest.h>

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

}  // namespace
