#include "fixture_elaborator.h"

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

}  // namespace
