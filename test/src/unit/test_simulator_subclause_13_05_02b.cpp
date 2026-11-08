#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PassByRef, RefFormalOfAClassStaticMethodWritesTheCallersHandle) {
  auto val = RunAndGet(
      "class Q;\n"
      "  int n = 3;\n"
      "  function int size(); return n; endfunction\n"
      "endclass\n"
      "class C;\n"
      "  static function void m_get_q(ref Q q, input int obj);\n"
      "    q = new;\n"
      "  endfunction\n"
      "  static function void m_get_q_out(output Q q, input int obj);\n"
      "    q = new;\n"
      "  endfunction\n"
      "  static function int get_first();\n"
      "    Q q;\n"
      "    m_get_q(q, 0);\n"
      "    return q.size();\n"
      "  endfunction\n"
      "  static function int get_first_out();\n"
      "    Q q;\n"
      "    m_get_q_out(q, 0);\n"
      "    return q.size();\n"
      "  endfunction\n"
      "endclass\n"
      "function automatic void mod_get_q(ref Q q);\n"
      "  q = new;\n"
      "endfunction\n"
      "module t;\n"
      "  int res;\n"
      "  initial begin\n"
      "    Q q;\n"
      "    mod_get_q(q);\n"
      "    res = C::get_first() * 100 + C::get_first_out() * 10 +\n"
      "          (q == null ? 0 : q.size());\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 333u);
}

TEST(PassByRef, RefFormalOfAStaticLifetimeModuleFunctionIsReported) {
  SimFixture f;
  ElaborateSrc(
      "module t;\n"
      "  int v;\n"
      "  function static void get_q(ref int q);\n"
      "    q = 7;\n"
      "  endfunction\n"
      "  initial get_q(v);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "ref argument 'q' not allowed in static subroutine 'get_q'",
                    3, "13.5.2"));
}

TEST(PassByRef, ClassStaticMethodWithARefFormalKeepsAutomaticLocals) {
  auto val = RunAndGet(
      "class C;\n"
      "  static function int fact(int n);\n"
      "    int acc;\n"
      "    acc = n;\n"
      "    if (n > 1) acc = acc * fact(n - 1);\n"
      "    return acc;\n"
      "  endfunction\n"
      "  static function void add(ref int r, input int n);\n"
      "    int v;\n"
      "    v = v + n;\n"
      "    r = r + v;\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int res;\n"
      "  int s;\n"
      "  initial begin\n"
      "    s = 0;\n"
      "    C::add(s, 5);\n"
      "    C::add(s, 5);\n"
      "    res = C::fact(4) * 100 + s;\n"
      "  end\n"
      "endmodule\n",
      "res");
  EXPECT_EQ(val, 2410u);
}

TEST(PassByRef, QueuePropertyActualIsTheObjectsQueue) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  class C; int q[$];\n"
      "    task grow(); feed(q); endtask\n"
      "  endclass\n"
      "  task automatic feed(ref int q[$]);\n"
      "    q.push_back(1); #10; q.push_back(2);\n"
      "  endtask\n"
      "  C h, g;\n"
      "  initial begin\n"
      "    h = new; g = new;\n"
      "    fork feed(h.q); g.grow(); join_none\n"
      "    #5 $display(\"%0d %0d\", h.q.size(), g.q.size());\n"
      "    #10 $display(\"%0d %0d %0d\", h.q.size(), h.q[0] + h.q[1],\n"
      "                 g.q.size());\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1\n2 3 2\n");
}

TEST(PassByRef, RefFormalOfAClassPropertyIsWrittenInPlace) {
  SimFixture f;
  std::string out = RunCapture(
      "class C; int k; int arr[3]; endclass\n"
      "module t;\n"
      "  task automatic w(ref int v); v = 1; #2 v += 1; endtask\n"
      "  initial begin\n"
      "    automatic C c = new;\n"
      "    fork\n"
      "      w(c.k);\n"
      "      w(c.arr[1]);\n"
      "      begin #1 $write(\"%0d %0d \", c.k, c.arr[1]); c.k += 10; end\n"
      "    join\n"
      "    $display(\"%0d %0d\", c.k, c.arr[1]);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "1 1 12 2\n");
}

}  // namespace
