#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §13.5.2 (printed page 348) forbids a ref formal to a subroutine whose
// lifetime is static, and §13.3.1 (printed page 339) makes every method of a
// class automatic; §8.10 (printed page 187) sets the static method qualifier
// apart from the static lifetime. A class static method's ref formal is
// therefore legal, and the write through it reaches the caller's handle: the
// ref form reads 3 from the object it constructed, the output form beside it
// 3, and the module's automatic function 3, packed as 333. The parser folded
// the qualifier into the lifetime flag, so the method was refused as a static
// subroutine and the run reported "ref argument 'q' not allowed in static
// subroutine 'm_get_q'".
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

// §13.5.2 (printed page 348): the rule still holds for a subroutine whose
// lifetime is static, `function static` written in a module, and the report
// names the formal, the subroutine and the subclause at the declaration.
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

// §8.10 (printed page 187) with §13.3.1 (printed page 339): a static method's
// variables are automatic, so a recursive call gets its own `acc` and two
// calls do not share `v`. fact(4) reads 24 and the two writes through the ref
// formal add 5 and 5 to `s`, packed as 2410; one shared cell apiece reads
// fact(4) as 1 and `s` as 15, which is 115.
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

}  // namespace
