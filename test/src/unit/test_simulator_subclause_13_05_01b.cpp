#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

namespace {

std::string PackageTypedefFormalSrc(const std::string& subroutine,
                                    const std::string& call) {
  return "package p;\n"
         "  typedef mailbox mb_t;\n" +
         subroutine +
         "endpackage\n"
         "module top;\n"
         "  mailbox mb = new;\n"
         "  int y;\n"
         "  initial begin\n"
         "    mb.put(1);\n" +
         call +
         "  end\n"
         "endmodule\n";
}

TEST(PassByValueSim, PackageFunctionMailboxFormalThroughThePackagesOwnTypedef) {
  EXPECT_EQ(RunAndGet(PackageTypedefFormalSrc(
                          "  function automatic int count(mb_t m);\n"
                          "    return m.num();\n"
                          "  endfunction\n",
                          "    y = p::count(mb);\n"),
                      "y"),
            1u);
}

TEST(PassByValueSim, PackageTaskMailboxFormalThroughThePackagesOwnTypedef) {
  EXPECT_EQ(RunAndGet(PackageTypedefFormalSrc(
                          "  task automatic count_into(mb_t m, output int n);\n"
                          "    n = m.num();\n"
                          "  endtask\n",
                          "    p::count_into(mb, y);\n"),
                      "y"),
            1u);
}

TEST(PassByValueSim, ClassFormalBoundFromNullHoldsTheObjectTheBodyAssigns) {
  EXPECT_EQ(RunAndGet("class C;\n"
                      "  int k = 5;\n"
                      "  function int get(); return k; endfunction\n"
                      "endclass\n"
                      "class D extends C;\n"
                      "  function new(); k = 9; endfunction\n"
                      "endclass\n"
                      "function automatic int init(C cs = null);\n"
                      "  D d;\n"
                      "  if (cs == null) begin\n"
                      "    d = new;\n"
                      "    cs = d;\n"
                      "  end\n"
                      "  return cs == null ? 1 : cs.get();\n"
                      "endfunction\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static C first = new;\n"
                      "    result = init(null) * 100 + init();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            909u);
}

TEST(PassByValueSim, AssignmentPatternActualFillsAnArrayFormal) {
  EXPECT_EQ(
      RunAndGet(
          "module t;\n"
          "  function automatic int f(int a[3]); "
          "return a[0] * 100 + a[1] * 10 + a[2]; endfunction\n"
          "  function automatic int g(int a[2:0]); "
          "return a[2] * 100 + a[1] * 10 + a[0]; endfunction\n"
          "  int x = 5;\n"
          "  int r;\n"
          "  initial r = f('{1, 2, 3}) + 1000 * f('{default: 2}) +\n"
          "             1000000 * g('{1, 2, 3}) - f('{0: x, default: 1});\n"
          "endmodule\n",
          "r"),
      123u + 222000u + 123000000u - 511u);
}

TEST(PassByValueSim, FormalOfAnArrayTypedefHasItsDimensions) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  typedef int arr_t[3];\n"
                 "  function automatic int f(arr_t a); "
                 "return a[0] * 100 + a[1] * 10 + a[2]; endfunction\n"
                 "  task automatic o(output arr_t r); r = '{4, 5, 6}; endtask\n"
                 "  arr_t ov;\n"
                 "  initial begin\n"
                 "    o(ov);\n"
                 "    $display(\"%0d %0d %0d %p\", f('{1, 2, 3}), "
                 "f(arr_t'{1, 2, 3}), f('{default: 2}), ov);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "123 123 222 '{4, 5, 6}\n");
}

TEST(PassByValueSim, MemberOfAnElementOfAPackedStructureArrayFormal) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "typedef struct packed { logic [3:0] hi; logic [3:0] lo; } B;\n"
                "module t;\n"
                "  function automatic int f(input B b[2]);\n"
                "    return b[1].lo * 10 + b[0].hi;\n"
                "  endfunction\n"
                "  task automatic tk(input B b[2], output int r);\n"
                "    r = b[1].hi;\n"
                "  endtask\n"
                "  B arr[2];\n"
                "  int r;\n"
                "  initial begin\n"
                "    arr[0] = '{hi: 3, lo: 1}; arr[1] = '{hi: 9, lo: 2};\n"
                "    tk(arr, r);\n"
                "    $display(\"%0d %0d\", f(arr), r);\n"
                "  end\n"
                "endmodule\n",
                f),
            "23 9\n");
}

TEST(PassByValueSim, UnwrittenOutputFormalCopiesOutItsTypesDefault) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module t;\n"
                "  function automatic void f(output logic [3:0] l,\n"
                "                            output int i,\n"
                "                            output bit [3:0] b);\n"
                "  endfunction\n"
                "  task automatic tk(output logic [1:0] a[2]); endtask\n"
                "  logic [3:0] l = 4'b1010; int i = 7; bit [3:0] b = 4'b1111;\n"
                "  logic [1:0] a[2] = '{2'b01, 2'b10};\n"
                "  initial begin\n"
                "    f(l, i, b); tk(a);\n"
                "    $display(\"%b %0d %b %b %b\", l, i, b, a[0], a[1]);\n"
                "  end\n"
                "endmodule\n",
                f),
            "xxxx 0 0000 xx xx\n");
}

TEST(PassByValueSim, StringOutputReplacesTheActualsTextWhateverItsLength) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  function automatic void f(output string s,\n"
                 "                            input string v);\n"
                 "    s = v;\n"
                 "  endfunction\n"
                 "  string a = \"ab\", b = \"abcdefgh\";\n"
                 "  initial begin\n"
                 "    f(a, \"abcdef\"); f(b, \"xy\");\n"
                 "    $display(\"%0d %s %0d %s\", a.len(), a, b.len(), b);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "6 abcdef 2 xy\n");
}

TEST(PassByValueSim, DISABLED_TheClauseExampleXorsAThousandByteCopy) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  byte pkt [1000:1];\n"
                 "  function automatic int crc( byte packet [1000:1] );\n"
                 "    for( int j= 1; j <= 1000; j++ ) begin\n"
                 "      crc ^= packet[j];\n"
                 "    end\n"
                 "  endfunction\n"
                 "  initial begin\n"
                 "    for (int j = 1; j <= 1000; j++) pkt[j] = j * 5 + 1;\n"
                 "    $display(\"%0d\", crc(pkt));\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "-64\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByValueSim, ClearingTheArrayCopyLeavesTheCallersArray) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  byte pkt [1000:1];\n"
                 "  function automatic int clear( byte packet [1000:1] );\n"
                 "    for (int j = 1; j <= 1000; j++) packet[j] = 0;\n"
                 "    return packet[1000] + packet[1];\n"
                 "  endfunction\n"
                 "  initial begin\n"
                 "    for (int j = 1; j <= 1000; j++) pkt[j] = j * 5 + 1;\n"
                 "    $display(\"%0d %0d %0d\", clear(pkt), pkt[1], "
                 "pkt[1000]);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "0 6 -119\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByValueSim, EachRecursiveActivationKeepsItsFormalAcrossTheInnerCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  function automatic int weigh(int n);\n"
                       "    int r;\n"
                       "    if (n == 0) return 0;\n"
                       "    r = weigh(n - 1);\n"
                       "    n = n * 10;\n"
                       "    return n + r;\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d\", weigh(3));\n"
                       "endmodule\n",
                       f),
            "60\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByValueSim, ATaskKeepsTheValueCopiedWhenItWasCalled) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  int x;\n"
                       "  task show(input int v);\n"
                       "    #5 $display(\"%0t %0d %0d\", $time, v, x);\n"
                       "    v = 99;\n"
                       "    #1 $display(\"%0t %0d %0d\", $time, v, x);\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    x = 1;\n"
                       "    fork\n"
                       "      show(x);\n"
                       "    join_none\n"
                       "    #2 x = 2;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5 1 2\n6 99 2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByValueSim, AHandleFormalIsCopiedButItsObjectIsShared) {
  SimFixture f;
  EXPECT_EQ(RunCapture("class C;\n"
                       "  int a;\n"
                       "endclass\n"
                       "module m;\n"
                       "  C h = new();\n"
                       "  C kept;\n"
                       "  function automatic void poke(C p);\n"
                       "    p.a = 7;\n"
                       "    p = new();\n"
                       "    p.a = 8;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    h.a = 1;\n"
                       "    kept = h;\n"
                       "    poke(h);\n"
                       "    $display(\"%0d %0d\", h.a, h == kept);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "7 1\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByValueSim, StructStringAndRealFormalsAreCopies) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  typedef struct { int a; byte b; } s_t;\n"
                       "  s_t s;\n"
                       "  string t;\n"
                       "  real r;\n"
                       "  logic [99:0] w;\n"
                       "  function automatic int spoil(s_t ps, string pt, "
                       "real pr, logic [99:0] pw);\n"
                       "    ps.a = 0;\n"
                       "    ps.b = 0;\n"
                       "    pt = \"gone\";\n"
                       "    pt[0] = \"G\";\n"
                       "    pr = 0.0;\n"
                       "    pw[99] = 0;\n"
                       "    return ps.a + ps.b + pt.len();\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    s = '{5, 6};\n"
                       "    t = \"kept\";\n"
                       "    r = 2.5;\n"
                       "    w = {1'b1, 99'd3};\n"
                       "    $display(\"%0d %0d %0d %s %0.1f %0d %0d\", "
                       "spoil(s, t, r, w), s.a, s.b, t, r, w[99], w[1:0]);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "4 5 6 kept 2.5 1 3\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByValueSim, AFormalIsACopyInEveryPlaceASubroutineIsDeclared) {
  SimFixture f;
  EXPECT_EQ(RunCapture("function automatic int unit_f(int v);\n"
                       "  v = v + 1;\n"
                       "  return v;\n"
                       "endfunction\n"
                       "package p;\n"
                       "  function automatic int pkg_f(int v);\n"
                       "    v = v + 2;\n"
                       "    return v;\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "class C;\n"
                       "  function int meth(int v);\n"
                       "    v = v + 3;\n"
                       "    return v;\n"
                       "  endfunction\n"
                       "  static function int smeth(int v);\n"
                       "    v = v + 4;\n"
                       "    return v;\n"
                       "  endfunction\n"
                       "endclass\n"
                       "interface ifc;\n"
                       "  function int if_f(int v);\n"
                       "    v = v + 5;\n"
                       "    return v;\n"
                       "  endfunction\n"
                       "endinterface\n"
                       "module m;\n"
                       "  ifc i();\n"
                       "  C c = new();\n"
                       "  int x;\n"
                       "  task static mod_t(int v, output int o);\n"
                       "    v = v + 6;\n"
                       "    o = v;\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    int o;\n"
                       "    x = 10;\n"
                       "    mod_t(x, o);\n"
                       "    $display(\"%0d %0d %0d %0d %0d %0d %0d\", "
                       "unit_f(x), p::pkg_f(x), c.meth(x), C::smeth(x), "
                       "i.if_f(x), o, x);\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "11 12 13 14 15 16 10\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByValueSim, AProgramFunctionFormalIsACopy) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program pg;\n"
                       "  int x;\n"
                       "  function automatic int bump(int v);\n"
                       "    v = v * 3;\n"
                       "    return v;\n"
                       "  endfunction\n"
                       "  initial begin\n"
                       "    x = 4;\n"
                       "    $display(\"%0d %0d\", bump(x), x);\n"
                       "  end\n"
                       "endprogram\n",
                       f),
            "12 4\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
