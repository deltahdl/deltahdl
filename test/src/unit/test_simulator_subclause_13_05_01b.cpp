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

}  // namespace
