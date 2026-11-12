#include <gtest/gtest.h>

#include <string>
#include <utility>

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

TEST(PassByRef, ACallerAndATaskSeeEachOthersWritesDuringTheCall) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module m;\n"
                       "  int x;\n"
                       "  task automatic t(ref int r);\n"
                       "    #5 $display(\"%0t in %0d\", $time, r);\n"
                       "    r = 7;\n"
                       "    #5 $display(\"%0t in %0d\", $time, r);\n"
                       "  endtask\n"
                       "  initial begin\n"
                       "    x = 1;\n"
                       "    fork\n"
                       "      t(x);\n"
                       "    join_none\n"
                       "    #2 x = 3;\n"
                       "    #4 $display(\"%0t out %0d\", $time, x);\n"
                       "    x = 8;\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "5 in 3\n6 out 7\n10 in 8\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByRef, TheClauseExamplesCallByReferenceAsByValue) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module m;\n"
                 "  byte packet1[1000:1];\n"
                 "  byte d [];\n"
                 "  function automatic int crc(ref byte packet [1000:1]);\n"
                 "    for(int j= 1; j <= 1000; j++) begin\n"
                 "      crc ^= packet[j];\n"
                 "    end\n"
                 "  endfunction\n"
                 "  task automatic show ( const ref byte data [] );\n"
                 "    for ( int j = 0; j < data.size ; j++ )\n"
                 "      $display( data[j] );\n"
                 "  endtask\n"
                 "  initial begin\n"
                 "    int k;\n"
                 "    for (int j = 1; j <= 1000; j++) packet1[j] = j;\n"
                 "    packet1[3] = 0;\n"
                 "    k = 0;\n"
                 "    k = crc(packet1);\n"
                 "    $display(\"%0d\", k);\n"
                 "    d = '{5, -2};\n"
                 "    show(d);\n"
                 "  end\n"
                 "endmodule\n",
                 f),
      "-21\n   5\n  -2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

std::string OutdatedRefSrc(const std::string& callee,
                           const std::string& calls) {
  return "module m;\n"
         "  int aa [int];\n"
         "  int ab [int];\n"
         "  int ag [int];\n"
         "  int da [];\n"
         "  int db [];\n"
         "  int dc [];\n"
         "  int dd [];\n"
         "  int de [];\n" +
         callee +
         "  initial begin\n"
         "    aa[1] = 1;\n"
         "    ab[1] = 1;\n"
         "    ag[1] = 1;\n"
         "    da = '{1, 2};\n"
         "    db = '{1, 2};\n"
         "    dc = '{1, 2};\n"
         "    dd = '{1, 2};\n"
         "    de = '{1, 2};\n" +
         calls +
         "    $display(\"%0d %0d %0d %0d\", aa.exists(1), aa.num(), "
         "ab.exists(1), ab.num());\n"
         "    $display(\"%0d %0d %0d %0d %0d %0d %0d %0d\", da[0], da.size(), "
         "db[0], dc.size(), dd[0], dd[1], ag[1], de[0]);\n"
         "  end\n"
         "endmodule\n";
}

std::string OutdatingBody(const std::string& kind, const std::string& ret) {
  return "  " + kind + " automatic " + ret +
         "w(ref int r, input int k);\n"
         "    case (k)\n"
         "      0: aa.delete(1);\n"
         "      1: ab.delete();\n"
         "      2: da = new[4];\n"
         "      3: db = new[2](db);\n"
         "      4: dc.delete();\n"
         "      5: dd = '{7, 8};\n"
         "      6: ag[5] = 1;\n"
         "      7: de[1] = 3;\n"
         "    endcase\n"
         "    r = 99;\n"
         "  end" +
         kind + "\n";
}

constexpr const char* kOutdatingCalls =
    "    w(aa[1], 0);\n"
    "    w(ab[1], 1);\n"
    "    w(da[0], 2);\n"
    "    w(db[0], 3);\n"
    "    w(dc[0], 4);\n"
    "    w(dd[0], 5);\n"
    "    w(ag[1], 6);\n"
    "    w(de[0], 7);\n";

TEST(PassByRef, AWriteThroughAnOutdatedDynamicArrayElementIsNotSeen) {
  for (const auto& [kind, ret] :
       {std::pair<const char*, const char*>{"task", ""},
        std::pair<const char*, const char*>{"function", "void "}}) {
    SimFixture f;
    std::string out = RunCapture(
        OutdatedRefSrc(OutdatingBody(kind, ret), kOutdatingCalls), f);
    EXPECT_EQ(out.substr(out.find('\n') + 1), "0 4 1 0 7 8 99 99\n") << kind;
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

TEST(PassByRef, DISABLED_AWriteThroughADeletedAssocElementLeavesItDeleted) {
  for (const auto& [kind, ret] :
       {std::pair<const char*, const char*>{"task", ""},
        std::pair<const char*, const char*>{"function", "void "}}) {
    SimFixture f;
    std::string out = RunCapture(
        OutdatedRefSrc(OutdatingBody(kind, ret), kOutdatingCalls), f);
    EXPECT_EQ(out.substr(0, out.find('\n') + 1), "0 0 0 0\n") << kind;
    EXPECT_FALSE(f.diag.HasErrors());
  }
}

std::string OutdatingMethodSrc(const std::string& assoc_line,
                               const std::string& dynamic_line) {
  return "class C;\n"
         "  int pa [int];\n"
         "  int pd [];\n"
         "  task w(ref int r, input int k);\n"
         "    if (k == 0) " +
         assoc_line + "\n    else " + dynamic_line +
         "\n"
         "    r = 99;\n"
         "  endtask\n"
         "endclass\n"
         "module m;\n"
         "  C o = new();\n"
         "  initial begin\n"
         "    o.pa[1] = 1;\n"
         "    o.pd = '{1, 2};\n"
         "    o.w(o.pa[1], 0);\n"
         "    o.w(o.pd[0], 1);\n"
         "    $display(\"%0d %0d %0d %0d %0d\", o.pa.exists(1), o.pa.num(), "
         "(o.pa.exists(1) ? o.pa[1] : -1), o.pd[0], o.pd.size());\n"
         "  end\n"
         "endmodule\n";
}

TEST(PassByRef, AMethodsWriteThroughALivePropertyElementIsSeen) {
  SimFixture f;
  EXPECT_EQ(RunCapture(OutdatingMethodSrc("pa[2] = 5;", "pd[1] = 3;"), f),
            "1 2 99 99 2\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(PassByRef,
     DISABLED_AMethodsWriteThroughAnOutdatedPropertyElementIsNotSeen) {
  SimFixture f;
  EXPECT_EQ(RunCapture(OutdatingMethodSrc("pa.delete(1);", "pd = new[3];"), f),
            "0 0 -1 0 3\n");
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
