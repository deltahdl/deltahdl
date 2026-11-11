#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ObjectMethodParsing, MethodCallDotNotation) {
  auto r = Parse(
      "class Packet;\n"
      "  function int current_status();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int status;\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    status = p.current_status();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ObjectMethodParsing, TaskCallDotNotation) {
  auto r = Parse(
      "class Worker;\n"
      "  task do_work();\n"
      "  endtask\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Worker w;\n"
      "    w = new;\n"
      "    w.do_work();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ObjectMethodParsing, MethodCallWithArgsDotNotation) {
  ParseOk(
      "class Adder;\n"
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
      "endmodule\n");
}

TEST(ObjectMethodParsing, MethodAutomaticLifetimeLegal) {
  ParseOk(
      "class C;\n"
      "  function automatic void foo();\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(ObjectMethodParsing, MethodNoLifetimeLegal) {
  ParseOk(
      "class C;\n"
      "  function void foo();\n"
      "  endfunction\n"
      "endclass\n");
}

TEST(ObjectMethodParsing, TaskAutomaticLifetimeLegal) {
  ParseOk(
      "class C;\n"
      "  task automatic do_it();\n"
      "  endtask\n"
      "endclass\n");
}

TEST(ObjectMethodParsing, TaskNoLifetimeLegal) {
  ParseOk(
      "class C;\n"
      "  task do_it();\n"
      "  endtask\n"
      "endclass\n");
}

TEST(ObjectMethodParsing, FunctionStaticLifetimeError) {
  auto r = Parse(
      "class C;\n"
      "  function static void foo();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "class method shall not have static lifetime", 2, "8.6"));
}

TEST(ObjectMethodParsing, TaskStaticLifetimeError) {
  auto r = Parse(
      "class C;\n"
      "  task static do_stuff();\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "class method shall not have static lifetime", 2, "8.6"));
}

TEST(ObjectMethodParsing, OutOfBlockStaticLifetimeIsReported) {
  auto r = Parse(
      "class C;\n"
      "  extern function void f();\n"
      "  extern task t();\n"
      "endclass\n"
      "function static void C::f(); endfunction\n"
      "task static C::t(); endtask\n"
      "function automatic void C::g(); endfunction\n"
      "interface ifc; endinterface\n"
      "task static ifc.u(); endtask\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "class method shall not have static lifetime", 5, "8.6"));
  EXPECT_TRUE(ReportedError(
      r.diags, "class method shall not have static lifetime", 6, "8.6"));
  EXPECT_FALSE(ReportedError(
      r.diags, "class method shall not have static lifetime", 7, "8.6"));
  EXPECT_FALSE(ReportedError(
      r.diags, "class method shall not have static lifetime", 9, "8.6"));
}

TEST(ObjectMethodParsing, StaticLifetimeIsReportedWhereverTheClassIsDeclared) {
  auto r = Parse(
      "module m;\n"
      "  class C1; function static int f(); return 0; endfunction endclass\n"
      "endmodule\n"
      "package k;\n"
      "  class C2; task static t(); endtask endclass\n"
      "endpackage\n"
      "program p;\n"
      "  class C3; function static void f(); endfunction endclass\n"
      "endprogram\n"
      "interface i;\n"
      "  class C4; function static void f(); endfunction endclass\n"
      "endinterface\n"
      "class O;\n"
      "  class N; function static void f(); endfunction endclass\n"
      "endclass\n"
      "module g;\n"
      "  if (1) begin : b\n"
      "    class C5; function static void f(); endfunction endclass\n"
      "  end\n"
      "endmodule\n");
  for (const uint32_t kLine : {2u, 5u, 8u, 11u, 14u, 18u}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "class method shall not have static lifetime", kLine, "8.6"))
        << kLine;
  }
}

TEST(ObjectMethodParsing, StaticLifetimeIsReportedBesideEveryQualifier) {
  auto r = Parse(
      "class O;\n"
      "  function static new(); endfunction\n"
      "  static function static int sf(); return 0; endfunction\n"
      "  virtual function static void vf(); endfunction\n"
      "  static task static st(); endtask\n"
      "  protected function static void pf(); endfunction\n"
      "  local task static lt(); endtask\n"
      "  static function automatic int sa(); return 0; endfunction\n"
      "  static task stt(); endtask\n"
      "  virtual function automatic void va(); endfunction\n"
      "  function void lv(); static int cnt; cnt++; endfunction\n"
      "endclass\n");
  for (const uint32_t kLine : {2u, 3u, 4u, 5u, 6u, 7u}) {
    EXPECT_TRUE(ReportedError(
        r.diags, "class method shall not have static lifetime", kLine, "8.6"))
        << kLine;
  }
  for (const uint32_t kLine : {8u, 9u, 10u, 11u}) {
    EXPECT_FALSE(ErrorOnLine(r.diags, kLine)) << kLine;
  }
}

}  // namespace
