#include <gtest/gtest.h>

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

// §8.24 lets a method's body be written outside its class, and that body is
// the class's method, so §8.6 refuses it a static lifetime as it refuses one
// written in the class. A task defined for an interface by a dotted name
// (§25.7) is no class method and keeps the lifetime it is written with.
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

}  // namespace
