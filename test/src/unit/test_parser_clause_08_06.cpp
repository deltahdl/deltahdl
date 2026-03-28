#include "fixture_parser.h"
#include "helpers_parser_verify.h"

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
  EXPECT_TRUE(r.has_errors);
}

TEST(ObjectMethodParsing, TaskStaticLifetimeError) {
  auto r = Parse(
      "class C;\n"
      "  task static do_stuff();\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
