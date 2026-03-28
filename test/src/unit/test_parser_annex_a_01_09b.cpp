#include "fixture_parser.h"

using namespace delta;

namespace {

// §8.6: class method shall not have static lifetime

TEST(ClassItemsParsing, FunctionStaticLifetimeError) {
  auto r = Parse(
      "class C;\n"
      "  function static void foo();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassItemsParsing, TaskStaticLifetimeError) {
  auto r = Parse(
      "class C;\n"
      "  task static do_stuff();\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

// §8.10: static and virtual are mutually exclusive

TEST(ClassItemsParsing, StaticVirtualFunctionError) {
  auto r = Parse(
      "class C;\n"
      "  static virtual function int foo();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

TEST(ClassItemsParsing, StaticVirtualTaskError) {
  auto r = Parse(
      "class C;\n"
      "  virtual static task bar();\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(r.has_errors);
}

}  // namespace
