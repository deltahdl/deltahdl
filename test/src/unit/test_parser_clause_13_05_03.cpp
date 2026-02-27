// §13.5.3: Default argument values

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserA23, ListOfTfVariableIdentifiersWithDefaults) {
  auto r = Parse(
      "module m;\n"
      "  function int compute(input int a = 1, input int b = 2);\n"
      "    compute = a + b;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->func_args.size(), 2u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
  EXPECT_NE(item->func_args[1].default_value, nullptr);
}

};

TEST(ParserA26, FuncBodyNewStyleWithDefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  function int foo(input int x = 5);\n"
      "    return x;\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

TEST(ParserA27, TaskBodyNewStyleDefaultValue) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(input int x = 5);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_NE(item->func_args[0].default_value, nullptr);
}

}  // namespace
