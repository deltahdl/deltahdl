// §13.5.2: Pass by reference


#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"

#include "fixture_parser.h"

using namespace delta;

};

namespace {

TEST(ParserA26, FuncBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  function void foo(const ref int x);\n"
      "  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TaskBodyNewStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

TEST(ParserA27, TfPortDirectionConstRefStatic) {
  auto r = Parse(
      "module m;\n"
      "  task my_task(const ref static int x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

// ---------------------------------------------------------------------------
// tf_port_declaration (old-style): const ref and var
// ---------------------------------------------------------------------------
TEST(ParserA27, TfPortDeclOldStyleConstRef) {
  auto r = Parse(
      "module m;\n"
      "  task my_task;\n"
      "    const ref int x;\n"
      "    $display(\"%0d\", x);\n"
      "  endtask\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->func_args.size(), 1u);
  EXPECT_TRUE(item->func_args[0].is_const);
  EXPECT_EQ(item->func_args[0].direction, Direction::kRef);
}

}  // namespace
