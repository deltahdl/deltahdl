#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

class ExampleSixParsing : public ::testing::Test {
 protected:
  ParseResult r_ = Parse(
      "module m;\n"
      "  typedef struct { int i; int j; } MyType;\n"
      "  import \"DPI-C\" function void f1(input MyType i [][]);\n"
      "  MyType a_10x5 [11:20][6:2];\n"
      "  MyType a_64x8 [64:1][-1:-8];\n"
      "  initial begin\n"
      "    f1(a_10x5);\n"
      "    f1(a_64x8);\n"
      "  end\n"
      "endmodule\n");
};

TEST_F(ExampleSixParsing, TheSystemVerilogSideParses) {
  ASSERT_NE(r_.cu, nullptr);
  EXPECT_FALSE(r_.has_errors);
  ASSERT_EQ(r_.cu->modules.size(), 1u);
}

TEST_F(ExampleSixParsing, TheFormalIsATwoDimensionalUnsizedUnpackedArray) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f1 =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(f1, nullptr);
  ASSERT_EQ(f1->func_args.size(), 1u);
  EXPECT_EQ(f1->func_args[0].name, "i");
  EXPECT_EQ(f1->func_args[0].data_type.type_name, "MyType");
  EXPECT_EQ(f1->func_args[0].direction, Direction::kInput);
  ASSERT_EQ(f1->func_args[0].unpacked_dims.size(), 2u);
  EXPECT_EQ(f1->func_args[0].unpacked_dims[0], nullptr);
  EXPECT_EQ(f1->func_args[0].unpacked_dims[1], nullptr);
}

TEST_F(ExampleSixParsing, TheActualsHaveSizedRangesOfTheirOwn) {
  ASSERT_NE(r_.cu, nullptr);
  int arrays = 0;
  for (const ModuleItem* item : r_.cu->modules[0]->items) {
    if (item->kind != ModuleItemKind::kVarDecl) continue;
    if (item->name != "a_10x5" && item->name != "a_64x8") continue;
    ++arrays;
    EXPECT_EQ(item->data_type.type_name, "MyType");
    ASSERT_EQ(item->unpacked_dims.size(), 2u);
    EXPECT_NE(item->unpacked_dims[0], nullptr);
    EXPECT_NE(item->unpacked_dims[1], nullptr);
  }
  EXPECT_EQ(arrays, 2);
}

}  // namespace
