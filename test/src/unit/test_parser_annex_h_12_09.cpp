#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

class ExampleSevenParsing : public ::testing::Test {
 protected:
  ParseResult r_ = Parse(
      "module m;\n"
      "  typedef struct { int i; } MyType;\n"
      "  import \"DPI-C\" function void f1(input MyType i [], output MyType o "
      "[]);\n"
      "  MyType source [11:20];\n"
      "  MyType target [11:20];\n"
      "  initial f1(source, target);\n"
      "endmodule\n");
};

TEST_F(ExampleSevenParsing, TheSystemVerilogSideParses) {
  ASSERT_NE(r_.cu, nullptr);
  EXPECT_FALSE(r_.has_errors);
  ASSERT_EQ(r_.cu->modules.size(), 1u);
}

TEST_F(ExampleSevenParsing, TheFormalsAreAnInputAndAnOutputOpenArray) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f1 =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(f1, nullptr);
  ASSERT_EQ(f1->func_args.size(), 2u);
  EXPECT_EQ(f1->func_args[0].name, "i");
  EXPECT_EQ(f1->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(f1->func_args[0].data_type.type_name, "MyType");
  ASSERT_EQ(f1->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(f1->func_args[0].unpacked_dims[0], nullptr);
  EXPECT_EQ(f1->func_args[1].name, "o");
  EXPECT_EQ(f1->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(f1->func_args[1].data_type.type_name, "MyType");
  ASSERT_EQ(f1->func_args[1].unpacked_dims.size(), 1u);
  EXPECT_EQ(f1->func_args[1].unpacked_dims[0], nullptr);
}

}  // namespace
