#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §H.12.10, the SystemVerilog side of Example 8: an import f1 taking one
// 128-bit packed logic vector, its formal unnamed as a prototype allows,
// and an import f2 taking an open array of 128-bit packed logic vectors.
class ExampleEightParsing : public ::testing::Test {
 protected:
  ParseResult r_ = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f1(input logic [127:0]);\n"
      "  import \"DPI-C\" function void f2(input logic [127:0] i []);\n"
      "endmodule\n");

  const ModuleItem* Import(const char* name) const {
    for (const ModuleItem* item : r_.cu->modules[0]->items) {
      if (item->kind == ModuleItemKind::kDpiImport && item->name == name) {
        return item;
      }
    }
    return nullptr;
  }
};

TEST_F(ExampleEightParsing, TheSystemVerilogSideParses) {
  ASSERT_NE(r_.cu, nullptr);
  EXPECT_FALSE(r_.has_errors);
  ASSERT_EQ(r_.cu->modules.size(), 1u);
  EXPECT_NE(Import("f1"), nullptr);
  EXPECT_NE(Import("f2"), nullptr);
}

// f1's one formal is a packed logic vector with a range and no name.
TEST_F(ExampleEightParsing, F1TakesOneUnnamedPackedVector) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f1 = Import("f1");
  ASSERT_NE(f1, nullptr);
  ASSERT_EQ(f1->func_args.size(), 1u);
  EXPECT_TRUE(f1->func_args[0].name.empty());
  EXPECT_EQ(f1->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(f1->func_args[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(f1->func_args[0].data_type.packed_dim_left, nullptr);
  EXPECT_TRUE(f1->func_args[0].unpacked_dims.empty());
}

// f2's one formal is the same packed vector with one unsized unpacked
// dimension, the open array.
TEST_F(ExampleEightParsing, F2TakesAnOpenArrayOfPackedVectors) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f2 = Import("f2");
  ASSERT_NE(f2, nullptr);
  ASSERT_EQ(f2->func_args.size(), 1u);
  EXPECT_EQ(f2->func_args[0].name, "i");
  EXPECT_EQ(f2->func_args[0].data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(f2->func_args[0].data_type.packed_dim_left, nullptr);
  ASSERT_EQ(f2->func_args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(f2->func_args[0].unpacked_dims[0], nullptr);
}

}  // namespace
