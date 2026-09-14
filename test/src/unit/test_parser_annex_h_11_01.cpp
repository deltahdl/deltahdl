#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// §H.11.1, the SystemVerilog side of Example 4: a parameter W of 33, an int,
// a bit [29:0] and a bit [W-1:0], and an import f7 handling 2-state packed
// arguments two ways -- two int unsigned formals the int and the 30-bit
// vector are associated with, and a [W-1:0] formal the 33-bit vector is
// passed to as a canonical vector -- called with the three from an initial
// block.
class ExampleFourParsing : public ::testing::Test {
 protected:
  ParseResult r_ = Parse(
      "module m;\n"
      "  parameter W = 33;\n"
      "  int abv1;\n"
      "  bit [29:0] abv2;\n"
      "  bit [W-1:0] abv3;\n"
      "  import \"DPI-C\" function void f7 (input int unsigned fbv1,\n"
      "                                   input int unsigned fbv2,\n"
      "                                   input [W-1:0] fbv3);\n"
      "  initial\n"
      "    f7(abv1, abv2, abv3);\n"
      "endmodule\n");
};

TEST_F(ExampleFourParsing, TheSystemVerilogSideParses) {
  ASSERT_NE(r_.cu, nullptr);
  EXPECT_FALSE(r_.has_errors);
  ASSERT_EQ(r_.cu->modules.size(), 1u);
}

// The import f7: two int unsigned inputs and a third input whose packed
// range is written in terms of the parameter.
TEST_F(ExampleFourParsing, TheImportTakesTwoUnsignedIntsAndAPackedVector) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f7 =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(f7, nullptr);
  EXPECT_EQ(f7->name, "f7");
  ASSERT_EQ(f7->func_args.size(), 3u);
  EXPECT_EQ(f7->func_args[0].name, "fbv1");
  EXPECT_EQ(f7->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(f7->func_args[0].data_type.is_signed);
  EXPECT_EQ(f7->func_args[1].name, "fbv2");
  EXPECT_EQ(f7->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_FALSE(f7->func_args[1].data_type.is_signed);
  EXPECT_EQ(f7->func_args[2].name, "fbv3");
  EXPECT_EQ(f7->func_args[2].direction, Direction::kInput);
  EXPECT_NE(f7->func_args[2].data_type.packed_dim_left, nullptr);
  EXPECT_NE(f7->func_args[2].data_type.packed_dim_right, nullptr);
}

}  // namespace
