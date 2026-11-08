#include <gtest/gtest.h>

#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST_F(DpiParseTest, DpiImportFormalLeavesPackedRangeUnspecified) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [] a);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  const DataType& type = items[0]->func_args[0].data_type;
  EXPECT_TRUE(type.has_unsized_packed_dim);
  EXPECT_EQ(type.packed_dim_left, nullptr);
  EXPECT_TRUE(type.extra_packed_dims.empty());
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportFormalOpensPackedPartBesideSizedUnpackedPart) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(logic [] arrayNx3 [3:1]);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& args = unit->modules[0]->items[0]->func_args;
  ASSERT_EQ(args.size(), 1u);
  EXPECT_TRUE(args[0].data_type.has_unsized_packed_dim);
  ASSERT_EQ(args[0].unpacked_dims.size(), 1u);
  EXPECT_NE(args[0].unpacked_dims[0], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportFormalOpensBothPackedAndUnpackedParts) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(bit [] arrayNxN []);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& args = unit->modules[0]->items[0]->func_args;
  ASSERT_EQ(args.size(), 1u);
  EXPECT_TRUE(args[0].data_type.has_unsized_packed_dim);
  ASSERT_EQ(args[0].unpacked_dims.size(), 1u);
  EXPECT_EQ(args[0].unpacked_dims[0], nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportFormalRejectsSizedPackedDimBeforeUnspecifiedOne) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [7:0] [] a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "formal argument 'a' gives a packed dimension no "
                            "range alongside a sized one",
                            2, "35.5.6.1"));
}

TEST_F(DpiParseTest, DpiImportFormalRejectsSizedPackedDimAfterUnspecifiedOne) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [] [7:0] a);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "formal argument 'a' gives a packed dimension no "
                            "range alongside a sized one",
                            2, "35.5.6.1"));
}

TEST_F(DpiParseTest, DpiImportFormalWithSizedPackedDimIsNotOpen) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit [7:0] a);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& args = unit->modules[0]->items[0]->func_args;
  ASSERT_EQ(args.size(), 1u);
  EXPECT_FALSE(args[0].data_type.has_unsized_packed_dim);
  EXPECT_NE(args[0].data_type.packed_dim_left, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, UnspecifiedPackedRangeIsRejectedOutsideAnImport) {
  Parse(
      "module m;\n"
      "  bit [] a;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(diag_.Diagnostics(), "expected expression", 2, "11.2"));
}

TEST_F(DpiParseTest, UnspecifiedPackedRangeIsRejectedOnAnImportResult) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function bit [] f(input int a);\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(diag_.Diagnostics(), "expected expression", 2, "11.2"));
}

}  // namespace
