#include <gtest/gtest.h>

#include "fixture_program.h"
#include "helpers_reported_error.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST_F(DpiParseTest, DpiImportBitLogicArgs) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void send_bits(\n"
      "    input bit [31:0] data,\n"
      "    input logic [7:0] ctrl\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[0]->func_args.size(), 2u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(items[0]->func_args[0].name, "data");
  EXPECT_EQ(items[0]->func_args[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[0]->func_args[1].name, "ctrl");
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportPermittedScalarArgsAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function int compute(\n"
      "    input int count,\n"
      "    input real weight,\n"
      "    input string label,\n"
      "    input chandle handle\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[0]->func_args.size(), 4u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(items[0]->func_args[1].data_type.kind, DataTypeKind::kReal);
  EXPECT_EQ(items[0]->func_args[2].data_type.kind, DataTypeKind::kString);
  EXPECT_EQ(items[0]->func_args[3].data_type.kind, DataTypeKind::kChandle);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportEventArgRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void notify(input event ev);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "type of formal argument 'ev' is not permitted for "
                            "a DPI imported subroutine",
                            2, "35.5.6"));
}

TEST_F(DpiParseTest, DpiImportAdditionalScalarArgsAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void take(\n"
      "    input byte b,\n"
      "    input shortint si,\n"
      "    input longint li,\n"
      "    input integer ii,\n"
      "    input time t,\n"
      "    input shortreal sr\n"
      "  );\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 6u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kByte);
  EXPECT_EQ(items[0]->func_args[1].data_type.kind, DataTypeKind::kShortint);
  EXPECT_EQ(items[0]->func_args[2].data_type.kind, DataTypeKind::kLongint);
  EXPECT_EQ(items[0]->func_args[3].data_type.kind, DataTypeKind::kInteger);
  EXPECT_EQ(items[0]->func_args[4].data_type.kind, DataTypeKind::kTime);
  EXPECT_EQ(items[0]->func_args[5].data_type.kind, DataTypeKind::kShortreal);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportNamedTypeArgAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  typedef int my_int_t;\n"
      "  import \"DPI-C\" function void take(input my_int_t value);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kDpiImport);
  ASSERT_EQ(items[1]->func_args.size(), 1u);
  EXPECT_EQ(items[1]->func_args[0].data_type.kind, DataTypeKind::kNamed);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportNonPermittedArgAmongPermittedRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void mixed(\n"
      "    input int ok,\n"
      "    input event bad\n"
      "  );\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "type of formal argument 'bad' is not permitted "
                            "for a DPI imported subroutine",
                            2, "35.5.6"));
}

TEST_F(DpiParseTest, DpiImportScalarBitLogicArgsAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input bit b, input logic l);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 2u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(items[0]->func_args[0].data_type.packed_dim_left, nullptr);
  EXPECT_EQ(items[0]->func_args[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(items[0]->func_args[1].data_type.packed_dim_left, nullptr);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportPackedStructArgAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(\n"
      "    input struct packed { bit a; logic b; } s);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kStruct);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportPackedUnionArgAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(\n"
      "    input union packed { bit [7:0] a; logic [7:0] b; } u);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kUnion);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportUnpackedUnionArgRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(\n"
      "    input union { bit [7:0] a; logic [7:0] b; } u);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "unpacked union formal argument 'u' is not "
                            "permitted for a DPI imported subroutine",
                            2, "35.5.6"));
}

TEST_F(DpiParseTest, DpiImportEnumArgAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(input enum { A, B } e);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kEnum);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportStructWithEventMemberRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(\n"
      "    input struct { event ev; int i; } s);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "type of formal argument 's' is not permitted for "
                            "a DPI imported subroutine",
                            2, "35.5.6"));
}

TEST_F(DpiParseTest, DpiImportStructWithPermittedMembersAccepted) {
  auto* unit = Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(\n"
      "    input struct { int i; real r; string s; } arg);\n"
      "endmodule\n");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_EQ(items[0]->func_args.size(), 1u);
  EXPECT_EQ(items[0]->func_args[0].data_type.kind, DataTypeKind::kStruct);
  EXPECT_FALSE(diag_.HasErrors());
}

TEST_F(DpiParseTest, DpiImportNestedStructWithEventMemberRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void f(\n"
      "    input struct { struct { event ev; } inner; } s);\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(diag_.Diagnostics(),
                            "type of formal argument 's' is not permitted for "
                            "a DPI imported subroutine",
                            2, "35.5.6"));
}

}  // namespace
