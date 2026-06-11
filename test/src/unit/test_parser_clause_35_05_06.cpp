#include "fixture_parser.h"
#include "fixture_program.h"

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

// §35.5.6: the C-compatible scalar types, string, and chandle are among the
// permitted formal-argument types, so an import declaring them parses cleanly.
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

// §35.5.6: an event is not one of the permitted formal-argument types for a
// DPI subroutine. The type parses as a data type but the clause restriction
// rejects it as a formal argument.
TEST_F(DpiParseTest, DpiImportEventArgRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void notify(input event ev);\n"
      "endmodule\n");
  EXPECT_TRUE(diag_.HasErrors());
}

// §35.5.6: the remaining C-compatible scalar and integral types named by the
// clause (byte, shortint, longint, integer, time, shortreal) are also part of
// the permitted set, so a DPI import using them parses without error.
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

// §35.5.6: user-defined types built from the permitted set (here a typedef of
// a permitted scalar) are themselves permitted as formal arguments. The named
// type is accepted, not rejected, by the permitted-type restriction.
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

// §35.5.6: the permitted-type restriction applies to every formal argument, so
// a non-permitted type is rejected even when it follows permitted arguments in
// the same import declaration.
TEST_F(DpiParseTest, DpiImportNonPermittedArgAmongPermittedRejected) {
  Parse(
      "module m;\n"
      "  import \"DPI-C\" function void mixed(\n"
      "    input int ok,\n"
      "    input event bad\n"
      "  );\n"
      "endmodule\n");
  EXPECT_TRUE(diag_.HasErrors());
}

}
