// §13.4.1: Return values and void functions

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- data_type_or_void ---
// data_type | void
TEST(ParserA221, DataTypeOrVoidReturn) {
  // void as function return type (data_type_or_void)
  auto r = Parse(
      "module m;\n"
      "  function void do_nothing; endfunction\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

};

// =============================================================================
// A.2.6 Function declarations
// =============================================================================
// ---------------------------------------------------------------------------
// function_data_type_or_implicit ::=
//   data_type_or_void | implicit_data_type
// ---------------------------------------------------------------------------
TEST(ParserA26, FuncReturnTypeExplicitInt) {
  auto r = Parse(
      "module m;\n  function int foo(); return 0; endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->name, "foo");
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kInt);
}

TEST(ParserA26, FuncReturnTypeVoid) {
  auto r = Parse("module m;\n  function void bar(); endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kVoid);
}

TEST(ParserA26, FuncReturnTypeLogicPacked) {
  auto r = Parse(
      "module m;\n  function logic [3:0] baz();\n"
      "    return 4'b0;\n  endfunction\nendmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->return_type.packed_dim_left, nullptr);
  EXPECT_NE(item->return_type.packed_dim_right, nullptr);
}

}  // namespace
