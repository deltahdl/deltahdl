#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

class ExampleTwoParsing : public ::testing::Test {
 protected:
  ParseResult r_ = Parse(
      "module m;\n"
      "  typedef struct {int x; int y;} pair;\n"
      "  import \"DPI-C\" function void f1(input int i1, pair i2,\n"
      "                                  output logic [63:0] o3);\n"
      "  export \"DPI-C\" function exported_sv_func;\n"
      "  function void exported_sv_func(input int i, output int o [0:7]);\n"
      "    begin end\n"
      "  endfunction\n"
      "endmodule\n");
};

TEST_F(ExampleTwoParsing, TheSystemVerilogSideParses) {
  ASSERT_NE(r_.cu, nullptr);
  EXPECT_FALSE(r_.has_errors);
  ASSERT_EQ(r_.cu->modules.size(), 1u);
}

TEST_F(ExampleTwoParsing, TheImportTakesAnIntAPairAndAWideLogicOutput) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f1 =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(f1, nullptr);
  EXPECT_EQ(f1->name, "f1");
  EXPECT_EQ(f1->return_type.kind, DataTypeKind::kVoid);
  ASSERT_EQ(f1->func_args.size(), 3u);
  EXPECT_EQ(f1->func_args[0].name, "i1");
  EXPECT_EQ(f1->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(f1->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(f1->func_args[1].name, "i2");
  EXPECT_EQ(f1->func_args[1].data_type.type_name, "pair");
  EXPECT_EQ(f1->func_args[1].direction, Direction::kInput);
  EXPECT_EQ(f1->func_args[2].name, "o3");
  EXPECT_EQ(f1->func_args[2].data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(f1->func_args[2].direction, Direction::kOutput);
  EXPECT_NE(f1->func_args[2].data_type.packed_dim_left, nullptr);
  EXPECT_NE(f1->func_args[2].data_type.packed_dim_right, nullptr);
}

TEST_F(ExampleTwoParsing, TheExportedFunctionTakesAnUnpackedOutputArray) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* exp =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiExport);
  ASSERT_NE(exp, nullptr);
  EXPECT_EQ(exp->name, "exported_sv_func");
  EXPECT_FALSE(exp->dpi_is_task);
  const ModuleItem* func =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(func, nullptr);
  EXPECT_EQ(func->name, "exported_sv_func");
  ASSERT_EQ(func->func_args.size(), 2u);
  EXPECT_EQ(func->func_args[0].direction, Direction::kInput);
  EXPECT_EQ(func->func_args[0].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(func->func_args[1].name, "o");
  EXPECT_EQ(func->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(func->func_args[1].data_type.kind, DataTypeKind::kInt);
  EXPECT_EQ(func->func_args[1].unpacked_dims.size(), 1u);
}

}  // namespace
