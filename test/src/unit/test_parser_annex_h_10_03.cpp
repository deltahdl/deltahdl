#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

class ExampleThreeParsing : public ::testing::Test {
 protected:
  ParseResult r_ = Parse(
      "module m;\n"
      "  typedef struct {int a; bit [6:1][1:8] b [65:2]; int c;} triple;\n"
      "  import \"DPI-C\" function void f1(input triple t);\n"
      "  export \"DPI-C\" function exported_sv_func;\n"
      "  function void exported_sv_func(input int i, output logic [63:0] o);\n"
      "    begin end\n"
      "  endfunction\n"
      "endmodule\n");
};

TEST_F(ExampleThreeParsing, TheSystemVerilogSideParses) {
  ASSERT_NE(r_.cu, nullptr);
  EXPECT_FALSE(r_.has_errors);
  ASSERT_EQ(r_.cu->modules.size(), 1u);
}

TEST_F(ExampleThreeParsing, TheTripleMixesIntsWithAPackedUnpackedBitArray) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* triple =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kTypedef);
  ASSERT_NE(triple, nullptr);
  EXPECT_EQ(triple->name, "triple");
  const std::vector<StructMember>& members =
      triple->typedef_type.struct_members;
  ASSERT_EQ(members.size(), 3u);
  EXPECT_EQ(members[0].name, "a");
  EXPECT_EQ(members[0].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(members[1].name, "b");
  EXPECT_EQ(members[1].type_kind, DataTypeKind::kBit);
  EXPECT_NE(members[1].packed_dim_left, nullptr);
  EXPECT_EQ(members[1].extra_packed_dims.size(), 1u);
  EXPECT_EQ(members[1].unpacked_dims.size(), 1u);
  EXPECT_EQ(members[2].name, "c");
  EXPECT_EQ(members[2].type_kind, DataTypeKind::kInt);
}

TEST_F(ExampleThreeParsing, TheImportTakesATripleAndTheExportALogicOutput) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f1 =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(f1, nullptr);
  ASSERT_EQ(f1->func_args.size(), 1u);
  EXPECT_EQ(f1->func_args[0].name, "t");
  EXPECT_EQ(f1->func_args[0].data_type.type_name, "triple");
  EXPECT_EQ(f1->func_args[0].direction, Direction::kInput);
  const ModuleItem* func =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kFunctionDecl);
  ASSERT_NE(func, nullptr);
  EXPECT_EQ(func->name, "exported_sv_func");
  ASSERT_EQ(func->func_args.size(), 2u);
  EXPECT_EQ(func->func_args[1].name, "o");
  EXPECT_EQ(func->func_args[1].direction, Direction::kOutput);
  EXPECT_EQ(func->func_args[1].data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(func->func_args[1].data_type.packed_dim_left, nullptr);
}

}  // namespace
