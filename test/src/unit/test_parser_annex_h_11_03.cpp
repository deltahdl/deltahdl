#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

// §H.11.3, the SystemVerilog side of Example 5: a typedef A of bit [2:0], a
// packed struct S of three bits, a packed union U of an A and an S, one
// variable of each, an import f8 taking one of each as input, and an initial
// block setting the struct's members, the array and the union's array
// member before calling f8 with the three.
class ExampleFiveParsing : public ::testing::Test {
 protected:
  ParseResult r_ = Parse(
      "module m;\n"
      "  typedef bit [2:0] A;\n"
      "  typedef struct packed { bit a; bit b; bit c; } S;\n"
      "  typedef union packed { A a; S s; } U;\n"
      "  S s;\n"
      "  U u;\n"
      "  A a;\n"
      "  import \"DPI-C\" function void f8(input A fa, input S fs, input U "
      "fu);\n"
      "  initial begin\n"
      "    s.a = 1'b1;\n"
      "    s.b = 1'b0;\n"
      "    s.c = 1'b0;\n"
      "    a = 3'b100;\n"
      "    u.a = 3'b100;\n"
      "    f8(a, s, u);\n"
      "  end\n"
      "endmodule\n");
};

TEST_F(ExampleFiveParsing, TheSystemVerilogSideParses) {
  ASSERT_NE(r_.cu, nullptr);
  EXPECT_FALSE(r_.has_errors);
  ASSERT_EQ(r_.cu->modules.size(), 1u);
}

// The three typedefs: the packed array A, the packed struct S of three bit
// members and the packed union U of an A and an S.
TEST_F(ExampleFiveParsing, ThePackedArrayStructAndUnionAreDeclared) {
  ASSERT_NE(r_.cu, nullptr);
  const std::vector<ModuleItem*>& items = r_.cu->modules[0]->items;
  std::vector<const ModuleItem*> typedefs;
  for (const ModuleItem* item : items) {
    if (item->kind == ModuleItemKind::kTypedef) typedefs.push_back(item);
  }
  ASSERT_EQ(typedefs.size(), 3u);
  EXPECT_EQ(typedefs[0]->name, "A");
  EXPECT_EQ(typedefs[0]->typedef_type.kind, DataTypeKind::kBit);
  EXPECT_NE(typedefs[0]->typedef_type.packed_dim_left, nullptr);
  EXPECT_EQ(typedefs[1]->name, "S");
  EXPECT_EQ(typedefs[1]->typedef_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(typedefs[1]->typedef_type.is_packed);
  EXPECT_EQ(typedefs[1]->typedef_type.struct_members.size(), 3u);
  EXPECT_EQ(typedefs[2]->name, "U");
  EXPECT_EQ(typedefs[2]->typedef_type.kind, DataTypeKind::kUnion);
  EXPECT_TRUE(typedefs[2]->typedef_type.is_packed);
  EXPECT_EQ(typedefs[2]->typedef_type.struct_members.size(), 2u);
}

// The import f8 takes the three as inputs, each under its type's name.
TEST_F(ExampleFiveParsing, TheImportTakesOneOfEachType) {
  ASSERT_NE(r_.cu, nullptr);
  const ModuleItem* f8 =
      FindItemByKind(r_.cu->modules[0]->items, ModuleItemKind::kDpiImport);
  ASSERT_NE(f8, nullptr);
  EXPECT_EQ(f8->name, "f8");
  ASSERT_EQ(f8->func_args.size(), 3u);
  EXPECT_EQ(f8->func_args[0].name, "fa");
  EXPECT_EQ(f8->func_args[0].data_type.type_name, "A");
  EXPECT_EQ(f8->func_args[1].name, "fs");
  EXPECT_EQ(f8->func_args[1].data_type.type_name, "S");
  EXPECT_EQ(f8->func_args[2].name, "fu");
  EXPECT_EQ(f8->func_args[2].data_type.type_name, "U");
  for (const FunctionArg& arg : f8->func_args) {
    EXPECT_EQ(arg.direction, Direction::kInput);
  }
}

}  // namespace
