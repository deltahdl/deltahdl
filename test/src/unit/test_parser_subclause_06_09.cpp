

#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// Collects every typedef in the first module into `typedefs` and returns the
// single variable declaration item (or nullptr if none was found).
static const ModuleItem* CollectTypedefsAndVar(ParseResult& r,
                                               TypedefMap& typedefs) {
  auto& items = r.cu->modules[0]->items;
  const ModuleItem* var = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kTypedef) {
      // A typedef's aliased type is parsed into typedef_type (data_type is
      // left empty for typedef items), matching how the elaborator builds its
      // TypedefMap. Keying off data_type made every typedef look scalar.
      typedefs.emplace(it->name, it->typedef_type);
    } else if (it->kind == ModuleItemKind::kVarDecl) {
      var = it;
    }
  }
  return var;
}

TEST(ScalarAndVectorDeclaration, ScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  logic a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, RegScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  reg a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, BitScalarNoRange) {
  auto r = Parse(
      "module t;\n"
      "  bit a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, RangeProducesDimensions) {
  auto r = Parse(
      "module t;\n"
      "  logic [3:0] a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, RegRangeProducesDimensions) {
  auto r = Parse(
      "module t;\n"
      "  reg [3:0] r;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReg);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, BitRangeProducesDimensions) {
  auto r = Parse(
      "module t;\n"
      "  bit [3:0] b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, ImplicitLogicScalarHasNoPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  var v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, ImplicitLogicVectorHasPackedDims) {
  auto r = Parse(
      "module t;\n"
      "  var [7:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ScalarAndVectorDeclaration, VectorIsRecognisedByIsVector) {
  auto r = Parse("module t; logic [7:0] v; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(IsVector(item->data_type));
}

TEST(ScalarAndVectorDeclaration, ScalarIsNotRecognisedByIsVector) {
  auto r = Parse("module t; logic v; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_FALSE(IsVector(item->data_type));
}

TEST(ScalarAndVectorDeclaration, RegVectorIsRecognisedByIsVector) {
  auto r = Parse("module t; reg [3:0] r; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(IsVector(item->data_type));
}

TEST(ScalarAndVectorDeclaration, BitVectorIsRecognisedByIsVector) {
  auto r = Parse("module t; bit [3:0] b; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(IsVector(item->data_type));
}

TEST(ScalarAndVectorDeclaration, ImplicitLogicVectorIsRecognisedByIsVector) {
  auto r = Parse("module t; var [7:0] v; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(IsVector(item->data_type));
}

TEST(ScalarAndVectorDeclaration, MatchingUserDefinedTypeVectorIsVector) {
  auto r = Parse(
      "module t;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  byte_t v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  TypedefMap typedefs;
  const ModuleItem* var = CollectTypedefsAndVar(r, typedefs);
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->data_type.kind, DataTypeKind::kNamed);
  EXPECT_FALSE(IsVector(var->data_type));
  EXPECT_TRUE(IsVector(var->data_type, typedefs));
}

TEST(ScalarAndVectorDeclaration, BitTypedefVectorIsVector) {
  auto r = Parse(
      "module t;\n"
      "  typedef bit [3:0] nibble_t;\n"
      "  nibble_t v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  TypedefMap typedefs;
  const ModuleItem* var = CollectTypedefsAndVar(r, typedefs);
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(IsVector(var->data_type, typedefs));
}

TEST(ScalarAndVectorDeclaration, RegTypedefVectorIsVector) {
  auto r = Parse(
      "module t;\n"
      "  typedef reg [3:0] nibble_t;\n"
      "  nibble_t v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  TypedefMap typedefs;
  const ModuleItem* var = CollectTypedefsAndVar(r, typedefs);
  ASSERT_NE(var, nullptr);
  EXPECT_TRUE(IsVector(var->data_type, typedefs));
}

TEST(ScalarAndVectorDeclaration, MatchingUserDefinedTypeScalarIsNotVector) {
  auto r = Parse(
      "module t;\n"
      "  typedef logic my_logic_t;\n"
      "  my_logic_t v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  TypedefMap typedefs;
  const ModuleItem* var = CollectTypedefsAndVar(r, typedefs);
  ASSERT_NE(var, nullptr);
  EXPECT_FALSE(IsVector(var->data_type, typedefs));
}

TEST(ScalarAndVectorDeclaration, MultidimensionalPackedArrayIsNotAVector) {
  auto r = Parse("module t; logic [3:0][7:0] m; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_FALSE(item->data_type.extra_packed_dims.empty());
  EXPECT_FALSE(IsVector(item->data_type));
}

}  // namespace
