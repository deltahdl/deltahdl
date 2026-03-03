// Non-LRM tests

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

static ModuleItem* FirstItem(ParseResult& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

namespace {

// =========================================================================
// §6.6.8: Chandle data type
// =========================================================================
TEST(ParserSection6, ChandleInClass) {
  // §6.6.8: chandle used in a class for DPI handle.
  auto r = ParseWithPreprocessor(
      "class Wrapper;\n"
      "  chandle ptr;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_GE(r.cu->classes[0]->members.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members[0]->data_type.kind,
            DataTypeKind::kChandle);
}

TEST(ParserSection6, ChandleMultipleDecls) {
  // chandle with multiple variables in a module.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  chandle h1, h2;\n"
              "endmodule\n"));
}

// =========================================================================
// §6.9: Vector declarations — signed vectors
// =========================================================================
TEST(ParserSection6, VectorUnsignedExplicit) {
  // §6.9: Explicit unsigned qualifier on a vector.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  logic unsigned [7:0] uv;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kLogic);
  EXPECT_FALSE(item->data_type.is_signed);
}

TEST(ParserSection6, VectorSignedBitType) {
  // §6.9: bit type with signed qualifier.
  auto r = ParseWithPreprocessor(
      "module t;\n"
      "  bit signed [15:0] sb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kBit);
  EXPECT_TRUE(item->data_type.is_signed);
}

}  // namespace
