// §7.2: Structures

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"
#include <gtest/gtest.h>
#include <string>

using namespace delta;

// =============================================================================
// Helper fixture
// =============================================================================
struct AggFixture {
  SourceManager mgr;
  Arena arena;
  Scheduler scheduler{arena};
  DiagEngine diag{mgr};
  SimContext ctx{scheduler, arena, diag};
};

// =============================================================================
// §7.2 Struct type metadata — StructTypeInfo registration
// =============================================================================
static void VerifyStructField(const StructFieldInfo &field,
                              const char *expected_name,
                              uint32_t expected_offset, uint32_t expected_width,
                              size_t index) {
  EXPECT_EQ(field.name, expected_name) << "field " << index;
  EXPECT_EQ(field.bit_offset, expected_offset) << "field " << index;
  EXPECT_EQ(field.width, expected_width) << "field " << index;
}

namespace {

TEST(StructType, RegisterAndFind_Metadata) {
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8}); // MSB field: bits [15:8]
  info.fields.push_back({"y", 0, 8}); // LSB field: bits [7:0]

  f.ctx.RegisterStructType("point_t", info);
  auto *found = f.ctx.FindStructType("point_t");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->type_name, "point_t");
  EXPECT_TRUE(found->is_packed);
  EXPECT_EQ(found->total_width, 16u);
  ASSERT_EQ(found->fields.size(), 2u);
}

TEST(StructType, RegisterAndFind_Fields) {
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "point_t";
  info.is_packed = true;
  info.total_width = 16;
  info.fields.push_back({"x", 8, 8});
  info.fields.push_back({"y", 0, 8});

  f.ctx.RegisterStructType("point_t", info);
  auto *found = f.ctx.FindStructType("point_t");
  ASSERT_NE(found, nullptr);
  ASSERT_EQ(found->fields.size(), 2u);

  VerifyStructField(found->fields[0], "x", 8, 8, 0);
  VerifyStructField(found->fields[1], "y", 0, 8, 1);
}

TEST(StructType, FindNonexistent) {
  AggFixture f;
  EXPECT_EQ(f.ctx.FindStructType("no_such_type"), nullptr);
}

TEST(StructType, SetVariableStructType) {
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "color_t";
  info.is_packed = true;
  info.total_width = 24;
  info.fields.push_back({"r", 16, 8});
  info.fields.push_back({"g", 8, 8});
  info.fields.push_back({"b", 0, 8});
  f.ctx.RegisterStructType("color_t", info);

  f.ctx.CreateVariable("pixel", 24);
  f.ctx.SetVariableStructType("pixel", "color_t");

  auto *type = f.ctx.GetVariableStructType("pixel");
  ASSERT_NE(type, nullptr);
  EXPECT_EQ(type->type_name, "color_t");
  EXPECT_EQ(type->fields.size(), 3u);
}

TEST(StructType, GetVariableStructTypeUnknown) {
  AggFixture f;
  EXPECT_EQ(f.ctx.GetVariableStructType("nonexistent"), nullptr);
}

TEST(StructType, FieldTypeKindPreserved) {
  AggFixture f;
  StructTypeInfo info;
  info.type_name = "typed_s";
  info.is_packed = true;
  info.total_width = 40;
  info.fields.push_back({"a", 8, 32, DataTypeKind::kInt});
  info.fields.push_back({"b", 0, 8, DataTypeKind::kByte});
  f.ctx.RegisterStructType("typed_s", info);
  auto *found = f.ctx.FindStructType("typed_s");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->fields[0].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(found->fields[1].type_kind, DataTypeKind::kByte);
}

} // namespace
