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

namespace {

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
