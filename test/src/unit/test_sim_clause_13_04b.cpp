// §13.4: Functions

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include "simulation/eval.h"
#include "simulation/eval_array.h"
#include "simulation/sim_context.h"

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

static Expr* ParseExprFrom(const std::string& src, AggFixture& f) {
  std::string code = "module t; initial x = " + src + "; endmodule";
  auto fid = f.mgr.AddFile("<test>", code);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  auto* item = cu->modules[0]->items[0];
  return item->body->rhs;
}

// =============================================================================
// §7.2 Struct type metadata — StructTypeInfo registration
// =============================================================================
static void VerifyStructField(const StructFieldInfo& field,
                              const char* expected_name,
                              uint32_t expected_offset, uint32_t expected_width,
                              size_t index) {
  EXPECT_EQ(field.name, expected_name) << "field " << index;
  EXPECT_EQ(field.bit_offset, expected_offset) << "field " << index;
  EXPECT_EQ(field.width, expected_width) << "field " << index;
}

namespace {

TEST(TaskCall, SetupReturnsNullForFunction) {
  AggFixture f;
  // Create a function (not task) declaration.
  auto* func = f.arena.Create<ModuleItem>();
  func->kind = ModuleItemKind::kFunctionDecl;
  func->name = "my_func";
  f.ctx.RegisterFunction("my_func", func);

  auto* call = f.arena.Create<Expr>();
  call->kind = ExprKind::kCall;
  call->callee = "my_func";

  auto* result = SetupTaskCall(call, f.ctx, f.arena);
  EXPECT_EQ(result, nullptr);
}

}  // namespace
