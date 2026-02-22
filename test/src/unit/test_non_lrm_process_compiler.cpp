// §non-lrm:process_compiler

#include <gtest/gtest.h>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "parser/ast.h"
#include "simulation/compiled_sim.h"
#include "simulation/sim_context.h"

using namespace delta;

namespace {

TEST(CompiledSim, NullBodyNotCompilable) {
  EXPECT_FALSE(ProcessCompiler::IsCompilable(nullptr));
}

TEST(CompiledSim, CompileReturnsValidForCombinational) {
  Arena arena;
  auto* assign = arena.Create<Stmt>();
  assign->kind = StmtKind::kBlockingAssign;

  auto* block = arena.Create<Stmt>();
  block->kind = StmtKind::kBlock;
  block->stmts.push_back(assign);

  auto compiled = ProcessCompiler::Compile(42, block);
  EXPECT_TRUE(compiled.IsValid());
  EXPECT_EQ(compiled.Id(), 42u);
}

}  // namespace
