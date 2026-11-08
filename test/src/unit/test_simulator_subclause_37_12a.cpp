#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_model_helpers2.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

TEST(ScopeModel, BlockItemDeclTypeClassification) {
  EXPECT_TRUE(VpiIsBlockItemDeclType(vpiLogicVar));
  EXPECT_TRUE(VpiIsBlockItemDeclType(vpiIntVar));
  EXPECT_TRUE(VpiIsBlockItemDeclType(vpiStructVar));
  EXPECT_TRUE(VpiIsBlockItemDeclType(vpiTypedef));
  EXPECT_TRUE(VpiIsBlockItemDeclType(vpiParameter));

  EXPECT_FALSE(VpiIsBlockItemDeclType(vpiAssignment));
  EXPECT_FALSE(VpiIsBlockItemDeclType(vpiNamedBegin));
  EXPECT_FALSE(VpiIsBlockItemDeclType(vpiModule));
}

TEST(ScopeModel, UnnamedBlockIsScopeOnlyWithDirectDeclaration) {
  VpiObject var_decl;
  var_decl.type = vpiLogicVar;
  VpiObject stmt;
  stmt.type = vpiAssignment;

  VpiObject declaring_begin;
  declaring_begin.type = vpiBegin;
  declaring_begin.children.push_back(&var_decl);
  EXPECT_TRUE(VpiBlockScopeIsScope(&declaring_begin));

  VpiObject stmt_only_begin;
  stmt_only_begin.type = vpiBegin;
  stmt_only_begin.children.push_back(&stmt);
  EXPECT_FALSE(VpiBlockScopeIsScope(&stmt_only_begin));

  VpiObject declaring_fork;
  declaring_fork.type = vpiFork;
  declaring_fork.children.push_back(&var_decl);
  EXPECT_TRUE(VpiBlockScopeIsScope(&declaring_fork));

  VpiObject stmt_only_fork;
  stmt_only_fork.type = vpiFork;
  stmt_only_fork.children.push_back(&stmt);
  EXPECT_FALSE(VpiBlockScopeIsScope(&stmt_only_fork));
}

TEST(ScopeModel, NamedBlockIsAlwaysScope) {
  VpiObject stmt;
  stmt.type = vpiAssignment;

  VpiObject named_begin;
  named_begin.type = vpiNamedBegin;
  named_begin.children.push_back(&stmt);
  EXPECT_TRUE(VpiBlockScopeIsScope(&named_begin));

  VpiObject named_fork;
  named_fork.type = vpiNamedFork;
  EXPECT_TRUE(VpiBlockScopeIsScope(&named_fork));
}

TEST(ScopeModel, BlockScopeIsScopeRejectsNullEmptyAndNonBlockKinds) {
  EXPECT_FALSE(VpiBlockScopeIsScope(nullptr));

  VpiObject empty_begin;
  empty_begin.type = vpiBegin;
  EXPECT_FALSE(VpiBlockScopeIsScope(&empty_begin));

  VpiObject empty_fork;
  empty_fork.type = vpiFork;
  EXPECT_FALSE(VpiBlockScopeIsScope(&empty_fork));

  VpiObject module;
  module.type = vpiModule;
  EXPECT_FALSE(VpiBlockScopeIsScope(&module));
}

TEST(ScopePublic, ForStatementIsScopeIffLocalVarDecls) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject local_for;
  local_for.type = vpiFor;
  local_for.local_var_decls = true;
  EXPECT_EQ(ctx.Get(vpiLocalVarDecls, &local_for), 1);
  EXPECT_TRUE(VpiBlockScopeIsScope(&local_for));

  VpiObject shared_for;
  shared_for.type = vpiFor;
  shared_for.local_var_decls = false;
  EXPECT_EQ(ctx.Get(vpiLocalVarDecls, &shared_for), 0);
  EXPECT_FALSE(VpiBlockScopeIsScope(&shared_for));

  SetGlobalVpiContext(nullptr);
}

TEST(ScopePublic, LoopControlVariableScopeIsItsLoopStatement) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject foreach_var;
  foreach_var.type = vpiIntVar;
  VpiObject foreach_stmt;
  foreach_stmt.type = vpiForeachStmt;
  foreach_var.parent = &foreach_stmt;
  foreach_stmt.children.push_back(&foreach_var);
  EXPECT_EQ(ctx.Handle(vpiScope, &foreach_var), &foreach_stmt);

  VpiObject scoped_for_var;
  scoped_for_var.type = vpiIntVar;
  VpiObject scoped_for;
  scoped_for.type = vpiFor;
  scoped_for.local_var_decls = true;
  scoped_for_var.parent = &scoped_for;
  scoped_for.children.push_back(&scoped_for_var);
  EXPECT_EQ(ctx.Handle(vpiScope, &scoped_for_var), &scoped_for);

  VpiObject shared_for_var;
  shared_for_var.type = vpiIntVar;
  VpiObject shared_for;
  shared_for.type = vpiFor;
  shared_for.local_var_decls = false;
  shared_for_var.parent = &shared_for;
  shared_for.children.push_back(&shared_for_var);
  EXPECT_NE(ctx.Handle(vpiScope, &shared_for_var), &shared_for);

  VpiObject block_var;
  block_var.type = vpiIntVar;
  VpiObject block;
  block.type = vpiBegin;
  block_var.parent = &block;
  block.children.push_back(&block_var);
  EXPECT_EQ(ctx.Handle(vpiScope, &block_var), &block);

  SetGlobalVpiContext(nullptr);
}

TEST(ScopePublic, ImportIterationReturnsOnlyReferencedImports) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject imported_a;
  imported_a.type = vpiParameter;
  imported_a.imported = true;
  VpiObject imported_b;
  imported_b.type = vpiFunction;
  imported_b.imported = true;
  VpiObject local_decl;
  local_decl.type = vpiParameter;
  VpiObject visible_unreferenced;
  visible_unreferenced.type = vpiFunction;
  visible_unreferenced.imported = false;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children.push_back(&imported_a);
  scope.children.push_back(&local_decl);
  scope.children.push_back(&imported_b);
  scope.children.push_back(&visible_unreferenced);

  std::vector<VpiHandle> imports = Collect(ctx, ctx.Iterate(vpiImport, &scope));
  ASSERT_EQ(imports.size(), 2u);
  EXPECT_EQ(imports[0], &imported_a);
  EXPECT_EQ(imports[1], &imported_b);

  VpiObject bare;
  bare.type = vpiModule;
  bare.children.push_back(&local_decl);
  EXPECT_EQ(ctx.Iterate(vpiImport, &bare), nullptr);

  SetGlobalVpiContext(nullptr);
}

TEST(ScopeModel, TaskFuncTypeClassification) {
  EXPECT_TRUE(VpiIsTaskFuncType(vpiTask));
  EXPECT_TRUE(VpiIsTaskFuncType(vpiFunction));
  EXPECT_TRUE(VpiIsTaskFuncType(vpiTaskFunc));

  EXPECT_FALSE(VpiIsTaskFuncType(vpiBegin));
  EXPECT_FALSE(VpiIsTaskFuncType(vpiModule));
}

TEST(ScopePublic, TaskWithNoStatementsHasNullStmt) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject io_decl;
  io_decl.type = vpiIODecl;
  VpiObject local_var;
  local_var.type = vpiLogicVar;

  VpiObject task;
  task.type = vpiTask;
  task.children.push_back(&io_decl);
  task.children.push_back(&local_var);

  EXPECT_EQ(ctx.Handle(vpiStmt, &task), nullptr);

  SetGlobalVpiContext(nullptr);
}

TEST(ScopePublic, TaskWithMultipleStatementsReturnsUnnamedBegin) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject s0, s1, s2;
  s0.type = vpiAssignment;
  s1.type = vpiAssignment;
  s2.type = vpiAssignment;

  VpiObject grouping_begin;
  grouping_begin.type = vpiBegin;
  grouping_begin.children.push_back(&s0);
  grouping_begin.children.push_back(&s1);
  grouping_begin.children.push_back(&s2);

  VpiObject task;
  task.type = vpiTask;
  task.children.push_back(&grouping_begin);

  VpiHandle body = ctx.Handle(vpiStmt, &task);
  ASSERT_EQ(body, &grouping_begin);
  EXPECT_EQ(ctx.Get(vpiType, body), vpiBegin);
  EXPECT_EQ(grouping_begin.children.size(), 3u);

  SetGlobalVpiContext(nullptr);
}

TEST(ScopePublic, FunctionWithSingleStatementReturnsThatStatement) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject only_stmt;
  only_stmt.type = vpiAssignment;

  VpiObject func;
  func.type = vpiFunction;
  func.children.push_back(&only_stmt);

  EXPECT_EQ(ctx.Handle(vpiStmt, &func), &only_stmt);

  SetGlobalVpiContext(nullptr);
}

TEST(ScopePublic, TaskFuncStmtSkipsDeclarationsToReachBody) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject io_decl;
  io_decl.type = vpiIODecl;
  VpiObject local_var;
  local_var.type = vpiLogicVar;
  VpiObject body;
  body.type = vpiAssignment;

  VpiObject task_func;
  task_func.type = vpiTaskFunc;
  task_func.children.push_back(&io_decl);
  task_func.children.push_back(&local_var);
  task_func.children.push_back(&body);

  EXPECT_EQ(ctx.Handle(vpiStmt, &task_func), &body);

  SetGlobalVpiContext(nullptr);
}

TEST(ScopeModel, JoinTypeClassification) {
  EXPECT_TRUE(VpiIsJoinType(vpiJoin));
  EXPECT_TRUE(VpiIsJoinType(vpiJoinNone));
  EXPECT_TRUE(VpiIsJoinType(vpiJoinAny));

  EXPECT_FALSE(VpiIsJoinType(vpiJoinAny + 100));
  EXPECT_FALSE(VpiIsJoinType(-1));
}

TEST(ScopePublic, ForkReportsJoinType) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject fork;
  fork.type = vpiNamedFork;

  fork.join_type = vpiJoin;
  EXPECT_EQ(ctx.Get(vpiJoinType, &fork), vpiJoin);
  fork.join_type = vpiJoinNone;
  EXPECT_EQ(ctx.Get(vpiJoinType, &fork), vpiJoinNone);
  fork.join_type = vpiJoinAny;
  EXPECT_EQ(ctx.Get(vpiJoinType, &fork), vpiJoinAny);

  fork.join_type = vpiJoinAny + 100;
  EXPECT_EQ(ctx.Get(vpiJoinType, &fork), vpiJoin);

  SetGlobalVpiContext(nullptr);
}

TEST(ScopePublic, VirtualInterfaceIterationExpandsArrayElements) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject standalone_vif;
  standalone_vif.type = vpiVirtualInterfaceVar;

  VpiObject elem0, elem1;
  elem0.type = vpiVirtualInterfaceVar;
  elem1.type = vpiVirtualInterfaceVar;
  VpiObject vif_array;
  vif_array.type = vpiArrayVar;
  vif_array.children.push_back(&elem0);
  vif_array.children.push_back(&elem1);

  VpiObject scope;
  scope.type = vpiModule;
  scope.children.push_back(&standalone_vif);
  scope.children.push_back(&vif_array);

  std::vector<VpiHandle> vifs =
      Collect(ctx, ctx.Iterate(vpiVirtualInterfaceVar, &scope));
  ASSERT_EQ(vifs.size(), 3u);
  EXPECT_EQ(vifs[0], &standalone_vif);
  EXPECT_EQ(vifs[1], &elem0);
  EXPECT_EQ(vifs[2], &elem1);

  std::vector<VpiHandle> vars = Collect(ctx, ctx.Iterate(vpiVariables, &scope));
  ASSERT_EQ(vars.size(), 2u);
  EXPECT_EQ(vars[0], &standalone_vif);
  EXPECT_EQ(vars[1], &vif_array);

  SetGlobalVpiContext(nullptr);
}

TEST(ScopePublic, VirtualInterfaceIterationUnsupportedInClassDefn) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject class_vif;
  class_vif.type = vpiVirtualInterfaceVar;

  VpiObject class_defn;
  class_defn.type = vpiClassDefn;
  class_defn.children.push_back(&class_vif);

  EXPECT_EQ(ctx.Iterate(vpiVirtualInterfaceVar, &class_defn), nullptr);

  SetGlobalVpiContext(nullptr);
}

class BlockScopesOfARun : public VpiDesignRun {
 protected:
  static std::string FullName(vpiHandle obj) {
    const char* full_name = vpi_get_str(vpiFullName, obj);
    return full_name == nullptr ? "" : full_name;
  }
};

TEST_F(BlockScopesOfARun, ANamedBeginIsAnObjectOfTheRun) {
  Run("module top; int x; initial begin : blk x = 1; end endmodule\n");
  vpiHandle blk = By("top.blk");
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(vpi_get(vpiType, blk), vpiNamedBegin);
  EXPECT_STREQ(vpi_get_str(vpiName, blk), "blk");
  EXPECT_EQ(FullName(blk), "top.blk");
}

TEST_F(BlockScopesOfARun, ANamedForkIsAnObjectOfTheRun) {
  Run("module top; initial fork : fk #1; join_any endmodule\n");
  vpiHandle fk = By("top.fk");
  ASSERT_NE(fk, nullptr);
  EXPECT_EQ(vpi_get(vpiType, fk), vpiNamedFork);
  EXPECT_EQ(FullName(fk), "top.fk");
}

TEST_F(BlockScopesOfARun, ANestedNamedBlockIsNamedUnderTheBlockAroundIt) {
  Run("module top; initial begin : outer begin : inner end end endmodule\n");
  vpiHandle inner = By("top.outer.inner");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inner), vpiNamedBegin);
  EXPECT_EQ(FullName(inner), "top.outer.inner");
  EXPECT_EQ(By("top.inner"), nullptr);
}

TEST_F(BlockScopesOfARun, ABlockInsideAnotherStatementIsAnObjectOfTheRun) {
  Run("module top; int x;\n"
      "  initial if (x == 0) begin : t end else begin : e end\n"
      "  initial case (x) 0: begin : c0 end default: begin : cd end endcase\n"
      "  initial for (int i = 0; i < 1; i++) begin : lp end\n"
      "endmodule\n");
  const std::vector<std::string> kNames{"top.t", "top.e", "top.c0", "top.cd",
                                        "top.lp"};
  for (const std::string& name : kNames) {
    vpiHandle blk = By(name);
    ASSERT_NE(blk, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, blk), vpiNamedBegin) << name;
  }
}

TEST_F(BlockScopesOfARun, ABlockOfASubmoduleIsNamedUnderItsInstance) {
  Run("module sub; initial begin : sb end endmodule\n"
      "module top; sub u(); endmodule\n");
  vpiHandle sb = By("top.u.sb");
  ASSERT_NE(sb, nullptr);
  EXPECT_EQ(FullName(sb), "top.u.sb");
}

TEST_F(BlockScopesOfARun, AForkReportsTheJoinKeywordThatClosedIt) {
  Run("module top;\n"
      "  initial fork : fj #1; join\n"
      "  initial fork : fa #1; join_any\n"
      "  initial fork : fn #1; join_none\n"
      "endmodule\n");
  ASSERT_NE(By("top.fj"), nullptr);
  EXPECT_EQ(vpi_get(vpiJoinType, By("top.fj")), vpiJoin);
  EXPECT_EQ(vpi_get(vpiJoinType, By("top.fa")), vpiJoinAny);
  EXPECT_EQ(vpi_get(vpiJoinType, By("top.fn")), vpiJoinNone);
}

TEST_F(BlockScopesOfARun, ANamedBlocksVariablesHangBeneathIt) {
  Run("module top; initial begin : blk\n"
      "  parameter int P = 1; int v; logic [3:0] w; int a [2];\n"
      "end endmodule\n");
  vpiHandle blk = By("top.blk");
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(NamesOf(vpiVariables, blk),
            (std::vector<std::string>{"a", "v", "w"}));
  vpiHandle v = By("top.blk.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiType, v), vpiIntVar);
  EXPECT_EQ(FullName(v), "top.blk.v");
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.w")), vpiLogicVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.a")), vpiRegArray);
}

TEST_F(BlockScopesOfARun, ABlocksNonIntegralVariablesHaveTheirOwnKinds) {
  Run("interface intf; endinterface\n"
      "module top; initial begin : blk\n"
      "  real r; realtime rt; shortreal sr; string s; chandle h;\n"
      "  event e; event ea [2]; enum {A, B} en; virtual intf vi;\n"
      "end endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.r")), vpiRealVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.rt")), vpiRealVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.sr")), vpiShortRealVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.s")), vpiStringVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.h")), vpiChandleVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.e")), vpiNamedEvent);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.ea")), vpiNamedEventArray);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.en")), vpiEnumVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.vi")), vpiVirtualInterfaceVar);
}

TEST_F(BlockScopesOfARun, ABlocksClassAndTypedefVariablesHaveTheirKinds) {
  Run("module top;\n"
      "  class C; endclass\n"
      "  typedef C c_t; typedef real r_t; typedef enum {X, Y} e_t;\n"
      "  initial begin : blk C obj; mailbox m; c_t t; r_t r; e_t en; end\n"
      "endmodule\n");
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.obj")), vpiClassVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.m")), vpiClassVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.t")), vpiClassVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.r")), vpiRealVar);
  EXPECT_EQ(vpi_get(vpiType, By("top.blk.en")), vpiEnumVar);
}

TEST_F(BlockScopesOfARun, AnUnnamedBlockThatDeclaresIsAScope) {
  Run("module top;\n"
      "  initial begin int v; v = 1; end\n"
      "  initial fork int f; join_none\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(KindsOf(vpiInternalScope, top),
            (std::vector<int>{vpiBegin, vpiFork}));
  vpiHandle it = vpi_iterate(vpiInternalScope, top);
  ASSERT_NE(it, nullptr);
  vpiHandle begin = vpi_scan(it);
  ASSERT_NE(begin, nullptr);
  EXPECT_EQ(NamesOf(vpiVariables, begin), (std::vector<std::string>{"v"}));
}

TEST_F(BlockScopesOfARun, AnUnnamedBlockThatDeclaresNothingIsNoScope) {
  Run("module top; initial begin\n"
      "  begin : BLK var logic v; v = 1'b1; end\n"
      "end endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(KindsOf(vpiInternalScope, top), (std::vector<int>{vpiNamedBegin}));
  EXPECT_NE(By("top.BLK"), nullptr);
}

TEST_F(BlockScopesOfARun, AnUnnamedBlockThatDeclaresNothingIsABegin) {
  Run("module top; int a, b; initial begin a = 1; b <= 2; end endmodule\n");
  vpiHandle it = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle begin = vpi_handle(vpiStmt, vpi_scan(it));
  ASSERT_NE(begin, nullptr);
  EXPECT_EQ(vpi_get(vpiType, begin), vpiBegin);
  EXPECT_EQ(KindsOf(vpiStmt, begin),
            (std::vector<int>{vpiAssignment, vpiAssignment}));
  vpiHandle stmts = vpi_iterate(vpiStmt, begin);
  ASSERT_NE(stmts, nullptr);
  vpiHandle first = vpi_scan(stmts);
  EXPECT_EQ(vpi_get(vpiBlocking, first), 1);
  EXPECT_EQ(vpi_get(vpiBlocking, vpi_scan(stmts)), 0);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, first)), VpiObjectOf(By("top")));
  EXPECT_EQ(KindsOf(vpiInternalScope, By("top")), std::vector<int>{});
}

TEST_F(BlockScopesOfARun, AnUnnamedForkThatDeclaresNothingIsAFork) {
  Run("module top; initial fork #1; #2; join_any endmodule\n");
  vpiHandle it = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle fork = vpi_handle(vpiStmt, vpi_scan(it));
  ASSERT_NE(fork, nullptr);
  EXPECT_EQ(vpi_get(vpiType, fork), vpiFork);
  EXPECT_EQ(vpi_get(vpiJoinType, fork), vpiJoinAny);
  EXPECT_EQ(KindsOf(vpiStmt, fork),
            (std::vector<int>{vpiDelayControl, vpiDelayControl}));
}

TEST_F(BlockScopesOfARun, ANamedBlockInsideAPlainBeginIsOneOfItsStatements) {
  Run("module top; initial begin\n"
      "  begin : BLK var logic v; v = 1'b1; end\n"
      "end endmodule\n");
  vpiHandle it = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(it, nullptr);
  vpiHandle begin = vpi_handle(vpiStmt, vpi_scan(it));
  ASSERT_NE(begin, nullptr);
  vpiHandle blk = By("top.BLK");
  ASSERT_NE(blk, nullptr);
  vpiHandle stmts = vpi_iterate(vpiStmt, begin);
  ASSERT_NE(stmts, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(stmts)), VpiObjectOf(blk));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, blk)), VpiObjectOf(By("top")));
  EXPECT_EQ(FullName(blk), "top.BLK");
}

TEST(ScopePublic, ABlocksStatementIterationReachesItsStatementsOnly) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  for (int kind : {vpiBegin, vpiNamedBegin, vpiFork, vpiNamedFork}) {
    VpiObject block;
    block.type = kind;
    VpiObject var;
    var.type = vpiIntVar;
    VpiObject assignment;
    assignment.type = vpiAssignment;
    VpiObject call;
    call.type = vpiTaskCall;
    block.children = {&var, &assignment, &call};
    EXPECT_EQ(Collect(ctx, ctx.Iterate(vpiStmt, &block)),
              (std::vector<VpiHandle>{&assignment, &call}))
        << kind;
  }
  SetGlobalVpiContext(nullptr);
}

TEST_F(BlockScopesOfARun, InternalScopesAreTheScopesAScopeHolds) {
  Run("module sub; endmodule\n"
      "module top; int x; sub u();\n"
      "  initial begin : blk begin : inner end end\n"
      "endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(NamesOf(vpiInternalScope, top),
            (std::vector<std::string>{"blk", "u"}));
  EXPECT_EQ(NamesOf(vpiInternalScope, By("top.blk")),
            (std::vector<std::string>{"inner"}));
}

TEST_F(BlockScopesOfARun, ABlockReachesTheScopeItStandsIn) {
  Run("module top; initial begin : outer begin : inner end end endmodule\n");
  vpiHandle outer = By("top.outer");
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, By("top.outer.inner"))),
            VpiObjectOf(outer));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, outer)), VpiObjectOf(By("top")));
}

TEST(ScopePublic, AStatementsScopeSkipsABlockThatIsNoScope) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject module;
  module.type = vpiModule;
  VpiObject plain_begin;
  plain_begin.type = vpiBegin;
  plain_begin.parent = &module;
  VpiObject assignment;
  assignment.type = vpiAssignment;
  assignment.parent = &plain_begin;
  plain_begin.children.push_back(&assignment);
  EXPECT_EQ(ctx.Handle(vpiScope, &assignment), &module);
  EXPECT_EQ(ctx.Handle(vpiScope, &module), nullptr);
  SetGlobalVpiContext(nullptr);
}

TEST(ScopePublic, AStatementInNoScopeReachesNone) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject assignment;
  assignment.type = vpiAssignment;
  EXPECT_EQ(ctx.Handle(vpiScope, &assignment), nullptr);
  SetGlobalVpiContext(nullptr);
}

TEST_F(BlockScopesOfARun, ALabelOnAStatementCreatesANamedBegin) {
  Run("module top; event e; initial trig: -> e; endmodule\n");
  vpiHandle trig = By("top.trig");
  ASSERT_NE(trig, nullptr);
  EXPECT_EQ(vpi_get(vpiType, trig), vpiNamedBegin);
  EXPECT_EQ(FullName(trig), "top.trig");
  EXPECT_EQ(KindsOf(vpiEventStmt, trig), std::vector<int>{vpiEventStmt});
  vpiHandle it = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, vpi_scan(it))), VpiObjectOf(trig));
}

TEST_F(BlockScopesOfARun, ALabelOnAPlainForLoopCreatesANamedBegin) {
  Run("module top; int j;\n"
      "  initial ln: for (j = 0; j < 1; j++) ;\n"
      "  initial le: for (; j < 2; j++) ;\n"
      "endmodule\n");
  for (const std::string& name : std::vector<std::string>{"top.ln", "top.le"}) {
    vpiHandle loop = By(name);
    ASSERT_NE(loop, nullptr) << name;
    EXPECT_EQ(vpi_get(vpiType, loop), vpiNamedBegin) << name;
  }
}

TEST_F(BlockScopesOfARun, AGeneratedBlocksVariableIsNamedUnderBothBlocks) {
  Run("module top;\n"
      "  if (1) begin : g initial begin : blk int v; v = 4; end end\n"
      "endmodule\n");
  vpiHandle v = By("top.g.blk.v");
  ASSERT_NE(v, nullptr);
  EXPECT_EQ(vpi_get(vpiType, v), vpiIntVar);
  EXPECT_EQ(FullName(v), "top.g.blk.v");
}

TEST_F(BlockScopesOfARun, ALabelOnAScopedLoopCreatesNoNamedBegin) {
  Run("module top; int a [2];\n"
      "  initial lf: foreach (a[i]) a[i] = i;\n"
      "  initial ld: for (int i = 0; i < 1; i++) ;\n"
      "endmodule\n");
  for (const std::string& name : std::vector<std::string>{"top.lf", "top.ld"}) {
    vpiHandle loop = By(name);
    EXPECT_TRUE(loop == nullptr || vpi_get(vpiType, loop) != vpiNamedBegin)
        << name;
  }
}

TEST(ScopeModel, VirtualInterfaceVarsAreOnlyTheVifsAndTheirArrays) {
  EXPECT_TRUE(VpiScopeVirtualInterfaceVars(nullptr).empty());
  EXPECT_TRUE(VpiScopeVariables(nullptr).empty());
  VpiObject element;
  element.type = vpiVirtualInterfaceVar;
  VpiObject range;
  range.type = vpiRange;
  VpiObject array;
  array.type = vpiArrayVar;
  array.children = {&element, &range};
  VpiObject plain;
  plain.type = vpiIntVar;
  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&plain, &array};
  EXPECT_EQ(VpiScopeVirtualInterfaceVars(&scope),
            (std::vector<VpiHandle>{&element}));
}

TEST(ScopeModel, BlockItemDeclarationAndLoopVariableKinds) {
  for (int type : {vpiIntegerVar, vpiRealVar, vpiShortRealVar, vpiTimeVar,
                   vpiByteVar, vpiShortIntVar, vpiLongIntVar, vpiBitVar,
                   vpiEnumVar, vpiUnionVar, vpiStringVar, vpiClassVar,
                   vpiChandleVar, vpiPackedArrayVar, vpiArrayVar}) {
    EXPECT_TRUE(VpiIsBlockItemDeclType(type)) << type;
  }
  EXPECT_FALSE(VpiIsLoopControlVarType(vpiTypedef));
  EXPECT_FALSE(VpiIsLoopControlVarType(vpiParameter));
}

TEST(ScopeModel, OnlyAnArrayOfVifsIsAVifArray) {
  EXPECT_FALSE(VpiIsVirtualInterfaceArray(nullptr));
  VpiObject plain;
  plain.type = vpiIntVar;
  EXPECT_FALSE(VpiIsVirtualInterfaceArray(&plain));
  VpiObject array;
  array.type = vpiArrayVar;
  array.children = {&plain};
  EXPECT_FALSE(VpiIsVirtualInterfaceArray(&array));
}

TEST(ScopeModel, EveryKindTheScopeClassGroupsIsAnInternalScope) {
  for (int type :
       {vpiTask, vpiInterface, vpiProgram, vpiPackage, vpiBegin, vpiNamedFork,
        vpiFork, vpiClassDefn, vpiClassTypespec, vpiClassObj, vpiClockingBlock,
        vpiGenScope, vpiFor, vpiForeachStmt}) {
    EXPECT_TRUE(VpiIsInternalScopeType(type)) << type;
  }
}

TEST(ScopeModel, AStatementIterationOfANonBlockIsNoNestedWalk) {
  VpiObject module;
  module.type = vpiModule;
  VpiObject iter;
  EXPECT_FALSE(VpiCollectNestedObjects(vpiStmt, &module, &iter));
  EXPECT_TRUE(iter.children.empty());
}

TEST(ScopeModel, AVariableInsideAStatementIsNoNestedScope) {
  VpiObject module;
  module.type = vpiModule;
  VpiObject stmt;
  stmt.type = vpiIf;
  VpiObject var;
  var.type = vpiReg;
  var.name = "inner";
  stmt.children = {&var};
  module.children = {&stmt};
  EXPECT_EQ(VpiNestedScopeNamed(&module, "inner"), nullptr);
  VpiObject block;
  block.type = vpiNamedBegin;
  block.name = "inner";
  stmt.children = {&var, &block};
  EXPECT_EQ(VpiNestedScopeNamed(&module, "inner"), &block);
}

TEST_F(BlockScopesOfARun, AVariableReachesTheScopeItIsDeclaredIn) {
  Run("module top;\n"
      "  int a;\n"
      "  initial begin : b int x; x = 1; end\n"
      "endmodule\n");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, By("top.a"))),
            VpiObjectOf(By("top")));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, By("top.b.x"))),
            VpiObjectOf(By("top.b")));
}

}  // namespace
}  // namespace delta
