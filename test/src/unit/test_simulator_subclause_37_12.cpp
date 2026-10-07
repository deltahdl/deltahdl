#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_model_helpers1.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

// §37.12 Scope: the VPI object model for a scope - the begin/fork blocks, tasks
// and functions, for/foreach statements, and the other scoped constructs the
// diagram draws. These tests observe the production helpers in vpi.cpp (and the
// VpiContext::Handle/Get/Iterate paths they feed) that apply the clause's
// numbered "Details".
//
// The diagram's structural reach (a scope's property/sequence decls, named
// events, parameters, internal scopes, typedefs, etc.) and its vpiName/
// vpiFullName strings are served by the generic machinery and carry no
// §37.12-specific rule of their own. The details that do are exercised below:
// scope-ness of an unnamed block (detail 1) and a for statement (detail 2), the
// loop control variable's scope (details 2 and 3), the vpiImport iteration
// (detail 4), the task/func body reached through vpiStmt (detail 5), the
// vpiJoinType of a fork-join (detail 6), and the vpiVirtualInterfaceVar /
// vpiVariables iterations over an array of virtual interfaces (detail 7).

// Walk an iterator to completion, collecting every object it yields in order.
std::vector<VpiHandle> Collect(VpiContext& ctx, VpiHandle iterator) {
  std::vector<VpiHandle> objects;
  if (!iterator) return objects;
  while (VpiHandle next = ctx.Scan(iterator)) objects.push_back(next);
  return objects;
}

// ---------------------------------------------------------------------------
// Detail 1: an unnamed begin/fork is a scope iff it directly contains a block
// item declaration; a named begin/fork is always a scope.
// ---------------------------------------------------------------------------

// D1: a block item declaration is a variable declaration or a type declaration.
// Statements and other constructs are not block item declarations.
TEST(ScopeModel, BlockItemDeclTypeClassification) {
  EXPECT_TRUE(VpiIsBlockItemDeclType(vpiLogicVar));  // a variable declaration
  EXPECT_TRUE(VpiIsBlockItemDeclType(vpiIntVar));
  EXPECT_TRUE(VpiIsBlockItemDeclType(vpiStructVar));
  EXPECT_TRUE(VpiIsBlockItemDeclType(vpiTypedef));  // a type declaration
  EXPECT_TRUE(
      VpiIsBlockItemDeclType(vpiParameter));  // a localparam declaration

  EXPECT_FALSE(VpiIsBlockItemDeclType(vpiAssignment));  // a statement
  EXPECT_FALSE(VpiIsBlockItemDeclType(vpiNamedBegin));  // a nested block
  EXPECT_FALSE(VpiIsBlockItemDeclType(vpiModule));
}

// D1: an unnamed begin or fork is a scope only when one of its direct children
// is a block item declaration; with only statement children it is not a scope.
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

  // The same rule governs an unnamed fork.
  VpiObject declaring_fork;
  declaring_fork.type = vpiFork;
  declaring_fork.children.push_back(&var_decl);
  EXPECT_TRUE(VpiBlockScopeIsScope(&declaring_fork));

  VpiObject stmt_only_fork;
  stmt_only_fork.type = vpiFork;
  stmt_only_fork.children.push_back(&stmt);
  EXPECT_FALSE(VpiBlockScopeIsScope(&stmt_only_fork));
}

// D1: a named begin or named fork is always a scope, even with no declaration
// among its children.
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

// D1 (boundary/error cases): a null block is not a scope; an unnamed begin with
// no members at all has no block item declaration and so is not a scope (the
// boundary of a block that itself holds a declaration); and a kind §37.12 does
// not give a conditional scope rule to - here a module - is not classified as
// one of these blocks.
TEST(ScopeModel, BlockScopeIsScopeRejectsNullEmptyAndNonBlockKinds) {
  EXPECT_FALSE(VpiBlockScopeIsScope(nullptr));

  VpiObject empty_begin;
  empty_begin.type = vpiBegin;  // no children -> no block item declaration
  EXPECT_FALSE(VpiBlockScopeIsScope(&empty_begin));

  VpiObject empty_fork;
  empty_fork.type = vpiFork;
  EXPECT_FALSE(VpiBlockScopeIsScope(&empty_fork));

  VpiObject module;
  module.type = vpiModule;
  EXPECT_FALSE(VpiBlockScopeIsScope(&module));
}

// ---------------------------------------------------------------------------
// Detail 2: a for statement is a scope iff vpiLocalVarDecls returns TRUE.
// ---------------------------------------------------------------------------

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

// ---------------------------------------------------------------------------
// Details 2 and 3: the scope of a loop control variable is its loop statement -
// the foreach statement always (detail 3), or the for statement when it is a
// scope (detail 2).
// ---------------------------------------------------------------------------

// D3: a foreach statement's loop control variable reaches the foreach statement
// as its scope. D2: a for statement's loop control variable reaches the for
// statement as its scope when the for declares its loop variables locally; when
// it does not, the for statement is not the variable's scope.
TEST(ScopePublic, LoopControlVariableScopeIsItsLoopStatement) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  // A foreach loop control variable -> the foreach statement (unconditional).
  VpiObject foreach_var;
  foreach_var.type = vpiIntVar;
  VpiObject foreach_stmt;
  foreach_stmt.type = vpiForeachStmt;
  foreach_var.parent = &foreach_stmt;
  foreach_stmt.children.push_back(&foreach_var);
  EXPECT_EQ(ctx.Handle(vpiScope, &foreach_var), &foreach_stmt);

  // A for loop control variable, with the for declaring its variables locally,
  // -> the for statement.
  VpiObject scoped_for_var;
  scoped_for_var.type = vpiIntVar;
  VpiObject scoped_for;
  scoped_for.type = vpiFor;
  scoped_for.local_var_decls = true;
  scoped_for_var.parent = &scoped_for;
  scoped_for.children.push_back(&scoped_for_var);
  EXPECT_EQ(ctx.Handle(vpiScope, &scoped_for_var), &scoped_for);

  // A for that is not a scope (shared loop variable) is not the variable's
  // scope, so the for-statement routing does not apply.
  VpiObject shared_for_var;
  shared_for_var.type = vpiIntVar;
  VpiObject shared_for;
  shared_for.type = vpiFor;
  shared_for.local_var_decls = false;
  shared_for_var.parent = &shared_for;
  shared_for.children.push_back(&shared_for_var);
  EXPECT_NE(ctx.Handle(vpiScope, &shared_for_var), &shared_for);

  SetGlobalVpiContext(nullptr);
}

// ---------------------------------------------------------------------------
// Detail 4: vpiImport reaches the objects actually imported into a scope.
// ---------------------------------------------------------------------------

// D4: a scope's vpiImport iteration returns the objects imported and actually
// referenced (those marked imported), not children merely declared in the scope
// nor items only made visible by the import.
TEST(ScopePublic, ImportIterationReturnsOnlyReferencedImports) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject imported_a;
  imported_a.type = vpiParameter;  // an imported, referenced item
  imported_a.imported = true;
  VpiObject imported_b;
  imported_b.type = vpiFunction;
  imported_b.imported = true;
  VpiObject local_decl;
  local_decl.type = vpiParameter;  // declared locally, not imported
  VpiObject visible_unreferenced;
  visible_unreferenced.type = vpiFunction;  // made visible but not referenced
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

  // A scope with no imported objects yields no iterator.
  VpiObject bare;
  bare.type = vpiModule;
  bare.children.push_back(&local_decl);
  EXPECT_EQ(ctx.Iterate(vpiImport, &bare), nullptr);

  SetGlobalVpiContext(nullptr);
}

// ---------------------------------------------------------------------------
// Detail 5: vpiStmt of a task/func is null with zero statements, the lone
// statement with one, and the unnamed begin grouping them with more than one.
// ---------------------------------------------------------------------------

// D5: the "task func" node groups tasks and functions.
TEST(ScopeModel, TaskFuncTypeClassification) {
  EXPECT_TRUE(VpiIsTaskFuncType(vpiTask));
  EXPECT_TRUE(VpiIsTaskFuncType(vpiFunction));
  EXPECT_TRUE(VpiIsTaskFuncType(vpiTaskFunc));

  EXPECT_FALSE(VpiIsTaskFuncType(vpiBegin));
  EXPECT_FALSE(VpiIsTaskFuncType(vpiModule));
}

// D5: a task with no statements reports a null body. The io decls and variables
// a task declares are not statements, so a task that holds only those still has
// an empty body.
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

// D5: when a task has more than one statement, the statements are grouped under
// an unnamed begin and vpiStmt reaches that begin (which in turn contains the
// statements).
TEST(ScopePublic, TaskWithMultipleStatementsReturnsUnnamedBegin) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject s0, s1, s2;
  s0.type = vpiAssignment;
  s1.type = vpiAssignment;
  s2.type = vpiAssignment;

  VpiObject grouping_begin;  // the unnamed begin wrapping the statements
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
  // The begin really does carry the statements it groups.
  EXPECT_EQ(grouping_begin.children.size(), 3u);

  SetGlobalVpiContext(nullptr);
}

// D5: a function with exactly one statement reports that statement directly,
// with no grouping begin synthesized.
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

// D5 (edge case): a task/func body reached through vpiStmt is the statement
// among the children, found past the io decls and variables the task also
// declares. This also exercises the combined vpiTaskFunc kind on the public
// handle path.
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
  // The declarations precede the body statement in child order.
  task_func.children.push_back(&io_decl);
  task_func.children.push_back(&local_var);
  task_func.children.push_back(&body);

  EXPECT_EQ(ctx.Handle(vpiStmt, &task_func), &body);

  SetGlobalVpiContext(nullptr);
}

// ---------------------------------------------------------------------------
// Detail 6: vpiJoinType reports one of vpiJoin/vpiJoinNone/vpiJoinAny.
// ---------------------------------------------------------------------------

// D6: only the three join constants are join types.
TEST(ScopeModel, JoinTypeClassification) {
  EXPECT_TRUE(VpiIsJoinType(vpiJoin));
  EXPECT_TRUE(VpiIsJoinType(vpiJoinNone));
  EXPECT_TRUE(VpiIsJoinType(vpiJoinAny));

  EXPECT_FALSE(VpiIsJoinType(vpiJoinAny + 100));
  EXPECT_FALSE(VpiIsJoinType(-1));
}

// D6: a fork-join scope reports its terminating join kind through vpiJoinType;
// a value outside the three legal join kinds collapses to vpiJoin.
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

  // An out-of-domain stored value is not a join type, so it reports vpiJoin.
  fork.join_type = vpiJoinAny + 100;
  EXPECT_EQ(ctx.Get(vpiJoinType, &fork), vpiJoin);

  SetGlobalVpiContext(nullptr);
}

// ---------------------------------------------------------------------------
// Detail 7: a scope's vpiVirtualInterfaceVar iteration expands an array of
// virtual interfaces into its elements, while vpiVariables reports the array as
// a single array var. The vif iteration is unsupported within a class defn.
// ---------------------------------------------------------------------------

// D7: iterating vpiVirtualInterfaceVar over a scope yields each standalone
// virtual interface var, and for a declared array of virtual interfaces, each
// element of the array separately.
TEST(ScopePublic, VirtualInterfaceIterationExpandsArrayElements) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);

  VpiObject standalone_vif;
  standalone_vif.type = vpiVirtualInterfaceVar;

  // An array of virtual interfaces: an array var whose elements are vif vars.
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
  EXPECT_EQ(vifs[1], &elem0);  // array expanded to its elements
  EXPECT_EQ(vifs[2], &elem1);

  // D7: vpiVariables reports the array of virtual interfaces as the single
  // array var that declares it, not its individual elements. The standalone
  // virtual interface var comes back beside it, §37.17 drawing `virtual
  // interface var` inside the `variables` class enclosure that this relation is
  // drawn to (§37.4.1).
  std::vector<VpiHandle> vars = Collect(ctx, ctx.Iterate(vpiVariables, &scope));
  ASSERT_EQ(vars.size(), 2u);
  EXPECT_EQ(vars[0], &standalone_vif);
  EXPECT_EQ(vars[1], &vif_array);

  SetGlobalVpiContext(nullptr);
}

// D7 (error/lexical-context case): the vpiVirtualInterfaceVar iteration is not
// supported within a lexical context such as a class defn, so it yields no
// iterator there even when the class declares virtual interface vars.
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

// ---------------------------------------------------------------------------
// The scopes of a run: the blocks a design's procedures write, built from the
// elaborated design rather than by hand.
// ---------------------------------------------------------------------------

class BlockScopesOfARun : public VpiDesignRun {
 protected:
  static std::string FullName(vpiHandle obj) {
    const char* full_name = vpi_get_str(vpiFullName, obj);
    return full_name == nullptr ? "" : full_name;
  }
};

// D1: a named begin is always a scope, so a procedure's named block is an
// object of the run, named under the instance whose procedure wrote it.
TEST_F(BlockScopesOfARun, ANamedBeginIsAnObjectOfTheRun) {
  Run("module top; int x; initial begin : blk x = 1; end endmodule\n");
  vpiHandle blk = By("top.blk");
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(vpi_get(vpiType, blk), vpiNamedBegin);
  EXPECT_STREQ(vpi_get_str(vpiName, blk), "blk");
  EXPECT_EQ(FullName(blk), "top.blk");
}

// D1: a named fork is always a scope as well.
TEST_F(BlockScopesOfARun, ANamedForkIsAnObjectOfTheRun) {
  Run("module top; initial fork : fk #1; join_any endmodule\n");
  vpiHandle fk = By("top.fk");
  ASSERT_NE(fk, nullptr);
  EXPECT_EQ(vpi_get(vpiType, fk), vpiNamedFork);
  EXPECT_EQ(FullName(fk), "top.fk");
}

// A named block inside another is named under the block around it.
TEST_F(BlockScopesOfARun, ANestedNamedBlockIsNamedUnderTheBlockAroundIt) {
  Run("module top; initial begin : outer begin : inner end end endmodule\n");
  vpiHandle inner = By("top.outer.inner");
  ASSERT_NE(inner, nullptr);
  EXPECT_EQ(vpi_get(vpiType, inner), vpiNamedBegin);
  EXPECT_EQ(FullName(inner), "top.outer.inner");
  EXPECT_EQ(By("top.inner"), nullptr);
}

// The blocks a procedure writes in the branches of an if, the items of a case
// and the body of a loop are scopes of the run all the same.
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

// A block of a submodule's procedure is a scope of that instance.
TEST_F(BlockScopesOfARun, ABlockOfASubmoduleIsNamedUnderItsInstance) {
  Run("module sub; initial begin : sb end endmodule\n"
      "module top; sub u(); endmodule\n");
  vpiHandle sb = By("top.u.sb");
  ASSERT_NE(sb, nullptr);
  EXPECT_EQ(FullName(sb), "top.u.sb");
}

// D6: a fork reports the join keyword that closed it.
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

// The variables a named block declares hang beneath it, each of the kind its
// type gives (§37.17), and a block parameter is none of them.
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

// A named block's variables of a real, string, chandle, event, enum or virtual
// interface type are the kinds §37.17 and §37.27 draw for them, as a module's
// of those types are, rather than regs (#5032).
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

// A block's variable of a class type is a class var, whether the design
// declares the class, the class is a built-in one, or a typedef names it; a
// variable of any other typedef is the kind of the type the typedef names
// (#5032).
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

// D1: an unnamed begin or fork that directly declares a block item is a scope,
// with the declared variable beneath it.
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

// D1: an unnamed begin that declares nothing directly is no scope, though a
// named block inside it declares a variable; the named block stands in the
// instance itself, as in the detail's example.
TEST_F(BlockScopesOfARun, AnUnnamedBlockThatDeclaresNothingIsNoScope) {
  Run("module top; initial begin\n"
      "  begin : BLK var logic v; v = 1'b1; end\n"
      "end endmodule\n");
  vpiHandle top = By("top");
  ASSERT_NE(top, nullptr);
  EXPECT_EQ(KindsOf(vpiInternalScope, top), (std::vector<int>{vpiNamedBegin}));
  EXPECT_NE(By("top.BLK"), nullptr);
}

// D1 with §37.60: an unnamed begin that declares nothing is no scope but is a
// begin of the run all the same, the body its procedure reaches, reaching the
// statements it holds in order, each standing in the instance (#5060, #5061).
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

// The same of an unnamed fork, which reports the join keyword closing it.
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

// D1's example: the named block inside the plain begin is a statement of the
// begin, while it stands in the instance as one of its scopes and is named
// under the instance alone (#5060).
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

// The vpiStmt iteration of a block reaches the statements it holds, in the
// order written, and none of the variables it declares (#5061).
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

// The vpiInternalScope relation is drawn to the scope class, so it reaches the
// instances and blocks a scope holds and none of its variables.
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

// A block reaches the scope it stands in through vpiScope: the block around
// it, or the instance.
TEST_F(BlockScopesOfARun, ABlockReachesTheScopeItStandsIn) {
  Run("module top; initial begin : outer begin : inner end end endmodule\n");
  vpiHandle outer = By("top.outer");
  ASSERT_NE(outer, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, By("top.outer.inner"))),
            VpiObjectOf(outer));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiScope, outer)), VpiObjectOf(By("top")));
}

// A statement's scope is the nearest object around it that is a scope: an
// unnamed begin declaring nothing is passed over (D1).
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

// A statement standing in no scope at all reaches none.
TEST(ScopePublic, AStatementInNoScopeReachesNone) {
  VpiContext ctx;
  SetGlobalVpiContext(&ctx);
  VpiObject assignment;
  assignment.type = vpiAssignment;
  EXPECT_EQ(ctx.Handle(vpiScope, &assignment), nullptr);
  SetGlobalVpiContext(nullptr);
}

// §9.3.5: a label on a statement other than a block creates a named begin
// around it, which D1 makes a scope, and the procedure runs that begin.
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

// §9.3.5: a label on a for loop that declares no variable creates a named
// begin around it like any other statement's.
TEST_F(BlockScopesOfARun, ALabelOnAPlainForLoopCreatesANamedBegin) {
  Run("module top; int j; initial ln: for (j = 0; j < 1; j++) ; endmodule\n");
  vpiHandle ln = By("top.ln");
  ASSERT_NE(ln, nullptr);
  EXPECT_EQ(vpi_get(vpiType, ln), vpiNamedBegin);
}

// §9.3.5: a label on a foreach loop, or on a for loop declaring its variables,
// names the block the loop itself creates, so no named begin stands around it.
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

}  // namespace
}  // namespace delta
