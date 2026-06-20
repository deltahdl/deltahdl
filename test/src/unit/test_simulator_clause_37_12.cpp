#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

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
// boundary of "directly contains a declaration"); and a kind §37.12 does not
// give a conditional scope rule to - here a module - is not classified as one
// of these blocks.
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
  // array var that declares it, not its individual elements.
  std::vector<VpiHandle> vars = Collect(ctx, ctx.Iterate(vpiVariables, &scope));
  ASSERT_EQ(vars.size(), 1u);
  EXPECT_EQ(vars[0], &vif_array);

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

}  // namespace
}  // namespace delta
