#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
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

class DoWhileForeach : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(DoWhileForeach, DoWhileReachesConditionAmongConditionAndBody) {
  VpiObject body;
  body.type = vpiBegin;
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&body, &condition};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiCondition, VpiHandleOf(&do_while))),
            &condition);
}

TEST_F(DoWhileForeach, DoWhileWithoutConditionReportsNoCondition) {
  VpiObject body;
  body.type = vpiBegin;

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&body};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&do_while)), nullptr);
}

TEST_F(DoWhileForeach, DoWhileConditionRelationIsScopedToDoWhile) {
  VpiObject expr;
  expr.type = vpiOperation;

  VpiObject not_a_do_while;
  not_a_do_while.type = vpiBegin;
  not_a_do_while.children = {&expr};

  EXPECT_EQ(vpi_handle(vpiCondition, VpiHandleOf(&not_a_do_while)), nullptr);
}

TEST_F(DoWhileForeach, DoWhileReachesBodyThroughVpiStmt) {
  VpiObject condition;
  condition.type = vpiOperation;
  VpiObject body;
  body.type = vpiBegin;

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&condition, &body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&do_while))), &body);
}

TEST_F(DoWhileForeach, ForeachStatementVariablesReachesIndexedArray) {
  VpiObject array;
  array.type = vpiPackedArrayVar;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .foreach_array = &array;

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, VpiHandleOf(&foreach))),
            &array);
}

TEST_F(DoWhileForeach, ForeachStatementVariablesReportsNoVariableWhenAbsent) {
  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;

  EXPECT_EQ(vpi_handle(vpiVariables, VpiHandleOf(&foreach)), nullptr);
}

TEST_F(DoWhileForeach, ForeachStatementVariablesIsScopedToForeachStatements) {
  VpiObject distractor_array;
  distractor_array.type = vpiPackedArrayVar;
  VpiObject vars_child;
  vars_child.type = vpiVariables;

  VpiObject not_a_foreach;
  not_a_foreach.type = vpiBegin;
  not_a_foreach.foreach_array = &distractor_array;
  not_a_foreach.children = {&vars_child};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, VpiHandleOf(&not_a_foreach))),
            &vars_child);
}

TEST_F(DoWhileForeach, ForeachStatementSkippedIndexIsNullOpPlaceholder) {
  VpiObject var_i;
  var_i.type = vpiIntegerVar;
  VpiObject var_k;
  var_k.type = vpiIntegerVar;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .loop_vars = {&var_i, nullptr, &var_k};

  vpiHandle it = vpi_iterate(vpiLoopVars, VpiHandleOf(&foreach));
  ASSERT_NE(it, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &var_i);
  vpiHandle skipped = vpi_scan(it);
  ASSERT_NE(skipped, nullptr);
  EXPECT_NE(VpiObjectOf(skipped), &var_i);
  EXPECT_NE(VpiObjectOf(skipped), &var_k);
  EXPECT_EQ(vpi_get(vpiType, skipped), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, skipped), vpiNullOp);
  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &var_k);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(DoWhileForeach,
       ForeachStatementBoundarySkipsEachGetDistinctNullOpPlaceholder) {
  VpiObject var_j;
  var_j.type = vpiIntegerVar;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .loop_vars = {nullptr, &var_j, nullptr};

  vpiHandle it = vpi_iterate(vpiLoopVars, VpiHandleOf(&foreach));
  ASSERT_NE(it, nullptr);

  vpiHandle first_skip = vpi_scan(it);
  ASSERT_NE(first_skip, nullptr);
  EXPECT_EQ(vpi_get(vpiType, first_skip), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, first_skip), vpiNullOp);

  EXPECT_EQ(VpiObjectOf(vpi_scan(it)), &var_j);

  vpiHandle last_skip = vpi_scan(it);
  ASSERT_NE(last_skip, nullptr);
  EXPECT_EQ(vpi_get(vpiType, last_skip), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, last_skip), vpiNullOp);

  EXPECT_NE(first_skip, last_skip);
  EXPECT_EQ(vpi_scan(it), nullptr);
}

TEST_F(DoWhileForeach, ForeachStatementReachesBodyThroughVpiStmt) {
  VpiObject array;
  array.type = vpiPackedArrayVar;
  VpiObject body;
  body.type = vpiBegin;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .foreach_array = &array;
  foreach
    .children = {&body};

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&foreach))), &body);
}

TEST_F(DoWhileForeach,
       ForeachStatementLoopVarsIterationIsScopedToForeachStatements) {
  VpiObject var_i;
  var_i.type = vpiIntegerVar;

  VpiObject not_a_foreach;
  not_a_foreach.type = vpiBegin;
  not_a_foreach.loop_vars = {&var_i};

  EXPECT_EQ(vpi_iterate(vpiLoopVars, VpiHandleOf(&not_a_foreach)), nullptr);
}

TEST_F(DoWhileForeach, EachKindABodyCarriesIsReachedByBothLoopKinds) {
  for (int loop_kind : {vpiDoWhile, vpiForeachStmt}) {
    for (int body_kind :
         {vpiAssignment, vpiNamedBegin, vpiFork, vpiDoWhile, vpiNullStmt}) {
      VpiObject body;
      body.type = body_kind;

      VpiObject loop;
      loop.type = loop_kind;
      loop.children = {&body};

      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiStmt, VpiHandleOf(&loop))), &body)
          << "loop kind " << loop_kind << ", body kind " << body_kind;
    }
  }
}

TEST_F(DoWhileForeach, NeitherLoopReportsABodyWhenItCarriesNoStatement) {
  VpiObject condition;
  condition.type = vpiOperation;

  VpiObject do_while;
  do_while.type = vpiDoWhile;
  do_while.children = {&condition};

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&do_while)), nullptr);

  VpiObject array;
  array.type = vpiPackedArrayVar;

  VpiObject foreach;
  foreach
    .type = vpiForeachStmt;
  foreach
    .foreach_array = &array;

  EXPECT_EQ(vpi_handle(vpiStmt, VpiHandleOf(&foreach)), nullptr);
}

class DoWhileAndForeachLoopsOfARun : public VpiDesignRun {
 protected:
  static vpiHandle FirstBody() {
    vpiHandle it = vpi_iterate(vpiProcess, By("top"));
    return it ? vpi_handle(vpiStmt, vpi_scan(it)) : nullptr;
  }

  static std::vector<int> FirstLoopVarKinds(vpiHandle scope) {
    std::vector<int> kinds;
    vpiHandle stmts = vpi_iterate(vpiStmt, scope);
    if (stmts == nullptr) return kinds;
    while (vpiHandle stmt = vpi_scan(stmts)) {
      if (vpi_get(vpiType, stmt) != vpiForeachStmt) continue;
      kinds.push_back(
          vpi_get(vpiType, vpi_scan(vpi_iterate(vpiLoopVars, stmt))));
    }
    return kinds;
  }
};

TEST_F(DoWhileAndForeachLoopsOfARun, ADoWhileLoopIsAnObjectOfTheRun) {
  Run("module top; int i; initial do i = i + 1; while (i < 3); endmodule\n");
  vpiHandle loop = FirstBody();
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiType, loop), vpiDoWhile);
  EXPECT_EQ(vpi_get(vpiOpType, vpi_handle(vpiCondition, loop)), vpiLtOp);
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiAssignment);
}

TEST_F(DoWhileAndForeachLoopsOfARun, AForeachLoopIsAnObjectOfTheRun) {
  Run("module top; int m [2][3]; initial foreach (m[, j]) m[0][j] = j;\n"
      "endmodule\n");
  vpiHandle loop = FirstBody();
  ASSERT_NE(loop, nullptr);
  EXPECT_EQ(vpi_get(vpiType, loop), vpiForeachStmt);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, loop)),
            VpiObjectOf(By("top.m")));
  vpiHandle vars = vpi_iterate(vpiLoopVars, loop);
  ASSERT_NE(vars, nullptr);
  vpiHandle skipped = vpi_scan(vars);
  vpiHandle j = vpi_scan(vars);
  ASSERT_NE(skipped, nullptr);
  ASSERT_NE(j, nullptr);
  EXPECT_EQ(vpi_get(vpiType, skipped), vpiOperation);
  EXPECT_EQ(vpi_get(vpiOpType, skipped), vpiNullOp);
  EXPECT_EQ(vpi_get(vpiType, j), vpiIntVar);
  EXPECT_STREQ(vpi_get_str(vpiName, j), "j");
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(vpi_get(vpiType, body), vpiAssignment);
}

TEST_F(DoWhileAndForeachLoopsOfARun, TheBodyNamesTheLoopsIndexVariable) {
  Run("module top; int k; int a [3]; initial foreach (a[k]) a[k] = k;\n"
      "endmodule\n");
  vpiHandle loop = FirstBody();
  ASSERT_NE(loop, nullptr);
  vpiHandle vars = vpi_iterate(vpiLoopVars, loop);
  ASSERT_NE(vars, nullptr);
  vpiHandle k = vpi_scan(vars);
  ASSERT_NE(k, nullptr);
  vpiHandle body = vpi_handle(vpiStmt, loop);
  ASSERT_NE(body, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiRhs, body)), VpiObjectOf(k));
  EXPECT_NE(VpiObjectOf(k), VpiObjectOf(By("top.k")));
}

TEST_F(DoWhileAndForeachLoopsOfARun, AnIndexVariableIsOfItsArraysIndexType) {
  Run("module top; typedef enum {A, B} e_t;\n"
      "  int s [string]; int g [integer]; int e [e_t]; int f [2];\n"
      "  initial foreach (s[i]) begin end\n"
      "  initial foreach (g[i]) begin end\n"
      "  initial foreach (e[i]) begin end\n"
      "  initial foreach (f[i]) begin end\n"
      "  initial begin : b int q [byte]; foreach (q[k]) begin end end\n"
      "endmodule\n");
  std::vector<int> kinds;
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  while (vpiHandle proc = vpi_scan(procs)) {
    vpiHandle loop = vpi_handle(vpiStmt, proc);
    if (loop != nullptr && vpi_get(vpiType, loop) == vpiNamedBegin) {
      vpiHandle held = vpi_iterate(vpiStmt, loop);
      loop = held == nullptr ? nullptr : vpi_scan(held);
    }
    ASSERT_NE(loop, nullptr);
    vpiHandle vars = vpi_iterate(vpiLoopVars, loop);
    ASSERT_NE(vars, nullptr);
    kinds.push_back(vpi_get(vpiType, vpi_scan(vars)));
  }
  EXPECT_EQ(kinds, (std::vector<int>{vpiStringVar, vpiIntegerVar, vpiEnumVar,
                                     vpiIntVar, vpiByteVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun, ABlocksArraysGiveTheirIndexTypes) {
  Run("module top; typedef enum {A, B} e_t; class C; endclass\n"
      "  typedef int arr_t [3]; localparam int N = 2;\n"
      "  initial begin : b\n"
      "    int f [2]; int d []; int t [e_t]; int c [C]; int p [N]; arr_t a;\n"
      "    bit [3:0] v;\n"
      "    foreach (f[i]) begin end\n"
      "    foreach (d[i]) begin end\n"
      "    foreach (t[i]) begin end\n"
      "    foreach (c[i]) begin end\n"
      "    foreach (p[i]) begin end\n"
      "    foreach (a[i]) begin end\n"
      "    foreach (v[i]) begin end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")),
            (std::vector<int>{vpiIntVar, vpiIntVar, vpiEnumVar, vpiClassVar,
                              vpiIntVar, vpiIntVar, vpiIntVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun,
       AClassIndexAndAPropertysArrayGiveTheirKinds) {
  Run("module top; class C; int m [2]; endclass\n"
      "  int c [C]; C o = new;\n"
      "  initial foreach (c[i]) begin end\n"
      "  initial foreach (o.m[i]) begin end\n"
      "endmodule\n");
  std::vector<int> kinds;
  vpiHandle procs = vpi_iterate(vpiProcess, By("top"));
  ASSERT_NE(procs, nullptr);
  while (vpiHandle proc = vpi_scan(procs)) {
    vpiHandle vars = vpi_iterate(vpiLoopVars, vpi_handle(vpiStmt, proc));
    ASSERT_NE(vars, nullptr);
    kinds.push_back(vpi_get(vpiType, vpi_scan(vars)));
  }
  EXPECT_EQ(kinds, (std::vector<int>{vpiClassVar, vpiIntVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun, APropertysArrayGivesItsIndexType) {
  Run("module sub; int g [2]; int aa [string]; endmodule\n"
      "module top; sub u ();\n"
      "  class H; int a [string]; endclass\n"
      "  class C; int m [string]; int f [2]; H h = new; endclass\n"
      "  C o = new; C objs [2];\n"
      "  initial begin : b objs[0] = new;\n"
      "    foreach (o.m[k]) begin end\n"
      "    foreach (o.h.a[k]) begin end\n"
      "    foreach (o.f[k]) begin end\n"
      "    foreach (objs[0].f[k]) begin end\n"
      "    foreach (u.g[k]) begin end\n"
      "    foreach (u.aa[k]) begin end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")),
            (std::vector<int>{vpiStringVar, vpiStringVar, vpiIntVar, vpiIntVar,
                              vpiIntVar, vpiStringVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun, AStructMembersArrayGivesItsIndexType) {
  Run("module top;\n"
      "  class H; int m [string]; endclass\n"
      "  typedef struct { int n; int aa [string]; H h; } s_t;\n"
      "  s_t s;\n"
      "  initial begin : b s.h = new;\n"
      "    foreach (s.aa[k]) begin end\n"
      "    foreach (s.h.m[k]) begin end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")),
            (std::vector<int>{vpiStringVar, vpiStringVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun, ATypeParameterBaseGivesItsIndexType) {
  Run("module top;\n"
      "  class B; int v [string]; endclass\n"
      "  class B2; int v [byte]; endclass\n"
      "  class C #(int N = 1, type T = B) extends T; endclass\n"
      "  class H; C #(.T(B2)) c = new; endclass\n"
      "  C c0 = new; C #(.T(B2)) c1 = new; C #(2, B2) c2 = new;\n"
      "  C #(.N(3)) c3 = new; H h = new;\n"
      "  initial begin : b\n"
      "    foreach (c0.v[k]) begin end\n"
      "    foreach (c1.v[k]) begin end\n"
      "    foreach (c2.v[k]) begin end\n"
      "    foreach (c3.v[k]) begin end\n"
      "    foreach (h.c.v[k]) begin end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")),
            (std::vector<int>{vpiStringVar, vpiByteVar, vpiByteVar,
                              vpiStringVar, vpiByteVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun,
       AStructMembersSpecializationGivesItsIndex) {
  Run("module top;\n"
      "  class B; int v [string]; endclass\n"
      "  class B2; int v [byte]; endclass\n"
      "  class C #(type T = B) extends T; endclass\n"
      "  typedef struct { C #(.T(B2)) c; } s_t;\n"
      "  s_t s;\n"
      "  initial begin : b s.c = new; foreach (s.c.v[k]) begin end end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")), (std::vector<int>{vpiByteVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun, ANestedStructMembersFixedArrayGivesInt) {
  Run("module top;\n"
      "  typedef struct { int f [2]; } in_t;\n"
      "  typedef struct { in_t inner; } out_t;\n"
      "  out_t s;\n"
      "  initial begin : b foreach (s.inner.f[k]) begin end end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")), (std::vector<int>{vpiIntVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun, ANestedStructMembersArrayGivesItsIndex) {
  Run("module top;\n"
      "  typedef struct { int aa [string]; } in_t;\n"
      "  typedef struct { in_t inner; struct { int aa [byte]; } flat; } "
      "out_t;\n"
      "  out_t s;\n"
      "  initial begin : b\n"
      "    foreach (s.inner.aa[k]) begin end\n"
      "    foreach (s.flat.aa[k]) begin end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")),
            (std::vector<int>{vpiStringVar, vpiByteVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun, ANamedBlocksArrayGivesItsIndexType) {
  Run("module top;\n"
      "  initial begin begin : b1 static int aa [string]; end end\n"
      "  initial begin : b foreach (b1.aa[k]) begin end end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")), (std::vector<int>{vpiStringVar}));
}

TEST_F(DoWhileAndForeachLoopsOfARun, AVirtualInterfacesArrayGivesItsIndexType) {
  Run("interface other; int aa [byte]; endinterface\n"
      "interface intf; int n; int aa [string]; struct { int f [2]; } s;\n"
      "  task t(); endtask\n"
      "endinterface\n"
      "module top; intf i (); virtual intf vif;\n"
      "  initial begin : b\n"
      "    vif = i;\n"
      "    foreach (vif.aa[k]) begin end\n"
      "    foreach (vif.s.f[k]) begin end\n"
      "  end\n"
      "endmodule\n");
  EXPECT_EQ(FirstLoopVarKinds(By("top.b")),
            (std::vector<int>{vpiStringVar, vpiIntVar}));
}

TEST_F(DoWhileForeach, DoWhileConditionOfANullHandleIsNull) {
  EXPECT_EQ(VpiDoWhileConditionExpr(nullptr), nullptr);
}

class LoopFormsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("module sub; int g [2]; endmodule\n"
        "module top; int s; bit b; bit [3:0] v; string str;\n"
        "  int dyn []; int q [$]; int aa [string];\n"
        "  int m2 [2][3]; int m3 [2][3][4];\n"
        "  typedef struct { int sa [2]; } st_t; st_t st;\n"
        "  class K; int km [3]; endclass\n"
        "  K o = new;\n"
        "  sub u();\n"
        "  function int f(int x); return x; endfunction\n"
        "  initial foreach (m2[i, j]) s = i;\n"
        "  initial foreach (m2[i, ]) s = i;\n"
        "  initial foreach (m3[i, , k]) s = i;\n"
        "  initial foreach (m2[i]) begin s = i; end\n"
        "  initial foreach (m2[i]) begin : fb s = i; end\n"
        "  initial foreach (v[i]) s = i;\n"
        "  initial foreach (str[i]) s = i;\n"
        "  initial foreach (dyn[i]) s = i;\n"
        "  initial foreach (q[i]) s = i;\n"
        "  initial foreach (aa[i]) s = 1;\n"
        "  initial foreach (o.km[i]) s = i;\n"
        "  initial foreach (u.g[i]) s = i;\n"
        "  initial foreach (st.sa[i]) s = i;\n"
        "  initial do begin s = 1; end while (s < 0);\n"
        "  initial do begin : db s = 1; end while (s < 0);\n"
        "  initial do s = 1; while (b);\n"
        "  initial do s = 1; while (f(0));\n"
        "  initial begin : nb do s = 1; while (s < 0); end\n"
        "endmodule\n");
  }

  static vpiHandle LoopAt(size_t n) {
    const std::vector<vpiHandle> kProcs = ObjectsOf(vpiProcess, By("top"));
    return n < kProcs.size() ? vpi_handle(vpiStmt, kProcs[n]) : nullptr;
  }

  static std::vector<std::string> LoopVarsOf(vpiHandle loop) {
    std::vector<std::string> vars;
    for (vpiHandle var : ObjectsOf(vpiLoopVars, loop)) {
      const char* name = vpi_get_str(vpiName, var);
      vars.emplace_back(OpOf(var) == vpiNullOp ? "-"
                        : name == nullptr      ? "?"
                                               : name);
    }
    return vars;
  }

  static int BodyKind(size_t n) {
    vpiHandle body = vpi_handle(vpiStmt, LoopAt(n));
    return body == nullptr ? 0 : vpi_get(vpiType, body);
  }

  static std::string IndexedName(size_t n) {
    vpiHandle var = vpi_handle(vpiVariables, LoopAt(n));
    const char* name = var == nullptr ? nullptr : vpi_get_str(vpiName, var);
    return name == nullptr ? "" : name;
  }
};

TEST_F(LoopFormsOfARun, EachIndexPositionIsAVariableOrANullOperation) {
  EXPECT_EQ(LoopVarsOf(LoopAt(0)), (std::vector<std::string>{"i", "j"}));
  EXPECT_EQ(LoopVarsOf(LoopAt(1)), (std::vector<std::string>{"i", "-"}));
  EXPECT_EQ(LoopVarsOf(LoopAt(2)), (std::vector<std::string>{"i", "-", "k"}));
}

TEST_F(LoopFormsOfARun, ABlockBodyIsReachedAsTheBlock) {
  EXPECT_EQ(BodyKind(3), vpiBegin);
  EXPECT_EQ(BodyKind(4), vpiNamedBegin);
  EXPECT_EQ(BodyKind(13), vpiBegin);
  EXPECT_EQ(BodyKind(14), vpiNamedBegin);
  for (size_t n : {3U, 13U}) {
    vpiHandle block = vpi_handle(vpiStmt, LoopAt(n));
    EXPECT_EQ(KindsOf(vpiStmt, block), std::vector<int>{vpiAssignment}) << n;
  }
}

TEST_F(LoopFormsOfARun, TheIndexedVariableIsEachKindOfArrayAndString) {
  vpiHandle top = By("top");
  const std::vector<std::pair<size_t, const char*>> kIndexed{
      {5, "v"}, {6, "str"}, {7, "dyn"}, {8, "q"}, {9, "aa"}};
  for (const auto& [n, name] : kIndexed) {
    vpiHandle var = vpi_handle(vpiVariables, LoopAt(n));
    ASSERT_NE(var, nullptr) << name;
    EXPECT_EQ(VpiObjectOf(var), VpiObjectOf(Named(vpiVariables, top, name)))
        << name;
  }
  EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiVariables, LoopAt(6))),
            vpiStringVar);
}

TEST_F(LoopFormsOfARun, DISABLED_AnArrayPropertyThroughAHandleIsAVariable) {
  vpiHandle var = vpi_handle(vpiVariables, LoopAt(10));
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(vpi_get(vpiType, var), vpiArrayVar);
  EXPECT_EQ(IndexedName(10), "km");
}

TEST_F(LoopFormsOfARun, TheIndexedVariableIsTheOneASelectNames) {
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiVariables, LoopAt(11))),
            VpiObjectOf(By("top.u.g")));
  EXPECT_EQ(IndexedName(12), "sa");
}

TEST_F(LoopFormsOfARun, ADoWhileConditionIsAVariableOrACall) {
  vpiHandle var = vpi_handle(vpiCondition, LoopAt(15));
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(VpiObjectOf(var), VpiObjectOf(By("top.b")));
  vpiHandle call = vpi_handle(vpiCondition, LoopAt(16));
  ASSERT_NE(call, nullptr);
  EXPECT_EQ(vpi_get(vpiType, call), vpiFuncCall);
  EXPECT_EQ(CalleeOf(call), "f");
}

TEST_F(LoopFormsOfARun, ADoWhileInANamedBlockIsADoWhile) {
  vpiHandle block = LoopAt(17);
  ASSERT_NE(block, nullptr);
  EXPECT_EQ(vpi_get(vpiType, block), vpiNamedBegin);
  EXPECT_EQ(KindsOf(vpiStmt, block), std::vector<int>{vpiDoWhile});
}

TEST_F(DoWhileAndForeachLoopsOfARun, EachPlaceRunsADoWhileAndAForeach) {
  const char* const kLoops =
      " begin do n = n + 1; while (n < 2); foreach (w[j]) w[j] = j; end ";
  const std::string kVars = "int n; int w [3];";
  Run("package pk; " + kVars + " task pt;" + kLoops + "endtask endpackage\n" +
      "interface ifc; " + kVars + " initial" + kLoops + "endinterface\n" +
      "program prg; " + kVars + " initial" + kLoops + "endprogram\n" +
      "module top; " + kVars + " ifc i0(); prg p0();\n" + "  class C; " +
      kVars + " function void cm;" + kLoops + "endfunction endclass\n" +
      "  task tk;" + kLoops + "endtask\n" + "  function void fn;" + kLoops +
      "endfunction\n" + "endmodule\n");
  std::vector<std::pair<const char*, vpiHandle>> places =
      OwnersInEachPlace("cm");
  places.emplace_back("module function", Named(vpiFunction, By("top"), "fn"));
  for (const auto& [where, place] : places) {
    vpiHandle block = place == nullptr ? nullptr : vpi_handle(vpiStmt, place);
    ASSERT_NE(block, nullptr) << where;
    const std::vector<vpiHandle> kLoopsRun = ObjectsOf(vpiStmt, block);
    ASSERT_EQ(kLoopsRun.size(), 2U) << where;
    vpiHandle do_while = kLoopsRun[0];
    vpiHandle each = kLoopsRun[1];
    EXPECT_EQ(vpi_get(vpiType, do_while), vpiDoWhile) << where;
    EXPECT_EQ(OpOf(vpi_handle(vpiCondition, do_while)), vpiLtOp) << where;
    EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiStmt, do_while)), vpiAssignment)
        << where;
    EXPECT_EQ(vpi_get(vpiType, each), vpiForeachStmt) << where;
    vpiHandle array = vpi_handle(vpiVariables, each);
    ASSERT_NE(array, nullptr) << where;
    EXPECT_STREQ(vpi_get_str(vpiName, array), "w") << where;
    EXPECT_EQ(NamesOf(vpiLoopVars, each), std::vector<std::string>{"j"})
        << where;
    EXPECT_EQ(vpi_get(vpiType, vpi_handle(vpiStmt, each)), vpiAssignment)
        << where;
  }
}

}  // namespace
}  // namespace delta
