#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

struct StatementKind {
  const char* label;
  int type;
  const char* text;
};

const std::vector<StatementKind>& StatementKinds() {
  static const std::vector<StatementKind> kKinds = {
      {"l_if", vpiIf, "if (a) b = 1;"},
      {"l_ifelse", vpiIfElse, "if (a) b = 1; else b = 0;"},
      {"l_while", vpiWhile, "while (0) b = 1;"},
      {"l_repeat", vpiRepeat, "repeat (2) b = 1;"},
      {"l_case", vpiCase, "case (s) 0: b = 1; default: b = 0; endcase"},
      {"l_for", vpiFor, "for (int k = 0; k < 2; k++) b = 1;"},
      {"l_foreach", vpiForeachStmt, "foreach (arr[k]) b = 1;"},
      {"l_dowhile", vpiDoWhile, "do b = 1; while (0);"},
      {"l_delay", vpiDelayControl, "#1 b = 1;"},
      {"l_event", vpiEventControl, "@(posedge clk) b = 1;"},
      {"l_blocking", vpiAssignment, "b = 1;"},
      {"l_nonblocking", vpiAssignment, "c <= 1;"},
      {"l_assign", vpiAssignStmt, "assign d = 1;"},
      {"l_deassign", vpiDeassign, "deassign d;"},
      {"l_force", vpiForce, "force a = 1;"},
      {"l_release", vpiRelease, "release a;"},
      {"l_disable", vpiDisable, "disable tk;"},
      {"l_disablefork", vpiDisableFork, "disable fork;"},
      {"l_expect", vpiExpectStmt, "expect (@(posedge clk) a) b = 1;"},
      {"l_trigger", vpiEventStmt, "-> e;"},
      {"l_systask", vpiSysTaskCall, "$display(\"x\");"},
      {"l_sysfunc", vpiSysFuncCall, "$random;"},
      {"l_task", vpiTaskCall, "tk();"},
      {"l_mtask", vpiMethodTaskCall, "h.mt();"},
      {"l_mfunc", vpiMethodFuncCall, "q.delete();"},
      {"l_func", vpiFuncCall, "vf();"},
      {"l_wait", vpiWait, "wait (a) b = 1;"},
      {"l_waitorder", vpiOrderedWait, "wait_order (e, f) b = 1;"},
      {"l_waitfork", vpiWaitFork, "wait fork;"},
  };
  return kKinds;
}

std::string DesignOf(bool labelled) {
  std::string src =
      "module top; logic a, b, c, d, clk; event e, f; logic [1:0] s;\n"
      "  int arr [0:1]; int q[$];\n"
      "  class K; task mt; endtask endclass\n"
      "  K h = new;\n"
      "  task tk; endtask\n"
      "  function void vf; endfunction\n"
      "  function int fr;\n"
      "    " +
      std::string(labelled ? "l_return: " : "") +
      "return 1;\n"
      "  endfunction\n"
      "  initial for (int k = 0; k < 2; k++) begin\n"
      "    if (k == 0) " +
      std::string(labelled ? "l_continue: " : "") +
      "continue;\n"
      "    " +
      std::string(labelled ? "l_break: " : "") +
      "break;\n"
      "  end\n"
      "  initial " +
      std::string(labelled ? "l_forever: " : "") +
      "forever @(posedge clk) b = ~b;\n";
  for (const StatementKind& kind : StatementKinds()) {
    src += "  initial ";
    if (labelled) src += std::string(kind.label) + ": ";
    src += std::string(kind.text) + "\n";
  }
  if (!labelled) {
    src +=
        "  initial ;\n  initial assert (a);\n  initial assume (a);\n  initial "
        "cover (a);\n";
  }
  return src + "endmodule\n";
}

class LabelsOfAtomicStatements : public VpiDesignRun {
 protected:
  static bool IsBlock(vpiHandle stmt) {
    const int kType = vpi_get(vpiType, stmt);
    return kType == vpiBegin || kType == vpiNamedBegin || kType == vpiFork ||
           kType == vpiNamedFork;
  }

  static void Walk(vpiHandle stmt, std::vector<vpiHandle>& out, int depth) {
    if (stmt == nullptr || depth > 8) return;
    out.push_back(stmt);
    Walk(vpi_handle(vpiStmt, stmt), out, depth + 1);
    Walk(vpi_handle(vpiElseStmt, stmt), out, depth + 1);
    for (vpiHandle inner : ObjectsOf(vpiStmt, stmt)) {
      Walk(inner, out, depth + 1);
    }
    for (vpiHandle item : ObjectsOf(vpiCaseItem, stmt)) {
      Walk(vpi_handle(vpiStmt, item), out, depth + 1);
    }
  }

  static std::vector<vpiHandle> StatementsOf(vpiHandle scope) {
    std::vector<vpiHandle> stmts;
    for (vpiHandle proc : ObjectsOf(vpiProcess, scope)) {
      Walk(vpi_handle(vpiStmt, proc), stmts, 0);
    }
    for (vpiHandle routine : ObjectsOf(vpiTaskFunc, scope)) {
      Walk(vpi_handle(vpiStmt, routine), stmts, 0);
    }
    return stmts;
  }

  static std::vector<vpiHandle> StatementsUnder(vpiHandle routine) {
    std::vector<vpiHandle> stmts;
    Walk(vpi_handle(vpiStmt, routine), stmts, 0);
    return stmts;
  }

  static std::string NameOf(vpiHandle obj) {
    const char* name = vpi_get_str(vpiName, obj);
    return name == nullptr ? "" : name;
  }

  static vpiHandle Labelled(const std::vector<vpiHandle>& stmts,
                            const std::string& label) {
    for (vpiHandle stmt : stmts) {
      if (!IsBlock(stmt) && NameOf(stmt) == label) return stmt;
    }
    return nullptr;
  }

  static vpiHandle FirstOfType(const std::vector<vpiHandle>& stmts, int type) {
    for (vpiHandle stmt : stmts) {
      if (vpi_get(vpiType, stmt) == type) return stmt;
    }
    return nullptr;
  }

  static void ExpectLabelled(const std::vector<vpiHandle>& stmts,
                             const char* label, int type) {
    vpiHandle stmt = Labelled(stmts, label);
    ASSERT_NE(stmt, nullptr) << label;
    EXPECT_EQ(vpi_get(vpiType, stmt), type) << label;
  }

  static void ExpectUnnamed(const std::vector<vpiHandle>& stmts, int type) {
    vpiHandle stmt = FirstOfType(stmts, type);
    ASSERT_NE(stmt, nullptr) << type;
    EXPECT_EQ(vpi_get_str(vpiName, stmt), nullptr) << type;
  }
};

TEST_F(LabelsOfAtomicStatements, ALabelledStatementOfEachKindIsNamedByIt) {
  Run(DesignOf(true));
  const std::vector<vpiHandle> kStmts = StatementsOf(By("top"));
  for (const StatementKind& kind : StatementKinds()) {
    ExpectLabelled(kStmts, kind.label, kind.type);
  }
  ExpectLabelled(kStmts, "l_return", vpiReturnStmt);
  ExpectLabelled(kStmts, "l_continue", vpiContinue);
  ExpectLabelled(kStmts, "l_break", vpiBreak);
  ExpectLabelled(kStmts, "l_forever", vpiForever);
}

TEST_F(LabelsOfAtomicStatements, AnUnlabelledStatementOfEachKindHasNoName) {
  Run(DesignOf(false));
  const std::vector<vpiHandle> kStmts = StatementsOf(By("top"));
  for (const StatementKind& kind : StatementKinds()) {
    ExpectUnnamed(kStmts, kind.type);
  }
  for (int type :
       {vpiReturnStmt, vpiContinue, vpiBreak, vpiForever, vpiNullStmt,
        vpiImmediateAssert, vpiImmediateAssume, vpiImmediateCover}) {
    ExpectUnnamed(kStmts, type);
  }
}

TEST_F(LabelsOfAtomicStatements, AnUnlabelledMethodTaskCallHasNoName) {
  Run("module top; class K; task mt; endtask endclass K h = new;\n"
      "  initial h.mt();\n"
      "endmodule\n");
  ExpectUnnamed(StatementsOf(By("top")), vpiMethodTaskCall);
}

constexpr const char* kLabelsEverywhere =
    "package pk; logic pv; task pt; l_pk: pv = 1; endtask endpackage\n"
    "interface ifc; logic v; initial l_ifc: v = 1; endinterface\n"
    "program prg; logic v; initial l_prg: v = 1; endprogram\n"
    "module top; logic v;\n"
    "  class C; logic m; task ct; l_cls: m = 1; endtask endclass\n"
    "  task tt; l_tsk: v = 1; endtask\n"
    "  function void ff; l_fn: v = 1; endfunction\n"
    "  ifc i0(); prg p0();\n"
    "endmodule\n";

TEST_F(LabelsOfAtomicStatements, ARoutinesLabelledStatementIsNamedByIt) {
  Run(kLabelsEverywhere);
  ExpectLabelled(StatementsUnder(Named(vpiTask, By("top"), "tt")), "l_tsk",
                 vpiAssignment);
  ExpectLabelled(StatementsUnder(Named(vpiFunction, By("top"), "ff")), "l_fn",
                 vpiAssignment);
}

TEST_F(LabelsOfAtomicStatements, AClassMethodsLabelledStatementIsNamedByIt) {
  Run(kLabelsEverywhere);
  ExpectLabelled(StatementsUnder(Named(
                     vpiMethods, Named(vpiClassDefn, By("top"), "C"), "ct")),
                 "l_cls", vpiAssignment);
}

TEST_F(LabelsOfAtomicStatements, APackageTasksLabelledStatementIsNamedByIt) {
  Run(kLabelsEverywhere);
  ExpectLabelled(StatementsUnder(Named(vpiTask, By("pk"), "pt")), "l_pk",
                 vpiAssignment);
}

TEST_F(LabelsOfAtomicStatements, AnInstancesLabelledStatementIsNamedByIt) {
  Run(kLabelsEverywhere);
  ExpectLabelled(StatementsOf(By("top.i0")), "l_ifc", vpiAssignment);
  ExpectLabelled(StatementsOf(By("top.p0")), "l_prg", vpiAssignment);
}

}  // namespace
}  // namespace delta
