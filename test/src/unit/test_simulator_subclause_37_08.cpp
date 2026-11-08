#include <gtest/gtest.h>

#include <algorithm>
#include <string>
#include <string_view>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_constants.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class InterfaceTfDecl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

TEST_F(InterfaceTfDecl, ForkJoinAccessTypeReportedVerbatim) {
  VpiObject tf_decl;
  tf_decl.type = vpiInterfaceTfDecl;
  tf_decl.access_type = vpiForkJoinAcc;

  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&tf_decl)), vpiForkJoinAcc);
}

TEST_F(InterfaceTfDecl, ExternAccessTypeReportedVerbatim) {
  VpiObject tf_decl;
  tf_decl.type = vpiInterfaceTfDecl;
  tf_decl.access_type = vpiExternAcc;

  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&tf_decl)), vpiExternAcc);
}

TEST_F(InterfaceTfDecl, OutOfDomainAccessTypeCollapsesToUndefined) {
  VpiObject odd;
  odd.type = vpiInterfaceTfDecl;
  odd.access_type = 99;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&odd)), vpiUndefined);

  VpiObject unset;
  unset.type = vpiInterfaceTfDecl;
  unset.access_type = 0;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&unset)), vpiUndefined);
}

TEST_F(InterfaceTfDecl, ClampIsScopedToInterfaceTfDecl) {
  VpiObject task;
  task.type = vpiTask;
  task.access_type = 99;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&task)), 99);
}

TEST_F(InterfaceTfDecl, AnObjectDrawnWithNoAccessTypeReportsNone) {
  VpiObject net;
  net.type = kVpiNet;
  net.access_type = 99;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&net)), vpiUndefined);
}

class InterfaceTfDeclOfARun : public VpiDesignRun {
 protected:
  static std::vector<std::string> DefinitionsOf(vpiHandle iface,
                                                std::string_view name,
                                                int relation) {
    std::vector<std::string> defs;
    for (vpiHandle decl : ObjectsOf(vpiInterfaceTfDecl, iface)) {
      if (name != vpi_get_str(vpiName, decl)) continue;
      vpiHandle tf = vpi_handle(relation, decl);
      defs.emplace_back(tf == nullptr ? "" : vpi_get_str(vpiFullName, tf));
    }
    std::ranges::sort(defs);
    return defs;
  }

  static std::vector<int> AccessOf(vpiHandle iface, std::string_view name) {
    std::vector<int> access;
    for (vpiHandle decl : ObjectsOf(vpiInterfaceTfDecl, iface)) {
      if (name == vpi_get_str(vpiName, decl)) {
        access.push_back(vpi_get(vpiAccessType, decl));
      }
    }
    return access;
  }
};

TEST_F(InterfaceTfDeclOfARun, AnInterfaceReachesADeclPerDefinitionOfItsTfs) {
  Run("interface bus;\n"
      "  extern task Load(input int x);\n"
      "  extern task Idle();\n"
      "  extern forkjoin task Ping();\n"
      "  extern forkjoin task Wait();\n"
      "  function int Own(); return 1; endfunction\n"
      "  modport tgt(export Load, export Ping, export Peek);\n"
      "  modport pinger(export Ping, import Own);\n"
      "endinterface\n"
      "module mem(bus.tgt b);\n"
      "  int seen;\n"
      "  task b.Load(input int x); seen = x; endtask\n"
      "  task b.Ping(); endtask\n"
      "  function int b.Peek(); return seen; endfunction\n"
      "endmodule\n"
      "module echo(bus.pinger p);\n"
      "  task p.Ping(); endtask\n"
      "endmodule\n"
      "module top; bus i(); mem m(i); echo e(i); endmodule\n");
  vpiHandle iface = By("top.i");
  ASSERT_NE(iface, nullptr);
  EXPECT_EQ(NamesOf(vpiInterfaceTfDecl, iface),
            (std::vector<std::string>{"Idle", "Load", "Peek", "Ping", "Ping",
                                      "Wait"}));
  EXPECT_EQ(DefinitionsOf(iface, "Load", vpiTask),
            std::vector<std::string>{"top.m.Load"});
  EXPECT_EQ(DefinitionsOf(iface, "Load", vpiFunction),
            std::vector<std::string>{""});
  EXPECT_EQ(AccessOf(iface, "Load"), std::vector<int>{vpiExternAcc});
  EXPECT_EQ(DefinitionsOf(iface, "Idle", vpiTask),
            std::vector<std::string>{""});
  EXPECT_EQ(DefinitionsOf(iface, "Ping", vpiTask),
            (std::vector<std::string>{"top.e.Ping", "top.m.Ping"}));
  EXPECT_EQ(AccessOf(iface, "Ping"),
            (std::vector<int>{vpiForkJoinAcc, vpiForkJoinAcc}));
  EXPECT_EQ(DefinitionsOf(iface, "Peek", vpiFunction),
            std::vector<std::string>{"top.m.Peek"});
  EXPECT_EQ(DefinitionsOf(iface, "Peek", vpiTask),
            std::vector<std::string>{""});
  EXPECT_EQ(AccessOf(iface, "Peek"), std::vector<int>{vpiExternAcc});
  EXPECT_EQ(DefinitionsOf(iface, "Wait", vpiTask),
            std::vector<std::string>{""});
  EXPECT_EQ(AccessOf(iface, "Wait"), std::vector<int>{vpiForkJoinAcc});
}

}  // namespace
}  // namespace delta
