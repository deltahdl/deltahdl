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

class InterfaceTfDeclIterationsOfARun : public VpiDesignRun {
 protected:
  void SetUp() override {
    VpiDesignRun::SetUp();
    Run("interface bus;\n"
        "  extern task Load(input int x);\n"
        "  extern task Idle();\n"
        "  extern function int Get();\n"
        "  extern forkjoin task Ping();\n"
        "  extern forkjoin task Solo();\n"
        "  extern forkjoin task Wait();\n"
        "  modport tgt(export Load, export Get, export Ping, export Solo,\n"
        "              export Peek, export task T(input int x),\n"
        "              export function int F());\n"
        "  modport pinger(export Ping);\n"
        "endinterface\n"
        "module mem(bus.tgt b);\n"
        "  int seen;\n"
        "  task b.Load(input int x); seen = x; endtask\n"
        "  function int b.Get(); return seen; endfunction\n"
        "  task b.Ping(); endtask\n"
        "  task b.Solo(); endtask\n"
        "  function int b.Peek(); return seen; endfunction\n"
        "  task b.T(input int x); seen = x; endtask\n"
        "  function int b.F(); return seen; endfunction\n"
        "endmodule\n"
        "module echo(bus.pinger p);\n"
        "  task p.Ping(); endtask\n"
        "endmodule\n"
        "module top; bus i(); mem m(i.tgt); echo e(i.pinger); endmodule\n");
  }

  static std::vector<std::vector<std::string>> PerDecl(std::string_view name,
                                                       int relation) {
    std::vector<std::vector<std::string>> per_decl;
    for (vpiHandle decl : ObjectsOf(vpiInterfaceTfDecl, By("top.i"))) {
      if (name != vpi_get_str(vpiName, decl)) continue;
      std::vector<std::string> defs;
      if (vpiHandle it = vpi_iterate(relation, decl)) {
        while (vpiHandle tf = vpi_scan(it)) {
          defs.emplace_back(vpi_get_str(vpiFullName, tf));
        }
      }
      std::ranges::sort(defs);
      per_decl.push_back(defs);
    }
    return per_decl;
  }

  static int AccessOf(std::string_view name) {
    for (vpiHandle decl : ObjectsOf(vpiInterfaceTfDecl, By("top.i"))) {
      if (name == vpi_get_str(vpiName, decl)) {
        return vpi_get(vpiAccessType, decl);
      }
    }
    return vpiUndefined;
  }

  using Defs = std::vector<std::vector<std::string>>;
};

TEST_F(InterfaceTfDeclIterationsOfARun,
       DISABLED_AnInterfaceHasOneDeclPerDeclaredSubroutine) {
  EXPECT_EQ(NamesOf(vpiInterfaceTfDecl, By("top.i")),
            (std::vector<std::string>{"F", "Get", "Idle", "Load", "Peek",
                                      "Ping", "Solo", "T", "Wait"}));
}

TEST_F(InterfaceTfDeclIterationsOfARun,
       DISABLED_ATaskDefinedOnceIteratesThatDefinition) {
  EXPECT_EQ(PerDecl("Load", vpiTask), (Defs{{"top.m.Load"}}));
  EXPECT_EQ(PerDecl("Solo", vpiTask), (Defs{{"top.m.Solo"}}));
  EXPECT_EQ(PerDecl("T", vpiTask), (Defs{{"top.m.T"}}));
}

TEST_F(InterfaceTfDeclIterationsOfARun,
       DISABLED_AForkJoinTaskIteratesEveryDefinition) {
  EXPECT_EQ(PerDecl("Ping", vpiTask), (Defs{{"top.e.Ping", "top.m.Ping"}}));
}

TEST_F(InterfaceTfDeclIterationsOfARun,
       AnUndefinedTaskOrAFunctionIteratesNoTask) {
  for (const char* name : {"Wait", "Idle", "Get", "Peek", "F"}) {
    EXPECT_EQ(PerDecl(name, vpiTask), (Defs{{}})) << name;
  }
}

TEST_F(InterfaceTfDeclIterationsOfARun,
       DISABLED_AFunctionDeclIteratesItsDefinition) {
  EXPECT_EQ(PerDecl("Peek", vpiFunction), (Defs{{"top.m.Peek"}}));
  EXPECT_EQ(PerDecl("Get", vpiFunction), (Defs{{"top.m.Get"}}));
  EXPECT_EQ(PerDecl("F", vpiFunction), (Defs{{"top.m.F"}}));
}

TEST_F(InterfaceTfDeclIterationsOfARun, ATaskDeclIteratesNoFunction) {
  for (const char* name : {"Load", "Solo", "T", "Idle"}) {
    EXPECT_EQ(PerDecl(name, vpiFunction), (Defs{{}})) << name;
  }
}

TEST_F(InterfaceTfDeclIterationsOfARun,
       ExternFunctionsAndPrototypedExportsAreExtern) {
  for (const char* name : {"Get", "T", "F"}) {
    EXPECT_EQ(AccessOf(name), vpiExternAcc) << name;
  }
  EXPECT_EQ(AccessOf("Solo"), vpiForkJoinAcc);
}

}  // namespace
}  // namespace delta
