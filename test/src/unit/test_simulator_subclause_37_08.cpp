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

// §37.8 Interface task or function declaration: the VPI object model for an
// "interface tf decl", which a design run builds for each subroutine an
// interface declares and a connected module defines (§25.7), reached from the
// interface (§37.6) and reaching the definition through vpiTask or vpiFunction:
//   D1 - an extern forkjoin task is one decl per module instance defining it,
//        so vpi_iterate yields more than one for it.
//   D2 - the access type reported for an interface tf decl is only ever
//        vpiForkJoinAcc or vpiExternAcc; no third value escapes the property.

class InterfaceTfDecl : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// D2: a fork-join access type is one of the two legal values and is reported
// back unchanged.
TEST_F(InterfaceTfDecl, ForkJoinAccessTypeReportedVerbatim) {
  VpiObject tf_decl;
  tf_decl.type = vpiInterfaceTfDecl;
  tf_decl.access_type = vpiForkJoinAcc;

  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&tf_decl)), vpiForkJoinAcc);
}

// D2: an extern access type is the other legal value and is also reported back
// unchanged.
TEST_F(InterfaceTfDecl, ExternAccessTypeReportedVerbatim) {
  VpiObject tf_decl;
  tf_decl.type = vpiInterfaceTfDecl;
  tf_decl.access_type = vpiExternAcc;

  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&tf_decl)), vpiExternAcc);
}

// D2: any other stored value is not a legal access type for an interface tf
// decl, so the property collapses to vpiUndefined rather than leaking a third
// value - including the zero/unset default.
TEST_F(InterfaceTfDecl, OutOfDomainAccessTypeCollapsesToUndefined) {
  VpiObject odd;
  odd.type = vpiInterfaceTfDecl;
  odd.access_type = 99;  // neither vpiForkJoinAcc nor vpiExternAcc
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&odd)), vpiUndefined);

  VpiObject unset;
  unset.type = vpiInterfaceTfDecl;
  unset.access_type = 0;  // default, still not a legal access type
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&unset)), vpiUndefined);
}

// D2 scope guard: the interface-tf-decl clamp is keyed on the object type, so
// the other objects the property is drawn on keep their own rules. §37.41
// draws it on the `task func` enclosure, and a task there reports the access it
// was declared with rather than this clause's two values.
TEST_F(InterfaceTfDecl, ClampIsScopedToInterfaceTfDecl) {
  VpiObject task;
  task.type = vpiTask;
  task.access_type = 99;  // would be clamped if the guard were not type-keyed
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&task)), 99);
}

// The property is drawn on the interface tf decl, on §37.34's constraint and on
// §37.41's task func enclosure, and on nothing else. An object the data model
// gives no access type reports none, rather than handing back a number the
// diagrams never gave it.
TEST_F(InterfaceTfDecl, AnObjectDrawnWithNoAccessTypeReportsNone) {
  VpiObject net;
  net.type = kVpiNet;
  net.access_type = 99;
  EXPECT_EQ(vpi_get(vpiAccessType, VpiHandleOf(&net)), vpiUndefined);
}

// A design run whose interface instance is read back for the interface tf
// decls §37.6 draws it reaching.
class InterfaceTfDeclOfARun : public VpiDesignRun {
 protected:
  // The full names of what each interface tf decl of `iface` named `name`
  // reaches through `relation`, vpiTask or vpiFunction, sorted, an empty name
  // for a decl reaching none.
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

  // The access types of the interface tf decls of `iface` named `name`.
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

// §37.6 with §25.7: an interface reaches an interface tf decl for each task or
// function it declares extern, or a modport of it exports, for a connected
// module to define: Load and Peek, of vpiExternAcc, each reaching the
// definition in m, and Idle, which no module defines, reaching none. D1: the
// extern forkjoin Ping is defined by both m and e (§25.7.4), so it is two decls
// of vpiForkJoinAcc, one per definition, and Wait, defined by none, one
// reaching none. Own, which the interface defines itself and a modport imports,
// is no such declaration. A task reaches no function, nor a function a task.
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

// §37.6 with §25.7.4: an interface standing as the design's top has no module
// connected to it, so its extern forkjoin task is one decl reaching no task.
TEST_F(InterfaceTfDeclOfARun, AnUnconnectedInterfaceReachesADeclOfNoTask) {
  Run("interface solo; extern forkjoin task Ping(); endinterface\n");
  vpiHandle iface = By("solo");
  ASSERT_NE(iface, nullptr);
  EXPECT_EQ(DefinitionsOf(iface, "Ping", vpiTask),
            std::vector<std::string>{""});
  EXPECT_EQ(AccessOf(iface, "Ping"), std::vector<int>{vpiForkJoinAcc});
}

}  // namespace
}  // namespace delta
