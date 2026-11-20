#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class Modport : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }
  VpiContext ctx_;
};

TEST_F(Modport, ReportsItsNameViaVpiName) {
  VpiObject modport;
  modport.type = vpiModport;
  modport.name = "phy";

  EXPECT_STREQ(vpi_get_str(vpiName, VpiHandleOf(&modport)), "phy");
}

TEST_F(Modport, InterfaceAndModportTraverseBothWays) {
  VpiObject iface;
  iface.type = vpiInterface;

  VpiObject modport;
  modport.type = vpiModport;
  modport.name = "phy";
  modport.parent = &iface;
  iface.children = {&modport};

  vpiHandle iter = vpi_iterate(vpiModport, VpiHandleOf(&iface));
  ASSERT_NE(iter, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_scan(iter)), &modport);
  EXPECT_EQ(vpi_scan(iter), nullptr);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInterface, VpiHandleOf(&modport))),
            &iface);
}

TEST_F(Modport, ModportAndIoDeclTraverseBothWays) {
  VpiObject modport;
  modport.type = vpiModport;

  VpiObject in_decl;
  in_decl.type = vpiIODecl;
  in_decl.parent = &modport;
  VpiObject out_decl;
  out_decl.type = vpiIODecl;
  out_decl.parent = &modport;
  modport.children = {&in_decl, &out_decl};

  vpiHandle iter = vpi_iterate(vpiIODecl, VpiHandleOf(&modport));
  ASSERT_NE(iter, nullptr);
  int count = 0;
  while (vpi_scan(iter) != nullptr) ++count;
  EXPECT_EQ(count, 2);

  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, VpiHandleOf(&in_decl))),
            &modport);
}

TEST_F(Modport, ModportWithNoIoDeclsIteratesToNone) {
  VpiObject modport;
  modport.type = vpiModport;

  EXPECT_EQ(vpi_iterate(vpiIODecl, VpiHandleOf(&modport)), nullptr);
}

TEST_F(Modport, ModportWithoutEnclosingInterfaceReachesNone) {
  VpiObject modport;
  modport.type = vpiModport;

  EXPECT_EQ(vpi_handle(vpiInterface, VpiHandleOf(&modport)), nullptr);
}

TEST_F(Modport, InterfaceWithNoModportsIteratesToNone) {
  VpiObject iface;
  iface.type = vpiInterface;

  EXPECT_EQ(vpi_iterate(vpiModport, VpiHandleOf(&iface)), nullptr);
}

TEST_F(Modport, IoDeclWithoutEnclosingModportReachesNone) {
  VpiObject io_decl;
  io_decl.type = vpiIODecl;

  EXPECT_EQ(vpi_handle(vpiModport, VpiHandleOf(&io_decl)), nullptr);
}

class ModportsOfARun : public VpiDesignRun {
 protected:
  static constexpr const char* kTwoModports =
      "interface ifc; logic a, b;\n"
      "  modport mp(input a, output b);\n"
      "  modport mq(input b);\n"
      "endinterface\n"
      "module top; ifc i0(); endmodule\n";

  static std::vector<std::string> ScannedNames(int type, vpiHandle ref) {
    std::vector<std::string> names;
    vpiHandle it = vpi_iterate(type, ref);
    if (it == nullptr) return names;
    while (vpiHandle obj = vpi_scan(it)) {
      names.emplace_back(vpi_get_str(vpiName, obj));
    }
    return names;
  }

  static vpiHandle Instance() {
    return vpi_handle_by_name(VpiText("top.i0"), nullptr);
  }
};

TEST_F(ModportsOfARun, AnInterfaceInstanceIteratesItsModports) {
  Run(kTwoModports);
  EXPECT_EQ(ScannedNames(vpiModport, Instance()),
            (std::vector<std::string>{"mp", "mq"}));
}

TEST_F(ModportsOfARun, AModportReachesItsInterfaceInstance) {
  Run(kTwoModports);
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  ASSERT_NE(mp, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInterface, mp)), VpiObjectOf(Instance()));
}

TEST_F(ModportsOfARun, AModportIteratesItsIoDecls) {
  Run(kTwoModports);
  EXPECT_EQ(ScannedNames(vpiIODecl, Named(vpiModport, Instance(), "mp")),
            (std::vector<std::string>{"a", "b"}));
  EXPECT_EQ(ScannedNames(vpiIODecl, Named(vpiModport, Instance(), "mq")),
            (std::vector<std::string>{"b"}));
}

TEST_F(ModportsOfARun, AnIoDeclReportsItsModportsDirection) {
  Run(kTwoModports);
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  vpiHandle mq = Named(vpiModport, Instance(), "mq");
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mp, "a")), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mp, "b")), vpiOutput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mq, "b")), vpiInput);
}

TEST_F(ModportsOfARun, AnIoDeclOfARefPortReportsVpiRef) {
  Run("interface ifc; logic a; modport mr(ref a); endinterface\n"
      "module top; ifc i0(); endmodule\n");
  vpiHandle mr = Named(vpiModport, Instance(), "mr");
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mr, "a")), vpiRef);
}

TEST_F(ModportsOfARun, AnIoDeclOfAnInoutPortReportsVpiInout) {
  Run("interface ifc; wire w; modport mb(inout w); endinterface\n"
      "module top; ifc i0(); endmodule\n");
  vpiHandle mb = Named(vpiModport, Instance(), "mb");
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mb, "w")), vpiInout);
}

TEST_F(ModportsOfARun, AModportsClockingBlockIsNoIoDecl) {
  Run("interface ifc; logic a;\n"
      "  extern task put();\n"
      "  task get(); endtask\n"
      "  clocking cb @(posedge a); endclocking\n"
      "  modport mp(input a, import get, export put, clocking cb);\n"
      "endinterface\n"
      "module tgt(ifc.mp b); task b.put(); endtask endmodule\n"
      "module top; ifc i0(); tgt t(i0.mp); endmodule\n");
  EXPECT_EQ(ScannedNames(vpiIODecl, Named(vpiModport, Instance(), "mp")),
            (std::vector<std::string>{"a", "get", "put"}));
}

TEST_F(ModportsOfARun, AnIoDeclReachesItsModport) {
  Run(kTwoModports);
  vpiHandle mq = Named(vpiModport, Instance(), "mq");
  ASSERT_NE(mq, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, Named(vpiIODecl, mq, "b"))),
            VpiObjectOf(mq));
}

TEST_F(ModportsOfARun, AModuleInstanceHasNoModports) {
  Run(kTwoModports);
  EXPECT_EQ(
      vpi_iterate(vpiModport, vpi_handle_by_name(VpiText("top"), nullptr)),
      nullptr);
}

TEST_F(ModportsOfARun, PrototypedImportsAndExportsAreIoDeclsByName) {
  Run("interface ifc;\n"
      "  task t(); endtask\n"
      "  function int g(int a); return a; endfunction\n"
      "  extern function int f(int a);\n"
      "  modport mp(import task t(), import g,\n"
      "             export function int f(int a));\n"
      "endinterface\n"
      "module tgt(ifc.mp b);\n"
      "  function int b.f(int a); return a; endfunction\n"
      "endmodule\n"
      "module top; ifc i0(); tgt u(i0.mp); endmodule\n");
  EXPECT_EQ(ScannedNames(vpiIODecl, Named(vpiModport, Instance(), "mp")),
            (std::vector<std::string>{"t", "g", "f"}));
}

TEST_F(ModportsOfARun, NamesUnderOneDirectionEachGiveAnIoDecl) {
  Run("interface ifc; logic a, b, c;\n"
      "  modport mp(input a, b, output c);\n"
      "endinterface\n"
      "module top; ifc i0(); endmodule\n");
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  EXPECT_EQ(ScannedNames(vpiIODecl, mp),
            (std::vector<std::string>{"a", "b", "c"}));
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mp, "b")), vpiInput);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, mp, "c")), vpiOutput);
}

TEST_F(ModportsOfARun, AModportListingOnlyAClockingBlockHasNoIoDecls) {
  Run("interface ifc(input logic clk);\n"
      "  clocking cb @(posedge clk); endclocking\n"
      "  modport mp(clocking cb);\n"
      "endinterface\n"
      "module top; logic clk; ifc i0(clk); endmodule\n");
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  ASSERT_NE(mp, nullptr);
  EXPECT_EQ(vpi_iterate(vpiIODecl, mp), nullptr);
}

TEST_F(ModportsOfARun, AnIoDeclNoModportListsReachesNoModport) {
  Run("module top(input logic p);\n"
      "  task t(input int x); endtask\n"
      "endmodule\n");
  vpiHandle top = vpi_handle_by_name(VpiText("top"), nullptr);
  std::vector<vpiHandle> ports = ObjectsOf(vpiIODecl, top);
  ASSERT_EQ(ports.size(), 1U);
  EXPECT_EQ(vpi_handle(vpiModport, ports[0]), nullptr);
  std::vector<vpiHandle> tasks = ObjectsOf(vpiTaskFunc, top);
  ASSERT_EQ(tasks.size(), 1U);
  std::vector<vpiHandle> args = ObjectsOf(vpiIODecl, tasks[0]);
  ASSERT_EQ(args.size(), 1U);
  EXPECT_EQ(vpi_handle(vpiModport, args[0]), nullptr);
}

TEST_F(ModportsOfARun, AnImportedOrExportedIoDeclReachesItsModport) {
  Run("interface ifc;\n"
      "  task get(); endtask\n"
      "  extern task put();\n"
      "  modport mp(import get, export put);\n"
      "endinterface\n"
      "module tgt(ifc.mp b); task b.put(); endtask endmodule\n"
      "module top; ifc i0(); tgt u(i0.mp); endmodule\n");
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  ASSERT_NE(mp, nullptr);
  for (const char* name : {"get", "put"}) {
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, Named(vpiIODecl, mp, name))),
              VpiObjectOf(mp))
        << name;
  }
}

TEST_F(ModportsOfARun, AModportExpressionsIoDeclReachesItsModport) {
  Run("interface ifc; logic [3:0] r;\n"
      "  modport mp(input .p(r[1:0]));\n"
      "endinterface\n"
      "module top; ifc i0(); endmodule\n");
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  ASSERT_NE(mp, nullptr);
  vpiHandle p = Named(vpiIODecl, mp, "p");
  ASSERT_NE(p, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, p)), VpiObjectOf(mp));
}

TEST_F(ModportsOfARun, APortListedTwiceReachesEachListingModport) {
  Run(kTwoModports);
  vpiHandle mp = Named(vpiModport, Instance(), "mp");
  vpiHandle mq = Named(vpiModport, Instance(), "mq");
  ASSERT_NE(mp, nullptr);
  ASSERT_NE(mq, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, Named(vpiIODecl, mp, "b"))),
            VpiObjectOf(mp));
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiModport, Named(vpiIODecl, mq, "b"))),
            VpiObjectOf(mq));
}

TEST_F(ModportsOfARun, AnArrayElementsModportReachesThatElement) {
  Run("interface ifc; logic a; modport mp(input a); endinterface\n"
      "module top; ifc i0[2](); endmodule\n");
  vpiHandle element = vpi_handle_by_name(VpiText("top.i0[1]"), nullptr);
  vpiHandle mp = Named(vpiModport, element, "mp");
  ASSERT_NE(mp, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInterface, mp)), VpiObjectOf(element));
}

TEST_F(ModportsOfARun, ANestedInstancesModportReachesThatInstance) {
  Run("interface ifc; logic a; modport mp(input a); endinterface\n"
      "interface outer; ifc n(); endinterface\n"
      "module mid; ifc i0(); endmodule\n"
      "module top; mid u(); outer o(); endmodule\n");
  for (const char* path : {"top.u.i0", "top.o.n"}) {
    vpiHandle inst = vpi_handle_by_name(VpiText(path), nullptr);
    vpiHandle mp = Named(vpiModport, inst, "mp");
    ASSERT_NE(mp, nullptr) << path;
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiInterface, mp)), VpiObjectOf(inst))
        << path;
  }
}

TEST_F(ModportsOfARun, ARunModportIsAVpiModport) {
  Run(kTwoModports);
  EXPECT_EQ(vpi_get(vpiType, Named(vpiModport, Instance(), "mp")), vpiModport);
}

TEST_F(ModportsOfARun, CommaListedModportsAreEachTheirOwnObject) {
  Run("interface ifc; logic x; modport a(input x), b(output x); endinterface\n"
      "module top; ifc i0(); endmodule\n");
  EXPECT_EQ(ScannedNames(vpiModport, Instance()),
            (std::vector<std::string>{"a", "b"}));
  vpiHandle b = Named(vpiModport, Instance(), "b");
  EXPECT_EQ(vpi_get(vpiType, b), vpiModport);
  EXPECT_EQ(vpi_get(vpiDirection, Named(vpiIODecl, b, "x")), vpiOutput);
}

}  // namespace
}  // namespace delta
