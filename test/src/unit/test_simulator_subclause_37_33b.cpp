#include <gtest/gtest.h>

#include <set>
#include <string>
#include <vector>

#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ClassVarsAndObjectsOfARun : public VpiDesignRun {
 protected:
  static void ExpectReportsItsObjectsId(vpiHandle var,
                                        const std::string& name) {
    ASSERT_NE(var, nullptr) << name;
    vpiHandle obj = vpi_handle(vpiClassObj, var);
    ASSERT_NE(obj, nullptr) << name;
    EXPECT_NE(vpi_get64(vpiObjId, obj), 0) << name;
    EXPECT_EQ(vpi_get64(vpiObjId, var), vpi_get64(vpiObjId, obj)) << name;
  }

  static void ExpectReportsNoObject(vpiHandle var, const std::string& name) {
    ASSERT_NE(var, nullptr) << name;
    EXPECT_EQ(vpi_handle(vpiClassObj, var), nullptr) << name;
    EXPECT_EQ(vpi_get64(vpiObjId, var), 0) << name;
  }

  static void ExpectDeclaredWith(vpiHandle var, vpiHandle defn,
                                 const std::string& name) {
    ASSERT_NE(var, nullptr) << name;
    ASSERT_NE(defn, nullptr) << name;
    EXPECT_EQ(VpiObjectOf(
                  vpi_handle(vpiClassDefn, vpi_handle(vpiClassTypespec, var))),
              VpiObjectOf(defn))
        << name;
  }

  static int WaitersOf(const char* name) {
    return static_cast<int>(
        ObjectsOf(vpiWaitingProcesses, vpi_handle(vpiClassObj, By(name)))
            .size());
  }
};

TEST_F(ClassVarsAndObjectsOfARun, AnAssignedClassVarReportsTheSharedObjectsId) {
  Run("module top; class A; endclass\n"
      "  A d = new;\n"
      "  A c;\n"
      "  initial c = d;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.d"));
  ASSERT_NE(obj, nullptr);
  EXPECT_NE(vpi_get64(vpiObjId, By("top.c")), 0);
  EXPECT_EQ(vpi_get64(vpiObjId, By("top.c")), vpi_get64(vpiObjId, obj));
  EXPECT_EQ(vpi_get64(vpiObjId, By("top.c")), vpi_get64(vpiObjId, By("top.d")));
}

TEST_F(ClassVarsAndObjectsOfARun, AClassTypedPropertyReportsItsObjectsId) {
  Run("module top; class B; endclass\n"
      "  class A; B b = new; B n; endclass\n"
      "  A a = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.a"));
  ASSERT_NE(obj, nullptr);
  vpiHandle b = Named(vpiVariables, obj, "b");
  ASSERT_NE(b, nullptr);
  vpiHandle held = vpi_handle(vpiClassObj, b);
  ASSERT_NE(held, nullptr);
  EXPECT_NE(vpi_get64(vpiObjId, b), 0);
  EXPECT_EQ(vpi_get64(vpiObjId, b), vpi_get64(vpiObjId, held));
  EXPECT_NE(vpi_get64(vpiObjId, held), vpi_get64(vpiObjId, obj));
  vpiHandle n = Named(vpiVariables, obj, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(vpi_get64(vpiObjId, n), 0);
}

TEST_F(ClassVarsAndObjectsOfARun, APackageClassVarReportsItsObjectsId) {
  Run("package pk; class P; endclass P pv = new; P pn; endpackage\n"
      "module top; endmodule\n");
  ExpectReportsItsObjectsId(By("pk::pv"), "pk::pv");
  ExpectReportsNoObject(By("pk::pn"), "pk::pn");
}

TEST_F(ClassVarsAndObjectsOfARun,
       DISABLED_APackageClassVarReachesItsDeclaredTypespec) {
  Run("package pk; class P; endclass P pv = new; P pn; endpackage\n"
      "module top; endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("pk"), "P");
  ExpectDeclaredWith(By("pk::pv"), defn, "pk::pv");
  ExpectDeclaredWith(By("pk::pn"), defn, "pk::pn");
}

TEST_F(ClassVarsAndObjectsOfARun, AUnitClassVarReportsItsObjectsId) {
  Run("class C; endclass\n"
      "C uv = new;\n"
      "C un;\n"
      "module top; endmodule\n");
  vpiHandle unit = Named(vpiPackage, nullptr, "$unit");
  ASSERT_NE(unit, nullptr);
  ExpectReportsItsObjectsId(Named(vpiVariables, unit, "uv"), "uv");
  ExpectReportsNoObject(Named(vpiVariables, unit, "un"), "un");
}

TEST_F(ClassVarsAndObjectsOfARun,
       DISABLED_AUnitClassVarReachesItsDeclaredTypespec) {
  Run("class C; endclass\n"
      "C uv = new;\n"
      "C un;\n"
      "module top; endmodule\n");
  vpiHandle unit = Named(vpiPackage, nullptr, "$unit");
  ASSERT_NE(unit, nullptr);
  vpiHandle defn = Named(vpiClassDefn, nullptr, "C");
  ExpectDeclaredWith(Named(vpiVariables, unit, "uv"), defn, "uv");
  ExpectDeclaredWith(Named(vpiVariables, unit, "un"), defn, "un");
}

TEST_F(ClassVarsAndObjectsOfARun, AProgramClassVarReportsItsObjectsId) {
  Run("program pg; class G; endclass G gv = new; G gn; endprogram\n");
  ExpectReportsItsObjectsId(By("pg.gv"), "pg.gv");
  ExpectReportsNoObject(By("pg.gn"), "pg.gn");
}

TEST_F(ClassVarsAndObjectsOfARun, AProgramClassVarReachesItsDeclaredTypespec) {
  Run("program pg; class G; endclass G gv = new; G gn; endprogram\n");
  vpiHandle defn = Named(vpiClassDefn, By("pg"), "G");
  ExpectDeclaredWith(By("pg.gv"), defn, "pg.gv");
  ExpectDeclaredWith(By("pg.gn"), defn, "pg.gn");
}

TEST_F(ClassVarsAndObjectsOfARun,
       DISABLED_ANamedBlockClassVarReportsItsObjectsId) {
  Run("module top; class C; endclass\n"
      "  initial begin : blk static C bv = new; C bn; end\n"
      "endmodule\n");
  ExpectReportsItsObjectsId(By("top.blk.bv"), "top.blk.bv");
  ExpectReportsNoObject(By("top.blk.bn"), "top.blk.bn");
}

TEST_F(ClassVarsAndObjectsOfARun,
       DISABLED_ANamedBlockClassVarReachesItsDeclaredTypespec) {
  Run("module top; class C; endclass\n"
      "  initial begin : blk static C bv = new; C bn; end\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ExpectDeclaredWith(By("top.blk.bv"), defn, "top.blk.bv");
  ExpectDeclaredWith(By("top.blk.bn"), defn, "top.blk.bn");
}

TEST_F(ClassVarsAndObjectsOfARun,
       ATypedefDeclaredModuleClassVarReachesItsClass) {
  Run("module top; class C; endclass typedef C T;\n"
      "  T v;\n"
      "  T w = new;\n"
      "endmodule\n");
  vpiHandle defn = Named(vpiClassDefn, By("top"), "C");
  ASSERT_NE(defn, nullptr);
  vpiHandle typespec = vpi_handle(vpiClassTypespec, By("top.v"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "C");
  ExpectDeclaredWith(By("top.v"), defn, "top.v");
  ExpectDeclaredWith(By("top.w"), defn, "top.w");
  EXPECT_EQ(
      VpiObjectOf(vpi_handle(
          vpiClassDefn,
          vpi_handle(vpiClassTypespec, vpi_handle(vpiClassObj, By("top.w"))))),
      VpiObjectOf(defn));
}

TEST_F(ClassVarsAndObjectsOfARun, EveryLiveObjectReportsItsOwnId) {
  Run("module top; class A; endclass\n"
      "  A a = new; A b = new;\n"
      "  mailbox m = new; mailbox n = new;\n"
      "  semaphore s = new; semaphore t = new;\n"
      "endmodule\n");
  std::set<PLI_INT64> ids;
  for (const char* name :
       {"top.a", "top.b", "top.m", "top.n", "top.s", "top.t"}) {
    vpiHandle obj = vpi_handle(vpiClassObj, By(name));
    ASSERT_NE(obj, nullptr) << name;
    const PLI_INT64 kId = vpi_get64(vpiObjId, obj);
    EXPECT_NE(kId, 0) << name;
    ids.insert(kId);
  }
  EXPECT_EQ(ids.size(), 6U);
}

TEST_F(ClassVarsAndObjectsOfARun, AnObjectMadeAfterOneIsDroppedHasAnId) {
  Run("module top; class A; int n; endclass\n"
      "  A a = new;\n"
      "  initial begin a = null; a = new; a.n = 4; end\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.a"));
  ASSERT_NE(obj, nullptr);
  const PLI_INT64 kId = vpi_get64(vpiObjId, obj);
  const PLI_INT32 kError = vpi_chk_error(nullptr);
  EXPECT_NE(kId, 0);
  EXPECT_EQ(kError, 0);
  EXPECT_EQ(IntegerOf(Named(vpiVariables, obj, "n")), 4);
}

TEST_F(ClassVarsAndObjectsOfARun, EachWaitingForkBranchIsItsOwnThread) {
  Run("module top; mailbox e = new; semaphore s = new(0);\n"
      "  initial fork\n"
      "    begin int x; e.get(x); end\n"
      "    begin int y; e.get(y); end\n"
      "  join_none\n"
      "  initial fork s.get(1); s.get(1); join_none\n"
      "endmodule\n");
  for (const char* name : {"top.e", "top.s"}) {
    const std::vector<vpiHandle> kWaiting =
        ObjectsOf(vpiWaitingProcesses, vpi_handle(vpiClassObj, By(name)));
    ASSERT_EQ(kWaiting.size(), 2U) << name;
    EXPECT_EQ(vpi_get(vpiType, kWaiting[0]), vpiThread) << name;
    EXPECT_EQ(vpi_get(vpiType, kWaiting[1]), vpiThread) << name;
    EXPECT_NE(VpiObjectOf(kWaiting[0]), VpiObjectOf(kWaiting[1])) << name;
  }
}

TEST_F(ClassVarsAndObjectsOfARun, AProcessPeekingAnEmptyMailboxIsWaiting) {
  Run("module top; mailbox e = new;\n"
      "  initial begin int x; e.peek(x); end\n"
      "endmodule\n");
  EXPECT_EQ(WaitersOf("top.e"), 1);
}

TEST_F(ClassVarsAndObjectsOfARun, AProcessPuttingToAFullMailboxIsWaiting) {
  Run("module top; mailbox b = new(1);\n"
      "  initial begin b.put(1); b.put(2); end\n"
      "endmodule\n");
  EXPECT_EQ(WaitersOf("top.b"), 1);
  EXPECT_EQ(IntsOf(vpiMessages, vpi_handle(vpiClassObj, By("top.b"))),
            std::vector<int>{1});
}

TEST_F(ClassVarsAndObjectsOfARun, AProcessWhoseWaitEndedIsNotWaiting) {
  Run("module top; mailbox e = new; semaphore s = new(0);\n"
      "  mailbox b = new(1);\n"
      "  initial begin int x; e.get(x); end\n"
      "  initial #1 e.put(4);\n"
      "  initial s.get(1);\n"
      "  initial #1 s.put(1);\n"
      "  initial begin b.put(1); b.put(2); end\n"
      "  initial begin int y; #1 b.get(y); end\n"
      "endmodule\n");
  EXPECT_EQ(WaitersOf("top.e"), 0);
  EXPECT_EQ(WaitersOf("top.s"), 0);
  EXPECT_EQ(WaitersOf("top.b"), 0);
}

TEST_F(ClassVarsAndObjectsOfARun, AMailboxYieldsOnlyTheMessagesStillQueued) {
  Run("module top; mailbox e = new; mailbox m = new;\n"
      "  initial begin int x;\n"
      "    m.put(1); m.put(2); m.put(3); m.put(4);\n"
      "    m.get(x); void'(m.try_get(x));\n"
      "  end\n"
      "endmodule\n");
  vpiHandle e = vpi_handle(vpiClassObj, By("top.e"));
  ASSERT_NE(e, nullptr);
  EXPECT_TRUE(ObjectsOf(vpiMessages, e).empty());
  EXPECT_EQ(IntsOf(vpiMessages, vpi_handle(vpiClassObj, By("top.m"))),
            (std::vector<int>{3, 4}));
}

TEST_F(ClassVarsAndObjectsOfARun, ABaseClassConstraintsParentIsTheObject) {
  Run("module top;\n"
      "  class B; rand int x; constraint b { x < 9; } endclass\n"
      "  class C extends B; constraint c { x > 0; } endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.h"));
  ASSERT_NE(obj, nullptr);
  vpiHandle b = Named(vpiConstraint, obj, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, b)), VpiObjectOf(obj));
}

TEST_F(ClassVarsAndObjectsOfARun, AStaticConstraintsParentIsTheObject) {
  Run("module top;\n"
      "  class C; rand int x; static constraint s { x != 3; } endclass\n"
      "  C h = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.h"));
  ASSERT_NE(obj, nullptr);
  vpiHandle s = Named(vpiConstraint, obj, "s");
  ASSERT_NE(s, nullptr);
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiParent, s)), VpiObjectOf(obj));
}

TEST_F(ClassVarsAndObjectsOfARun, AClassObjYieldsItsEventsOfEitherLifetime) {
  Run("module top; class A; event e; static event se; int n; endclass\n"
      "  A a = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.a"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(NamesOf(vpiNamedEvent, obj), (std::vector<std::string>{"e", "se"}));
}

TEST_F(ClassVarsAndObjectsOfARun,
       AClassObjYieldsItsEventArraysOfEitherLifetime) {
  Run("module top; class A; event ea[2]; static event sa[3]; endclass\n"
      "  A a = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.a"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(NamesOf(vpiNamedEventArray, obj),
            (std::vector<std::string>{"ea", "sa"}));
}

TEST_F(ClassVarsAndObjectsOfARun, AClassObjYieldsItsDeclaredConstructor) {
  Run("module top; class A; int n;\n"
      "    function new(); n = 1; endfunction\n"
      "    function int f(); return n; endfunction\n"
      "  endclass\n"
      "  A a = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.a"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(NamesOf(vpiMethods, obj), (std::vector<std::string>{"f", "new"}));
}

TEST_F(ClassVarsAndObjectsOfARun, ABuiltInClassObjYieldsNoMethod) {
  Run("module top; mailbox m = new; semaphore s = new;\n"
      "endmodule\n");
  for (const char* name : {"top.m", "top.s"}) {
    vpiHandle obj = vpi_handle(vpiClassObj, By(name));
    ASSERT_NE(obj, nullptr) << name;
    EXPECT_TRUE(ObjectsOf(vpiMethods, obj).empty()) << name;
  }
}

TEST_F(ClassVarsAndObjectsOfARun, AFullNameReachesTheLiveObjectsMember) {
  Run("module top; class Packet; int Id; endclass\n"
      "  Packet p = new;\n"
      "  initial begin p.Id = 3; #1 p = new; p.Id = 9; end\n"
      "endmodule\n");
  vpiHandle member = By("top.p.Id");
  ASSERT_NE(member, nullptr);
  EXPECT_EQ(IntegerOf(member), 9);
  EXPECT_EQ(VpiObjectOf(member),
            VpiObjectOf(Named(vpiVariables,
                              vpi_handle(vpiClassObj, By("top.p")), "Id")));
}

TEST_F(ClassVarsAndObjectsOfARun,
       DISABLED_AClassObjsInternalScopesAreItsNestedClasses) {
  Run("module top; class O; class I; int n; endclass int m; endclass\n"
      "  O o = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.o"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(NamesOf(vpiInternalScope, obj), std::vector<std::string>{"I"});
  EXPECT_EQ(KindsOf(vpiInternalScope, obj), std::vector<int>{vpiClassDefn});
}

}  // namespace
}  // namespace delta
