#include <gtest/gtest.h>

#include <initializer_list>
#include <string>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DataHidingElaboration, PublicMemberAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.x = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.secret = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            8, "8.18"));
}

TEST(DataHidingElaboration, ProtectedMemberAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  protected int hidden;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.hidden = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access protected member from outside", 8,
                            "8.18"));
}

TEST(DataHidingElaboration, LocalMethodAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local function int get_id();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.get_id();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            10, "8.18"));
}

TEST(DataHidingElaboration, PublicMethodAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  function void show(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.show();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ProtectedMethodAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  protected function void secret(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.secret();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access protected member from outside", 8,
                            "8.18"));
}

TEST(DataHidingElaboration, ConstructorLocalAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ConstructorProtectedAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  protected function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalNotVisibleViaDerivedHandle) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  local int secret;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    d.secret = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            10, "8.18"));
}

TEST(DataHidingElaboration, ProtectedAccessibleInSubclassMethod) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  protected int hidden;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int read_hidden();\n"
             "    return hidden;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ProtectedMethodAccessibleInSubclassMethod) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  protected function int secret();\n"
             "    return 7;\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int reveal();\n"
             "    return secret();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, SameClassInstanceLocalAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int i;\n"
             "  function int compare(Packet other);\n"
             "    return (this.i == other.i);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, SameClassInstanceProtectedAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  protected int i;\n"
             "  function int compare(Packet other);\n"
             "    return (this.i == other.i);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial fork\n"
      "    p.secret = 1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            7, "8.18"));
}

TEST(DataHidingElaboration, HandleRedeclaredInAForkArmChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial fork\n"
             "    Open p;\n"
             "    p.secret = 1;\n"
             "  join\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessInAForInitializationIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  int i;\n"
      "  initial for (p.secret = 0; i < 2; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            7, "8.18"));
}

TEST(DataHidingElaboration, LocalMemberAccessInAForStepIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 2; p.secret = 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            7, "8.18"));
}

TEST(DataHidingElaboration, LocalMemberAccessInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial assert (1) p.secret = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            6, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInAnAssertionPassStmtChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial assert (1) begin\n"
             "    Open p;\n"
             "    p.secret = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial assert (1) else p.secret = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            6, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInAnAssertionFailStmtChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial assert (1) else begin\n"
             "    Open p;\n"
             "    p.secret = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessInARandcaseItemIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : p.secret = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            8, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInARandcaseItemChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    randcase\n"
             "      1 : begin\n"
             "        Open p;\n"
             "        p.secret = 1;\n"
             "      end\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration,
     LocalMemberAccessInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { p.secret = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            8, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInARandsequenceCodeBlockChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : { Open p; p.secret = 1; };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ABlockLocalHandleDoesNotRebindTheNameAfterIt) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "class Open;\n"
      "  int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    Open p;\n"
      "    p.secret = 1;\n"
      "  end\n"
      "  initial p.secret = 2;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            13, "8.18"));
}

TEST(DataHidingElaboration, ABlockLocalHandleDoesNotEarnTheNameAReport) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "class Open;\n"
      "  int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Open p;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "  end\n"
      "  initial p.secret = 2;\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(DataHidingElaboration, SiblingBlocksBindTheSameNameSeparately) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "class Open;\n"
      "  int secret;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Open p;\n"
      "    p.secret = 1;\n"
      "  end\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p.secret = 2;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            14, "8.18"));
  EXPECT_EQ(f.diag.Diagnostics().size(), 1u);
}

std::string StaticHandleClassSrc(const std::string& k_decl,
                                 const std::string& handle_decl) {
  return "class C;\n  " + k_decl + "\n  " + handle_decl + "\nendclass\n";
}

std::string StaticHandleModuleSrc(const std::string& stmt) {
  return "module m;\n  int x;\n  C c;\n  initial " + stmt + "\nendmodule\n";
}

void ExpectScopedAccessReported(const std::string& src,
                                std::string_view message) {
  ElabFixture f;
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message,
                            LineHolding(src, "initial"), "8.18"));
}

TEST(ScopedStaticHandleHiding, LocalMemberBehindTheStaticHandleIsReported) {
  ExpectScopedAccessReported(
      StaticHandleClassSrc("local int k = 9;", "static C m_inst;") +
          StaticHandleModuleSrc("x = C::m_inst.k;"),
      "cannot access local member from outside its class");
}

TEST(ScopedStaticHandleHiding, ProtectedMemberBehindTheStaticHandleIsReported) {
  ExpectScopedAccessReported(
      StaticHandleClassSrc("protected int k = 9;", "static C m_inst;") +
          StaticHandleModuleSrc("x = C::m_inst.k;"),
      "cannot access protected member from outside its class hierarchy");
}

std::string PackageStaticHandleSrc(const std::string& class_src,
                                   const std::string& stmt) {
  return "package p;\n" + class_src +
         "endpackage\nmodule m;\n  int x;\n  initial " + stmt + "\nendmodule\n";
}

TEST(ScopedStaticHandleHiding,
     LocalMemberBehindThePackageClassStaticHandleIsReported) {
  ExpectScopedAccessReported(
      PackageStaticHandleSrc(
          StaticHandleClassSrc("local int k = 9;", "static C m_inst;"),
          "x = p::C::m_inst.k;"),
      "cannot access local member from outside its class");
}

TEST(ScopedStaticHandleHiding, LocalStaticHandleNamedByTheClassIsReported) {
  ExpectScopedAccessReported(
      StaticHandleClassSrc("int k = 9;", "static local C m_inst;") +
          StaticHandleModuleSrc("c = C::m_inst;"),
      "cannot access local member from outside its class");
}

TEST(ScopedStaticHandleHiding, PublicMemberBehindThePublicStaticHandleIsOk) {
  EXPECT_TRUE(ElabOk(StaticHandleClassSrc("int k = 9;", "static C m_inst;") +
                     StaticHandleModuleSrc("x = C::m_inst.k;")));
}

std::string NestedStaticHandleClassSrc(const std::string& k_decl,
                                       const std::string& handle_decl) {
  return "class Outer;\n  class Inner;\n    " + k_decl + "\n    " +
         handle_decl + "\n  endclass\nendclass\n";
}

std::string NestedStaticHandleModuleSrc(const std::string& stmt) {
  return "module m;\n  int x;\n  Outer::Inner c;\n  initial " + stmt +
         "\nendmodule\n";
}

TEST(NestedStaticHandleHiding, LocalMemberBehindTheStaticHandleIsReported) {
  ExpectScopedAccessReported(
      NestedStaticHandleClassSrc("local int k = 9;", "static Inner m_inst;") +
          NestedStaticHandleModuleSrc("x = Outer::Inner::m_inst.k;"),
      "cannot access local member from outside its class");
}

TEST(NestedStaticHandleHiding, LocalStaticHandleNamedByTheClassIsReported) {
  ExpectScopedAccessReported(
      NestedStaticHandleClassSrc("int k = 9;", "static local Inner m_inst;") +
          NestedStaticHandleModuleSrc("c = Outer::Inner::m_inst;"),
      "cannot access local member from outside its class");
}

TEST(NestedStaticHandleHiding,
     LocalMemberBehindThePackageClassStaticHandleIsReported) {
  ExpectScopedAccessReported(
      PackageStaticHandleSrc(NestedStaticHandleClassSrc("local int k = 9;",
                                                        "static Inner m_inst;"),
                             "x = p::Outer::Inner::m_inst.k;"),
      "cannot access local member from outside its class");
}

TEST(NestedStaticHandleHiding, PublicMemberBehindThePublicStaticHandleIsOk) {
  EXPECT_TRUE(
      ElabOk(NestedStaticHandleClassSrc("int k = 9;", "static Inner m_inst;") +
             NestedStaticHandleModuleSrc("x = Outer::Inner::m_inst.k;")));
}

std::string SiblingStaticHandleClassSrc(const std::string& k_decl,
                                        const std::string& handle_decl,
                                        const std::string& mid_open = "",
                                        const std::string& mid_close = "") {
  return "class Outer;\n  class A;\n    " + k_decl + "\n  endclass\n" +
         mid_open + "  class B;\n    " + handle_decl + "\n  endclass\n" +
         mid_close + "endclass\n";
}

std::string SiblingStaticHandleModuleSrc(const std::string& stmt) {
  return "module m;\n  int x;\n  initial " + stmt + "\nendmodule\n";
}

TEST(SiblingStaticHandleHiding, LocalMemberBehindTheStaticHandleIsReported) {
  ExpectScopedAccessReported(
      SiblingStaticHandleClassSrc("local int k = 9;", "static A a;") +
          SiblingStaticHandleModuleSrc("x = Outer::B::a.k;"),
      "cannot access local member from outside its class");
}

TEST(SiblingStaticHandleHiding,
     LocalMemberBehindTheScopedTypeHandleIsReported) {
  ExpectScopedAccessReported(
      SiblingStaticHandleClassSrc("local int k = 9;", "static Outer::A a;") +
          SiblingStaticHandleModuleSrc("x = Outer::B::a.k;"),
      "cannot access local member from outside its class");
}

TEST(SiblingStaticHandleHiding,
     LocalMemberBehindTheDeeperChainHandleIsReported) {
  ExpectScopedAccessReported(
      SiblingStaticHandleClassSrc("local int k = 9;", "static A a;",
                                  "  class Mid;\n", "  endclass\n") +
          SiblingStaticHandleModuleSrc("x = Outer::Mid::B::a.k;"),
      "cannot access local member from outside its class");
}

TEST(SiblingStaticHandleHiding, PublicMemberBehindThePublicStaticHandleIsOk) {
  EXPECT_TRUE(ElabOk(SiblingStaticHandleClassSrc("int k = 9;", "static A a;") +
                     SiblingStaticHandleModuleSrc("x = Outer::B::a.k;")));
}

TEST(DataHidingElaboration, ASubclassMethodReachesNoBaseLocalMember) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  local int secret;\n"
      "  protected int guarded;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  function int f(); return secret; endfunction\n"
      "  function int g(); return this.secret; endfunction\n"
      "  function int h(); return super.secret; endfunction\n"
      "  function int k(); return guarded + this.guarded; endfunction\n"
      "  function int n(int secret); return secret; endfunction\n"
      "endclass\n"
      "module m; endmodule\n",
      f);
  const char* const kMessage =
      "cannot access local member from outside its class";
  for (const int kLine : {6, 7, 8}) {
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), kMessage, kLine, "8.18"))
        << kLine;
  }
  for (const int kLine : {9, 10}) {
    EXPECT_FALSE(
        ReportedError(f.diag.Diagnostics(), "cannot access", kLine, "8.18"))
        << kLine;
  }
}

TEST(DataHidingElaboration, HandleAccessFromMethodsAndSubroutinesIsChecked) {
  ElabFixture f;
  ElabOk(
      "class C;\n"
      "  local int secret;\n"
      "  protected int guarded;\n"
      "  function int same(C other); return other.secret; endfunction\n"
      "endclass\n"
      "class D;\n"
      "  C c;\n"
      "  function int f(); return c.secret; endfunction\n"
      "  function int g(); return c.guarded; endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C h;\n"
      "  function int t(); return h.secret; endfunction\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "cannot access local member from outside its class", 8, "8.18"));
  EXPECT_TRUE(ReportedError(diags,
                            "cannot access protected member from outside its "
                            "class hierarchy",
                            9, "8.18"));
  EXPECT_TRUE(ReportedError(
      diags, "cannot access local member from outside its class", 13, "8.18"));
  EXPECT_FALSE(ReportedError(diags, "cannot access", 4, "8.18"));
}

TEST(DataHidingElaboration, ALocalOrProtectedConstructorIsReachedFromInside) {
  ElabFixture f;
  ElabOk(
      "class L;\n"
      "  local function new(); endfunction\n"
      "  static function L make(); L l = new; return l; endfunction\n"
      "endclass\n"
      "class P; protected function new(); endfunction endclass\n"
      "class LD extends L; endclass\n"
      "class PD extends P; endclass\n"
      "module a; class K; endclass K k; initial k = new; endmodule\n"
      "module b; class K; endclass endmodule\n"
      "module m; a ua();\n"
      "  L l = new;\n"
      "  P p;\n"
      "  PD pd;\n"
      "  int da[];\n"
      "  initial begin p = new; pd = new; da = new[2]; end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "class 'LD' extends 'L', whose constructor is "
                            "local and so is reached by no subclass",
                            6, "8.18"));
  EXPECT_FALSE(ReportedError(diags, "extends 'P'", 7, "8.18"));
  EXPECT_TRUE(ReportedError(
      diags, "cannot access local member from outside its class", 11, "8.18"));
  EXPECT_TRUE(ReportedError(diags,
                            "cannot access protected member from outside its "
                            "class hierarchy",
                            15, "8.18"));
  EXPECT_FALSE(ReportedError(diags, "cannot access", 3, "8.18"));
}

}  // namespace
