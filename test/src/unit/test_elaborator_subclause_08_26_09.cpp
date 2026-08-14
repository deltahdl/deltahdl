

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassAllowedContent, NoConstraintsOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// The report stands at the interface class declaration rather than at the
// constraint block: CheckInterfaceClassMemberKind in
// src/elaborator/elaborator_validate_class_overrides.cpp passes the class's own
// location.
TEST(InterfaceClassAllowedContent, ConstraintBlockError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "  constraint c { }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain constraint blocks", 1,
                            "8.26.9"));
}

TEST(InterfaceClassAllowedContent, CovergroupError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "  covergroup cg; endgroup\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain covergroups", 1, "8.26.9"));
}

TEST(InterfaceClassAllowedContent, ConstraintBlockInExtendedInterfaceError) {
  ElabFixture f;
  ElabOk(
      "interface class Base;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "interface class Derived extends Base;\n"
      "  constraint c { }\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain constraint blocks", 4,
                            "8.26.9"));
}

TEST(InterfaceClassAllowedContent, CovergroupInExtendedInterfaceError) {
  ElabFixture f;
  ElabOk(
      "interface class Base;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "interface class Derived extends Base;\n"
      "  covergroup cg; endgroup\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "shall not contain covergroups", 4, "8.26.9"));
}

TEST(InterfaceClassRandomize, RandomizeOnInterfaceHandleOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  rand int x;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj = new;\n"
             "    IC iref = obj;\n"
             "    void'(iref.randomize());\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassRandomize,
     RandomizeWithInlineConstraintOnInterfaceHandleOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  rand int x;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C obj = new;\n"
             "    IC iref = obj;\n"
             "    void'(iref.randomize() with { });\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassRandomize, RandModeOnInterfaceHandleError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    IC iref = obj;\n"
      "    iref.rand_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 13,
                            "8.26.9"));
}

TEST(InterfaceClassRandomize, ConstraintModeOnInterfaceHandleError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  rand int x;\n"
      "  constraint c { x > 0; }\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C obj = new;\n"
      "    IC iref = obj;\n"
      "    iref.constraint_mode(0);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "is not legal on interface class handle", 14,
                            "8.26.9"));
}

TEST(InterfaceClassPrePostRandomize, OverridePreRandomizeInImplementor) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  int count;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "  function void pre_randomize();\n"
             "    count = count + 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize, OverridePostRandomizeInImplementor) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  int count;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "  function void post_randomize();\n"
             "    count = count + 1;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize,
     BuiltinRandomizeMethodsAcrossInterfacesNoConflict) {
  // §8.26.9 special case: even when more than one implemented interface class
  // carries pre_randomize/post_randomize, those names shall not be treated as
  // an interface method name conflict. Declaring both in two distinct
  // interfaces and implementing both routes the names through the interface
  // method-conflict resolution, which exempts them rather than flagging the
  // collision an ordinary same-named method from two interfaces would draw.
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "class C implements A, B;\n"
             "  virtual function void fa(); endfunction\n"
             "  virtual function void fb(); endfunction\n"
             "  virtual function void pre_randomize(); endfunction\n"
             "  virtual function void post_randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize,
     PrePostRandomizeDeclaredInTwoExtendedInterfacesNoConflict) {
  // §8.26.9: "pre_randomize() and post_randomize() shall not cause method name
  // conflicts", so an interface class may extend two interface classes that
  // both declare them.
  //
  // The declarations have to be the ones §18.6.2 fixes. It gives the prototypes
  // as `function void pre_randomize();` and `function void post_randomize();`,
  // and a declaration of either name is a declaration of that built-in method,
  // so a differing return type is not an incompatible signature but an illegal
  // declaration -- rejected on its own, before any question of conflict arises.
  // That means every legal declaration of these two names carries the same
  // signature, and the exemption can only be about the name being inherited
  // from two places rather than about reconciling signatures.
  //
  // What this establishes is therefore narrower than the foil below implies:
  // the foil contrasts an ordinary method with differing return types, an axis
  // no legal version of this source can have. Reading them as a matched pair
  // would overstate what the accepting result here shows.
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "  pure virtual function void pre_randomize();\n"
             "  pure virtual function void post_randomize();\n"
             "endclass\n"
             "interface class D extends A, B;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassPrePostRandomize,
     OrdinaryMethodIncompatibleSignaturesAcrossExtendedInterfacesConflicts) {
  // §8.26.6.1: an ordinary method prototyped in two extended interface classes
  // with different return types is a conflict, because no single
  // implementation can validly override both prototypes. This is the case the
  // clause's own example describes, with bar() standing in for its funcBase.
  //
  // It is not a foil for the exemption above, though it once read as one. That
  // case cannot be written with differing return types at all: §18.6.2 fixes
  // the prototype of pre_randomize and post_randomize, so any legal
  // declaration of them carries the one signature and the arrangements are not
  // comparable. What this test establishes on its own is that the conflict
  // machinery fires for an ordinary method, which is worth holding regardless.
  //
  // The report names §8.26.6.1, the clause the conflict belongs to, and stands
  // at the declaration of D, the class both prototypes reach.
  ElabFixture f;
  ElabOk(
      "interface class A;\n"
      "  pure virtual function void fa();\n"
      "  pure virtual function void bar();\n"
      "endclass\n"
      "interface class B;\n"
      "  pure virtual function void fb();\n"
      "  pure virtual function bit bar();\n"
      "endclass\n"
      "interface class D extends A, B;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "incompatible signatures in interface", 9,
                            "8.26.6.1"));
}

TEST(InterfaceClassPrePostRandomize,
     PrePostRandomizeNoConflictMultipleInterfaces) {
  EXPECT_TRUE(
      ElabOk("interface class A;\n"
             "  pure virtual function void fa();\n"
             "endclass\n"
             "interface class B;\n"
             "  pure virtual function void fb();\n"
             "endclass\n"
             "interface class C;\n"
             "  pure virtual function void fc();\n"
             "endclass\n"
             "class D implements A, B, C;\n"
             "  virtual function void fa(); endfunction\n"
             "  virtual function void fb(); endfunction\n"
             "  virtual function void fc(); endfunction\n"
             "  function void pre_randomize(); endfunction\n"
             "  function void post_randomize(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

}  // namespace
