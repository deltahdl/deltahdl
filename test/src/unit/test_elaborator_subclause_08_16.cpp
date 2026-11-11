#include <gtest/gtest.h>

#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassCastElaboration, SubclassToSuperclassAssignOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int i;\n"
             "endclass\n"
             "class LinkedPacket extends Packet;\n"
             "  int j;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    LinkedPacket lp;\n"
             "    lp = new;\n"
             "    p = lp;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration, CastAsFunctionOk) {
  EXPECT_TRUE(
      ElabOk("class Base; int x; endclass\n"
             "class Derived extends Base; int y; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Base b;\n"
             "    Derived d;\n"
             "    int ok;\n"
             "    d = new;\n"
             "    b = d;\n"
             "    ok = $cast(d, b);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration, CastWithNullOk) {
  EXPECT_TRUE(
      ElabOk("class Base; endclass\n"
             "class Derived extends Base; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Derived d;\n"
             "    $cast(d, null);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration, DirectSuperclassToSubclassAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "class Base; endclass\n"
      "class Derived extends Base; endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Base b;\n"
      "    Derived d;\n"
      "    b = new;\n"
      "    d = b;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "class handle assignment requires assignment compatible "
                    "types",
                    8, "8.4"));
}

TEST(ClassCastElaboration, UnrelatedClassTypesAssignError) {
  ElabFixture f;
  ElaborateSrc(
      "class A; endclass\n"
      "class B; endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    A a;\n"
      "    B b;\n"
      "    a = new;\n"
      "    b = a;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "class handle assignment requires assignment compatible "
                    "types",
                    8, "8.4"));
}

TEST(ClassCastElaboration, DeepHierarchyUpcastOk) {
  EXPECT_TRUE(
      ElabOk("class Grand; endclass\n"
             "class Mid extends Grand; endclass\n"
             "class Leaf extends Mid; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Grand g;\n"
             "    Leaf l;\n"
             "    l = new;\n"
             "    g = l;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration, CastDeepHierarchyDowncastOk) {
  EXPECT_TRUE(
      ElabOk("class Grand; endclass\n"
             "class Mid extends Grand; endclass\n"
             "class Leaf extends Mid; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Grand g;\n"
             "    Leaf l;\n"
             "    l = new;\n"
             "    g = l;\n"
             "    $cast(l, g);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassCastElaboration,
     SuperclassHandleAssignedToSubclassIsReportedInEveryPlace) {
  ElabFixture f;
  ElaborateSrc(
      "class B; endclass\n"
      "class D extends B; endclass\n"
      "class L extends D; endclass\n"
      "function automatic D ret_d(B b);\n"
      "  return b;\n"
      "endfunction\n"
      "function automatic B ret_b(D d);\n"
      "  return d;\n"
      "endfunction\n"
      "class H;\n"
      "  B b; D d;\n"
      "  function void m();\n"
      "    d = b;\n"
      "    b = d;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  B b; D d; L l;\n"
      "  p pi();\n"
      "  ifc i();\n"
      "  initial begin\n"
      "    l = b;\n"
      "    l = d;\n"
      "    d <= b;\n"
      "    d = l;\n"
      "    b = l;\n"
      "    b <= d;\n"
      "  end\n"
      "endmodule\n"
      "program p;\n"
      "  B b; D d;\n"
      "  initial d = b;\n"
      "  initial b = d;\n"
      "endprogram\n"
      "interface ifc;\n"
      "  B b; D d;\n"
      "  initial d = b;\n"
      "  initial b = d;\n"
      "endinterface\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(diags,
                            "return expression in function 'ret_d' is not "
                            "assignment-compatible with the function's return "
                            "type",
                            5, "12.8"));
  for (const int kLine : {13, 22, 23, 24, 32, 37}) {
    EXPECT_TRUE(ReportedError(
        diags, "class handle assignment requires assignment compatible types",
        kLine, "8.4"))
        << kLine;
  }
  for (const int kLine : {8, 14, 25, 26, 27, 33, 38}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

TEST(ClassCastElaboration,
     DISABLED_DowncastInAPackageInitializerOrCallIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "class B; endclass\n"
      "class D extends B; endclass\n"
      "package pk;\n"
      "  B pb; D pd;\n"
      "  D pi = pb;\n"
      "  B pj = pd;\n"
      "  function automatic void f(); pd = pb; endfunction\n"
      "  function automatic void g(); pb = pd; endfunction\n"
      "endpackage\n"
      "class H;\n"
      "  B b; D d;\n"
      "  D d2 = b;\n"
      "  B b2 = d;\n"
      "endclass\n"
      "function automatic void take_d(D d); endfunction\n"
      "function automatic void take_b(B b); endfunction\n"
      "function automatic void out_b(output B o); endfunction\n"
      "function automatic void out_d(output D o); endfunction\n"
      "function automatic B ret_b(); return null; endfunction\n"
      "function automatic D ret_d(); return null; endfunction\n"
      "module m;\n"
      "  B b; D d;\n"
      "  D md = b;\n"
      "  B mb = d;\n"
      "  initial begin\n"
      "    automatic D ld = b;\n"
      "    automatic B lb = d;\n"
      "    take_d(b);\n"
      "    take_b(d);\n"
      "    out_b(d);\n"
      "    out_d(b);\n"
      "    d = ret_b();\n"
      "    b = ret_d();\n"
      "  end\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  for (const int kLine : {5, 7, 12, 23, 26, 28, 30, 32}) {
    EXPECT_TRUE(ReportedError(
        diags, "class handle assignment requires assignment compatible types",
        kLine, "8.4"))
        << kLine;
  }
  for (const int kLine : {6, 8, 13, 24, 27, 29, 31, 33}) {
    EXPECT_FALSE(ErrorOnLine(diags, kLine)) << kLine;
  }
}

}  // namespace
