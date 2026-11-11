#include <gtest/gtest.h>

#include <cstdint>
#include <initializer_list>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(TypedConstructorCallElaboration, BasicTypedConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = D::new;\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, TypedConstructorWithArgsElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  int x;\n"
             "  function new(int v); x = v; endfunction\n"
             "endclass\n"
             "class D extends C;\n"
             "  function new(int v); super.new(v); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = D::new(42);\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, TypedConstructorSameTypeElaborates) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  function new(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = C::new;\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, ParameterizedTypedConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class E #(type T = int) extends C;\n"
             "  T x;\n"
             "  function new(T x_init);\n"
             "    super.new();\n"
             "    x = x_init;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = E#(.T(byte))::new(.x_init(5));\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, TypedConstructorInDeclarationElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  C c = D::new;\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, IncompatibleTypedConstructorRejected) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class U; endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = U::new;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typed constructor call type is not assignment compatible", 5, "8.8"));
}

TEST(TypedConstructorCallElaboration,
     IncompatibleTypedConstructorWithArgsRejected) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class U;\n"
      "  function new(int x); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "  initial c = U::new(1);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typed constructor call type is not assignment compatible", 7, "8.8"));
}

TEST(TypedConstructorCallElaboration,
     BaseTypeConstructorToDerivedTargetRejected) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class D extends C; endclass\n"
      "module m;\n"
      "  D d;\n"
      "  initial d = C::new;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typed constructor call type is not assignment compatible", 5, "8.8"));
}

TEST(TypedConstructorCallElaboration, IncompatibleModuleLevelDeclInitRejected) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class U; endclass\n"
      "module m;\n"
      "  C c = U::new;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typed constructor call type is not assignment compatible", 4, "8.8"));
}

TEST(TypedConstructorCallElaboration, BlockLocalDeclInitElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    static C c = D::new;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(TypedConstructorCallElaboration, IncompatibleBlockLocalDeclInitRejected) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class U; endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    static C c = U::new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typed constructor call type is not assignment compatible", 5, "8.8"));
}

TEST(TypedConstructorCallElaboration, BaseToDerivedBlockLocalDeclInitRejected) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class D extends C; endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    static D d = C::new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "typed constructor call type is not assignment compatible", 5, "8.8"));
}

TEST(TypedConstructorCallElaboration,
     MultiLevelDerivedTypedConstructorElaborates) {
  EXPECT_TRUE(
      ElabOk("class C; endclass\n"
             "class D extends C; endclass\n"
             "class E extends D; endclass\n"
             "module m;\n"
             "  C c;\n"
             "  initial c = E::new;\n"
             "endmodule\n"));
}

constexpr const char* kNotCompatible =
    "typed constructor call type is not assignment compatible";

TEST(TypedConstructorCallElaboration,
     IncompatibleTypedConstructorIsReportedInEachProcedure) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "class D extends C; endclass\n"
      "class U; endclass\n"
      "interface class I; endclass\n"
      "class J implements I; endclass\n"
      "class K;\n"
      "  function void m(); C c; c = U::new; endfunction\n"
      "  function void m2(); C c; c = D::new; endfunction\n"
      "endclass\n"
      "function void uf(); C c; c = U::new; endfunction\n"
      "function void uf2(); C c; c = D::new; endfunction\n"
      "interface ifc;\n"
      "  C c = U::new;\n"
      "  C c2 = D::new;\n"
      "endinterface\n"
      "program pg;\n"
      "  C c = U::new;\n"
      "  C c2 = D::new;\n"
      "endprogram\n"
      "module t;\n"
      "  ifc i();\n"
      "  pg p();\n"
      "  I ii = J::new;\n"
      "  I ij = U::new;\n"
      "  task tk(); C c; c = U::new; endtask\n"
      "  task tk2(); C c; c = D::new; endtask\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {7u, 10u, 13u, 17u, 24u, 25u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCompatible, kLine, "8.8"))
        << kLine;
  }
  for (const uint32_t kLine : {8u, 11u, 14u, 18u, 23u, 26u}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), kLine)) << kLine;
  }
}

TEST(TypedConstructorCallElaboration,
     DISABLED_IncompatibleTypedConstructorInAPackageOrDeclarationIsReported) {
  ElabFixture f;
  ElabOk(
      "package k;\n"
      "  class PC; endclass\n"
      "  class PD extends PC; endclass\n"
      "  class PU; endclass\n"
      "  PC pc = PU::new;\n"
      "  PC pc2 = PD::new;\n"
      "  class PK; PC kc = PU::new; endclass\n"
      "  class PK2; PC kc = PD::new; endclass\n"
      "  function void pf(); PC c; c = PU::new; endfunction\n"
      "  function void pf2(); PC c; c = PD::new; endfunction\n"
      "endpackage\n"
      "class C; endclass\n"
      "class D extends C; endclass\n"
      "class U; endclass\n"
      "C uc = U::new;\n"
      "C uc2 = D::new;\n"
      "class K; C c1 = U::new; endclass\n"
      "class K2; C c1 = D::new; endclass\n"
      "module t;\n"
      "  if (1) begin : g\n"
      "    C gc = U::new;\n"
      "    C gc2 = D::new;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {5u, 7u, 9u, 15u, 17u, 21u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCompatible, kLine, "8.8"))
        << kLine;
  }
  for (const uint32_t kLine : {6u, 8u, 10u, 16u, 18u, 22u}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), kLine)) << kLine;
  }
}

TEST(TypedConstructorCallElaboration,
     DISABLED_TypedConstructorIntoANonClassTargetIsReported) {
  ElabFixture f;
  ElabOk(
      "class C; endclass\n"
      "module t;\n"
      "  int x;\n"
      "  string s;\n"
      "  int y = C::new;\n"
      "  C c = C::new;\n"
      "  initial begin\n"
      "    x = C::new;\n"
      "    s = C::new;\n"
      "    c = C::new;\n"
      "  end\n"
      "endmodule\n",
      f);
  for (const uint32_t kLine : {5u, 8u, 9u}) {
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), kNotCompatible, kLine, "8.8"))
        << kLine;
  }
  for (const uint32_t kLine : {6u, 10u}) {
    EXPECT_FALSE(ErrorOnLine(f.diag.Diagnostics(), kLine)) << kLine;
  }
}

}  // namespace
