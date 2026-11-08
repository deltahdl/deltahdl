#include <gtest/gtest.h>

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

}  // namespace
