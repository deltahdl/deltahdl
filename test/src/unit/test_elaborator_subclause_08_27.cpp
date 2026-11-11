#include <gtest/gtest.h>

#include <cstdint>
#include <string_view>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassObjectElaboration, ForwardTypedefClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class C2;\n"
             "class C1;\n"
             "  C2 c;\n"
             "endclass\n"
             "class C2;\n"
             "  C1 c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ClassWithoutForwardTypedefOk) {
  EXPECT_TRUE(
      ElabOk("class MyClass;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ForwardTypedefInterfaceClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef interface class IC;\n"
             "interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, UnresolvedForwardTypedefClassError) {
  ElabFixture f;
  ElabOk(
      "typedef class C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is never resolved by a definition in the same scope", 1, "6.18"));
}

TEST(ClassObjectElaboration, UnresolvedBareForwardTypedefClassError) {
  ElabFixture f;
  ElabOk(
      "typedef C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "is never resolved by a definition in the same scope", 1, "6.18"));
}

TEST(ClassObjectElaboration, ForwardTypedefParameterizedClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class C;\n"
             "module top;\n"
             "  C#(1, real) v2;\n"
             "  C#(.p(2), .T(real)) v3;\n"
             "endmodule\n"
             "class C #(parameter p = 2, type T = int);\n"
             "endclass\n"));
}

TEST(ClassObjectElaboration, BareForwardTypedefWithoutClassKeywordOk) {
  EXPECT_TRUE(
      ElabOk("typedef C2;\n"
             "class C1;\n"
             "  C2 c;\n"
             "endclass\n"
             "class C2;\n"
             "  C1 c;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(ClassObjectElaboration, ForwardDeclaredClassIsRecordedWithNoWidth) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "typedef class C;\n"
      "typedef logic [7:0] byte_t;\n"
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  byte_t v;\n"
      "  initial v = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto width_of = [design](std::string_view name) -> int64_t {
    auto it = design->type_widths.find(name);
    if (it == design->type_widths.end()) return -1;
    return it->second;
  };
  EXPECT_EQ(width_of("byte_t"), 8);
  EXPECT_EQ(width_of("C"), 0);
}

TEST(ClassObjectElaboration, ForwardTypedefLetsALaterClassBeNamedInEveryScope) {
  ElabFixture f;
  ElaborateSrc(
      "typedef class C2;\n"
      "typedef class C3;\n"
      "class C1; C2 c; endclass\n"
      "class C2; C1 c; endclass\n"
      "class D #(type T = int); T v; endclass\n"
      "class R1; function C3 f(); return null; endfunction endclass\n"
      "class R2; function void f(C3 a); endfunction endclass\n"
      "class R3; function void f(); C3 l; endfunction endclass\n"
      "class R4; D #(C3) d; endclass\n"
      "class C3; endclass\n"
      "module m;\n"
      "  typedef class C4;\n"
      "  typedef M2;\n"
      "  C4 h;\n"
      "  class C4; endclass\n"
      "  class M1; M2 x; endclass\n"
      "  class M2; endclass\n"
      "  if (1) begin : g\n"
      "    typedef class G1;\n"
      "    G1 gh;\n"
      "    class G1; endclass\n"
      "  end\n"
      "endmodule\n"
      "package pk;\n"
      "  typedef class P2;\n"
      "  class P1; P2 x; endclass\n"
      "  class P2; endclass\n"
      "endpackage\n"
      "interface ifc;\n"
      "  typedef class I2;\n"
      "  I2 ih;\n"
      "  class I2; endclass\n"
      "endinterface\n"
      "program prg;\n"
      "  typedef class Q2;\n"
      "  Q2 qh;\n"
      "  class Q2; endclass\n"
      "endprogram\n"
      "class Outer;\n"
      "  typedef class In2;\n"
      "  class In1; In2 x; endclass\n"
      "  class In2; endclass\n"
      "endclass\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassObjectElaboration,
     ClassNamingItselfAndAUnitForwardTypedefNeedNoMore) {
  ElabFixture f;
  ElaborateSrc(
      "class N;\n"
      "  N next;\n"
      "endclass\n"
      "typedef class Z;\n"
      "module m;\n"
      "  Z h;\n"
      "endmodule\n"
      "class Z; endclass\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ClassObjectElaboration, ModuleItemNamingALaterClassIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  C4 h;\n"
      "  class C4; endclass\n"
      "endmodule\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "declaration of type 'C4' does not precede this reference to it",
      2, "6.18"));
}

TEST(ClassObjectElaboration,
     DISABLED_LaterClassAsATypeActualOrABaseIsReported) {
  {
    ElabFixture f;
    ElaborateSrc(
        "class D #(type T = int); T v; endclass\n"
        "class R4; D #(C3) d; endclass\n"
        "class C3; endclass\n",
        f);
    const auto& diags = f.diag.Diagnostics();
    EXPECT_TRUE(ReportedError(
        diags, "declaration of type 'C3' does not precede this reference to it",
        2, "6.18"));
  }
  {
    ElabFixture f;
    ElaborateSrc(
        "class E1 extends C3; endclass\n"
        "class C3; endclass\n",
        f);
    const auto& diags = f.diag.Diagnostics();
    EXPECT_TRUE(ReportedError(
        diags, "declaration of type 'C3' does not precede this reference to it",
        1, "6.18"));
  }
  {
    ElabFixture f;
    ElaborateSrc(
        "class D #(type T = int); T v; endclass\n"
        "module m;\n"
        "  D #(C5) d;\n"
        "  class C5; endclass\n"
        "endmodule\n",
        f);
    const auto& diags = f.diag.Diagnostics();
    EXPECT_TRUE(ReportedError(
        diags, "declaration of type 'C5' does not precede this reference to it",
        3, "6.18"));
  }
}

TEST(ClassObjectElaboration,
     DISABLED_ForwardTypedefResolvedOnlyInAnEnclosingScopeIsReported) {
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  typedef class X;\n"
        "  X h;\n"
        "endmodule\n"
        "class X; endclass\n",
        f);
    const auto& diags = f.diag.Diagnostics();
    EXPECT_TRUE(ReportedError(
        diags, "is never resolved by a definition in the same scope", 2,
        "6.18"));
  }
  {
    ElabFixture f;
    ElaborateSrc(
        "module m;\n"
        "  if (1) begin : g\n"
        "    typedef class Y;\n"
        "    Y h;\n"
        "  end\n"
        "  class Y; endclass\n"
        "endmodule\n",
        f);
    const auto& diags = f.diag.Diagnostics();
    EXPECT_TRUE(ReportedError(
        diags, "is never resolved by a definition in the same scope", 3,
        "6.18"));
  }
}

TEST(ClassObjectElaboration,
     DISABLED_UnitForwardClassDefinedAsAStructureIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "typedef class W;\n"
      "class U; W w; endclass\n"
      "typedef struct { int a; } W;\n",
      f);
  const auto& diags = f.diag.Diagnostics();
  EXPECT_TRUE(ReportedError(
      diags, "typedef 'W' does not conform to its forward declaration as class",
      3, "6.18"));
}

}  // namespace
