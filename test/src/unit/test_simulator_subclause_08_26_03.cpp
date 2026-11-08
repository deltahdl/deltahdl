#include <gtest/gtest.h>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(InterfaceClassTypeAccess, ScopeResolutionParamAccess) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  parameter int SIZE = 64;\n"
                      "  pure virtual function void foo();\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = IC::SIZE;\n"
                      "endmodule\n",
                      "result"),
            64u);
}

TEST(InterfaceClassTypeAccess, ScopeResolutionEnumValueAccess) {
  EXPECT_EQ(RunAndGet("interface class IntfC;\n"
                      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
                      "  pure virtual function t1_t funcC();\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = IntfC::TWO;\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassTypeAccess, ScopeResolutionMultipleParams) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class IC;\n"
      "  parameter int WIDTH = 8;\n"
      "  parameter int DEPTH = 16;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module t;\n"
      "  int r1, r2;\n"
      "  initial begin\n"
      "    r1 = IC::WIDTH;\n"
      "    r2 = IC::DEPTH;\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(f, design, {{"r1", 8u}, {"r2", 16u}});
}

TEST(InterfaceClassTypeAccess, ExtendedInterfaceInheritsStaticProperties) {
  SimFixture f;
  auto* base = MakeClassType(f, "IA", {});
  base->is_interface = true;
  base->static_properties["SIZE"] = MakeLogic4VecVal(f.arena, 32, 64);

  auto* ext = MakeClassType(f, "IB", {});
  ext->is_interface = true;
  ext->extended_interfaces.push_back(base);

  EXPECT_TRUE(ext->IsA(base));
}

TEST(InterfaceClassTypeAccess, ParamInheritedByExtendingInterfaceEndToEnd) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  parameter int SIZE = 64;\n"
                      "  pure virtual function void fa();\n"
                      "endclass\n"
                      "interface class IB extends IA;\n"
                      "  pure virtual function void fb();\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = IB::SIZE;\n"
                      "endmodule\n",
                      "result"),
            64u);
}

TEST(InterfaceClassTypeAccess, EnumValueInheritedByExtendingInterfaceEndToEnd) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
                      "  pure virtual function void fa();\n"
                      "endclass\n"
                      "interface class IB extends IA;\n"
                      "  pure virtual function void fb();\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = IB::THREE;\n"
                      "endmodule\n",
                      "result"),
            2u);
}

TEST(InterfaceClassTypeAccess, ParamInheritedThroughChainedExtends) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  parameter int WIDTH = 8;\n"
                      "  pure virtual function void fa();\n"
                      "endclass\n"
                      "interface class IB extends IA;\n"
                      "  pure virtual function void fb();\n"
                      "endclass\n"
                      "interface class IC extends IB;\n"
                      "  pure virtual function void fc();\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial result = IC::WIDTH;\n"
                      "endmodule\n",
                      "result"),
            8u);
}

TEST(InterfaceClassTypeAccess,
     LowererCopiesInheritedParamIntoExtendingInterface) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class IA;\n"
      "  parameter int SIZE = 64;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class IB extends IA;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* ib = f.ctx.FindClassType("IB");
  ASSERT_NE(ib, nullptr);
  auto it = ib->static_properties.find("SIZE");
  ASSERT_NE(it, ib->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 64u);
}

TEST(InterfaceClassTypeAccess,
     LowererCopiesInheritedEnumMembersIntoExtendingInterface) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class IA;\n"
      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
      "  pure virtual function void fa();\n"
      "endclass\n"
      "interface class IB extends IA;\n"
      "  pure virtual function void fb();\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* ib = f.ctx.FindClassType("IB");
  ASSERT_NE(ib, nullptr);
  auto it = ib->enum_members.find("THREE");
  ASSERT_NE(it, ib->enum_members.end());
  EXPECT_EQ(it->second, 2u);
}

TEST(InterfaceClassTypeAccess, LowererDoesNotCopyParamIntoImplementingClass) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class IC;\n"
      "  parameter int SIZE = 64;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "endmodule\n",
      f);
  ASSERT_FALSE(f.has_errors);
  LowerAndRun(design, f);
  auto* ic = f.ctx.FindClassType("IC");
  ASSERT_NE(ic, nullptr);
  EXPECT_NE(ic->static_properties.find("SIZE"), ic->static_properties.end());
  auto* c = f.ctx.FindClassType("C");
  ASSERT_NE(c, nullptr);
  EXPECT_EQ(c->static_properties.find("SIZE"), c->static_properties.end());
}

TEST(InterfaceClassTypeAccess, TypedefTypeViaScopeResolutionUsedAtRuntime) {
  EXPECT_EQ(RunAndGet("interface class IntfC;\n"
                      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
                      "  pure virtual function t1_t funcC();\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    IntfC::t1_t v;\n"
                      "    v = IntfC::THREE;\n"
                      "    result = v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            2u);
}

TEST(InterfaceClassTypeAccess,
     InheritedTypedefTypeViaExtendingInterfaceAtRuntime) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
                      "  pure virtual function void fa();\n"
                      "endclass\n"
                      "interface class IB extends IA;\n"
                      "  pure virtual function void fb();\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    IB::t1_t v;\n"
                      "    v = IB::TWO;\n"
                      "    result = v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassTypeAccess, InterfaceParamInConstantExpressionWidth) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  parameter int WIDTH = 8;\n"
                      "  pure virtual function void foo();\n"
                      "endclass\n"
                      "module t;\n"
                      "  logic [IC::WIDTH-1:0] v;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    v = '1;\n"
                      "    result = v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            255u);
}

TEST(InterfaceClassTypeAccess, InterfaceParamViaLocalparamConstantExpression) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  parameter int WIDTH = 8;\n"
                      "  pure virtual function void foo();\n"
                      "endclass\n"
                      "module t;\n"
                      "  localparam int W = IC::WIDTH;\n"
                      "  logic [W-1:0] v;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    v = '1;\n"
                      "    result = v;\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            255u);
}

TEST(InterfaceClassTypeAccess, SpecializedTypedefReturnTypeWidthEndToEnd) {
  EXPECT_EQ(
      RunAndGet("interface class IntfA #(type T1 = logic);\n"
                "  typedef T1[1:0] T2;\n"
                "  pure virtual function T2 funcA();\n"
                "endclass\n"
                "interface class IntfB #(type T = bit) extends IntfA #(T);\n"
                "  pure virtual function T2 funcB();\n"
                "endclass\n"
                "class Impl implements IntfB#(bit[1:0]);\n"
                "  virtual function IntfA#(bit[1:0])::T2 funcA();\n"
                "    return 3;\n"
                "  endfunction\n"
                "  virtual function IntfA#(bit[1:0])::T2 funcB();\n"
                "    return 2;\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  Impl im = new;\n"
                "  int result;\n"
                "  initial result = $bits(im.funcB());\n"
                "endmodule\n",
                "result"),
      4u);
}

TEST(InterfaceClassTypeAccess, SpecializedTypedefReturnTypeFollowsActual) {
  EXPECT_EQ(
      RunAndGet("interface class IntfA #(type T1 = logic);\n"
                "  typedef T1[1:0] T2;\n"
                "  pure virtual function T2 funcA();\n"
                "endclass\n"
                "class Impl implements IntfA#(bit[3:0]);\n"
                "  virtual function IntfA#(bit[3:0])::T2 funcA();\n"
                "    return 5;\n"
                "  endfunction\n"
                "  function IntfA#(bit[1:0])::T2 narrow();\n"
                "    return 1;\n"
                "  endfunction\n"
                "endclass\n"
                "module t;\n"
                "  Impl im = new;\n"
                "  int result;\n"
                "  initial\n"
                "    result = $bits(im.funcA()) * 100 + $bits(im.narrow());\n"
                "endmodule\n",
                "result"),
      804u);
}

}  // namespace
