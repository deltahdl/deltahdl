#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

TEST(InterfaceClassTypeAccess, InterfaceParamRegisteredAsStaticProperty) {
  SimFixture f;
  auto* type = MakeClassType(f, "IC", {});
  type->is_interface = true;
  type->static_properties["SIZE"] = MakeLogic4VecVal(f.arena, 32, 64);

  auto* found = f.ctx.FindClassType("IC");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_interface);
  auto it = found->static_properties.find("SIZE");
  ASSERT_NE(it, found->static_properties.end());
  EXPECT_EQ(it->second.ToUint64(), 64u);
}

TEST(InterfaceClassTypeAccess, InterfaceEnumMembersRegistered) {
  SimFixture f;
  auto* type = MakeClassType(f, "IntfC", {});
  type->is_interface = true;
  type->enum_members["ONE"] = 0;
  type->enum_members["TWO"] = 1;
  type->enum_members["THREE"] = 2;

  auto* found = f.ctx.FindClassType("IntfC");
  ASSERT_NE(found, nullptr);
  EXPECT_EQ(found->enum_members["ONE"], 0u);
  EXPECT_EQ(found->enum_members["TWO"], 1u);
  EXPECT_EQ(found->enum_members["THREE"], 2u);
}

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

TEST(InterfaceClassTypeAccess, ImplementingClassDoesNotInheritStaticProps) {
  SimFixture f;
  auto* iface = MakeClassType(f, "IC", {});
  iface->is_interface = true;
  iface->static_properties["SIZE"] = MakeLogic4VecVal(f.arena, 32, 64);

  auto* impl = MakeClassType(f, "C", {});
  impl->extended_interfaces.push_back(iface);

  auto it = impl->static_properties.find("SIZE");
  EXPECT_EQ(it, impl->static_properties.end());
}

// §8.26.3: a parameter declared in an interface class is inherited by an
// extending interface class, so it can be read through the extending class
// name with the scope resolution operator.
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

// §8.26.3: typedefs (here, the enumeration constants of a member typedef) are
// likewise inherited through extends and reachable via the extending class.
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

// §8.26.3: the inheritance is transitive across a chain of extending interface
// classes, so a parameter from the root is reachable through the leaf.
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

// §8.26.3: the lowerer itself performs the extends-inheritance — after
// lowering, the extending interface's type carries the base parameter as a
// static property. Observing the lowered ClassTypeInfo exercises that
// production path directly (not a hand-built type).
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

// §8.26.3: typedef enumeration constants are inherited through extends too; the
// lowered extending interface carries the base enum members.
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

// §8.26.3: parameters and typedefs are NOT inherited through implements. After
// lowering, the implementing class does not carry the interface's parameter as
// a static property, while the interface class itself still does. This observes
// the lowerer's interface-only inheritance guard rather than a hand-built type.
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

}  // namespace
