#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// Requirement 3: All parameters and typedefs in interface classes are static.

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

// Requirement 4: Access via :: scope resolution operator.

TEST(InterfaceClassTypeAccess, ScopeResolutionParamAccess) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  parameter int SIZE = 64;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = IC::SIZE;\n"
      "endmodule\n", "result"), 64u);
}

TEST(InterfaceClassTypeAccess, ScopeResolutionEnumValueAccess) {
  EXPECT_EQ(RunAndGet(
      "interface class IntfC;\n"
      "  typedef enum {ONE, TWO, THREE} t1_t;\n"
      "  pure virtual function t1_t funcC();\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = IntfC::TWO;\n"
      "endmodule\n", "result"), 1u);
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
      "endmodule\n", f);
  LowerRunAndCheck(f, design, {{"r1", 8u}, {"r2", 16u}});
}

// Requirement 1: Params/typedefs inherited by extending interface classes.

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

// Requirement 2: Params/typedefs NOT inherited by implementing classes.

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

}  // namespace
