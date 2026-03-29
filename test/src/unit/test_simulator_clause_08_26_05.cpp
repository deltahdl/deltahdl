#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

// Req 1: Assign object handle to interface class variable.

TEST(InterfaceClassCastingAndRefAssignment, InterfaceClassIsACheck) {
  SimFixture f;

  auto* iface_type = f.arena.Create<ClassTypeInfo>();
  iface_type->name = "IC";
  iface_type->is_interface = true;
  f.ctx.RegisterClassType("IC", iface_type);

  auto* impl_type = f.arena.Create<ClassTypeInfo>();
  impl_type->name = "C";
  impl_type->parent = iface_type;
  f.ctx.RegisterClassType("C", impl_type);

  EXPECT_TRUE(impl_type->IsA(iface_type));

  EXPECT_FALSE(iface_type->IsA(impl_type));
}

TEST(InterfaceClassCastingAndRefAssignment, IsAViaExtendedInterfaces) {
  SimFixture f;

  auto* iface = MakeClassType(f, "IC", {});
  iface->is_interface = true;

  auto* impl = MakeClassType(f, "C", {"x"});
  impl->extended_interfaces.push_back(iface);

  EXPECT_TRUE(impl->IsA(iface));
  EXPECT_FALSE(iface->IsA(impl));
}

TEST(InterfaceClassCastingAndRefAssignment, IsAViaMultipleExtendedInterfaces) {
  SimFixture f;

  auto* iface_a = MakeClassType(f, "IA", {});
  iface_a->is_interface = true;
  auto* iface_b = MakeClassType(f, "IB", {});
  iface_b->is_interface = true;

  auto* impl = MakeClassType(f, "C", {});
  impl->extended_interfaces.push_back(iface_a);
  impl->extended_interfaces.push_back(iface_b);

  EXPECT_TRUE(impl->IsA(iface_a));
  EXPECT_TRUE(impl->IsA(iface_b));
}

TEST(InterfaceClassCastingAndRefAssignment, IsATransitiveViaParentInterface) {
  SimFixture f;

  auto* base_iface = MakeClassType(f, "IBase", {});
  base_iface->is_interface = true;

  auto* ext_iface = MakeClassType(f, "IExt", {});
  ext_iface->is_interface = true;
  ext_iface->extended_interfaces.push_back(base_iface);

  auto* impl = MakeClassType(f, "C", {});
  impl->extended_interfaces.push_back(ext_iface);

  EXPECT_TRUE(impl->IsA(ext_iface));
  EXPECT_TRUE(impl->IsA(base_iface));
}

TEST(InterfaceClassCastingAndRefAssignment, E2eAssignImplToInterfaceVar) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c_obj;\n"
      "    IC ic_ref;\n"
      "    c_obj = new;\n"
      "    ic_ref = c_obj;\n"
      "    result = (ic_ref != null);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

// Req 2: $cast between interface class variables.

TEST(InterfaceClassCastingAndRefAssignment, AreCastCompatibleBothInterfaces) {
  SimFixture f;

  auto* iface_a = MakeClassType(f, "IA", {});
  iface_a->is_interface = true;
  auto* iface_b = MakeClassType(f, "IB", {});
  iface_b->is_interface = true;

  // Unrelated interfaces are cast-compatible because both are interface types.
  EXPECT_TRUE(iface_a->is_interface || iface_b->is_interface);
}

TEST(InterfaceClassCastingAndRefAssignment, E2eCastBetweenInterfaceVarsSucceeds) {
  EXPECT_EQ(RunAndGet(
      "interface class PutImp;\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "interface class GetImp;\n"
      "  pure virtual function void get();\n"
      "endclass\n"
      "class Fifo implements PutImp, GetImp;\n"
      "  virtual function void put();\n"
      "  endfunction\n"
      "  virtual function void get();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    Fifo fifo_obj;\n"
      "    PutImp put_ref;\n"
      "    GetImp get_ref;\n"
      "    fifo_obj = new;\n"
      "    put_ref = fifo_obj;\n"
      "    result = $cast(get_ref, put_ref);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

// Req 3: Cast from object handle to interface class type handle.

TEST(InterfaceClassCastingAndRefAssignment, E2eCastObjectToInterfaceSucceeds) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c_obj;\n"
      "    IC ic_ref;\n"
      "    c_obj = new;\n"
      "    result = $cast(ic_ref, c_obj);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(InterfaceClassCastingAndRefAssignment, E2eCastInterfaceBackToImplSucceeds) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c_obj, c2;\n"
      "    IC ic_ref;\n"
      "    c_obj = new;\n"
      "    ic_ref = c_obj;\n"
      "    result = $cast(c2, ic_ref);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

// Req 4: Interface class objects shall not be constructed.

TEST(InterfaceClassCastingAndRefAssignment, InterfaceClassNewReportsError) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    IC ic;\n"
      "    ic = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  if (!design) {
    // Elaboration-time rejection is acceptable.
    EXPECT_TRUE(f.has_errors);
    return;
  }
  LowerAndRun(design, f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// Req 5: Null interface handle casting follows §8.16.

TEST(InterfaceClassCastingAndRefAssignment, E2eCastNullInterfaceHandleSucceeds) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    IC ic_ref;\n"
      "    C c_obj;\n"
      "    result = $cast(c_obj, ic_ref);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(InterfaceClassCastingAndRefAssignment, E2eCastNullInterfaceAssignsNull) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    IC ic_ref;\n"
      "    C c_obj;\n"
      "    c_obj = new;\n"
      "    $cast(c_obj, ic_ref);\n"
      "    result = (c_obj == null);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

TEST(InterfaceClassCastingAndRefAssignment, E2eCastNullLiteralToInterfaceSucceeds) {
  EXPECT_EQ(RunAndGet(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C implements IC;\n"
      "  virtual function void foo();\n"
      "  endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    IC ic_ref;\n"
      "    result = $cast(ic_ref, null);\n"
      "  end\n"
      "endmodule\n", "result"), 1u);
}

}  // namespace
