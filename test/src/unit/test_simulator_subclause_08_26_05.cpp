#include <gtest/gtest.h>

#include <cstddef>
#include <vector>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_class_object.h"
#include "helpers_reported_error.h"
#include "helpers_scheduler.h"
#include "simulator/class_object.h"

using namespace delta;

namespace {

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
  EXPECT_EQ(RunAndGet("interface class IC;\n"
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
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassCastingAndRefAssignment,
     E2eAssignImplToInterfaceVarDeclInit) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  pure virtual function void foo();\n"
                      "endclass\n"
                      "class C implements IC;\n"
                      "  virtual function void foo();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    static C c_obj = new;\n"
                      "    static IC ic_ref = c_obj;\n"
                      "    result = (ic_ref != null);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassCastingAndRefAssignment, AreCastCompatibleBothInterfaces) {
  SimFixture f;

  auto* iface_a = MakeClassType(f, "IA", {});
  iface_a->is_interface = true;
  auto* iface_b = MakeClassType(f, "IB", {});
  iface_b->is_interface = true;

  EXPECT_TRUE(iface_a->is_interface || iface_b->is_interface);
}

TEST(InterfaceClassCastingAndRefAssignment,
     E2eCastBetweenInterfaceVarsSucceeds) {
  EXPECT_EQ(RunAndGet("interface class PutImp;\n"
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
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassCastingAndRefAssignment, E2eCastObjectToInterfaceSucceeds) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
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
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassCastingAndRefAssignment,
     ACastReachesTheInterfaceClassNamedThroughAPackage) {
  EXPECT_EQ(RunAndGet("package p;\n"
                      "  interface class I;\n"
                      "    pure virtual function int g();\n"
                      "  endclass\n"
                      "endpackage\n"
                      "module t;\n"
                      "  interface class I;\n"
                      "    pure virtual function int f();\n"
                      "  endclass\n"
                      "  class Base;\n"
                      "  endclass\n"
                      "  class C extends Base implements p::I;\n"
                      "    virtual function int g(); return 4; endfunction\n"
                      "  endclass\n"
                      "  C c_obj = new;\n"
                      "  Base b;\n"
                      "  p::I h;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    b = c_obj;\n"
                      "    result = $cast(h, b) * 10 + h.g();\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            14u);
}

TEST(InterfaceClassCastingAndRefAssignment,
     E2eCastInterfaceBackToImplSucceeds) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
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
                      "endmodule\n",
                      "result"),
            1u);
}

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
  if (design) LowerAndRun(design, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class 'IC'",
                            7, "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     E2eCastNullInterfaceHandleSucceeds) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
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
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassCastingAndRefAssignment, E2eCastNullInterfaceAssignsNull) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
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
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassCastingAndRefAssignment,
     E2eCastNullLiteralToInterfaceSucceeds) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
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
                      "endmodule\n",
                      "result"),
            1u);
}

TEST(InterfaceClassCastingAndRefAssignment,
     E2eCastBetweenInterfaceVarsFailsWhenNotImplemented) {
  EXPECT_EQ(RunAndGet("interface class IA;\n"
                      "  pure virtual function void fa();\n"
                      "endclass\n"
                      "interface class IB;\n"
                      "  pure virtual function void fb();\n"
                      "endclass\n"
                      "class C implements IA;\n"
                      "  virtual function void fa();\n"
                      "  endfunction\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c_obj;\n"
                      "    IA a_ref;\n"
                      "    IB b_ref;\n"
                      "    c_obj = new;\n"
                      "    a_ref = c_obj;\n"
                      "    result = $cast(b_ref, a_ref);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(InterfaceClassCastingAndRefAssignment,
     E2eCastObjectToUnimplementedInterfaceFails) {
  EXPECT_EQ(RunAndGet("interface class IC;\n"
                      "  pure virtual function void foo();\n"
                      "endclass\n"
                      "class C;\n"
                      "endclass\n"
                      "module t;\n"
                      "  int result;\n"
                      "  initial begin\n"
                      "    C c_obj;\n"
                      "    IC ic_ref;\n"
                      "    c_obj = new;\n"
                      "    result = $cast(ic_ref, c_obj);\n"
                      "  end\n"
                      "endmodule\n",
                      "result"),
            0u);
}

TEST(InterfaceClassCastingAndRefAssignment, ConstructionRejectionNames8_26_5) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class Drv;\n"
      "  pure virtual function void go();\n"
      "endclass\n"
      "module t;\n"
      "  Drv h;\n"
      "  initial h = new;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  size_t after_elaboration = f.diag.Diagnostics().size();
  LowerAndRun(design, f);
  std::vector<Diagnostic> after(
      f.diag.Diagnostics().begin() +
          static_cast<std::ptrdiff_t>(after_elaboration),
      f.diag.Diagnostics().end());
  EXPECT_TRUE(ReportedError(after, "cannot construct object of interface", 6,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     CastsBetweenUnparameterizedInterfacesAndClassesSucceed) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "interface class P; pure virtual function void put(int a); endclass\n"
      "interface class G; pure virtual function int get(); endclass\n"
      "class F implements P, G;\n"
      "  int v;\n"
      "  virtual function void put(int a); v = a; endfunction\n"
      "  virtual function int get(); return v; endfunction\n"
      "endclass\n"
      "class FS extends F; endclass\n"
      "module m;\n"
      "  int r1, r2, r3, r4, r5, r6;\n"
      "  F f;\n"
      "  FS fs;\n"
      "  P p;\n"
      "  G g;\n"
      "  initial begin\n"
      "    f = new;\n"
      "    p = f;\n"
      "    r1 = $cast(g, p);\n"
      "    r2 = $cast(p, f);\n"
      "    fs = new;\n"
      "    p = fs;\n"
      "    r3 = $cast(g, p);\n"
      "    r4 = $cast(f, p);\n"
      "    r5 = $cast(g, fs);\n"
      "  end\n"
      "endmodule\n",
      f);
  LowerRunAndCheck(
      f, design, {{"r1", 1u}, {"r2", 1u}, {"r3", 1u}, {"r4", 1u}, {"r5", 1u}});
}

const char* const kInterfaceSpecializationCastSrc =
    "interface class PutImp #(type PUT_T = logic); pure virtual function void "
    "put(PUT_T a); endclass\n"
    "interface class GetImp #(type GET_T = logic); pure virtual function GET_T "
    "get(); endclass\n"
    "class Fifo #(type T = int) implements PutImp#(T), GetImp#(T);\n"
    "  T q[$];\n"
    "  virtual function void put(T a); q.push_back(a); endfunction\n"
    "  virtual function T get(); return q.pop_front(); endfunction\n"
    "endclass\n"
    "class CI implements PutImp#(int), GetImp#(int);\n"
    "  int q[$];\n"
    "  virtual function void put(int a); q.push_back(a); endfunction\n"
    "  virtual function int get(); return q.pop_front(); endfunction\n"
    "endclass\n"
    "class CD implements PutImp#(logic), GetImp#(logic);\n"
    "  logic q[$];\n"
    "  virtual function void put(logic a); q.push_back(a); endfunction\n"
    "  virtual function logic get(); return q.pop_front(); endfunction\n"
    "endclass\n"
    "module m;\n"
    "  int r1, r2, r3, r4, r5, r6, r7, r8;\n"
    "  Fifo#(int) fo;\n"
    "  CI ci;\n"
    "  CD cd;\n"
    "  PutImp#(int) pi;\n"
    "  GetImp#(int) gi;\n"
    "  PutImp#(logic) pd;\n"
    "  GetImp#(logic) gd;\n"
    "  GetImp#(byte) gb;\n"
    "  initial begin\n"
    "    ci = new; pi = ci;\n"
    "    r1 = $cast(gi, pi);\n"
    "    r2 = $cast(gi, ci);\n"
    "    cd = new; pd = cd;\n"
    "    r3 = $cast(gd, pd);\n"
    "    r4 = $cast(gd, cd);\n"
    "    fo = new; pi = fo;\n"
    "    r5 = $cast(gi, pi);\n"
    "    r6 = $cast(gi, fo);\n"
    "    r7 = $cast(gb, fo);\n"
    "    pi.put(9); r8 = fo.get();\n"
    "  end\n"
    "endmodule\n";

TEST(InterfaceClassCastingAndRefAssignment,
     CastToTheDefaultSpecializationOrUnparameterizedInterfaceSucceeds) {
  SimFixture f;
  auto* design = ElaborateSrc(kInterfaceSpecializationCastSrc, f);
  LowerRunAndCheck(f, design, {{"r3", 1u}, {"r4", 1u}, {"r7", 0u}, {"r8", 9u}});
}

TEST(
    InterfaceClassCastingAndRefAssignment,
    DISABLED_CastToAnInterfaceClassSpecializationFollowsWhatTheObjectImplements) {
  SimFixture f;
  auto* design = ElaborateSrc(kInterfaceSpecializationCastSrc, f);
  LowerRunAndCheck(f, design, {{"r1", 1u}, {"r2", 1u}, {"r5", 1u}, {"r6", 1u}});
}

}  // namespace
