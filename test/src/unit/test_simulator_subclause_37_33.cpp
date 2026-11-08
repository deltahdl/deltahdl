#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "simulator/sv_vpi_user.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class ClassVariablesAndObjects : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

std::vector<vpiHandle> ScanAll(vpiHandle it) {
  std::vector<vpiHandle> seen;
  if (!it) return seen;
  while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
  return seen;
}

TEST_F(ClassVariablesAndObjects, ClassObjectReportsItsObjectId) {
  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.obj_id = 42;

  EXPECT_EQ(vpi_get(vpiObjId, VpiHandleOf(&class_obj)), 42);
}

TEST_F(ClassVariablesAndObjects, ClassVariableReportsReferencedObjectId) {
  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.obj_id = 7;

  VpiObject referencing_var;
  referencing_var.type = vpiClassVar;
  referencing_var.referenced_object = &class_obj;
  EXPECT_EQ(vpi_get(vpiObjId, VpiHandleOf(&referencing_var)), 7);

  VpiObject null_var;
  null_var.type = vpiClassVar;
  EXPECT_EQ(vpi_get(vpiObjId, VpiHandleOf(&null_var)), 0);
}

TEST_F(ClassVariablesAndObjects,
       WaitingProcessesIterationReturnsWaitingThreads) {
  VpiObject waiter_a;
  waiter_a.type = vpiThread;
  VpiObject not_a_thread;
  not_a_thread.type = vpiConstant;
  VpiObject waiter_b;
  waiter_b.type = vpiThread;

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&waiter_a, &not_a_thread, &waiter_b};

  vpiHandle it = vpi_iterate(vpiWaitingProcesses, VpiHandleOf(&class_obj));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &waiter_a);
  EXPECT_EQ(VpiObjectOf(seen[1]), &waiter_b);
}

TEST_F(ClassVariablesAndObjects, MessagesIterationReturnsMailboxMessages) {
  VpiObject message_a;
  message_a.type = vpiConstant;
  VpiObject not_a_message;
  not_a_message.type = vpiThread;
  VpiObject message_b;
  message_b.type = vpiOperation;

  VpiObject mailbox;
  mailbox.type = vpiClassObj;
  mailbox.children = {&message_a, &not_a_message, &message_b};

  vpiHandle it = vpi_iterate(vpiMessages, VpiHandleOf(&mailbox));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &message_a);
  EXPECT_EQ(VpiObjectOf(seen[1]), &message_b);
}

TEST_F(ClassVariablesAndObjects, ClassObjRelationReachesReferencedObject) {
  VpiObject class_obj;
  class_obj.type = vpiClassObj;

  VpiObject referencing_var;
  referencing_var.type = vpiClassVar;
  referencing_var.referenced_object = &class_obj;
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassObj, VpiHandleOf(&referencing_var))),
            &class_obj);

  VpiObject null_var;
  null_var.type = vpiClassVar;
  EXPECT_EQ(vpi_handle(vpiClassObj, VpiHandleOf(&null_var)), nullptr);
}

TEST_F(ClassVariablesAndObjects, ClassTypespecDiffersBetweenVariableAndObject) {
  VpiObject declared_typespec;
  declared_typespec.type = vpiClassTypespec;
  declared_typespec.name = "Packet";

  VpiObject created_typespec;
  created_typespec.type = vpiClassTypespec;
  created_typespec.name = "LinkedPacket";

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&created_typespec};

  VpiObject class_var;
  class_var.type = vpiClassVar;
  class_var.children = {&declared_typespec};
  class_var.referenced_object = &class_obj;

  vpiHandle from_var = vpi_handle(vpiClassTypespec, VpiHandleOf(&class_var));
  vpiHandle from_obj = vpi_handle(vpiClassTypespec, VpiHandleOf(&class_obj));
  ASSERT_EQ(VpiObjectOf(from_var), &declared_typespec);
  ASSERT_EQ(VpiObjectOf(from_obj), &created_typespec);
  EXPECT_NE(from_var, from_obj);
}

TEST_F(ClassVariablesAndObjects,
       MethodsIterationFromObjectExcludesBuiltinsAcrossLifetimes) {
  VpiObject static_method;
  static_method.type = vpiFunction;
  static_method.automatic = false;
  VpiObject implicit_builtin;
  implicit_builtin.type = vpiFunction;
  implicit_builtin.implicit_builtin_method = true;
  VpiObject automatic_method;
  automatic_method.type = vpiTask;
  automatic_method.automatic = true;
  VpiObject member_var;
  member_var.type = vpiLogicVar;

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&static_method, &member_var, &implicit_builtin,
                        &automatic_method};

  vpiHandle it = vpi_iterate(vpiMethods, VpiHandleOf(&class_obj));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &static_method);
  EXPECT_EQ(VpiObjectOf(seen[1]), &automatic_method);
}

TEST_F(ClassVariablesAndObjects,
       VariablesIterationFromObjectReturnsBothLifetimes) {
  VpiObject static_var;
  static_var.type = vpiLogicVar;
  static_var.automatic = false;
  VpiObject automatic_var;
  automatic_var.type = vpiIntVar;
  automatic_var.automatic = true;

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&static_var, &automatic_var};

  vpiHandle it = vpi_iterate(vpiVariables, VpiHandleOf(&class_obj));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &static_var);
  EXPECT_EQ(VpiObjectOf(seen[1]), &automatic_var);
}

TEST_F(ClassVariablesAndObjects,
       NamedEventIterationsFromObjectReturnBothLifetimes) {
  VpiObject static_event;
  static_event.type = vpiNamedEvent;
  static_event.automatic = false;
  VpiObject automatic_event;
  automatic_event.type = vpiNamedEvent;
  automatic_event.automatic = true;
  VpiObject event_array;
  event_array.type = vpiNamedEventArray;

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&static_event, &event_array, &automatic_event};

  vpiHandle ev_it = vpi_iterate(vpiNamedEvent, VpiHandleOf(&class_obj));
  ASSERT_NE(ev_it, nullptr);
  std::vector<vpiHandle> events = ScanAll(ev_it);
  ASSERT_EQ(events.size(), 2u);
  EXPECT_EQ(VpiObjectOf(events[0]), &static_event);
  EXPECT_EQ(VpiObjectOf(events[1]), &automatic_event);

  vpiHandle arr_it = vpi_iterate(vpiNamedEventArray, VpiHandleOf(&class_obj));
  ASSERT_NE(arr_it, nullptr);
  std::vector<vpiHandle> arrays = ScanAll(arr_it);
  ASSERT_EQ(arrays.size(), 1u);
  EXPECT_EQ(VpiObjectOf(arrays[0]), &event_array);
}

TEST_F(ClassVariablesAndObjects,
       VirtualInterfaceVarIterationExpandsArrayWhileVariablesReportsItWhole) {
  VpiObject scalar_vif;
  scalar_vif.type = vpiVirtualInterfaceVar;
  VpiObject vif_elem0;
  vif_elem0.type = vpiVirtualInterfaceVar;
  VpiObject vif_elem1;
  vif_elem1.type = vpiVirtualInterfaceVar;
  VpiObject vif_array;
  vif_array.type = vpiArrayVar;
  vif_array.children = {&vif_elem0, &vif_elem1};

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&scalar_vif, &vif_array};

  vpiHandle vif_it =
      vpi_iterate(vpiVirtualInterfaceVar, VpiHandleOf(&class_obj));
  ASSERT_NE(vif_it, nullptr);
  std::vector<vpiHandle> vifs = ScanAll(vif_it);
  ASSERT_EQ(vifs.size(), 3u);
  EXPECT_EQ(VpiObjectOf(vifs[0]), &scalar_vif);
  EXPECT_EQ(VpiObjectOf(vifs[1]), &vif_elem0);
  EXPECT_EQ(VpiObjectOf(vifs[2]), &vif_elem1);

  vpiHandle var_it = vpi_iterate(vpiVariables, VpiHandleOf(&class_obj));
  ASSERT_NE(var_it, nullptr);
  std::vector<vpiHandle> vars = ScanAll(var_it);
  ASSERT_EQ(vars.size(), 2u);
  EXPECT_EQ(VpiObjectOf(vars[0]), &scalar_vif);
  EXPECT_EQ(VpiObjectOf(vars[1]), &vif_array);
}

TEST_F(ClassVariablesAndObjects,
       ParameterIterationReturnsPortAndBodyParameters) {
  VpiObject port_param;
  port_param.type = vpiParameter;
  port_param.local_param = false;
  VpiObject body_param;
  body_param.type = vpiParameter;
  body_param.local_param = true;

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&port_param, &body_param};

  vpiHandle it = vpi_iterate(vpiParameter, VpiHandleOf(&class_obj));
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &port_param);
  EXPECT_EQ(VpiObjectOf(seen[1]), &body_param);

  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&body_param)), 1);
  EXPECT_EQ(vpi_get(vpiLocalParam, VpiHandleOf(&port_param)), 0);
}

TEST_F(ClassVariablesAndObjects, HandleByNameReachesNonStaticDataMember) {
  VpiObject data_member;
  data_member.type = vpiIntegerVar;
  data_member.name = "Id";

  VpiObject packet_obj;
  packet_obj.type = vpiClassObj;
  packet_obj.children = {&data_member};

  VpiObject class_var;
  class_var.type = vpiClassVar;
  class_var.name = "p";
  class_var.referenced_object = &packet_obj;

  VpiObject top;
  top.type = vpiModule;
  top.children = {&class_var};

  EXPECT_EQ(VpiObjectOf(vpi_handle_by_name(VpiText("p.Id"), VpiHandleOf(&top))),
            &data_member);
}

int g_class_vars_seen = 0;
std::string g_class_var_name;
int g_declared_type = 0;
bool g_variables_class_reached_it = false;

PLI_INT32 ProbeClassVarsCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;

  vpiHandle itr = vpi_iterate(vpiClassVar, mod);
  if (itr != nullptr) {
    while (vpiHandle var = vpi_scan(itr)) {
      ++g_class_vars_seen;
      g_declared_type = vpi_get(vpiType, var);
      if (const char* name = vpi_get_str(vpiName, var)) g_class_var_name = name;
    }
  }

  vpiHandle vars = vpi_iterate(vpiVariables, mod);
  if (vars != nullptr) {
    while (vpiHandle var = vpi_scan(vars)) {
      if (vpi_get(vpiType, var) == vpiClassVar) {
        g_variables_class_reached_it = true;
      }
    }
  }
  return 0;
}

TEST(ClassVariablesDesign, ADeclaredClassVariableIsAClassVarObject) {
  VpiContext vpi_ctx;
  SetGlobalVpiContext(&vpi_ctx);
  g_class_vars_seen = 0;
  g_class_var_name.clear();
  g_declared_type = 0;
  g_variables_class_reached_it = false;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &ProbeClassVarsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  class Packet;\n"
      "    integer Id;\n"
      "  endclass\n"
      "  Packet p;\n"
      "  integer plain;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_class_vars_seen, 1);
  EXPECT_EQ(g_class_var_name, "p");
  EXPECT_EQ(g_declared_type, vpiClassVar);
  EXPECT_TRUE(g_variables_class_reached_it);
}

class ClassObjectsOfARun : public VpiDesignRun {
 protected:
  static int IntValueOf(vpiHandle obj) {
    s_vpi_value value = {};
    value.format = vpiIntVal;
    vpi_get_value(obj, &value);
    return value.value.integer;
  }
};

TEST_F(ClassObjectsOfARun, AClassVarReachesTheObjectItsValueNames) {
  Run("module top;\n"
      "  class B; int k = 7; endclass\n"
      "  class A; int n = 5; logic [3:0] q = 4'b1010; B b = new; endclass\n"
      "  class C extends A; int m = 9; endclass\n"
      "  A a = new;\n"
      "  C d = new;\n"
      "  A c;\n"
      "  A z;\n"
      "  initial c = d;\n"
      "endmodule\n");
  vpiHandle a = By("top.a");
  ASSERT_NE(a, nullptr);
  vpiHandle obj = vpi_handle(vpiClassObj, a);
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(vpi_get(vpiType, obj), vpiClassObj);
  EXPECT_EQ(vpi_handle(vpiClassObj, a), obj);
  EXPECT_NE(vpi_get64(vpiObjId, obj), 0);
  EXPECT_EQ(vpi_get64(vpiObjId, a), vpi_get64(vpiObjId, obj));
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiClassTypespec, obj)), "A");
  EXPECT_EQ(NamesOf(vpiVariables, obj),
            (std::vector<std::string>{"b", "n", "q"}));
  EXPECT_EQ(IntValueOf(Named(vpiVariables, obj, "n")), 5);
  EXPECT_EQ(IntValueOf(Named(vpiVariables, obj, "q")), 10);
  vpiHandle b = Named(vpiVariables, obj, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(vpi_get(vpiType, b), vpiClassVar);
  EXPECT_EQ(IntValueOf(Named(vpiVariables, vpi_handle(vpiClassObj, b), "k")),
            7);

  vpiHandle derived = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(derived, nullptr);
  EXPECT_EQ(derived, vpi_handle(vpiClassObj, By("top.d")));
  EXPECT_NE(vpi_get64(vpiObjId, derived), vpi_get64(vpiObjId, obj));
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiClassTypespec, derived)),
               "C");
  EXPECT_EQ(NamesOf(vpiVariables, derived),
            (std::vector<std::string>{"b", "m", "n", "q"}));
  EXPECT_EQ(IntValueOf(Named(vpiVariables, derived, "m")), 9);

  vpiHandle z = By("top.z");
  ASSERT_NE(z, nullptr);
  EXPECT_EQ(vpi_handle(vpiClassObj, z), nullptr);
  EXPECT_EQ(vpi_get64(vpiObjId, z), 0);
}

TEST_F(ClassObjectsOfARun, AClassObjsEventArrayIsANamedEventArray) {
  Run("module top;\n"
      "  class A; event ea[2]; int ia[2]; endclass\n"
      "  A a = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.a"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(NamesOf(vpiNamedEventArray, obj), std::vector<std::string>{"ea"});
  EXPECT_EQ(NamesOf(vpiVariables, obj), std::vector<std::string>{"ia"});
}

TEST_F(ClassObjectsOfARun, AValuePutToAPropertyVariableIsTheObjects) {
  Run("module top;\n"
      "  class A; int n = 5; static int s = 3; endclass\n"
      "  A a = new;\n"
      "  A e = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.a"));
  ASSERT_NE(obj, nullptr);
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 9;
  vpi_put_value(Named(vpiVariables, obj, "n"), &value, nullptr, vpiNoDelay);
  EXPECT_EQ(IntValueOf(Named(vpiVariables, obj, "n")), 9);
  value.value.integer = 8;
  vpi_put_value(Named(vpiVariables, obj, "s"), &value, nullptr, vpiNoDelay);
  vpiHandle other = vpi_handle(vpiClassObj, By("top.e"));
  ASSERT_NE(other, nullptr);
  EXPECT_EQ(IntValueOf(Named(vpiVariables, other, "s")), 8);
  EXPECT_EQ(IntValueOf(Named(vpiVariables, other, "n")), 5);
}

TEST_F(ClassObjectsOfARun, AClassObjsTypespecReachesTheClassDefn) {
  Run("module top;\n"
      "  class A; int n; endclass\n"
      "  class C extends A; int m; endclass\n"
      "  C d = new;\n"
      "  A c;\n"
      "  initial c = d;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(obj, nullptr);
  vpiHandle defn = vpi_handle(vpiClassDefn, vpi_handle(vpiClassTypespec, obj));
  ASSERT_NE(defn, nullptr);
  EXPECT_EQ(vpi_get(vpiType, defn), vpiClassDefn);
  EXPECT_STREQ(vpi_get_str(vpiName, defn), "C");
  EXPECT_EQ(VpiObjectOf(defn),
            VpiObjectOf(Named(vpiClassDefn, By("top"), "C")));
}

TEST_F(ClassObjectsOfARun, AClassObjReachesTheDefnOfItsOwnInstance) {
  Run("module m;\n"
      "  class A; int n; endclass\n"
      "  A a = new;\n"
      "  A b;\n"
      "  initial b = new;\n"
      "endmodule\n"
      "module top;\n"
      "  m u1();\n"
      "  m u2();\n"
      "endmodule\n");
  for (const std::string& inst : {"top.u1", "top.u2"}) {
    vpiHandle own = Named(vpiClassDefn, By(inst), "A");
    ASSERT_NE(own, nullptr);
    for (const std::string& var : {"a", "b"}) {
      std::string path = inst;
      path.append(".").append(var);
      vpiHandle obj = vpi_handle(vpiClassObj, By(path));
      ASSERT_NE(obj, nullptr);
      vpiHandle typespec = vpi_handle(vpiClassTypespec, obj);
      EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, typespec)),
                VpiObjectOf(own));
    }
  }
}

TEST_F(ClassObjectsOfARun, ANameThroughANullClassVariableReachesNothing) {
  Run("module top;\n"
      "  class C; int x; endclass\n"
      "  C c;\n"
      "endmodule\n");
  ASSERT_NE(vpi_handle_by_name(VpiText("top.c"), nullptr), nullptr);
  EXPECT_EQ(vpi_handle_by_name(VpiText("top.c.x"), nullptr), nullptr);
}
TEST_F(ClassObjectsOfARun, AClassObjReachesItsClasssMethods) {
  Run("module top;\n"
      "  class A; function int f(); return 1; endfunction\n"
      "    task t(); endtask\n"
      "  endclass\n"
      "  class C extends A; function int f(); return 2; endfunction\n"
      "    static function int g(); return 3; endfunction\n"
      "  endclass\n"
      "  C c = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(NamesOf(vpiMethods, obj),
            (std::vector<std::string>{"f", "g", "t"}));
  EXPECT_EQ(
      VpiObjectOf(Named(vpiMethods, obj, "f")),
      VpiObjectOf(Named(vpiMethods, Named(vpiClassDefn, By("top"), "C"), "f")));
  EXPECT_EQ(
      VpiObjectOf(Named(vpiMethods, obj, "t")),
      VpiObjectOf(Named(vpiMethods, Named(vpiClassDefn, By("top"), "A"), "t")));
}

TEST_F(ClassObjectsOfARun, AClassObjReachesItsClasssParameters) {
  Run("module top;\n"
      "  class P #(int N = 2, type T = int);\n"
      "    localparam int W = 4;\n"
      "    T v;\n"
      "  endclass\n"
      "  P #(5) p = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.p"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(NamesOf(vpiParameter, obj),
            (std::vector<std::string>{"N", "T", "W"}));
  vpiHandle n = Named(vpiParameter, obj, "N");
  vpiHandle w = Named(vpiParameter, obj, "W");
  ASSERT_NE(n, nullptr);
  ASSERT_NE(w, nullptr);
  EXPECT_EQ(IntValueOf(n), 5);
  EXPECT_EQ(vpi_get(vpiLocalParam, n), 0);
  EXPECT_EQ(IntValueOf(w), 4);
  EXPECT_EQ(vpi_get(vpiLocalParam, w), 1);
  EXPECT_NE(Named(vpiTypeParameter, obj, "T"), nullptr);
}

TEST_F(ClassObjectsOfARun, AClassVarReachesTheTypespecItWasDeclaredWith) {
  Run("class U; endclass\n"
      "package pk; class C; endclass class P; endclass endpackage\n"
      "module top; import pk::P;\n"
      "  class C; endclass\n"
      "  class D extends C; endclass\n"
      "  D d = new;\n"
      "  C c;\n"
      "  pk::C q;\n"
      "  U u;\n"
      "  P w;\n"
      "  initial c = d;\n"
      "endmodule\n");
  const auto kDefnOf = [](const char* var) {
    return vpi_handle(vpiClassDefn, vpi_handle(vpiClassTypespec, By(var)));
  };
  vpiHandle typespec = vpi_handle(vpiClassTypespec, By("top.c"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "C");
  EXPECT_STREQ(
      vpi_get_str(vpiName, vpi_handle(vpiClassTypespec,
                                      vpi_handle(vpiClassObj, By("top.c")))),
      "D");
  EXPECT_EQ(VpiObjectOf(kDefnOf("top.c")),
            VpiObjectOf(Named(vpiClassDefn, By("top"), "C")));
  EXPECT_EQ(VpiObjectOf(kDefnOf("top.q")),
            VpiObjectOf(Named(vpiClassDefn, By("pk"), "C")));
  EXPECT_EQ(VpiObjectOf(kDefnOf("top.u")),
            VpiObjectOf(Named(vpiClassDefn, nullptr, "U")));
  EXPECT_EQ(VpiObjectOf(kDefnOf("top.w")),
            VpiObjectOf(Named(vpiClassDefn, By("pk"), "P")));
}

TEST_F(ClassObjectsOfARun, AClassTypedPropertyReachesItsDeclaredTypespec) {
  Run("package p; class P; endclass endpackage\n"
      "module top;\n"
      "  class B; endclass\n"
      "  class D extends B; endclass\n"
      "  class A; B b; p::P q; int n; endclass\n"
      "  A a = new;\n"
      "  D d = new;\n"
      "  initial a.b = d;\n"
      "endmodule\n");
  vpiHandle b_defn = Named(vpiClassDefn, By("top"), "B");
  vpiHandle a_defn = Named(vpiClassDefn, By("top"), "A");
  vpiHandle typespec =
      vpi_handle(vpiClassTypespec, Named(vpiVariables, a_defn, "b"));
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "B");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, typespec)),
            VpiObjectOf(b_defn));
  vpiHandle q_typespec =
      vpi_handle(vpiClassTypespec, Named(vpiVariables, a_defn, "q"));
  ASSERT_NE(q_typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, q_typespec), "P");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, q_typespec)),
            VpiObjectOf(Named(vpiClassDefn, By("p"), "P")));
  vpiHandle b = Named(vpiVariables, vpi_handle(vpiClassObj, By("top.a")), "b");
  ASSERT_NE(b, nullptr);
  vpiHandle held = vpi_handle(vpiClassTypespec, b);
  ASSERT_NE(held, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, held), "B");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, held)), VpiObjectOf(b_defn));
  EXPECT_STREQ(vpi_get_str(vpiName, vpi_handle(vpiClassTypespec,
                                               vpi_handle(vpiClassObj, b))),
               "D");
}

TEST_F(ClassObjectsOfARun, APackageScopedClassPropertyIsAClassVarOfTheObject) {
  Run("package p; class P; endclass endpackage\n"
      "module top; class A; p::P q; endclass\n"
      "  A a = new;\n"
      "endmodule\n");
  vpiHandle q = Named(vpiVariables, vpi_handle(vpiClassObj, By("top.a")), "q");
  ASSERT_NE(q, nullptr);
  EXPECT_EQ(vpi_get(vpiType, q), vpiClassVar);
  vpiHandle typespec = vpi_handle(vpiClassTypespec, q);
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "P");
  EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, typespec)),
            VpiObjectOf(Named(vpiClassDefn, By("p"), "P")));
}

TEST_F(ClassObjectsOfARun, ATypedefDeclaredClassPropertyReachesItsClass) {
  Run("module top; class C; endclass typedef C c_t;\n"
      "  class A; c_t x; endclass\n"
      "  A a = new;\n"
      "endmodule\n");
  vpiHandle c_defn = Named(vpiClassDefn, By("top"), "C");
  for (vpiHandle holder : {Named(vpiClassDefn, By("top"), "A"),
                           vpi_handle(vpiClassObj, By("top.a"))}) {
    vpiHandle typespec =
        vpi_handle(vpiClassTypespec, Named(vpiVariables, holder, "x"));
    ASSERT_NE(typespec, nullptr);
    EXPECT_STREQ(vpi_get_str(vpiName, typespec), "C");
    EXPECT_EQ(VpiObjectOf(vpi_handle(vpiClassDefn, typespec)),
              VpiObjectOf(c_defn));
  }
}

TEST_F(ClassObjectsOfARun, ANestedClassObjectHoldsItsClassTypedProperty) {
  Run("module top; class B; endclass\n"
      "  class O; class I; B b; endclass endclass\n"
      "  O::I i = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.i"));
  ASSERT_NE(obj, nullptr);
  vpiHandle b = Named(vpiVariables, obj, "b");
  ASSERT_NE(b, nullptr);
  EXPECT_EQ(vpi_get(vpiType, b), vpiClassVar);
}

TEST_F(ClassObjectsOfARun, AMailboxsClassObjIteratesItsMessagesAndWaiters) {
  Run("module top; mailbox m = new; mailbox e = new; semaphore s = new(0);\n"
      "  initial begin m.put(7); m.put(2.5); m.put(\"ab\"); end\n"
      "  initial begin int x; e.get(x); end\n"
      "  initial s.get(1);\n"
      "endmodule\n");
  vpiHandle m = vpi_handle(vpiClassObj, By("top.m"));
  ASSERT_NE(m, nullptr);
  EXPECT_EQ(vpi_handle(vpiClassObj, By("top.m")), m);
  EXPECT_EQ(vpi_get64(vpiObjId, m), vpi_get64(vpiObjId, By("top.m")));
  vpiHandle typespec = vpi_handle(vpiClassTypespec, m);
  ASSERT_NE(typespec, nullptr);
  EXPECT_STREQ(vpi_get_str(vpiName, typespec), "mailbox");
  EXPECT_EQ(vpi_handle(vpiClassDefn, typespec), nullptr);
  const std::vector<vpiHandle> kMessages = ObjectsOf(vpiMessages, m);
  ASSERT_EQ(kMessages.size(), 3U);
  EXPECT_EQ(IntValueOf(kMessages[0]), 7);
  EXPECT_EQ(vpi_get(vpiConstType, kMessages[0]), vpiBinaryConst);
  EXPECT_EQ(vpi_get(vpiConstType, kMessages[1]), vpiRealConst);
  EXPECT_EQ(vpi_get(vpiConstType, kMessages[2]), vpiStringConst);
  EXPECT_TRUE(ObjectsOf(vpiWaitingProcesses, m).empty());
  for (const char* waited : {"top.e", "top.s"}) {
    vpiHandle obj = vpi_handle(vpiClassObj, By(waited));
    ASSERT_NE(obj, nullptr) << waited;
    const std::vector<vpiHandle> kWaiting = ObjectsOf(vpiWaitingProcesses, obj);
    ASSERT_EQ(kWaiting.size(), 1U) << waited;
    EXPECT_EQ(vpi_get(vpiType, kWaiting[0]), vpiThread) << waited;
  }
  EXPECT_STREQ(
      vpi_get_str(vpiName, vpi_handle(vpiClassTypespec,
                                      vpi_handle(vpiClassObj, By("top.s")))),
      "semaphore");
}

TEST_F(ClassObjectsOfARun,
       AParameterizedMailboxsMessagesHaveItsTypesConstType) {
  Run("module top; mailbox #(string) t = new; mailbox #(real) u = new;\n"
      "  initial begin t.put(\"ab\"); u.put(2.5); end\n"
      "endmodule\n");
  const std::vector<vpiHandle> kStrings =
      ObjectsOf(vpiMessages, vpi_handle(vpiClassObj, By("top.t")));
  ASSERT_EQ(kStrings.size(), 1U);
  EXPECT_EQ(vpi_get(vpiConstType, kStrings[0]), vpiStringConst);
  const std::vector<vpiHandle> kReals =
      ObjectsOf(vpiMessages, vpi_handle(vpiClassObj, By("top.u")));
  ASSERT_EQ(kReals.size(), 1U);
  EXPECT_EQ(vpi_get(vpiConstType, kReals[0]), vpiRealConst);
}

TEST_F(ClassObjectsOfARun, AClassObjsVirtualInterfaceArrayIsIteratedByElement) {
  Run("interface ifc; endinterface\n"
      "module top; ifc i0 ();\n"
      "  class C; virtual ifc vs [2]; virtual ifc v; int n; endclass\n"
      "  C c = new;\n"
      "endmodule\n");
  vpiHandle obj = vpi_handle(vpiClassObj, By("top.c"));
  ASSERT_NE(obj, nullptr);
  EXPECT_EQ(NamesOf(vpiVirtualInterfaceVar, obj),
            (std::vector<std::string>{"v", "vs[0]", "vs[1]"}));
}
}  // namespace
}  // namespace delta
