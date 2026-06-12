#include <gtest/gtest.h>

#include <vector>

#include "simulator/sv_vpi_user.h"
#include "simulator/vpi.h"

namespace delta {
namespace {

// §37.33 Class variables and class objects: the VPI object model for a class
// variable (class var) and the class object (class obj) it references. The
// figure's structural edges that are plain type matches (constraint, the
// internal scope, the class typespec child) are served by the generic
// object-model machinery; the tests below observe the Details that need
// dedicated production code or that this clause specifically blesses:
//   - Detail 1: a class object reports its own unique identifier (vpiObjId).
//   - Detail 2: a class variable reports the identifier of the object it
//     references, or 0 when it references none.
//   - Detail 3: vpiWaitingProcesses on a class object (mailbox/semaphore) reaches
//     the threads of the processes waiting on it.
//   - Detail 4: vpiMessages on a class object (mailbox) reaches its messages.
//   - Detail 5: vpiClassObj of a class variable reaches the referenced object
//     (null when it references none); vpiClassTypespec distinguishes the type a
//     variable was declared with from the type the object was created with.
//   - Detail 6: vpiMethods from a class object returns the explicitly declared
//     methods of both lifetimes and omits implicit built-ins.
//   - Detail 7: vpiVirtualInterfaceVar expands a declared array of virtual
//     interfaces into its elements, while vpiVariables reports that array whole.
//   - Detail 8: vpiParameter returns both parameter-port-list and body
//     parameters; vpiLocalParam is TRUE for the body ones (§37.28).
//   - Detail 9: vpi_handle_by_name() reaches a non-static data member through the
//     class variable that holds the object.

// The fixture installs a context so the public vpi_get/vpi_iterate/vpi_scan/
// VpiHandleC/vpi_handle_by_name entry points run their real dispatch.
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

// D1: a class object's vpiObjId is its own identifier.
TEST_F(ClassVariablesAndObjects, ClassObjectReportsItsObjectId) {
  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.obj_id = 42;

  EXPECT_EQ(vpi_get(vpiObjId, &class_obj), 42);
}

// D2: a class variable does not carry its own identifier - it reports the
// identifier of the object it references. A class variable that references no
// object (it holds null) reports 0.
TEST_F(ClassVariablesAndObjects, ClassVariableReportsReferencedObjectId) {
  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.obj_id = 7;

  VpiObject referencing_var;
  referencing_var.type = vpiClassVar;
  referencing_var.referenced_object = &class_obj;
  EXPECT_EQ(vpi_get(vpiObjId, &referencing_var), 7);

  VpiObject null_var;
  null_var.type = vpiClassVar;  // references nothing
  EXPECT_EQ(vpi_get(vpiObjId, &null_var), 0);
}

// D3: a class object's vpiWaitingProcesses iteration reaches the thread objects
// of the processes waiting on it (a mailbox or semaphore resource). The targets
// are threads, so a non-thread child is never reported.
TEST_F(ClassVariablesAndObjects, WaitingProcessesIterationReturnsWaitingThreads) {
  VpiObject waiter_a;
  waiter_a.type = vpiThread;
  VpiObject not_a_thread;
  not_a_thread.type = vpiConstant;
  VpiObject waiter_b;
  waiter_b.type = vpiThread;

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&waiter_a, &not_a_thread, &waiter_b};

  vpiHandle it = vpi_iterate(vpiWaitingProcesses, &class_obj);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &waiter_a);
  EXPECT_EQ(seen[1], &waiter_b);
}

// D4: a class object's vpiMessages iteration reaches the messages a mailbox
// holds, which are expression objects. A non-expression child is not a message
// and never appears.
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

  vpiHandle it = vpi_iterate(vpiMessages, &mailbox);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &message_a);
  EXPECT_EQ(seen[1], &message_b);
}

// D5: vpiClassObj of a class variable reaches the object it references. A class
// variable holding null references nothing, so the relation reports a null
// handle.
TEST_F(ClassVariablesAndObjects, ClassObjRelationReachesReferencedObject) {
  VpiObject class_obj;
  class_obj.type = vpiClassObj;

  VpiObject referencing_var;
  referencing_var.type = vpiClassVar;
  referencing_var.referenced_object = &class_obj;
  EXPECT_EQ(VpiHandleC(vpiClassObj, &referencing_var), &class_obj);

  VpiObject null_var;
  null_var.type = vpiClassVar;  // references nothing
  EXPECT_EQ(VpiHandleC(vpiClassObj, &null_var), nullptr);
}

// D5: vpiClassTypespec of a class variable is the type the variable was declared
// with, while vpiClassTypespec of the class object is the type the object was
// created with. When a base-class variable references a derived-class object the
// two differ (the LRM's Packet variable vs. its LinkedPacket object).
TEST_F(ClassVariablesAndObjects, ClassTypespecDiffersBetweenVariableAndObject) {
  VpiObject declared_typespec;  // "Packet"
  declared_typespec.type = vpiClassTypespec;
  declared_typespec.name = "Packet";

  VpiObject created_typespec;  // "LinkedPacket"
  created_typespec.type = vpiClassTypespec;
  created_typespec.name = "LinkedPacket";

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&created_typespec};

  VpiObject class_var;
  class_var.type = vpiClassVar;
  class_var.children = {&declared_typespec};
  class_var.referenced_object = &class_obj;

  vpiHandle from_var = VpiHandleC(vpiClassTypespec, &class_var);
  vpiHandle from_obj = VpiHandleC(vpiClassTypespec, &class_obj);
  ASSERT_EQ(from_var, &declared_typespec);
  ASSERT_EQ(from_obj, &created_typespec);
  EXPECT_NE(from_var, from_obj);
}

// D6: a class object's vpiMethods iteration returns the explicitly declared
// methods - of both lifetimes, a static one and an automatic one - and omits an
// implicit built-in method (one provided with no explicit declaration). A
// non-method child is never a method.
TEST_F(ClassVariablesAndObjects,
       MethodsIterationFromObjectExcludesBuiltinsAcrossLifetimes) {
  VpiObject static_method;
  static_method.type = vpiFunction;
  static_method.automatic = false;  // static property/method
  VpiObject implicit_builtin;
  implicit_builtin.type = vpiFunction;
  implicit_builtin.implicit_builtin_method = true;  // dropped
  VpiObject automatic_method;
  automatic_method.type = vpiTask;
  automatic_method.automatic = true;  // automatic property/method
  VpiObject member_var;
  member_var.type = vpiVariables;  // not a method

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&static_method, &member_var, &implicit_builtin,
                        &automatic_method};

  vpiHandle it = vpi_iterate(vpiMethods, &class_obj);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);

  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &static_method);
  EXPECT_EQ(seen[1], &automatic_method);
}

// D6: a class object's vpiVariables iteration returns the class's data members
// of both lifetimes - a static one and an automatic one - since the iteration is
// not filtered by declared lifetime. (The companion rule that an array of
// virtual interfaces is reported as a single array var is exercised separately.)
TEST_F(ClassVariablesAndObjects, VariablesIterationFromObjectReturnsBothLifetimes) {
  VpiObject static_var;
  static_var.type = vpiVariables;
  static_var.automatic = false;  // static property
  VpiObject automatic_var;
  automatic_var.type = vpiVariables;
  automatic_var.automatic = true;  // automatic property

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&static_var, &automatic_var};

  vpiHandle it = vpi_iterate(vpiVariables, &class_obj);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &static_var);
  EXPECT_EQ(seen[1], &automatic_var);
}

// D6: the same lifetime-agnostic rule covers the class object's named events.
// vpiNamedEvent returns the class's named events of both lifetimes - a static
// one and an automatic one - and vpiNamedEventArray returns its named event
// arrays. Each relation reaches only objects of its own kind, so a child of the
// other kind is not reported.
TEST_F(ClassVariablesAndObjects, NamedEventIterationsFromObjectReturnBothLifetimes) {
  VpiObject static_event;
  static_event.type = vpiNamedEvent;
  static_event.automatic = false;  // static property
  VpiObject automatic_event;
  automatic_event.type = vpiNamedEvent;
  automatic_event.automatic = true;  // automatic property
  VpiObject event_array;
  event_array.type = vpiNamedEventArray;

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&static_event, &event_array, &automatic_event};

  vpiHandle ev_it = vpi_iterate(vpiNamedEvent, &class_obj);
  ASSERT_NE(ev_it, nullptr);
  std::vector<vpiHandle> events = ScanAll(ev_it);
  ASSERT_EQ(events.size(), 2u);
  EXPECT_EQ(events[0], &static_event);
  EXPECT_EQ(events[1], &automatic_event);

  vpiHandle arr_it = vpi_iterate(vpiNamedEventArray, &class_obj);
  ASSERT_NE(arr_it, nullptr);
  std::vector<vpiHandle> arrays = ScanAll(arr_it);
  ASSERT_EQ(arrays.size(), 1u);
  EXPECT_EQ(arrays[0], &event_array);
}

// D7: vpiVirtualInterfaceVar from a class object returns the virtual interface
// var declarations, expanding a declared array of virtual interfaces into its
// individual elements; whereas vpiVariables reports that same array declaration
// as the single array var that declares it.
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

  vpiHandle vif_it = vpi_iterate(vpiVirtualInterfaceVar, &class_obj);
  ASSERT_NE(vif_it, nullptr);
  std::vector<vpiHandle> vifs = ScanAll(vif_it);
  ASSERT_EQ(vifs.size(), 3u);
  EXPECT_EQ(vifs[0], &scalar_vif);
  EXPECT_EQ(vifs[1], &vif_elem0);
  EXPECT_EQ(vifs[2], &vif_elem1);

  vpiHandle var_it = vpi_iterate(vpiVariables, &class_obj);
  ASSERT_NE(var_it, nullptr);
  std::vector<vpiHandle> vars = ScanAll(var_it);
  ASSERT_EQ(vars.size(), 1u);
  EXPECT_EQ(vars[0], &vif_array);
}

// D8: a class object's vpiParameter iteration returns both the parameters from
// the parameter port list and those declared within the body as class items.
// vpiLocalParam (§37.28) is TRUE for a body parameter and FALSE for a port-list
// one, which is how the two origins are told apart.
TEST_F(ClassVariablesAndObjects, ParameterIterationReturnsPortAndBodyParameters) {
  VpiObject port_param;
  port_param.type = vpiParameter;
  port_param.local_param = false;  // parameter port list
  VpiObject body_param;
  body_param.type = vpiParameter;
  body_param.local_param = true;  // declared in the body

  VpiObject class_obj;
  class_obj.type = vpiClassObj;
  class_obj.children = {&port_param, &body_param};

  vpiHandle it = vpi_iterate(vpiParameter, &class_obj);
  ASSERT_NE(it, nullptr);
  std::vector<vpiHandle> seen = ScanAll(it);
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(seen[0], &port_param);
  EXPECT_EQ(seen[1], &body_param);

  EXPECT_EQ(vpi_get(vpiLocalParam, &body_param), 1);
  EXPECT_EQ(vpi_get(vpiLocalParam, &port_param), 0);
}

// D9: vpi_handle_by_name() accepts a full name down to a non-static data member.
// The member lives on the class object the variable references, so resolution
// descends through the class variable into that object's members; the member is
// reachable even though it is non-static and therefore carries no full name.
TEST_F(ClassVariablesAndObjects, HandleByNameReachesNonStaticDataMember) {
  VpiObject data_member;  // the "Id" member of class Packet
  data_member.type = vpiIntegerVar;
  data_member.name = "Id";  // non-static: no vpiFullName of its own

  VpiObject packet_obj;
  packet_obj.type = vpiClassObj;
  packet_obj.children = {&data_member};

  VpiObject class_var;  // "p", a Packet handle
  class_var.type = vpiClassVar;
  class_var.name = "p";
  class_var.referenced_object = &packet_obj;

  VpiObject top;
  top.type = vpiModule;
  top.children = {&class_var};

  // Resolved relative to top, "p.Id" reaches the member through the variable.
  EXPECT_EQ(vpi_handle_by_name("p.Id", &top), &data_member);
}

}  // namespace
}  // namespace delta
