#include <gtest/gtest.h>

#include <cstring>
#include <vector>

#include "simulator/vpi.h"

namespace delta {
namespace {

// §38.37.3 ("Registering multiple system tasks and system functions") says that
// "multiple system tasks and system functions can be registered at least two
// different ways": separate s_vpi_systf_data structures with one
// vpi_register_systf() call apiece, which is the method §38.37.1 and §38.37.2
// use, or "a static array of s_vpi_systf_data structures" with one call per
// structure in it. Of the second it adds the rule that makes the clause's own
// loop work: "If the final element in the array is set to 0, then the calls to
// vpi_register_systf() can be placed in a loop that terminates when it reaches
// the 0." These tests register the clause's own three-entry list both ways and
// observe the tool answering each structure separately, stopping at the zero,
// and refusing the zero as a registration.

int MyTaskCalltf(const char*) { return 0; }
int MyTaskComptf(const char*) { return 0; }
int MyIntFuncCalltf(const char*) { return 0; }
int MyIntFuncComptf(const char*) { return 0; }
int MySizedFuncCalltf(const char*) { return 0; }
int MySizedFuncComptf(const char*) { return 0; }
int MySizedFuncSizetf(const char*) { return 8; }

// §38.37.3's example list: a system task, an integer system function and a
// sized system function, with a zero final element ending the array. The
// entries are returned rather than declared at namespace scope so that each
// test walks a list no other test has registered from.
struct SystfTestList {
  s_vpi_systf_data entries[4] = {};
};

SystfTestList MakeSystfTestList() {
  SystfTestList list;
  list.entries[0].type = vpiSysTask;
  list.entries[0].tfname = "$my_task";
  list.entries[0].calltf = &MyTaskCalltf;
  list.entries[0].compiletf = &MyTaskComptf;

  list.entries[1].type = vpiSysFunc;
  list.entries[1].sysfunctype = vpiIntFunc;
  list.entries[1].tfname = "$my_int_func";
  list.entries[1].calltf = &MyIntFuncCalltf;
  list.entries[1].compiletf = &MyIntFuncComptf;

  list.entries[2].type = vpiSysFunc;
  list.entries[2].sysfunctype = vpiSizedFunc;
  list.entries[2].tfname = "$my_sized_func";
  list.entries[2].calltf = &MySizedFuncCalltf;
  list.entries[2].compiletf = &MySizedFuncComptf;
  list.entries[2].sizetf = &MySizedFuncSizetf;

  // §38.37.3: "shall be last entry in list" - the element set to 0.
  return list;
}

// §38.37.3's loop: "the calls to vpi_register_systf() can be placed in a loop
// that terminates when it reaches the 0", the 0 being read out of the type
// field of the final element.
int RegisterFromList(SystfTestList& list) {
  int registered = 0;
  for (p_vpi_systf_data p = &list.entries[0]; p->type != 0; ++p) {
    if (vpi_register_systf(p) != nullptr) ++registered;
  }
  return registered;
}

class VpiMultipleSystfRegistration : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

// §38.37.3, second method: one vpi_register_systf() call per structure in a
// static array registers every one of them. Each structure keeps its own name,
// type, return-value kind and routines, so the three registrations are three
// different system tasks and functions rather than one overwritten three times.
TEST_F(VpiMultipleSystfRegistration, StaticArrayRegistersEveryStructureInIt) {
  SystfTestList list = MakeSystfTestList();

  EXPECT_EQ(RegisterFromList(list), 3);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 3u);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[0].tfname, "$my_task");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[0].type, vpiSysTask);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[0].calltf, &MyTaskCalltf);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[1].tfname, "$my_int_func");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].sysfunctype, vpiIntFunc);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[1].calltf, &MyIntFuncCalltf);
  EXPECT_STREQ(vpi_ctx_.RegisteredSystfs()[2].tfname, "$my_sized_func");
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[2].sysfunctype, vpiSizedFunc);
  EXPECT_EQ(vpi_ctx_.RegisteredSystfs()[2].sizetf, &MySizedFuncSizetf);
}

// §38.37.3: each call in the loop is a registration of its own, so each answers
// with its own callback object and each object reads back the structure that
// registered it. A tool that kept one record for the array would hand the same
// handle back, or read the last structure out of every one of them.
TEST_F(VpiMultipleSystfRegistration, EachStructureAnswersWithItsOwnCallback) {
  SystfTestList list = MakeSystfTestList();

  vpiHandle task = vpi_register_systf(&list.entries[0]);
  vpiHandle func = vpi_register_systf(&list.entries[1]);
  ASSERT_NE(task, nullptr);
  ASSERT_NE(func, nullptr);
  EXPECT_NE(task, func);

  s_vpi_systf_data read_back = {};
  vpi_get_systf_info(task, &read_back);
  EXPECT_STREQ(read_back.tfname, "$my_task");
  EXPECT_EQ(read_back.type, vpiSysTask);

  vpi_get_systf_info(func, &read_back);
  EXPECT_STREQ(read_back.tfname, "$my_int_func");
  EXPECT_EQ(read_back.sysfunctype, vpiIntFunc);
}

// §38.37.3: the zero final element ends the list. A loop that terminates on it
// registers the three structures ahead of it and nothing else, so the element
// itself leaves no nameless system task behind in the registry.
TEST_F(VpiMultipleSystfRegistration, LoopStopsAtTheZeroFinalElement) {
  SystfTestList list = MakeSystfTestList();

  RegisterFromList(list);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 3u);
  for (const VpiSystfData& registered : vpi_ctx_.RegisteredSystfs()) {
    ASSERT_NE(registered.tfname, nullptr);
    EXPECT_NE(std::strcmp(registered.tfname, ""), 0);
  }
}

// §38.37.3: the zero is the end of the list rather than a structure to
// register, which is what lets a loop use it as its terminating condition. A
// loop written one element too long hands it to vpi_register_systf() anyway,
// and the refusal is what keeps it out of the registry: §38.37.1 has the type
// field carry "an integer constant of vpiSysTask or vpiSysFunc", and the zeroed
// element carries neither.
TEST_F(VpiMultipleSystfRegistration, ZeroFinalElementIsRefusedAsARegistration) {
  SystfTestList list = MakeSystfTestList();

  EXPECT_EQ(vpi_register_systf(&list.entries[3]), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());

  SVpiErrorInfo info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_STREQ(info.message,
               "system task or function registration must carry a type of "
               "vpiSysTask or vpiSysFunc");
}

// §38.37.1 by way of §38.37.3: a type of neither vpiSysTask nor vpiSysFunc is
// no more registrable than the zero terminator, whatever else the structure
// carries. A well-formed name and a full set of routines do not make a record
// whose type field names no kind of application into one.
TEST_F(VpiMultipleSystfRegistration, TypeOutsideTheTwoConstantsIsRefused) {
  s_vpi_systf_data data = {};
  data.type = vpiSysFuncCall;
  data.tfname = "$neither";
  data.calltf = &MyTaskCalltf;
  data.compiletf = &MyTaskComptf;

  EXPECT_EQ(vpi_register_systf(&data), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

// §38.37.3, first method: "allocate and define separate s_vpi_systf_data
// structures for each system task and system function, and call
// vpi_register_systf() once for each structure". Doing that with the same three
// applications leaves the registry holding what the array method left, entry
// for entry - the two ways are two ways of registering the same thing, not two
// different registrations.
TEST_F(VpiMultipleSystfRegistration,
       SeparateStructuresRegisterWhatTheArrayDid) {
  SystfTestList list = MakeSystfTestList();
  RegisterFromList(list);
  std::vector<VpiSystfData> by_array = vpi_ctx_.RegisteredSystfs();

  VpiContext separate_ctx;
  SetGlobalVpiContext(&separate_ctx);

  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = "$my_task";
  task.calltf = &MyTaskCalltf;
  task.compiletf = &MyTaskComptf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);

  s_vpi_systf_data int_func = {};
  int_func.type = vpiSysFunc;
  int_func.sysfunctype = vpiIntFunc;
  int_func.tfname = "$my_int_func";
  int_func.calltf = &MyIntFuncCalltf;
  int_func.compiletf = &MyIntFuncComptf;
  ASSERT_NE(vpi_register_systf(&int_func), nullptr);

  s_vpi_systf_data sized_func = {};
  sized_func.type = vpiSysFunc;
  sized_func.sysfunctype = vpiSizedFunc;
  sized_func.tfname = "$my_sized_func";
  sized_func.calltf = &MySizedFuncCalltf;
  sized_func.compiletf = &MySizedFuncComptf;
  sized_func.sizetf = &MySizedFuncSizetf;
  ASSERT_NE(vpi_register_systf(&sized_func), nullptr);

  const std::vector<VpiSystfData>& by_structure =
      separate_ctx.RegisteredSystfs();
  ASSERT_EQ(by_structure.size(), by_array.size());
  for (size_t i = 0; i < by_array.size(); ++i) {
    EXPECT_STREQ(by_structure[i].tfname, by_array[i].tfname) << "entry " << i;
    EXPECT_EQ(by_structure[i].type, by_array[i].type) << "entry " << i;
    EXPECT_EQ(by_structure[i].sysfunctype, by_array[i].sysfunctype)
        << "entry " << i;
    EXPECT_EQ(by_structure[i].calltf, by_array[i].calltf) << "entry " << i;
    EXPECT_EQ(by_structure[i].compiletf, by_array[i].compiletf)
        << "entry " << i;
    EXPECT_EQ(by_structure[i].sizetf, by_array[i].sizetf) << "entry " << i;
  }
}

}  // namespace
}  // namespace delta
