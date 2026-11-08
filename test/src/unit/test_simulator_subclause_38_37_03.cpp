#include <gtest/gtest.h>

#include <cstring>
#include <vector>

#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

PLI_INT32 MyTaskCalltf(PLI_BYTE8*) { return 0; }
PLI_INT32 MyTaskComptf(PLI_BYTE8*) { return 0; }
PLI_INT32 MyIntFuncCalltf(PLI_BYTE8*) { return 0; }
PLI_INT32 MyIntFuncComptf(PLI_BYTE8*) { return 0; }
PLI_INT32 MySizedFuncCalltf(PLI_BYTE8*) { return 0; }
PLI_INT32 MySizedFuncComptf(PLI_BYTE8*) { return 0; }
PLI_INT32 MySizedFuncSizetf(PLI_BYTE8*) { return 8; }

struct SystfTestList {
  s_vpi_systf_data entries[4] = {};
};

SystfTestList MakeSystfTestList() {
  SystfTestList list;
  list.entries[0].type = vpiSysTask;
  list.entries[0].tfname = VpiText("$my_task");
  list.entries[0].calltf = &MyTaskCalltf;
  list.entries[0].compiletf = &MyTaskComptf;

  list.entries[1].type = vpiSysFunc;
  list.entries[1].sysfunctype = vpiIntFunc;
  list.entries[1].tfname = VpiText("$my_int_func");
  list.entries[1].calltf = &MyIntFuncCalltf;
  list.entries[1].compiletf = &MyIntFuncComptf;

  list.entries[2].type = vpiSysFunc;
  list.entries[2].sysfunctype = vpiSizedFunc;
  list.entries[2].tfname = VpiText("$my_sized_func");
  list.entries[2].calltf = &MySizedFuncCalltf;
  list.entries[2].compiletf = &MySizedFuncComptf;
  list.entries[2].sizetf = &MySizedFuncSizetf;

  return list;
}

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

TEST_F(VpiMultipleSystfRegistration, LoopStopsAtTheZeroFinalElement) {
  SystfTestList list = MakeSystfTestList();

  RegisterFromList(list);

  ASSERT_EQ(vpi_ctx_.RegisteredSystfs().size(), 3u);
  for (const s_vpi_systf_data& registered : vpi_ctx_.RegisteredSystfs()) {
    ASSERT_NE(registered.tfname, nullptr);
    EXPECT_NE(std::strcmp(registered.tfname, ""), 0);
  }
}

TEST_F(VpiMultipleSystfRegistration, ZeroFinalElementIsRefusedAsARegistration) {
  SystfTestList list = MakeSystfTestList();

  EXPECT_EQ(vpi_register_systf(&list.entries[3]), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());

  s_vpi_error_info info = {};
  EXPECT_EQ(vpi_chk_error(&info), vpiError);
  EXPECT_STREQ(info.message,
               "system task or function registration must carry a type of "
               "vpiSysTask or vpiSysFunc");
}

TEST_F(VpiMultipleSystfRegistration, TypeOutsideTheTwoConstantsIsRefused) {
  s_vpi_systf_data data = {};
  data.type = vpiSysFuncCall;
  data.tfname = VpiText("$neither");
  data.calltf = &MyTaskCalltf;
  data.compiletf = &MyTaskComptf;

  EXPECT_EQ(vpi_register_systf(&data), nullptr);
  EXPECT_TRUE(vpi_ctx_.RegisteredSystfs().empty());
}

TEST_F(VpiMultipleSystfRegistration,
       SeparateStructuresRegisterWhatTheArrayDid) {
  SystfTestList list = MakeSystfTestList();
  RegisterFromList(list);
  std::vector<s_vpi_systf_data> by_array = vpi_ctx_.RegisteredSystfs();

  VpiContext separate_ctx;
  SetGlobalVpiContext(&separate_ctx);

  s_vpi_systf_data task = {};
  task.type = vpiSysTask;
  task.tfname = VpiText("$my_task");
  task.calltf = &MyTaskCalltf;
  task.compiletf = &MyTaskComptf;
  ASSERT_NE(vpi_register_systf(&task), nullptr);

  s_vpi_systf_data int_func = {};
  int_func.type = vpiSysFunc;
  int_func.sysfunctype = vpiIntFunc;
  int_func.tfname = VpiText("$my_int_func");
  int_func.calltf = &MyIntFuncCalltf;
  int_func.compiletf = &MyIntFuncComptf;
  ASSERT_NE(vpi_register_systf(&int_func), nullptr);

  s_vpi_systf_data sized_func = {};
  sized_func.type = vpiSysFunc;
  sized_func.sysfunctype = vpiSizedFunc;
  sized_func.tfname = VpiText("$my_sized_func");
  sized_func.calltf = &MySizedFuncCalltf;
  sized_func.compiletf = &MySizedFuncComptf;
  sized_func.sizetf = &MySizedFuncSizetf;
  ASSERT_NE(vpi_register_systf(&sized_func), nullptr);

  const std::vector<s_vpi_systf_data>& by_structure =
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
