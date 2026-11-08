#include <gtest/gtest.h>

#include <vector>

#include "fixture_simulator.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_object.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class VpiCompatibility : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  std::vector<vpiHandle> ScanAll(vpiHandle it) {
    std::vector<vpiHandle> seen;
    if (it == nullptr) return seen;
    while (vpiHandle h = vpi_scan(it)) seen.push_back(h);
    return seen;
  }

  VpiContext ctx_;
};

TEST_F(VpiCompatibility, ARegIterationOnAnArrayRetrievesElementsOfEveryKind) {
  VpiObject reg_word;
  reg_word.type = vpiReg;
  VpiObject integer_word;
  integer_word.type = vpiIntegerVar;
  VpiObject time_word;
  time_word.type = vpiTimeVar;

  VpiObject array;
  array.type = vpiRegArray;
  array.children = {&reg_word, &integer_word, &time_word};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiReg, VpiHandleOf(&array)));
  ASSERT_EQ(seen.size(), 3u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &reg_word);
  EXPECT_EQ(VpiObjectOf(seen[1]), &integer_word);
  EXPECT_EQ(VpiObjectOf(seen[2]), &time_word);
}

TEST_F(VpiCompatibility, ARegIterationOnAScopeIsUnaffected) {
  VpiObject reg;
  reg.type = vpiReg;
  VpiObject int_var;
  int_var.type = vpiIntegerVar;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg, &int_var};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiReg, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 1u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &reg);
}

TEST_F(VpiCompatibility, AVariablesIterationIncludesRegsAndRegArrays) {
  VpiObject reg;
  reg.type = vpiReg;
  VpiObject array;
  array.type = vpiRegArray;

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&reg, &array};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiVariables, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &reg);
  EXPECT_EQ(VpiObjectOf(seen[1]), &array);
}

TEST_F(VpiCompatibility, ARegArrayIterationIncludesArraysOfEveryVariable) {
  VpiObject int_word;
  int_word.type = vpiIntegerVar;
  VpiObject int_array;
  int_array.type = vpiRegArray;
  int_array.children = {&int_word};

  VpiObject real_word;
  real_word.type = vpiRealVar;
  VpiObject real_array;
  real_array.type = vpiRegArray;
  real_array.children = {&real_word};

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&int_array, &real_array};

  std::vector<vpiHandle> seen =
      ScanAll(vpi_iterate(vpiRegArray, VpiHandleOf(&scope)));
  ASSERT_EQ(seen.size(), 2u);
  EXPECT_EQ(VpiObjectOf(seen[0]), &int_array);
  EXPECT_EQ(VpiObjectOf(seen[1]), &real_array);
}

TEST_F(VpiCompatibility, MemoryAndMemoryWordAreRelationsRatherThanObjects) {
  VpiObject word;
  word.type = vpiReg;
  VpiObject memory;
  memory.type = vpiRegArray;
  memory.children = {&word};

  VpiObject scope;
  scope.type = vpiModule;
  scope.children = {&memory};

  std::vector<vpiHandle> memories =
      ScanAll(vpi_iterate(vpiMemory, VpiHandleOf(&scope)));
  ASSERT_EQ(memories.size(), 1u);
  EXPECT_EQ(VpiObjectOf(memories[0]), &memory);
  EXPECT_EQ(vpi_get(vpiType, memories[0]), vpiRegArray);

  std::vector<vpiHandle> words =
      ScanAll(vpi_iterate(vpiMemoryWord, VpiHandleOf(&memory)));
  ASSERT_EQ(words.size(), 1u);
  EXPECT_EQ(VpiObjectOf(words[0]), &word);
  EXPECT_EQ(vpi_get(vpiType, words[0]), vpiReg);
}

int g_array_kind = 0;
int g_integer_kind = 0;
int g_real_kind = 0;
int g_reg_kind = 0;
int g_arrays_seen = 0;

PLI_INT32 InspectKindsCalltf(PLI_BYTE8*) {
  vpiHandle mod = vpi_handle_by_name(VpiText("m1"), nullptr);
  if (mod == nullptr) return 0;

  vpiHandle mem = vpi_handle_by_name(VpiText("m1.mem"), nullptr);
  if (mem != nullptr) g_array_kind = vpi_get(vpiType, mem);
  vpiHandle i = vpi_handle_by_name(VpiText("m1.i"), nullptr);
  if (i != nullptr) g_integer_kind = vpi_get(vpiType, i);
  vpiHandle r = vpi_handle_by_name(VpiText("m1.r"), nullptr);
  if (r != nullptr) g_real_kind = vpi_get(vpiType, r);
  vpiHandle b = vpi_handle_by_name(VpiText("m1.b"), nullptr);
  if (b != nullptr) g_reg_kind = vpi_get(vpiType, b);

  vpiHandle it = vpi_iterate(vpiRegArray, mod);
  if (it == nullptr) return 0;
  while (vpi_scan(it) != nullptr) ++g_arrays_seen;
  return 0;
}

void RegisterKindProbe() {
  g_array_kind = 0;
  g_integer_kind = 0;
  g_real_kind = 0;
  g_reg_kind = 0;
  g_arrays_seen = 0;

  s_vpi_systf_data data = {};
  data.type = vpiSysTask;
  data.tfname = VpiText("$probe");
  data.calltf = &InspectKindsCalltf;
  ASSERT_NE(vpi_register_systf(&data), nullptr);
}

TEST_F(VpiCompatibility, ADesignsVariablesCarryTheKindsTheTableRequires) {
  RegisterKindProbe();

  SimFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  reg [7:0] mem [0:3];\n"
      "  integer i;\n"
      "  real r;\n"
      "  reg b;\n"
      "endmodule\n"
      "module t;\n"
      "  m m1();\n"
      "  initial $probe;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);

  EXPECT_EQ(g_array_kind, vpiRegArray);
  EXPECT_EQ(g_integer_kind, vpiIntegerVar);
  EXPECT_EQ(g_real_kind, vpiRealVar);
  EXPECT_EQ(g_reg_kind, vpiReg);
  EXPECT_EQ(g_arrays_seen, 1);
}

}  // namespace
}  // namespace delta
